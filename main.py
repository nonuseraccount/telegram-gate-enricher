# -*- coding: utf-8 -*-
"""
Telegram Proxy Validator and Organizer
========================================

Author: Unavailable User (Conceptual Request)
Developed by: Gemini
Date: 2025-07-24
Version: 2.0.0

Project Overview:
-----------------
This script is a professional, multi-stage pipeline designed to process
Telegram proxies. It fetches proxy sources from URLs or local files, validates
each proxy's format, optionally normalizes its secret, checks connectivity,
enriches it with detailed geolocation data, and organizes the results into a
clean, sorted, and structured output.

It robustly handles various proxy URI schemes (tg://, https://t.me/) and
secret formats (Raw Hex, Fake-TLS/Base64).

Required Libraries:
-------------------
To run this script, you must install the necessary Python libraries:
pip install requests tqdm dnspython geoip2-database

Configuration:
--------------
The script is managed by two separate JSON files in the 'data' directory:
1.  `subscription_urls.json`: Defines the sources for the proxies.
2.  `preferences.json`: Controls the script's behavior, including the new
    `ENABLE_SECRET_NORMALIZATION` option.

Pipeline Stages:
----------------
1.  **Cleanup:** (Optional) Deletes the previous output directory.
2.  **Load:** The `DataLoader` fetches raw proxy data.
3.  **Process & Enrich:** The `TelegramProxyProcessor` validates and optionally
    normalizes each unique proxy.
4.  **Organize & Save:** The `OutputOrganizer` sorts and saves the final
    validated proxies into a structured output.

"""

import json
import logging
import os
import re
import sys
import shutil
import ipaddress
import socket
import base64
import binascii
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urlparse, parse_qs

# Third-party imports
try:
    import dns.resolver
    import geoip2.database
    import requests
    from tqdm.auto import tqdm
except ImportError as e:
    print(f"Error: A required library is missing. {e}")
    print("Please install all required libraries by running:")
    print("pip install requests tqdm dnspython geoip2-database")
    sys.exit(1)


# ================================================================
# 1. CONFIGURATION & CONSTANTS
# ================================================================

DATA_DIRECTORY = Path("data")
SUBSCRIPTION_URLS_FILE = DATA_DIRECTORY / "subscription_urls.json"
PREFERENCES_FILE = DATA_DIRECTORY / "preferences.json"

DEFAULT_PREFERENCES = {
    "ENABLE_CLEANUP_ON_START": True,
    "ENABLE_CONNECTIVITY_CHECK": True,
    "ENABLE_SECRET_VALIDATION": True,
    "ENABLE_SECRET_NORMALIZATION": True,
    "CONNECTIVITY_TIMEOUT": 2,
    "GEOIP_DATABASE_URL": "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
}

APP_LOGGER_NAME = "TelegramProxyPipeline"
OUTPUT_DIRECTORY = Path("output")
GEOIP_DIR = Path("geoip-lite")
GEOIP_DATABASE_PATH = GEOIP_DIR / "GeoLite2-Country.mmdb"

# ================================================================
# 2. UTILITY & HELPER CLASSES
# ================================================================

class InvalidSecretFormatError(ValueError):
    """Custom exception for errors in the proxy secret format."""
    pass

class ProxySecretNormalizer:
    """
    A class to normalize Telegram proxy secrets to their raw hex format.
    Handles both Base64 (Fake-TLS) and raw 'ee'/'dd'-prefixed hex secrets,
    outputting a pure hexadecimal string.
    """
    def __init__(self, secret: str):
        if not isinstance(secret, str) or not secret:
            raise InvalidSecretFormatError("Input secret must be a non-empty string.")
        self.original_secret: str = secret.strip()
        # A simple regex for 'ee' or 'dd' prefixed hex strings.
        self._hex_pattern = re.compile(r'^(ee|dd)[0-9a-fA-F]{32,}', re.IGNORECASE)

    def normalize(self) -> str:
        """
        Normalizes the secret to its raw 32-character hexadecimal representation.
        """
        if self._hex_pattern.match(self.original_secret):
            # It's a hex secret. Strip the prefix and return the next 32 characters.
            return self.original_secret[2:34].lower()
        
        try:
            # It's not a hex secret, so assume it's Base64.
            padded_secret = self.original_secret + '=' * (-len(self.original_secret) % 4)
            decoded_bytes = base64.urlsafe_b64decode(padded_secret)
            hex_secret = decoded_bytes.hex()
            
            # The actual secret is the first 16 bytes (32 hex characters).
            # Some old formats might have a 'dd' prefix *inside* the decoded hex.
            if hex_secret.lower().startswith('dd'):
                return hex_secret[2:34].lower()
            
            return hex_secret[:32].lower()
            
        except (binascii.Error, ValueError):
            # If it's neither a valid hex pattern nor decodable Base64, fail.
            raise InvalidSecretFormatError(
                f"Secret '{self.original_secret}' is not a recognized format."
            )

class ColorFormatter(logging.Formatter):
    """A custom logging formatter that adds color to log levels for readability."""
    GREY, RED, RESET = "\x1b[38;20m", "\x1b[31;20m", "\x1b[0m"
    FORMAT = "%(asctime)s [%(levelname)s] - %(message)s"
    FORMATS = { logging.INFO: GREY + FORMAT + RESET, logging.ERROR: RED + FORMAT + RESET }
    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt, datefmt="%Y-%m-%d %H:%M:%S")
        return formatter.format(record)

def setup_logger() -> logging.Logger:
    """Sets up an isolated, color-coded logger for the application."""
    logger = logging.getLogger(APP_LOGGER_NAME)
    logger.setLevel(logging.INFO)
    logger.propagate = False
    if logger.hasHandlers(): logger.handlers.clear()
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setFormatter(ColorFormatter())
    logger.addHandler(console_handler)
    return logger

def get_country_flag(country_code: str) -> str:
    """Converts a two-letter country code to its corresponding flag emoji."""
    if not country_code or country_code == "NA": return "🏴‍☠️"
    return "".join(chr(127397 + ord(char)) for char in country_code.upper())

def is_valid_ip_address(ip: str) -> bool:
    """Validates whether a string is a valid IPv4 or IPv6 address."""
    try:
        ipaddress.ip_address(ip)
        return True
    except ValueError:
        return False

# ================================================================
# 3. STAGE 1: DIRECTORY CLEANER
# ================================================================

class DirectoryCleaner:
    """Handles the cleanup of the output directory."""
    def __init__(self, directory: Path, log: logging.Logger):
        self.directory = directory
        self.log = log

    def run(self):
        self.log.info("--- Starting Cleanup Stage ---")
        if self.directory.exists():
            try:
                shutil.rmtree(self.directory)
                self.log.info(f"Successfully removed old output directory: '{self.directory}'")
            except OSError as e:
                self.log.error(f"Error removing directory {self.directory}: {e}")
        else:
            self.log.info("Output directory does not exist, no cleanup needed.")
        self.directory.mkdir(exist_ok=True)

# ================================================================
# 4. STAGE 2: CORE DATA LOADING CLASS
# ================================================================

class DataLoader:
    """A class dedicated to loading proxy data from local files or URLs."""
    def __init__(self, sources: Dict[str, str], log: logging.Logger):
        self.sources = sources
        self.log = log

    def _load_single_source(self, source_url: str, description: str) -> Dict[str, Any]:
        if not source_url:
            self.log.warning(f"Source for '{description}' is empty. Skipping.")
            return {}
        if source_url.lower().startswith(('http://', 'https://')):
            self.log.info(f"Fetching {description} from URL: {source_url}")
            try:
                with requests.get(source_url, stream=True, timeout=30) as r:
                    r.raise_for_status()
                    content = r.content
                    return json.loads(content.decode('utf-8'))
            except (requests.exceptions.RequestException, json.JSONDecodeError) as e:
                self.log.error(f"Failed to load from URL '{source_url}': {e}")
                return {}
        else:
            self.log.info(f"Loading {description} from local path: {source_url}")
            try:
                with open(source_url, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except (FileNotFoundError, json.JSONDecodeError) as e:
                self.log.error(f"Failed to load from file '{source_url}': {e}")
                return {}

    def run(self) -> Dict[str, Any]:
        self.log.info("--- Starting Data Loading Stage ---")
        channel_data = self._load_single_source(self.sources.get("channel_source", ""), "channel proxies")
        subscription_data = self._load_single_source(self.sources.get("subscription_source", ""), "subscription proxies")
        return {**channel_data, **subscription_data}

# ================================================================
# 5. STAGE 3: TELEGRAM PROXY PROCESSING & ENRICHMENT
# ================================================================

class TelegramProxyProcessor:
    """Parses, validates, and enriches Telegram proxy configurations."""
    def __init__(self, raw_data: Dict[str, Any], preferences: Dict[str, Any], log: logging.Logger):
        self.raw_data = raw_data
        self.preferences = preferences
        self.log = log
        self.geoip_reader = self._load_geoip_database()
        self.dns_resolver = dns.resolver.Resolver(configure=False)
        self.dns_resolver.nameservers = ['8.8.8.8', '1.1.1.1']
        self.failures = []

    def _load_geoip_database(self) -> Optional[geoip2.database.Reader]:
        GEOIP_DIR.mkdir(exist_ok=True)
        if not GEOIP_DATABASE_PATH.exists():
            self.log.info("GeoIP database not found. Attempting to download...")
            url = self.preferences.get("GEOIP_DATABASE_URL")
            if not url:
                self.log.error("GEOIP_DATABASE_URL not found in preferences.")
                return None
            try:
                with requests.get(url, stream=True, timeout=60) as r:
                    r.raise_for_status()
                    with GEOIP_DATABASE_PATH.open('wb') as f:
                        shutil.copyfileobj(r.raw, f)
                self.log.info(f"Successfully downloaded GeoIP database to '{GEOIP_DATABASE_PATH}'.")
            except Exception as e:
                self.log.error(f"Failed to download GeoIP database: {e}")
                return None
        try:
            return geoip2.database.Reader(GEOIP_DATABASE_PATH)
        except Exception as e:
            self.log.error(f"Failed to load GeoIP database: {e}")
            return None

    def _check_port_connectivity(self, ip: str, port: int) -> bool:
        timeout = self.preferences.get("CONNECTIVITY_TIMEOUT", 2)
        try:
            with socket.create_connection((ip, port), timeout=timeout):
                return True
        except (socket.timeout, socket.error):
            return False

    def _resolve_host(self, hostname: str) -> Optional[str]:
        if is_valid_ip_address(hostname):
            return hostname
        try:
            answers = self.dns_resolver.resolve(hostname, 'A', raise_on_no_answer=False)
            return answers[0].to_text() if answers else None
        except dns.exception.DNSException:
            return None

    def _get_country_info(self, ip: str) -> Dict[str, str]:
        """Gets country information (code, name, flag) from an IP address."""
        if not self.geoip_reader or not ip:
            return {"code": "NA", "name": "N/A", "flag": get_country_flag("NA")}
        try:
            response = self.geoip_reader.country(ip)
            code = response.country.iso_code or "NA"
            name = response.country.name or "N/A"
            return {"code": code, "name": name, "flag": get_country_flag(code)}
        except geoip2.errors.AddressNotFoundError:
            return {"code": "NA", "name": "N/A", "flag": get_country_flag("NA")}

    def run(self) -> List[Dict[str, Any]]:
        self.log.info("--- Starting Telegram Proxy Processing & Enrichment Stage ---")
        if not self.geoip_reader:
            self.log.warning("GeoIP database not loaded. Country information will be unavailable.")

        all_proxies_from_sources = set(p for pl in self.raw_data.values() if isinstance(pl, list) for p in pl if isinstance(p, str))
        self.log.info(f"Found {len(all_proxies_from_sources)} unique proxy links to process.")
        
        enriched_proxies = []
        for proxy_url in tqdm(all_proxies_from_sources, desc="Processing Proxies"):
            try:
                normalized_url = 'tg://proxy?' + proxy_url.split('?', 1)[1] if '/proxy?' in proxy_url else proxy_url
                parsed = urlparse(normalized_url)
                if not (parsed.scheme == 'tg' and parsed.netloc in ('proxy', 'socks')):
                    self.failures.append({"proxy": proxy_url, "reason": "Invalid proxy URI scheme"})
                    continue

                params = parse_qs(parsed.query)
                server, port, secret_str = params.get('server', [None])[0], params.get('port', [None])[0], params.get('secret', [None])[0]

                if not all([server, port, secret_str]):
                    self.failures.append({"proxy": proxy_url, "reason": "Missing server, port, or secret"})
                    continue
                
                secret_to_use = secret_str
                if self.preferences.get("ENABLE_SECRET_VALIDATION", True):
                    try:
                        normalizer = ProxySecretNormalizer(secret_str)
                        normalized_secret = normalizer.normalize()
                        
                        if self.preferences.get("ENABLE_SECRET_NORMALIZATION", True):
                            secret_to_use = normalized_secret
                        # If normalization is off, secret_to_use remains the original secret_str,
                        # but we know it's a valid format because normalize() didn't raise an exception.

                    except InvalidSecretFormatError as e:
                        self.failures.append({"proxy": proxy_url, "reason": str(e)})
                        continue

                resolved_ip = self._resolve_host(server)
                if not resolved_ip:
                    self.failures.append({"proxy": proxy_url, "reason": f"DNS resolution failed for host: {server}"})
                    continue
                
                if self.preferences.get("ENABLE_CONNECTIVITY_CHECK", False) and not self._check_port_connectivity(resolved_ip, int(port)):
                    self.failures.append({"proxy": proxy_url, "reason": f"Connectivity check failed for {resolved_ip}:{port}"})
                    continue

                country_info = self._get_country_info(resolved_ip)
                enriched_proxies.append({
                    "original_host": server,
                    "ip": resolved_ip,
                    "port": int(port),
                    "secret": secret_to_use,
                    "country_code": country_info["code"],
                    "country_name": country_info["name"],
                    "country_flag": country_info["flag"],
                    "tg_link": f"tg://proxy?server={resolved_ip}&port={port}&secret={secret_str}" # Use original secret for client
                })
            except Exception as e:
                self.failures.append({"proxy": proxy_url, "reason": f"General parsing error: {e}"})

        # De-duplicate proxies based on the final secret and connection info
        final_proxies = []
        seen_proxies = set()
        for proxy in enriched_proxies:
            proxy_identifier = (proxy['ip'], proxy['port'], proxy['secret'])
            if proxy_identifier not in seen_proxies:
                final_proxies.append(proxy)
                seen_proxies.add(proxy_identifier)

        self.log.info(f"Successfully processed and enriched {len(final_proxies)} unique proxies.")
        return final_proxies

# ================================================================
# 6. STAGE 4: OUTPUT ORGANIZER CLASS
# ================================================================

class OutputOrganizer:
    """Categorizes and saves validated proxies to JSON files in a sorted order."""
    def __init__(self, validated_proxies: List[Dict[str, Any]], base_path: Path, log: logging.Logger):
        self.proxies = validated_proxies
        self.base_path = base_path
        self.log = log

    def _save_json_file(self, path: Path, data: List[Dict[str, Any]]):
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('w', encoding='utf-8') as f:
            json.dump(data, f, indent=4, ensure_ascii=False)

    def run(self):
        self.log.info("--- Starting Output Organization and Saving Stage ---")
        if not self.proxies:
            self.log.warning("No validated proxies to save.")
            return

        # Sort all proxies by IP address for consistent output
        try:
            sorted_proxies = sorted(self.proxies, key=lambda p: ipaddress.ip_address(p['ip']))
        except (ValueError, KeyError):
            self.log.warning("Could not sort proxies by IP. Saving in default order.")
            sorted_proxies = self.proxies

        all_proxies_path = self.base_path / "all_valid_proxies.json"
        self.log.info(f"Saving all {len(sorted_proxies)} valid proxies to '{all_proxies_path}'...")
        self._save_json_file(all_proxies_path, sorted_proxies)

        self.log.info("Categorizing proxies by country...")
        country_groups = defaultdict(list)
        for proxy in sorted_proxies:
            country_groups[proxy.get("country_code", "NA")].append(proxy)

        country_dir = self.base_path / "countries"
        for country_code, proxy_list in tqdm(country_groups.items(), desc="Saving by Country"):
            country_file_path = country_dir / f"{country_code.lower()}.json"
            self._save_json_file(country_file_path, proxy_list)
        
        self.log.info(f"Saved proxies for {len(country_groups)} countries in '{country_dir}'.")

# ================================================================
# 7. MAIN EXECUTION BLOCK
# ================================================================

def setup_configuration(log: logging.Logger) -> Tuple[Optional[Dict], Optional[Dict]]:
    DATA_DIRECTORY.mkdir(exist_ok=True)
    if not PREFERENCES_FILE.exists():
        log.warning(f"Preferences file '{PREFERENCES_FILE}' not found. Creating with default settings.")
        with PREFERENCES_FILE.open('w', encoding='utf-8') as f: json.dump(DEFAULT_PREFERENCES, f, indent=4)
    
    if not SUBSCRIPTION_URLS_FILE.exists():
        log.warning(f"Subscription URLs file '{SUBSCRIPTION_URLS_FILE}' not found. Creating a sample.")
        sample_urls = {"channel_source": "data/archive_proxies_channel.json", "subscription_source": ""}
        with SUBSCRIPTION_URLS_FILE.open('w', encoding='utf-8') as f: json.dump(sample_urls, f, indent=4)
        
        sample_data_path = Path(sample_urls["channel_source"])
        if not sample_data_path.exists():
            with sample_data_path.open('w', encoding='utf-8') as f:
                json.dump({"sample_channel": ["https://t.me/proxy?server=proxy.example.com&port=443&secret=7gAAAAAAAAAAAAAAAAAAAAB3ZWIud2hhdHNhcHAuY29t"]}, f, indent=4)
        
        log.info("Default configuration files created. Please edit them and run again.")
        sys.exit(0)

    try:
        with PREFERENCES_FILE.open('r', encoding='utf-8') as f: preferences = json.load(f)
        with SUBSCRIPTION_URLS_FILE.open('r', encoding='utf-8') as f: subscriptions = json.load(f)
        return preferences, subscriptions
    except json.JSONDecodeError as e:
        log.error(f"Could not parse a config file: {e}")
        return None, None

def main():
    """Main function to orchestrate the data loading and processing pipeline."""
    log = setup_logger()
    log.info("Starting Telegram Proxy Processing Pipeline...")

    preferences, subscriptions = setup_configuration(log)
    if not preferences or not subscriptions: sys.exit(1)

    if preferences.get("ENABLE_CLEANUP_ON_START", False):
        DirectoryCleaner(OUTPUT_DIRECTORY, log).run()

    data_loader = DataLoader(sources=subscriptions, log=log)
    combined_proxies = data_loader.run()
    
    if not combined_proxies:
        log.error("Failed to load any proxy data. Check subscription_urls.json. Aborting.")
        sys.exit(1)
    log.info("--- Data Loading Complete ---")

    processor = TelegramProxyProcessor(raw_data=combined_proxies, preferences=preferences, log=log)
    validated_proxies = processor.run()
    log.info("--- Proxy Processing Complete ---")

    organizer = OutputOrganizer(validated_proxies, OUTPUT_DIRECTORY, log)
    organizer.run()

    if processor.failures:
        failures_output_path = OUTPUT_DIRECTORY / "processing_failures.json"
        with failures_output_path.open('w', encoding='utf-8') as f:
            json.dump(processor.failures, f, indent=4, ensure_ascii=False)
        log.error(f"Saved {len(processor.failures)} failed proxies to '{failures_output_path}'")

    log.info("--- Pipeline Finished Successfully ---")


if __name__ == "__main__":
    main()
