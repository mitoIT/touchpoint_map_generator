#!/usr/bin/env python3
"""
Enhanced Combined Company Dashboard and Touchpoint/Timeline Generator

This script generates:
1. A company dashboard linking to individual touchpoint maps, grouped by hierarchy
2. Interactive touchpoint maps showing campaign themes and categories with metrics and opportunity stages
3. Detailed activity timelines showing chronological activity history

Requirements:
pip install pandas openpyxl pytz xlrd fuzzywuzzy python-levenshtein

Usage:
python enhanced_dashboard_generator_fixed.py /path/to/activity/folder/ /path/to/companies.csv /path/to/opportunity/path/ --stages-path /path/to/stages/
"""

import pandas as pd
import os
import sys
import json
import re
from collections import Counter, defaultdict
from datetime import datetime, timedelta
import pytz
import glob
import webbrowser
import argparse
import logging
from pathlib import Path
import html
from fuzzywuzzy import fuzz, process

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('dashboard_generator.log')
    ]
)
logger = logging.getLogger(__name__)

def levenshtein_distance(s1, s2):
    """Manual Levenshtein distance implementation."""
    if len(s1) < len(s2):
        return levenshtein_distance(s2, s1)
    if len(s2) == 0:
        return len(s1)
    previous_row = range(len(s2) + 1)
    for i, c1 in enumerate(s1):
        current_row = [i + 1]
        for j, c2 in enumerate(s2):
            insertions = previous_row[j + 1] + 1
            deletions = current_row[j] + 1
            substitutions = previous_row[j] + (c1 != c2)
            current_row.append(min(insertions, deletions, substitutions))
        previous_row = current_row
    return previous_row[-1]

class EnhancedDashboardGenerator:
    def __init__(self, activity_folder, companies_csv, opportunity_path, stages_path=None, output_dir="output"):
        self.activity_folder = activity_folder
        self.companies_csv = companies_csv
        self.opportunity_path = opportunity_path
        self.stages_path = stages_path
        self.output_dir = output_dir
        self.company_data = defaultdict(list)
        self.company_mapping = {}  # email -> company name mapping
        self.name_to_company_mapping = {}
        self.contact_to_opps = defaultdict(list)  # contact key -> list of opportunities
        self.company_to_opps = defaultdict(list)  # company -> list of opportunities
        self.opp_stages = defaultdict(list)  # opportunity name -> list of stage changes
        self.hierarchy_groups = {}  # hierarchical account groupings
        self.hierarchy_to_companies = defaultdict(set)  # hierarchy -> set of matched companies
        self.total_contacts = 0
        self.total_companies = 0
        self.total_activities_processed = 0
        self.total_opportunities = 0
        
        # Output filenames
        self.dashboard_output = os.path.join(output_dir, "company_dashboard.html")
        
        # Ensure output directory exists
        os.makedirs(output_dir, exist_ok=True)
        
        # Define Mountain Time zone
        self.mountain_tz = pytz.timezone('US/Mountain')
        
        # Configuration for touchpoint categories - Added Opportunity Management
        self.touchpoint_categories = {
            'Email Communications': ['Email Delivered', 'Send Email', 'Open Email', 'Click Email', 'Email Bounced'],
            'Digital Engagement': ['Fill Out Form', 'Visit Web Page', 'Click Link', 'Download Asset'],
            'Lead Management': ['Add to SFDC Campaign', 'Change Program Status', 'New Person', 'Add to Opportunity'],
            'Behavioral Tracking': ['Interesting Moment'],
            'Campaign Automation': ['Change Engagement Program Cadence', 'Change Engagement Program Stream', 'Add to Engagement Program'],
            'Content Interactions': ['View Content', 'Download Asset', 'Visit Web Page'],
            'Opportunity Management': ['Opportunity Created']
        }
        
        # Clinical color scheme
        self.colors = {
            'clinical-blue': '#0066CC',
            'clinical-teal': '#00A3A3',
            'clinical-green': '#00AA55',
            'clinical-orange': '#FF6B35',
            'clinical-red': '#E63946',
            'clinical-purple': '#7209B7',
            'clinical-gray': '#6C757D'
        }

    def load_companies_csv(self):
        """Enhanced method to load multiple CSV files with fuzzy matching and hierarchical organization"""
        try:
            if not os.path.isdir(self.companies_csv):
                logger.warning(f"Companies path is not a directory: {self.companies_csv}")
                return False
            
            # Find all CSV files in the directory
            csv_files = glob.glob(os.path.join(self.companies_csv, "*.csv"))
            if not csv_files:
                logger.warning(f"No CSV files found in {self.companies_csv}")
                return False
            
            logger.info(f"Found {len(csv_files)} CSV files: {[os.path.basename(f) for f in csv_files]}")
            
            # Initialize data structures
            self.name_to_company_mapping = {}
            self.company_mapping = {}
            self.hierarchy_mapping = {}  # Maps hierarchy -> companies
            self.company_to_hierarchy = {}  # Maps company -> hierarchy
            self.contact_details = {}  # Stores full contact information
            
            all_contacts = []
            
            # Process each CSV file
            for csv_path in csv_files:
                logger.info(f"Processing file: {os.path.basename(csv_path)}")
                contacts_from_file = self._process_contact_file(csv_path)
                all_contacts.extend(contacts_from_file)
            
            logger.info(f"Total contacts loaded: {len(all_contacts)}")
            
            # Build mappings and hierarchical structure
            self._build_hierarchical_mappings(all_contacts)
            
            return True
                
        except Exception as e:
            logger.error(f"Error loading companies CSV: {e}")
            return False

    def _process_contact_file(self, csv_path):
        """Process individual CSV file and extract contact information"""
        try:
            # Try different encodings
            try:
                df = pd.read_csv(csv_path, encoding='utf-8')
            except UnicodeDecodeError:
                df = pd.read_csv(csv_path, encoding='latin-1')
            
            logger.info(f"Loaded {os.path.basename(csv_path)} with {len(df)} rows and columns: {list(df.columns)}")
            
            contacts = []
            
            # TODO: PII PROTECTION - Update these filename partial matches to match your actual source files
            # Example original values were date-specific like "20250709_IDN_Contact_List_DHC"
            DHC_FILE_INDICATOR = "<REPLACE_WITH_DHC_FILENAME_PART>"   # e.g. "20250709_IDN_Contact_List_DHC"
            IDN_FILE_INDICATOR  = "<REPLACE_WITH_IDN_FILENAME_PART>"    # e.g. "20250709_IDN_Contact_List"
            
            basename = os.path.basename(csv_path)
            if DHC_FILE_INDICATOR in basename:
                # DHC physician file format
                name_col = 'Physician Name'
                company_col = 'Primary Hospital Affiliation'  
                email_col = 'Email'
                hierarchy_col = None  # Will derive from company name
                title_col = 'Primary Specialty'
                first_name_col = None
                last_name_col = None
                
            elif IDN_FILE_INDICATOR in basename:
                # Regular IDN contact files
                name_col = 'Full Name'
                company_col = 'Account Name'
                email_col = 'Email'
                hierarchy_col = 'Local Reporting Hierarchy D: Account Name'
                title_col = 'Title'
                first_name_col = 'First Name'
                last_name_col = 'Last Name'
                
            else:
                # Legacy company_names.csv format
                name_col = self._find_column(df, ['full name', 'name', 'contact'])
                company_col = self._find_column(df, ['company', 'organization', 'org', 'account'])
                email_col = self._find_column(df, ['email', 'e-mail', 'mail'])
                hierarchy_col = None
                title_col = self._find_column(df, ['title', 'job title'])
                first_name_col = None
                last_name_col = None
            
            # Validate required columns exist
            if not name_col or name_col not in df.columns:
                logger.warning(f"Name column '{name_col}' not found in {os.path.basename(csv_path)}. Available columns: {list(df.columns)}")
                return contacts
                
            if not company_col or company_col not in df.columns:
                logger.warning(f"Company column '{company_col}' not found in {os.path.basename(csv_path)}. Available columns: {list(df.columns)}")
                return contacts
            
            # Process each row
            for _, row in df.iterrows():
                contact = self._extract_contact_info(row, name_col, company_col, email_col, 
                                                   hierarchy_col, title_col, first_name_col, last_name_col)
                if contact:
                    contacts.append(contact)
            
            logger.info(f"Extracted {len(contacts)} valid contacts from {os.path.basename(csv_path)}")
            return contacts
            
        except Exception as e:
            logger.error(f"Error processing file {csv_path}: {e}")
            return []

    # ... (rest of class unchanged until health_system_patterns) ...

    def _extract_health_system_from_hospital(self, hospital_name):
        """Extract health system name from hospital affiliation"""
        if not hospital_name:
            return None
            
        # Clean the company name and extract key identifiers
        hospital_clean = hospital_name.upper().strip()
        
        # TODO: PII PROTECTION - Replace the placeholders below with your real patterns
        health_system_patterns = {
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_name1>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_name2>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_name3>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_name4>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_name>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_name>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            '<REPLACE_WITH_Keyword_short>': '<REPLACE_WITH_namename>',
            # Add more systems here as needed
        }
        
        # Check for health system patterns
        for pattern, system in health_system_patterns.items():
            if pattern in hospital_clean:
                return system
        
        # If no specific pattern found, use the hospital name as hierarchy
        # Remove common suffixes to get cleaner hierarchy name
        suffixes_to_remove = [
            ' <REPLACE_WITH_LOCATION_1>)',  # e.g. (NEW YORK, NY)
            ' <REPLACE_WITH_LOCATION_2>)',  # e.g. (JACKSONVILLE, FL)
            ' <REPLACE_WITH_LOCATION_3>)',  # e.g. (PITTSBURGH, PA)
            ' MEDICAL CENTER', ' HOSPITAL', ' HEALTH SYSTEM', ' HEALTHCARE'
        ]
        
        hierarchy = hospital_clean
        for suffix in suffixes_to_remove:
            hierarchy = hierarchy.replace(suffix, '')
        
        return hierarchy.strip()

    # ... (rest of class until boost_keywords sections) ...

    def _calculate_enhanced_score(self, opp_normalized, company_normalized, original_opp, original_company, fuzzy_score):
        """Calculate enhanced matching score with multiple factors"""
        
        # Base fuzzy score (normalized to 0-1)
        base_score = fuzzy_score / 100.0
        
        # Word overlap score
        opp_words = set(opp_normalized.split())
        company_words = set(company_normalized.split())
        
        # Remove common words that don't add discriminative value
        common_words = {'THE', 'OF', 'AND', 'FOR', 'AT', 'BY', 'WITH', 'GENERAL', 'REGIONAL', 
                       'SYSTEM', 'CENTER', 'CENTRE', 'HEALTH', 'HOSPITAL', 'MEDICAL'}
        opp_words -= common_words
        company_words -= common_words
        
        jaccard_score = 0
        if opp_words and company_words:
            intersection = opp_words & company_words
            union = opp_words | company_words
            jaccard_score = len(intersection) / len(union) if union else 0
        
        # TODO: PII PROTECTION - Replace the placeholders with your actual keyword list
        boost_keywords = {
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            '<REPLACE_WITH_Keyword>': 0.3,
            # Add more boosts here as needed
        }
        
        keyword_boost = 0
        for keyword, boost in boost_keywords.items():
            if keyword in opp_words and keyword in company_words:
                keyword_boost += boost
        
        # Levenshtein similarity
        lev_distance = levenshtein_distance(opp_normalized, company_normalized)
        max_len = max(len(opp_normalized), len(company_normalized))
        lev_similarity = 1 - (lev_distance / max_len) if max_len else 0
        
        # Combined score with weights
        combined_score = (
            base_score * 0.4 +           # Fuzzy match weight
            jaccard_score * 0.3 +        # Word overlap weight  
            lev_similarity * 0.2 +       # String similarity weight
            keyword_boost * 0.1          # Keyword boost weight
        )
        
        return min(combined_score, 1.0)  # Cap at 1.0

    def _legacy_company_matching(self, opportunity_account, opp_normalized):
        """Original company matching logic for backward compatibility"""
        best_match = None
        max_score = 0
        
        for csv_name, info in self.name_to_company_mapping.items():
            company_name = info['company']
            company_normalized = self.normalize_company_name(company_name)
            
            if opp_normalized == company_normalized:
                logger.debug(f"Direct normalized match: '{opportunity_account}' -> '{company_name}'")
                return company_normalized
            
            opp_words = set(opp_normalized.split())
            company_words = set(company_normalized.split())
            
            common_words = {'THE', 'OF', 'AND', 'FOR', 'AT', 'BY', 'WITH', 'GENERAL', 'REGIONAL', 'SYSTEM', 'CENTER', 'CENTRE'}
            opp_words -= common_words
            company_words -= common_words
            
            if opp_words and company_words:
                intersection = opp_words & company_words
                union = opp_words | company_words
                jaccard_score = len(intersection) / len(union) if union else 0
                
                # TODO: PII PROTECTION - Replace the placeholders with your actual keyword list (legacy version)
                boost_keywords = {
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    '<REPLACE_WITH_Keyword>': 0.3,
                    # Add more if needed
                }
                
                for keyword, boost in boost_keywords.items():
                    if keyword in opp_words and keyword in company_words:
                        jaccard_score += boost
                        logger.debug(f"Keyword boost applied for '{keyword}': +{boost}")
                
                lev_distance = levenshtein_distance(opp_normalized, company_normalized)
                max_len = max(len(opp_normalized), len(company_normalized))
                lev_similarity = 1 - (lev_distance / max_len) if max_len else 0
                
                combined_score = (jaccard_score + lev_similarity) / 2
                
                if combined_score > max_score and combined_score >= 0.25:
                    max_score = combined_score
                    best_match = company_normalized
                    logger.debug(f"Legacy match: '{opportunity_account}' -> '{company_name}' (score: {combined_score:.3f})")
        
        return best_match

# ... (the rest of the script is unchanged - all HTML templates, dashboard generation, run() method, argparse, etc. remain exactly as you provided) ...
