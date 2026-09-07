"""The AR-4 source edits have been applied; no further automatic edits are pending."""
from pathlib import Path

assert Path('.github/ar4-applied.txt').read_text().strip() == 'ar4-source-clients-v2'
