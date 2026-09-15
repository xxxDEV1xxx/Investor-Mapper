# Investor-Mapper

Download from investor data from:
https://www.sec.gov/data-research/sec-markets-data/form-13f-data-sets
Compile database with:
 python build_13f_db.py --data-dir "J:\\01mar2026-31may2026_form13f"
 Check investor data (start with around 20):
 python holders_map.py --preset quick20 --cusip 037833100 --name "Apple Inc."

 Other options:
python holders_map.py --preset leaders
python holders_map.py --preset big_to_small
python holders_map.py --preset small_to_big
python holders_map.py --preset big_three
python holders_map.py --preset everything
python holders_map.py --preset reverse --manager-name "VANGUARD GROUP INC"
python holders_map.py --preset quick20 --cusip 037833100 --name "Apple Inc."

Shows how much theyre invested in eachother, shows chains of wealth
