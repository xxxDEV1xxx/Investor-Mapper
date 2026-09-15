"""
holders_map.py -- Query 13f_holdings.db (built by build_13f_db.py) and
render a folium "trading card" map. No TSV parsing here at all -- just SQL
against the master file, so this is fast every time.
Click a dot -> full holder detail opens in a scrollable side panel, same
pattern as REFM.py's click-panel (not a default Leaflet popup).
Usage:
    python holders_map.py --find-cusip "APPLE"
    python holders_map.py --ticker AAPL --top 20
    python holders_map.py --cusip 037833100 --name "Apple Inc." --top 20
"""
import argparse
import colorsys
import math
import os
import re
import sqlite3
import sys
import threading
import time
import webbrowser
import http.server
import socketserver
from pathlib import Path
import pandas as pd
import folium
from folium.plugins import MarkerCluster
DB_PATH = Path(r"J:\True-Sentinel\Investor-Mapper\13f_holdings.db")
# ticker -> verified CUSIP (confirmed via --find-cusip against real data)
COMPANIES = {
    "AAPL": {"cusip": "037833100", "name": "Apple Inc."},
    "AMZN": {"cusip": "023135106", "name": "Amazon.com Inc"},
}
def find_cusip_data(conn, pattern):
    """Reusable by both the CLI and the FastAPI route -- returns a DataFrame."""
    return pd.read_sql_query(
        "SELECT cusip, nameofissuer, COUNT(*) as rows "
        "FROM holdings WHERE nameofissuer LIKE ? "
        "GROUP BY cusip, nameofissuer ORDER BY rows DESC LIMIT 100",
        conn, params=[f"%{pattern}%"])
def find_cusip(conn, pattern):
    df = find_cusip_data(conn, pattern)
    if df.empty:
        print(f"[NOTE] No matches for {pattern!r}.")
        return
    print(f"\n{'CUSIP':<12} {'ROWS':>8}  NAMEOFISSUER (as filed)")
    print("-" * 60)
    for _, r in df.iterrows():
        print(f"{r['cusip']:<12} {r['rows']:>8,}  {r['nameofissuer']}")
    print("\n[NOTE] The CUSIP with the most rows is almost always the right one.")
def load_holdings(conn, cusip, top_n):
    query = """
    SELECT h.accession_number, h.nameofissuer, h.value, h.sshprnamt,
           f.report_period, f.is_amendment, f.manager_name, f.city,
           f.state_or_country, f.lat, f.lon,
           s.table_value_total
    FROM holdings h
    LEFT JOIN filers  f ON f.accession_number = h.accession_number
    LEFT JOIN summary s ON s.accession_number = h.accession_number
    WHERE h.cusip = ?
    ORDER BY h.value DESC
    """
    df = pd.read_sql_query(query, conn, params=[cusip])
    if df.empty:
        sys.exit(f"[ERROR] No holdings found for CUSIP {cusip} in the master DB. "
                  f"Run build_13f_db.py first, or check the CUSIP with --find-cusip.")
    # Rough amendment handling: keep the largest position per manager name.
    df = (df.sort_values("value", ascending=False)
            .drop_duplicates(subset=["manager_name"], keep="first"))
    df["pct_of_portfolio"] = df["value"] / df["table_value_total"] * 100
    df = df.sort_values("value", ascending=False).reset_index(drop=True)
    if top_n and top_n > 0:
        df = df.head(top_n).reset_index(drop=True)
    df["rank"] = df.index + 1
    return df
# ---------------------------------------------------------------------------
# CROSS-HOLDING LINES -- when a plotted holder is ITSELF a public company
# that another plotted holder also owns shares of, draw a line between them.
# ---------------------------------------------------------------------------
_SUFFIX_RE = re.compile(r'\b(INC|INCORPORATED|CORP|CORPORATION|CO|COMPANY|'
                         r'LLC|LTD|LIMITED|GROUP|HOLDINGS|HOLDING|PLC|LP|THE)\b\.?',
                         re.I)
_PUNCT_RE = re.compile(r'[^A-Z0-9]+')
def normalize_name(name):
    """Exact-after-normalization matching, not fuzzy substring -- loose
    substring matching produced false hits (Apple Inc vs Maui Land &
    Pineapple Inc) when testing --find-cusip earlier, so this stays
    conservative on purpose."""
    if not name:
        return ""
    s = _SUFFIX_RE.sub(' ', str(name).upper())
    s = _PUNCT_RE.sub(' ', s)
    return ' '.join(s.split())
def spectrum_color(pct):
    """pct in [0,1]: 1.0 = highest value on this render (red),
    0.0 = lowest value on this render (magenta/violet).

    Matches the GNSS mapper track-path gradient exactly:
    red → orange → yellow → green → cyan → blue → magenta
    (HSV hue 0° … ~300°)."""
    pct = max(0.0, min(1.0, float(pct)))
    hue = (1.0 - pct) * 0.83  # 0.00 = red, 0.83 ≈ magenta
    r, g, b = colorsys.hsv_to_rgb(hue, 1.0, 1.0)
    return '#{:02x}{:02x}{:02x}'.format(int(r * 255), int(g * 255), int(b * 255))
def _bearing_deg(lat1, lon1, lat2, lon2):
    """Initial bearing from point 1 → point 2 (degrees, 0 = north, clockwise)."""
    φ1, φ2 = math.radians(lat1), math.radians(lat2)
    Δλ = math.radians(lon2 - lon1)
    y = math.sin(Δλ) * math.cos(φ2)
    x = math.cos(φ1) * math.sin(φ2) - math.sin(φ1) * math.cos(φ2) * math.cos(Δλ)
    return (math.degrees(math.atan2(y, x)) + 360) % 360
def _point_along(lat1, lon1, lat2, lon2, fraction):
    """Linear interpolation. fraction=0 → start, fraction=1 → end."""
    return (
        lat1 + (lat2 - lat1) * fraction,
        lon1 + (lon2 - lon1) * fraction,
    )
def _fmt_value(v):
    """Compact dollar formatting for legend / tooltips."""
    if v is None or (isinstance(v, float) and math.isnan(v)):
        return "—"
    v = float(v)
    if abs(v) >= 1e12:
        return f"${v/1e12:.2f}T"
    if abs(v) >= 1e9:
        return f"${v/1e9:.2f}B"
    if abs(v) >= 1e6:
        return f"${v/1e6:.1f}M"
    if abs(v) >= 1e3:
        return f"${v/1e3:.0f}K"
    return f"${v:,.0f}"
def _arrow_wing_points(from_latlon, to_latlon, wing_len=0.55, spread_deg=18):
    """Return two lat/lon points that form long narrow arrow arms at the
    'to' end. Arms are pure map geometry so they stay locked to the line
    at every zoom/pan.

    wing_len is in degrees (~0.55° ≈ 60 km) — long thin chevron arms.
    spread_deg is half-angle between the two arms (narrow = pointed)."""
    lat1, lon1 = from_latlon
    lat2, lon2 = to_latlon
    # unit vector from tip back toward source
    dlat, dlon = lat1 - lat2, lon1 - lon2
    length = math.hypot(dlat, dlon) or 1e-9
    ulat, ulon = dlat / length, dlon / length
    # perpendicular
    plat, plon = -ulon, ulat
    rad = math.radians(spread_deg)
    c, s = math.cos(rad), math.sin(rad)
    # scale wing length: keep arms readable on short segments too
    wl = min(wing_len, max(0.18, length * 0.12))
    w1 = (lat2 + (ulat * c + plat * s) * wl,
          lon2 + (ulon * c + plon * s) * wl)
    w2 = (lat2 + (ulat * c - plat * s) * wl,
          lon2 + (ulon * c - plon * s) * wl)
    return w1, w2


def add_arrowed_line(map_or_group, from_latlon, to_latlon, color,
                     weight=2.5, opacity=0.9, tooltip=None):
    """Draw a PolyLine from → to with long narrow arrow arms drawn as
    geometry at the 'to' end (stays locked to the line at all zooms)."""
    pl = folium.PolyLine(
        locations=[from_latlon, to_latlon],
        color=color,
        weight=weight,
        opacity=opacity,
        tooltip=tooltip,
    )
    pl.add_to(map_or_group)

    # Arrow arms as two PolyLine segments from tip → wing (anchored geometry)
    w1, w2 = _arrow_wing_points(from_latlon, to_latlon)
    tip = to_latlon
    for wing in (w1, w2):
        folium.PolyLine(
            locations=[tip, wing],
            color=color,
            weight=max(1.5, weight * 0.85),
            opacity=opacity,
            line_cap="round",
        ).add_to(map_or_group)

    return pl
def find_cross_holdings(conn, plotted_df, max_lines=300):
    """Among currently-plotted holders, find pairs where one IS a public
    company another plotted holder also owns shares of. Returns lines
    colored by rank among the lines drawn (highest value = red, lowest =
    magenta). Marks mutual pairs (A↔B) with mutual=True."""
    plotted = plotted_df.dropna(subset=["lat", "lon"]).drop_duplicates("manager_name")
    plotted_set = set(plotted["manager_name"])
    norm_to_orig = {normalize_name(n): n for n in plotted_set}
    latlon = plotted.set_index("manager_name")[["lat", "lon"]].to_dict("index")
    issuers = pd.read_sql_query(
        "SELECT nameofissuer, cusip, COUNT(*) as n FROM holdings "
        "GROUP BY nameofissuer, cusip", conn)
    issuers["norm"] = issuers["nameofissuer"].apply(normalize_name)
    issuer_cusip = (issuers.sort_values("n", ascending=False)
                            .drop_duplicates(subset=["norm"])
                            .set_index("norm")["cusip"].to_dict())
    self_cusip = {orig: issuer_cusip[norm]
                  for norm, orig in norm_to_orig.items() if norm in issuer_cusip}
    if not self_cusip:
        return [], {}
    raw = []
    for target_name, target_cusip in self_cusip.items():
        holders = pd.read_sql_query(
            "SELECT h.value, f.manager_name, s.table_value_total "
            "FROM holdings h "
            "JOIN filers f ON f.accession_number = h.accession_number "
            "LEFT JOIN summary s ON s.accession_number = h.accession_number "
            "WHERE h.cusip = ?", conn, params=[target_cusip])
        holders = (holders.sort_values("value", ascending=False)
                           .drop_duplicates(subset=["manager_name"]))
        for _, r in holders.iterrows():
            src = r["manager_name"]
            if src == target_name or src not in plotted_set:
                continue
            raw.append({
                "from": src, "to": target_name,
                "value": r["value"],
                "portfolio": r["table_value_total"],
            })
    if not raw:
        return [], {}

    # Directed edge map: (from,to) -> {value, portfolio}
    edge = {}
    for r in raw:
        edge[(r["from"], r["to"])] = {
            "value": r["value"],
            "portfolio": r["portfolio"],
        }
    mutual_set = {(a, b) for (a, b) in edge if (b, a) in edge}

    raw.sort(key=lambda x: x["value"] or 0, reverse=True)
    raw = raw[:max_lines]

    n = len(raw)
    lines = []
    for i, r in enumerate(raw):
        pct = 1.0 if n == 1 else 1.0 - (i / (n - 1))
        is_mutual = (r["from"], r["to"]) in mutual_set
        counter = edge.get((r["to"], r["from"])) if is_mutual else None
        lines.append({
            "from_latlon": (latlon[r["from"]]["lat"], latlon[r["from"]]["lon"]),
            "to_latlon": (latlon[r["to"]]["lat"], latlon[r["to"]]["lon"]),
            "from_name": r["from"], "to_name": r["to"],
            "value": r["value"],
            "portfolio": r["portfolio"],
            "color": spectrum_color(pct),
            "mutual": is_mutual,
            "mutual_value": counter["value"] if counter else None,
            "mutual_portfolio": counter["portfolio"] if counter else None,
        })

    # Cycles + mutual ratio buckets (from the full directed edge set, not the line cap)
    cycles = find_holding_cycles(edge, latlon, max_len=9001, max_cycles=9001)
    ratio_stats = mutual_ratio_buckets(edge)
    return lines, {"cycles": cycles, "ratio_stats": ratio_stats}


def find_holding_cycles(edge, latlon, max_len=9001, max_cycles=9001):
    """Find simple directed cycles of length 3..max_len among cross-holding
    nodes. A cycle is A→B→C→…→A where each arrow is a real 13F position.
    Returns list of {nodes, edges, min_value, total_value, length}."""
    # adjacency: from -> [(to, value), ...]
    adj = {}
    for (a, b), info in edge.items():
        adj.setdefault(a, []).append((b, info["value"] or 0))

    found = []
    seen_norm = set()  # canonical rotation of cycle to dedupe

    def normalize(path):
        # path is closed without repeating start at end
        i = path.index(min(path))
        rot = path[i:] + path[:i]
        rev = list(reversed(path))
        j = rev.index(min(rev))
        rot_rev = rev[j:] + rev[:j]
        return tuple(rot) if rot <= rot_rev else tuple(rot_rev)

    def dfs(start, node, path, path_set):
        if len(found) >= max_cycles:
            return
        if len(path) > max_len:
            return
        for nxt, val in adj.get(node, []):
            if nxt == start and len(path) >= 3:
                key = normalize(path)
                if key not in seen_norm:
                    seen_norm.add(key)
                    # collect edge values along the cycle
                    cyc_edges = []
                    total = 0.0
                    mn = float("inf")
                    for i in range(len(path)):
                        a = path[i]
                        b = path[(i + 1) % len(path)]
                        v = (edge.get((a, b)) or {}).get("value") or 0
                        cyc_edges.append({"from": a, "to": b, "value": v})
                        total += v
                        mn = min(mn, v)
                    # centroid for panel anchor
                    pts = [latlon[n] for n in path if n in latlon]
                    if pts:
                        clat = sum(p["lat"] for p in pts) / len(pts)
                        clon = sum(p["lon"] for p in pts) / len(pts)
                    else:
                        clat = clon = None
                    found.append({
                        "nodes": list(path),
                        "edges": cyc_edges,
                        "length": len(path),
                        "min_value": mn if mn != float("inf") else 0,
                        "total_value": total,
                        "lat": clat,
                        "lon": clon,
                    })
                continue
            if nxt in path_set:
                continue
            if len(path) + 1 > max_len:
                continue
            path.append(nxt)
            path_set.add(nxt)
            dfs(start, nxt, path, path_set)
            path_set.remove(nxt)
            path.pop()

    nodes = sorted(adj.keys())
    for start in nodes:
        if len(found) >= max_cycles:
            break
        dfs(start, start, [start], {start})

    # Prefer longer / larger cycles first for display
    found.sort(key=lambda c: (c["length"], c["total_value"]), reverse=True)
    return found[:max_cycles]


def mutual_ratio_buckets(edge):
    """Count undirected mutual pairs by ratio / size-band heuristics."""
    seen = set()
    buckets = {
        "near_sym": 0,      # <5×
        "mod_asym": 0,      # 5–20×
        "high_asym": 0,     # 20–100×
        "extreme_asym": 0,  # ≥100×
        "billions_vs_hm": 0,
        "both_light": 0,
        "n_mutual": 0,
    }
    for (a, b), info in edge.items():
        if (b, a) not in edge:
            continue
        key = frozenset([a, b])
        if key in seen:
            continue
        seen.add(key)
        buckets["n_mutual"] += 1
        av = info["value"] or 0
        bv = edge[(b, a)]["value"] or 0
        ap = info.get("portfolio")
        bp = edge[(b, a)].get("portfolio")
        hz = mutual_heuristics(av, bv, ap, bp)
        r = hz["ratio"]
        if r is None:
            buckets["extreme_asym"] += 1
        elif r < 5:
            buckets["near_sym"] += 1
        elif r < 20:
            buckets["mod_asym"] += 1
        elif r < 100:
            buckets["high_asym"] += 1
        else:
            buckets["extreme_asym"] += 1
        if "BILLIONS vs ≤HUNDREDS-M" in hz["flags"]:
            buckets["billions_vs_hm"] += 1
        if "BOTH LIGHT (<0.5% books)" in hz["flags"]:
            buckets["both_light"] += 1
    return buckets


def mutual_heuristics(a_val, b_val, a_port=None, b_port=None):
    """Structural flags for a mutual (A↔B) edge pair. No narrative —
    just measurable asymmetry and relative commitment."""
    a_val = float(a_val or 0)
    b_val = float(b_val or 0)
    hi, lo = max(a_val, b_val), min(a_val, b_val)
    ratio = (hi / lo) if lo > 0 else float("inf")

    a_pct = (100.0 * a_val / a_port) if a_port and a_port > 0 else None
    b_pct = (100.0 * b_val / b_port) if b_port and b_port > 0 else None

    flags = []
    if ratio >= 100:
        flags.append("EXTREME ASYM (≥100×)")
    elif ratio >= 20:
        flags.append("HIGH ASYM (≥20×)")
    elif ratio >= 5:
        flags.append("MOD ASYM (≥5×)")
    else:
        flags.append("NEAR-SYMMETRIC (<5×)")

    if a_pct is not None and a_pct >= 5:
        flags.append(f"A HEAVY ({a_pct:.1f}% book)")
    if b_pct is not None and b_pct >= 5:
        flags.append(f"B HEAVY ({b_pct:.1f}% book)")
    if a_pct is not None and b_pct is not None:
        if a_pct < 0.5 and b_pct < 0.5:
            flags.append("BOTH LIGHT (<0.5% books)")
        elif min(a_pct, b_pct) < 0.25 and max(a_pct, b_pct) >= 2:
            flags.append("ONE LIGHT / ONE MATERIAL")

    if hi >= 1e9 and lo >= 1e7 and lo < 5e8:
        flags.append("BILLIONS vs ≤HUNDREDS-M")

    return {
        "ratio": ratio if ratio != float("inf") else None,
        "a_pct": a_pct,
        "b_pct": b_pct,
        "flags": flags,
        "hi": hi,
        "lo": lo,
    }
# ---------------------------------------------------------------------------
# PRESET SYSTEM
# ---------------------------------------------------------------------------
PRESETS = {
    "quick20":     {"label": "Quick Look \u2014 Top 20",          "mode": "company", "top": 20,  "lines": False},
    "full":        {"label": "Full Holder Map",                   "mode": "company", "top": 0,   "lines": True},
    "whales":      {"label": "Mega Holders Only",                 "mode": "company", "top": 0,   "lines": True,  "min_value": 5e9},
    "longtail":    {"label": "Long Tail \u2014 Small Holders",     "mode": "company", "top": 0,   "lines": False, "max_value": 5e7, "cap": 200},
    "reverse":     {"label": "Reverse View \u2014 What They Hold", "mode": "manager", "top": 25,  "table_only": True},
    "leaders":     {"label": "Market Cap Leaders",                "mode": "market",  "companies": 25,  "holders_each": 5},
    "big_to_small":{"label": "Big Money \u2192 Small Caps",        "mode": "cross",   "direction": "big_to_small", "limit": 9001},
    "small_to_big":{"label": "Small Fish \u2192 Giants",           "mode": "cross",   "direction": "small_to_big", "limit": 9001},
    "big_three":   {"label": "The Big Three Footprint",          "mode": "cross",   "direction": "value", "limit": 9001,
                     "name_filter": ["VANGUARD", "BLACKROCK", "STATE STREET"]},
    "everything":  {"label": "Everything, Everywhere",           "mode": "market",  "companies": 150, "holders_each": 3},
    "custom":      {"label": "Custom Search",                    "mode": "company", "top": 20,  "lines": True},
}
def top_companies_by_value(conn, limit=25):
    return pd.read_sql_query("""
        SELECT cusip, nameofissuer, SUM(value) as total_value, COUNT(*) as n_holders
        FROM holdings GROUP BY cusip
        HAVING n_holders >= 5
        ORDER BY total_value DESC LIMIT ?
    """, conn, params=[limit])
def market_leaders_holdings(conn, n_companies=25, holders_each=5):
    """Top N companies by institutional value, each with its top-K holders."""
    leaders = top_companies_by_value(conn, n_companies)
    frames = []
    for _, row in leaders.iterrows():
        h = load_holdings(conn, row["cusip"], holders_each)
        if not h.empty:
            h["target_company"] = row["nameofissuer"]
            frames.append(h)
    return pd.concat(frames, ignore_index=True) if frames else pd.DataFrame()
def load_holdings_by_manager(conn, manager_name, top_n=25):
    """TABLE ONLY -- see PRESETS['reverse']. No issuer HQ data exists to map this."""
    query = """
    SELECT h.value, h.sshprnamt, h.nameofissuer, h.cusip, f.manager_name
    FROM holdings h
    JOIN filers f ON f.accession_number = h.accession_number
    WHERE f.manager_name = ?
    ORDER BY h.value DESC
    """
    df = pd.read_sql_query(query, conn, params=[manager_name])
    if df.empty:
        return df
    if top_n and top_n > 0:
        df = df.head(top_n).reset_index(drop=True)
    df["rank"] = df.index + 1
    return df
def issuer_size_map(conn, cusips):
    """SUM(value) per cusip -- proxy for institutional size, restricted to a
    cusip list to keep this cheap against a 3.8M-row table."""
    placeholders = ",".join("?" * len(cusips))
    q = f"SELECT cusip, SUM(value) as total_value FROM holdings WHERE cusip IN ({placeholders}) GROUP BY cusip"
    return dict(conn.execute(q, cusips).fetchall())
def self_cusip_universe(conn):
    """Companies that are BOTH a 13F issuer AND themselves a 13F filer --
    the only issuers we can geocode as a 'target', since Form 13F never
    discloses an issuer's address, only a filer's."""
    filers = pd.read_sql_query("SELECT DISTINCT manager_name FROM filers", conn)
    issuers = pd.read_sql_query(
        "SELECT nameofissuer, cusip, COUNT(*) as n FROM holdings GROUP BY nameofissuer, cusip", conn)
    filers["norm"] = filers["manager_name"].apply(normalize_name)
    issuers["norm"] = issuers["nameofissuer"].apply(normalize_name)
    issuer_best = issuers.sort_values("n", ascending=False).drop_duplicates(subset=["norm"])
    return filers.merge(issuer_best, on="norm", how="inner")  # manager_name, norm, nameofissuer, cusip, n
def build_relationship_card_html(name, city, state, value, role_label):
    val = f"${value:,.0f}" if pd.notna(value) else "\u2014"
    return f"""
<b style="font-size:13px">{name}</b><br>
<span style="font-size:11px;color:#6b5a44;">{city or ''}, {state or ''}</span>
<hr style="border-top:1px solid #3b2f22;">
<div class="card-stat-label">{role_label}</div>
<div class="card-stat-value">{val}</div>
<div style="font-size:10px;color:#6b5a44;margin-top:6px;">Source: SEC Form 13F (EDGAR)</div>
"""
def cross_scan(conn, direction="big_to_small", limit=9001, name_filter=None):
    """Market-wide cross-holding scan, restricted to self_cusip_universe --
    the only set geocodable on BOTH ends. direction: 'big_to_small',
    'small_to_big', or 'value' (just biggest positions, for a name_filter
    like the Big Three)."""
    universe = self_cusip_universe(conn)
    if universe.empty:
        return pd.DataFrame(), []
    cusips = universe["cusip"].tolist()
    sizes = issuer_size_map(conn, cusips)
    placeholders = ",".join("?" * len(cusips))
    holdings = pd.read_sql_query(f"""
        SELECT h.value, h.cusip as to_cusip, h.nameofissuer as to_issuer,
               f.manager_name as from_name, f.lat as from_lat, f.lon as from_lon,
               f.city as from_city, f.state_or_country as from_state
        FROM holdings h
        JOIN filers f ON f.accession_number = h.accession_number
        WHERE h.cusip IN ({placeholders})
    """, conn, params=cusips)
    norm_to_cusip = dict(zip(universe["norm"], universe["cusip"]))
    holdings["from_norm"] = holdings["from_name"].apply(normalize_name)
    holdings = holdings[holdings["from_norm"].isin(norm_to_cusip)].copy()
    holdings["from_cusip"] = holdings["from_norm"].map(norm_to_cusip)
    holdings = holdings[holdings["from_cusip"] != holdings["to_cusip"]]
    holdings["from_size"] = holdings["from_cusip"].map(sizes)
    holdings["to_size"] = holdings["to_cusip"].map(sizes)
    holdings = holdings.dropna(subset=["from_size", "to_size", "from_lat", "from_lon"])
    if holdings.empty:
        return pd.DataFrame(), []
    if name_filter:
        pattern = "|".join(name_filter)
        holdings = holdings[holdings["from_name"].str.contains(pattern, case=False, na=False)]
    if direction in ("big_to_small", "small_to_big"):
        holdings["size_ratio"] = holdings["from_size"] / holdings["to_size"].replace(0, pd.NA)
        holdings = holdings.sort_values("size_ratio", ascending=(direction == "small_to_big"))
    else:
        holdings = holdings.sort_values("value", ascending=False)
    top = holdings.head(limit).copy()
    if top.empty:
        return pd.DataFrame(), []
    universe_by_cusip = universe.set_index("cusip")["manager_name"].to_dict()
    top["to_name"] = top["to_cusip"].map(universe_by_cusip)
    filer_locs = pd.read_sql_query(
        "SELECT manager_name, lat, lon, city, state_or_country FROM filers", conn
    ).drop_duplicates(subset=["manager_name"]).dropna(subset=["lat", "lon"])
    loc_map = filer_locs.set_index("manager_name").to_dict("index")

    # Mutual detection among the selected edges
    edge_val = {}
    for _, r in top.iterrows():
        edge_val[(r["from_name"], r["to_name"])] = r["value"]
    mutual_set = {(a, b) for (a, b) in edge_val if (b, a) in edge_val}

    lines = []
    node_value = {}
    n = len(top)
    for i, (_, r) in enumerate(top.iterrows()):
        to_loc = loc_map.get(r["to_name"])
        if not to_loc:
            continue
        pct = 1.0 if n == 1 else 1.0 - (i / (n - 1))
        is_mutual = (r["from_name"], r["to_name"]) in mutual_set
        counter = edge_val.get((r["to_name"], r["from_name"])) if is_mutual else None
        lines.append({
            "from_latlon": (r["from_lat"], r["from_lon"]),
            "to_latlon": (to_loc["lat"], to_loc["lon"]),
            "from_name": r["from_name"], "to_name": r["to_issuer"],
            "value": r["value"], "color": spectrum_color(pct),
            "mutual": is_mutual, "mutual_value": counter,
        })
        node_value[r["from_name"]] = max(node_value.get(r["from_name"], 0), r["value"])
        node_value[r["to_name"]] = max(node_value.get(r["to_name"], 0), r["value"])
    involved = list(node_value.keys())
    markers = filer_locs[filer_locs["manager_name"].isin(involved)].copy()
    markers["value"] = markers["manager_name"].map(node_value)
    markers = markers.sort_values("value", ascending=False).reset_index(drop=True)
    markers["rank"] = markers.index + 1
    return markers, lines
def run_preset(conn, preset_id, search_cusip=None, search_name=None, search_manager=None):
    """Dispatch a preset. Returns (kind, df_or_lines_tuple, label)."""
    p = PRESETS.get(preset_id)
    if not p:
        raise ValueError(f"Unknown preset: {preset_id}")
    if p["mode"] == "company":
        if not search_cusip:
            raise ValueError("This preset needs a company (search_cusip).")
        df = load_holdings(conn, search_cusip, p.get("top", 20))
        if "min_value" in p:
            df = df[df["value"] >= p["min_value"]].reset_index(drop=True)
            df["rank"] = df.index + 1
        if "max_value" in p:
            df = df[df["value"] <= p["max_value"]]
            if "cap" in p:
                df = df.head(p["cap"])
            df = df.reset_index(drop=True)
            df["rank"] = df.index + 1
        if p.get("lines"):
            lines, analysis = find_cross_holdings(conn, df)
        else:
            lines, analysis = [], {}
        return "company", (df, lines, analysis), p["label"]
    if p["mode"] == "manager":
        if not search_manager:
            raise ValueError("This preset needs a manager name (search_manager).")
        df = load_holdings_by_manager(conn, search_manager, p.get("top", 25))
        return "table", df, p["label"]
    if p["mode"] == "market":
        df = market_leaders_holdings(conn, p["companies"], p["holders_each"])
        if not df.empty:
            lines, analysis = find_cross_holdings(conn, df)
        else:
            lines, analysis = [], {}
        return "company", (df, lines, analysis), p["label"]
    if p["mode"] == "cross":
        markers, lines = cross_scan(conn, direction=p.get("direction", "value"),
                                     limit=p.get("limit", 9001),
                                     name_filter=p.get("name_filter"))
        return "relationship", (markers, lines), p["label"]
    raise ValueError(f"Preset {preset_id} has no handler for mode {p['mode']}")
# ---------------------------------------------------------------------------
# VINTAGE "TRADING CARD" STYLE + CLICK PANEL (same pattern as REFM.py)
# ---------------------------------------------------------------------------
CARD_CSS = """
<style>
  #refm-panel, #refm-legend {
    font-family: 'Georgia', 'Times New Roman', serif !important;
    background: #f4ecd8 !important;
    background-image: repeating-linear-gradient(0deg, rgba(0,0,0,0.02) 0px, rgba(0,0,0,0.02) 1px, transparent 1px, transparent 3px);
    border: 2px solid #3b2f22 !important;
    color: #2b2116 !important;
  }
  .card-rank { display:inline-block; background:#3b2f22; color:#f4ecd8; font-weight:bold;
    padding:2px 8px; border-radius:2px; font-family:'Courier New', monospace; letter-spacing:1px; }
  .card-masthead { font-family:'Georgia', serif; font-weight:bold; font-size:15px;
    text-transform:uppercase; letter-spacing:1px; border-bottom:3px double #3b2f22;
    padding-bottom:4px; margin-bottom:6px; }
  .card-stat-label { color:#6b5a44; font-size:10px; text-transform:uppercase; }
  .card-stat-value { font-size:13px; font-weight:bold; }
  .crosshold-arrow, .crosshold-mutual,
  .leaflet-div-icon.crosshold-arrow,
  .leaflet-div-icon.crosshold-mutual {
    background: transparent !important;
    border: none !important;
  }
  /* minimizable spectrum legend */
  #ch-legend {
    position: fixed;
    bottom: 28px;
    left: 12px;
    z-index: 1000;
    width: 220px;
    background: #f4ecd8;
    border: 2px solid #3b2f22;
    border-radius: 3px;
    box-shadow: 0 2px 8px rgba(0,0,0,.28);
    font-family: Georgia, 'Times New Roman', serif;
    color: #2b2116;
    font-size: 11px;
    user-select: none;
  }
  #ch-legend-head {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: 5px 8px;
    cursor: pointer;
    border-bottom: 1px solid #3b2f22;
    font-weight: bold;
    letter-spacing: 0.5px;
    text-transform: uppercase;
    font-size: 10px;
  }
  #ch-legend-head:hover { background: rgba(59,47,34,0.06); }
  #ch-legend-body { padding: 8px 10px 10px; }
  #ch-legend.collapsed #ch-legend-body { display: none; }
  #ch-legend.collapsed #ch-legend-head { border-bottom: none; }
  #ch-legend-chev { font-size: 10px; opacity: 0.7; }
  .ch-bar {
    height: 12px;
    border-radius: 2px;
    border: 1px solid #3b2f22;
    background: linear-gradient(to right,
      #ff0000 0%, #ffaa00 16%, #ffff00 33%, #00ff00 50%,
      #00ffff 66%, #0000ff 83%, #ff00ff 100%);
  }
  .ch-labels {
    display: flex;
    justify-content: space-between;
    margin-top: 4px;
    font-family: 'Courier New', monospace;
    font-size: 10px;
  }
  .ch-note {
    margin-top: 6px;
    font-size: 9px;
    color: #6b5a44;
    line-height: 1.35;
  }
  .ch-mutual-key {
    margin-top: 6px;
    font-size: 10px;
    color: #1a7a1a;
    font-weight: bold;
  }
</style>
"""
def rank_color(rank):
    if rank <= 3:
        return "#b8860b"
    if rank <= 10:
        return "#8c8c8c"
    return "#8a5a3b"
def build_card_html(row, company_name):
    pct = f"{row['pct_of_portfolio']:.2f}%" if pd.notna(row['pct_of_portfolio']) else "—"
    value = f"${row['value']:,.0f}" if pd.notna(row['value']) else "—"
    shares = f"{row['sshprnamt']:,.0f}" if pd.notna(row['sshprnamt']) else "—"
    amended = " (amended filing)" if str(row.get("is_amendment")) == "Y" else ""
    return f"""
<b style="font-size:13px">{row['manager_name']}</b><br>
<span class="card-rank">No. {int(row['rank'])}</span><br><br>
<span style="font-size:11px;color:#6b5a44;">{row.get('city','')}, {row.get('state_or_country','')}</span>
<hr style="border-top:1px solid #3b2f22;">
<table style="width:100%;font-size:12px;">
  <tr><td class="card-stat-label">Shares Held</td><td class="card-stat-value" style="text-align:right">{shares}</td></tr>
  <tr><td class="card-stat-label">Position Value</td><td class="card-stat-value" style="text-align:right">{value}</td></tr>
  <tr><td class="card-stat-label">% of Filer's Portfolio</td><td class="card-stat-value" style="text-align:right">{pct}</td></tr>
</table>
<hr style="border-top:1px solid #3b2f22;">
<div style="font-size:10px;color:#6b5a44;">
  Quarter ending {row.get('report_period','?')}{amended} &middot; Source: SEC Form 13F (EDGAR)
</div>
"""
def build_legend_html(vmin, vmax, n_lines, n_mutual=0, ratio_stats=None, n_cycles=0):
    """Compact minimizable spectrum legend (GNSS track-path equivalent)
    plus mutual ratio buckets and cycle count."""
    hi = _fmt_value(vmax)
    lo = _fmt_value(vmin)
    mutual_row = ""
    if n_mutual:
        mutual_row = (
            f'<div class="ch-mutual-key">$$ = mutual holdings '
            f'({n_mutual} pair{"s" if n_mutual != 1 else ""})</div>'
        )
    bucket_row = ""
    rs = ratio_stats or {}
    if rs.get("n_mutual"):
        bucket_row = (
            f'<div class="ch-note" style="margin-top:6px;border-top:1px solid #3b2f22;padding-top:5px;">'
            f'<b>Mutual ratio buckets</b><br>'
            f'near-sym &lt;5×: {rs.get("near_sym",0)} &nbsp;·&nbsp; '
            f'mod 5–20×: {rs.get("mod_asym",0)}<br>'
            f'high 20–100×: {rs.get("high_asym",0)} &nbsp;·&nbsp; '
            f'extreme ≥100×: {rs.get("extreme_asym",0)}<br>'
            f'B vs ≤HM: {rs.get("billions_vs_hm",0)} &nbsp;·&nbsp; '
            f'both light: {rs.get("both_light",0)}'
            f'</div>'
        )
    cycle_row = ""
    if n_cycles:
        cycle_row = (
            f'<div class="ch-mutual-key" style="color:#4a3060;">'
            f'⟳ = closed chains ({n_cycles} cycle{"s" if n_cycles != 1 else ""}, len≥3)'
            f'</div>'
        )
    return f"""
<div id="ch-legend">
  <div id="ch-legend-head" onclick="(function(el){{
      var box=document.getElementById('ch-legend');
      box.classList.toggle('collapsed');
      el.querySelector('#ch-legend-chev').textContent =
        box.classList.contains('collapsed') ? '\\u25B6' : '\\u25BC';
    }})(this)">
    <span>Cross-Holding Value</span>
    <span id="ch-legend-chev">&#9660;</span>
  </div>
  <div id="ch-legend-body">
    <div class="ch-bar"></div>
    <div class="ch-labels">
      <span style="color:#c00">{hi}</span>
      <span style="color:#a0a">{lo}</span>
    </div>
    <div class="ch-note">
      Red = highest position value among {n_lines} lines on this map<br>
      Magenta = lowest &middot; arrow points at held company
    </div>
    {mutual_row}
    {bucket_row}
    {cycle_row}
  </div>
</div>
"""
CLICK_PANEL_HTML = """
<div id="refm-panel"
     style="position:fixed;top:96px;left:12px;z-index:1002;width:340px;display:none;
            background:rgba(255,255,255,0.97);border-radius:4px;
            box-shadow:0 2px 8px rgba(0,0,0,.28);font-family:monospace;">
  <div style="display:flex;align-items:center;justify-content:space-between;
              padding:4px 8px;border-bottom:1px solid #ccc;font-size:11px;">
    <b>Holder Card</b>
    <span id="refm-panel-close" style="cursor:pointer;padding:0 4px;
          font-family:Arial,sans-serif;font-size:15px;line-height:1;">&times;</span>
  </div>
  <div id="refm-panel-body" style="padding:8px 10px;overflow-y:auto;
       max-height:calc(100vh - 190px);"></div>
</div>
"""
CLICK_PANEL_JS = """
window.addEventListener('load', function () {
    var map   = __MAP__;
    var panel = document.getElementById('refm-panel');
    var body  = document.getElementById('refm-panel-body');
    var btn   = document.getElementById('refm-panel-close');
    var last = null, lastStyle = null;
    function clearHighlight() {
        if (last && lastStyle && last.setStyle) last.setStyle(lastStyle);
        last = null; lastStyle = null;
    }
    function highlight(layer) {
        clearHighlight();
        if (!layer || !layer.setStyle) return;
        var o = layer.options || {};
        lastStyle = {color: o.color, weight: o.weight, opacity: o.opacity};
        last = layer;
        layer.setStyle({color: '#000000', weight: 4, opacity: 1});
        if (layer.bringToFront) layer.bringToFront();
    }
    function show(content, layer) {
        body.innerHTML = (typeof content === 'string')
            ? content
            : ((content && content.outerHTML) || '');
        panel.style.display = 'block';
        body.scrollTop = 0;
        highlight(layer);
    }
    function hide() { panel.style.display = 'none'; clearHighlight(); }
    btn.onclick = hide;
    document.addEventListener('keydown', function (e) { if (e.key === 'Escape') hide(); });
    function bind(layer) {
        if (layer.eachLayer) { try { layer.eachLayer(bind); } catch (err) {} }
        if (!layer.getPopup || !layer.getPopup()) return;
        var content = layer.getPopup().getContent();
        layer.unbindPopup();
        layer.on('click', function (e) {
            show(content, layer);
            if (e && e.originalEvent) L.DomEvent.stopPropagation(e.originalEvent);
        });
    }
    map.eachLayer(bind);
    map.on('layeradd', function (e) { bind(e.layer); });
});
"""
MUTUAL_PANEL_CSS = """
<style>
  /* Vintage newspaper / Beckett-style mutual trading cards */
  .mp-card {
    position: fixed;
    z-index: 1005;
    width: 268px;
    background: #f2e8d5;
    background-image:
      repeating-linear-gradient(0deg, rgba(0,0,0,0.03) 0px, rgba(0,0,0,0.03) 1px, transparent 1px, transparent 3px),
      radial-gradient(ellipse at 30% 20%, rgba(180,140,80,0.08), transparent 60%);
    border: 1px solid #2a2118;
    box-shadow: 2px 3px 0 #2a2118, 0 0 0 1px #c4b396;
    font-family: 'Times New Roman', Times, Georgia, serif;
    color: #1a140e;
    font-size: 11px;
  }
  .mp-head {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: 5px 8px 4px;
    cursor: move;
    border-bottom: 3px double #2a2118;
    font-weight: bold;
    font-size: 10px;
    letter-spacing: 1.5px;
    text-transform: uppercase;
    user-select: none;
    background: transparent;
    color: #1a140e;
  }
  .mp-masthead {
    font-size: 9px;
    letter-spacing: 2px;
    color: #5a4a38;
  }
  .mp-head-btns { display: flex; gap: 8px; }
  .mp-btn {
    cursor: pointer;
    opacity: 0.75;
    font-family: 'Times New Roman', serif;
    font-size: 13px;
    line-height: 1;
    padding: 0 2px;
  }
  .mp-btn:hover { opacity: 1; }
  .mp-body { padding: 6px 10px 10px; }
  .mp-card.collapsed .mp-body { display: none; }
  .mp-pair-title {
    text-align: center;
    font-weight: bold;
    font-size: 11px;
    letter-spacing: 0.5px;
    margin: 2px 0 6px;
    padding-bottom: 4px;
    border-bottom: 1px solid #2a2118;
  }
  .mp-row {
    display: flex;
    justify-content: space-between;
    gap: 6px;
    padding: 3px 0;
    border-bottom: 1px dotted rgba(42,33,24,0.25);
  }
  .mp-row:last-of-type { border-bottom: none; }
  .mp-name {
    color: #3a2e22;
    font-size: 10px;
    max-width: 155px;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
  }
  .mp-val {
    font-family: 'Courier New', Courier, monospace;
    font-weight: bold;
    font-size: 11px;
    white-space: nowrap;
  }
  .mp-pct {
    font-family: 'Courier New', monospace;
    font-size: 9px;
    color: #5a4a38;
    margin-left: 4px;
  }
  .mp-heuristics {
    margin-top: 7px;
    padding-top: 6px;
    border-top: 1px solid #2a2118;
  }
  .mp-ratio {
    font-family: 'Courier New', monospace;
    font-size: 11px;
    font-weight: bold;
    text-align: center;
    margin-bottom: 4px;
  }
  .mp-flag {
    display: inline-block;
    font-size: 8px;
    letter-spacing: 0.5px;
    text-transform: uppercase;
    border: 1px solid #2a2118;
    padding: 1px 4px;
    margin: 2px 2px 0 0;
    background: rgba(42,33,24,0.06);
  }
  .mp-flag.extreme { background: #2a2118; color: #f2e8d5; }
  .mp-flag.high { border-width: 2px; }
  .mp-footer {
    margin-top: 6px;
    font-size: 8px;
    color: #6b5a44;
    text-align: center;
    letter-spacing: 0.5px;
  }
  #mutual-tethers line {
    stroke: #1a140e;
    stroke-width: 1.25;
    stroke-opacity: 0.9;
  }
</style>
"""

CHAIN_CONSOLE_CSS = """
<style>
  /* ONLY the consolidated CLOSED HOLDING CHAINS console. */
  .ch-chain-console {
    width: 520px;
    min-width: 340px;
    max-width: 85vw;
    min-height: 120px;
    height: 520px;
    max-height: 82vh;
    resize: both;
    overflow: hidden;
  }

  .ch-chain-console .ch-chain-head {
    cursor: move;
  }

  .ch-chain-body {
    height: calc(100% - 31px);
    min-height: 0;
    display: flex;
    flex-direction: column;
  }

  .ch-chain-console.collapsed {
    height: auto !important;
    min-height: 0;
    resize: none;
  }

  .ch-chain-console.collapsed .ch-chain-body {
    display: none;
  }

  .ch-chain-summary {
    flex: 0 0 auto;
    padding: 2px 0 6px;
    border-bottom: 1px solid #2a2118;
    font-family: 'Courier New', Courier, monospace;
    font-size: 9px;
    color: #5a4a38;
  }

  .ch-chain-scroll {
    flex: 1 1 auto;
    min-height: 0;
    overflow-y: auto;
    overflow-x: hidden;
    padding-right: 5px;
    scrollbar-width: thin;
  }

  .ch-chain-entry {
    padding: 7px 2px 8px;
    border-bottom: 2px solid #2a2118;
  }

  .ch-chain-entry:last-child {
    border-bottom: none;
  }

  .ch-chain-entry-head {
    display: flex;
    align-items: baseline;
    gap: 8px;
    font-family: 'Courier New', Courier, monospace;
    font-size: 9px;
    font-weight: bold;
  }

  .ch-chain-number {
    letter-spacing: 1px;
  }

  .ch-chain-len {
    color: #5a4a38;
  }

  .ch-chain-total {
    margin-left: auto;
    white-space: nowrap;
    font-size: 10px;
  }

  .ch-chain-path {
    margin: 4px 0 5px;
    padding: 4px 5px;
    background: rgba(42,33,24,0.055);
    border: 1px solid rgba(42,33,24,0.25);
    font-family: 'Courier New', Courier, monospace;
    font-size: 9px;
    line-height: 1.35;
    white-space: normal;
    overflow-wrap: anywhere;
  }

  .ch-chain-edge {
    display: flex;
    justify-content: space-between;
    gap: 10px;
    padding: 2px 3px;
    border-bottom: 1px dotted rgba(42,33,24,0.20);
    font-family: 'Courier New', Courier, monospace;
    font-size: 9px;
  }

  .ch-chain-edge:last-child {
    border-bottom: none;
  }

  .ch-chain-edge-name {
    min-width: 0;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
  }

  .ch-chain-edge-value {
    flex: 0 0 auto;
    font-weight: bold;
    white-space: nowrap;
  }

  .ch-chain-stats {
    display: flex;
    flex-wrap: wrap;
    gap: 5px 10px;
    margin-top: 5px;
    padding-top: 5px;
    border-top: 1px solid rgba(42,33,24,0.35);
    font-family: 'Courier New', Courier, monospace;
    font-size: 8px;
  }

  .ch-chain-flag {
    border: 1px solid #2a2118;
    padding: 1px 3px;
    background: rgba(42,33,24,0.06);
  }

  .ch-chain-console .mp-footer {
    flex: 0 0 auto;
  }
</style>
"""

MUTUAL_PANEL_JS = r"""
window.addEventListener('load', function () {
  var map = __MAP__;
  var panels = __PANELS__;
  var root = document.getElementById('mutual-root');
  var svg = document.getElementById('mutual-tethers');
  if (!root || !svg || !panels || !panels.length) return;

  function fmt(v) {
    if (v == null || isNaN(v)) return '—';
    v = Number(v);
    if (Math.abs(v) >= 1e12) return '$' + (v/1e12).toFixed(2) + 'T';
    if (Math.abs(v) >= 1e9)  return '$' + (v/1e9).toFixed(2) + 'B';
    if (Math.abs(v) >= 1e6)  return '$' + (v/1e6).toFixed(1) + 'M';
    if (Math.abs(v) >= 1e3)  return '$' + (v/1e3).toFixed(0) + 'K';
    return '$' + v.toLocaleString();
  }
  function fmtPct(p) {
    if (p == null || isNaN(p)) return '';
    return '(' + Number(p).toFixed(2) + '% bk)';
  }
  function fmtRatio(r) {
    if (r == null || !isFinite(r)) return '—';
    if (r >= 100) return r.toFixed(0) + '×';
    if (r >= 10) return r.toFixed(1) + '×';
    return r.toFixed(2) + '×';
  }
  function flagClass(f) {
    if (/EXTREME/.test(f)) return 'mp-flag extreme';
    if (/HIGH ASYM/.test(f)) return 'mp-flag high';
    return 'mp-flag';
  }
  function esc(s) {
    return String(s == null ? '' : s)
      .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')
      .replace(/"/g,'&quot;');
  }

  var startX = 14, startY = 100;
  panels.forEach(function (p, i) {
    var card = document.createElement('div');
    card.className = 'mp-card';
    card.id = p.id;
    card.dataset.lat = p.lat;
    card.dataset.lon = p.lon;
    var col = i % 3;
    var row = Math.floor(i / 3);
    card.style.left = (startX + col * 280) + 'px';
    card.style.top  = (startY + row * 28) + 'px';

    var shortA = (p.a_name || '').length > 26 ? (p.a_name.slice(0, 24) + '…') : (p.a_name || '');
    var shortB = (p.b_name || '').length > 26 ? (p.b_name.slice(0, 24) + '…') : (p.b_name || '');

    var flagsHtml = (p.flags || []).map(function (f) {
      return '<span class="' + flagClass(f) + '">' + esc(f) + '</span>';
    }).join('');

    card.innerHTML =
      '<div class="mp-head">' +
        '<span class="mp-masthead">MUTUAL POSITION · FORM 13F</span>' +
        '<span class="mp-head-btns">' +
          '<span class="mp-btn mp-min" title="Minimize">–</span>' +
          '<span class="mp-btn mp-close" title="Close">×</span>' +
        '</span>' +
      '</div>' +
      '<div class="mp-body">' +
        '<div class="mp-pair-title">' + esc(shortA) + '  ↔  ' + esc(shortB) + '</div>' +
        '<div class="mp-row">' +
          '<span class="mp-name" title="' + esc(p.a_name) + '">' + esc(shortA) + ' →</span>' +
          '<span><span class="mp-val">' + fmt(p.a_holds_b) + '</span>' +
          '<span class="mp-pct">' + fmtPct(p.a_pct) + '</span></span></div>' +
        '<div class="mp-row">' +
          '<span class="mp-name" title="' + esc(p.b_name) + '">' + esc(shortB) + ' →</span>' +
          '<span><span class="mp-val">' + fmt(p.b_holds_a) + '</span>' +
          '<span class="mp-pct">' + fmtPct(p.b_pct) + '</span></span></div>' +
        '<div class="mp-heuristics">' +
          '<div class="mp-ratio">RATIO  ' + fmtRatio(p.ratio) + '</div>' +
          '<div>' + flagsHtml + '</div>' +
        '</div>' +
        '<div class="mp-footer">Source: SEC Form 13F · absolute $ &amp; % of 13F book</div>' +
      '</div>';

    root.appendChild(card);

    var line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    line.setAttribute('id', p.id + '-tether');
    svg.appendChild(line);

    card.querySelector('.mp-min').addEventListener('click', function (e) {
      e.stopPropagation();
      card.classList.toggle('collapsed');
      this.textContent = card.classList.contains('collapsed') ? '+' : '–';
      updateTethers();
    });
    card.querySelector('.mp-close').addEventListener('click', function (e) {
      e.stopPropagation();
      card.style.display = 'none';
      line.style.display = 'none';
    });

    var head = card.querySelector('.mp-head');
    var dragging = false, ox = 0, oy = 0;
    head.addEventListener('mousedown', function (e) {
      if (e.target.classList.contains('mp-btn')) return;
      dragging = true;
      ox = e.clientX - card.offsetLeft;
      oy = e.clientY - card.offsetTop;
      e.preventDefault();
    });
    window.addEventListener('mousemove', function (e) {
      if (!dragging) return;
      card.style.left = Math.max(0, e.clientX - ox) + 'px';
      card.style.top  = Math.max(0, e.clientY - oy) + 'px';
      updateTethers();
    });
    window.addEventListener('mouseup', function () { dragging = false; });
  });

  function edgePoint(card, ax, ay) {
    var r = card.getBoundingClientRect();
    var cx = Math.max(r.left, Math.min(ax, r.right));
    var cy = Math.max(r.top,  Math.min(ay, r.bottom));
    if (cx > r.left && cx < r.right && cy > r.top && cy < r.bottom) {
      var dl = ax - r.left, dr = r.right - ax, dt = ay - r.top, db = r.bottom - ay;
      var m = Math.min(dl, dr, dt, db);
      if (m === dl) cx = r.left;
      else if (m === dr) cx = r.right;
      else if (m === dt) cy = r.top;
      else cy = r.bottom;
    }
    return {x: cx, y: cy};
  }

  function updateTethers() {
    panels.forEach(function (p) {
      var card = document.getElementById(p.id);
      var line = document.getElementById(p.id + '-tether');
      if (!card || !line || card.style.display === 'none') return;
      try {
        var pt = map.latLngToContainerPoint([Number(card.dataset.lat), Number(card.dataset.lon)]);
        var mapRect = map.getContainer().getBoundingClientRect();
        var ax = mapRect.left + pt.x;
        var ay = mapRect.top  + pt.y;
        var ep = edgePoint(card, ax, ay);
        line.setAttribute('x1', ax);
        line.setAttribute('y1', ay);
        line.setAttribute('x2', ep.x);
        line.setAttribute('y2', ep.y);
      } catch (err) {}
    });
  }

  map.on('move zoom moveend zoomend', updateTethers);
  window.addEventListener('resize', updateTethers);
  setTimeout(updateTethers, 200);
  setTimeout(updateTethers, 800);
});
"""
CYCLE_PANEL_JS = r"""
window.addEventListener('load', function () {
  var map = __MAP__;
  var cycles = __CYCLES__;
  var root = document.getElementById('mutual-root');
  if (!root || !cycles || !cycles.length) return;

  function fmt(v) {
    if (v == null || isNaN(v)) return '—';
    v = Number(v);
    if (Math.abs(v) >= 1e12) return '$' + (v/1e12).toFixed(2) + 'T';
    if (Math.abs(v) >= 1e9)  return '$' + (v/1e9).toFixed(2) + 'B';
    if (Math.abs(v) >= 1e6)  return '$' + (v/1e6).toFixed(1) + 'M';
    if (Math.abs(v) >= 1e3)  return '$' + (v/1e3).toFixed(0) + 'K';
    return '$' + v.toLocaleString();
  }

  function esc(s) {
    return String(s == null ? '' : s)
      .replace(/&/g,'&amp;').replace(/</g,'&lt;')
      .replace(/>/g,'&gt;').replace(/"/g,'&quot;');
  }

  function shortName(n) {
    n = n || '';
    return n.length > 34 ? n.slice(0, 32) + '…' : n;
  }

  /*
   * One consolidated chain console.
   * Every detected chain remains present; nothing is sampled or hidden.
   * The console itself is draggable, minimizable and CSS-resizable.
   */
  var card = document.createElement('div');
  card.className = 'mp-card ch-chain-console';
  card.id = 'closed-chain-console';
  card.style.left = '20px';
  card.style.top = '100px';

  var rows = cycles.map(function (c, i) {
    var steps = (c.edges || []).map(function (e) {
      return '<div class="ch-chain-edge">' +
        '<span class="ch-chain-edge-name" title="' +
          esc(e.from) + ' → ' + esc(e.to) + '">' +
          esc(shortName(e.from)) + ' → ' + esc(shortName(e.to)) +
        '</span>' +
        '<span class="ch-chain-edge-value">' + fmt(e.value) + '</span>' +
      '</div>';
    }).join('');

    var nodeRing = (c.nodes || []).map(shortName).join(' → ') + ' → ' + shortName((c.nodes || [])[0]);

    return '<section class="ch-chain-entry">' +
      '<div class="ch-chain-entry-head">' +
        '<span class="ch-chain-number">CHAIN #' + (i + 1) + '</span>' +
        '<span class="ch-chain-len">LEN ' + esc(c.length) + '</span>' +
        '<span class="ch-chain-total">' + fmt(c.total_value) + '</span>' +
      '</div>' +
      '<div class="ch-chain-path" title="' +
        esc((c.nodes || []).join(' → ') + ' → ' + ((c.nodes || [])[0] || '')) +
        '">' + esc(nodeRing) + '</div>' +
      '<div class="ch-chain-edges">' + steps + '</div>' +
      '<div class="ch-chain-stats">' +
        '<span>MIN LEG <b>' + fmt(c.min_value) + '</b></span>' +
        '<span>SUM <b>' + fmt(c.total_value) + '</b></span>' +
        '<span class="ch-chain-flag">CYCLE ≥3</span>' +
        '<span class="ch-chain-flag">RETURNS TO START</span>' +
      '</div>' +
    '</section>';
  }).join('');

  card.innerHTML =
    '<div class="mp-head ch-chain-head">' +
      '<span class="mp-masthead">CLOSED HOLDING CHAINS · FORM 13F</span>' +
      '<span class="mp-head-btns">' +
        '<span class="mp-btn ch-chain-min" title="Minimize">–</span>' +
        '<span class="mp-btn ch-chain-close" title="Close">×</span>' +
      '</span>' +
    '</div>' +
    '<div class="mp-body ch-chain-body">' +
      '<div class="ch-chain-summary">' +
        '<b>' + cycles.length + '</b> closed chain' +
        (cycles.length === 1 ? '' : 's') +
        ' · every detected chain shown below' +
      '</div>' +
      '<div class="ch-chain-scroll">' + rows + '</div>' +
      '<div class="mp-footer">Directed path closes: A→B→…→A · Form 13F positions</div>' +
    '</div>';

  root.appendChild(card);

  card.querySelector('.ch-chain-min').addEventListener('click', function (e) {
    e.stopPropagation();
    card.classList.toggle('collapsed');
    this.textContent = card.classList.contains('collapsed') ? '+' : '–';
  });

  card.querySelector('.ch-chain-close').addEventListener('click', function (e) {
    e.stopPropagation();
    card.style.display = 'none';
  });

  // Drag by header only.
  var head = card.querySelector('.ch-chain-head');
  var dragging = false, ox = 0, oy = 0;

  head.addEventListener('mousedown', function (e) {
    if (e.target.classList.contains('mp-btn')) return;
    dragging = true;
    ox = e.clientX - card.offsetLeft;
    oy = e.clientY - card.offsetTop;
    e.preventDefault();
  });

  window.addEventListener('mousemove', function (e) {
    if (!dragging) return;
    card.style.left = Math.max(0, e.clientX - ox) + 'px';
    card.style.top  = Math.max(0, e.clientY - oy) + 'px';
  });

  window.addEventListener('mouseup', function () {
    dragging = false;
  });
});
"""
def build_map(df, ticker, company_name, top_n, lines=None, analysis=None,
              cluster_threshold=150):
    analysis = analysis or {}
    geocoded = df.dropna(subset=["lat", "lon"])
    if geocoded.empty:
        sys.exit("[ERROR] No holders could be geocoded -- nothing to map.")
    quarter_label = geocoded["report_period"].mode().iat[0] \
        if not geocoded["report_period"].mode().empty else "unknown"

    # Base map with no default tiles — we add named layers for the control
    m = folium.Map(
        location=[geocoded["lat"].mean(), geocoded["lon"].mean()],
        zoom_start=4,
        tiles=None,
        max_zoom=19,
    )

    # --- basemap options (same set the GNSS mapper exposes, no API key) ---
    light = folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/Canvas/World_Light_Gray_Base/MapServer/tile/{z}/{y}/{x}",
        attr="Tiles &copy; Esri",
        name="Light Gray",
        max_zoom=16,
        control=True,
    )
    light.add_to(m)
    # labels overlay for light gray (no place names otherwise)
    folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/Canvas/World_Light_Gray_Reference/MapServer/tile/{z}/{y}/{x}",
        attr="Tiles &copy; Esri",
        name="Labels",
        overlay=True,
        control=False,
        max_zoom=16,
    ).add_to(m)

    folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/Canvas/World_Dark_Gray_Base/MapServer/tile/{z}/{y}/{x}",
        attr="Tiles &copy; Esri",
        name="Dark Gray",
        max_zoom=16,
        control=True,
    ).add_to(m)

    folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/World_Street_Map/MapServer/tile/{z}/{y}/{x}",
        attr="Tiles &copy; Esri",
        name="Street",
        max_zoom=19,
        control=True,
    ).add_to(m)

    folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}",
        attr="Tiles &copy; Esri",
        name="Satellite",
        max_zoom=19,
        control=True,
    ).add_to(m)

    label = f"All {len(geocoded)} holders of {ticker}" if not top_n or top_n <= 0 \
        else f"Top {top_n} holders of {ticker}"
    use_cluster = len(geocoded) > cluster_threshold
    if use_cluster:
        sink = MarkerCluster(name=label, options={"maxClusterRadius": 40,
                                                    "disableClusteringAtZoom": 8})
        sink.add_to(m)
        print(f"[NOTE] {len(geocoded):,} holders -- clustering enabled")
    else:
        sink = folium.FeatureGroup(name=label, show=True)
    for _, row in geocoded.iterrows():
        color = rank_color(int(row["rank"]))
        radius = 6 + max(0, (top_n - row["rank"])) * 0.6 if top_n and top_n > 0 else 6
        folium.CircleMarker(
            location=[row["lat"], row["lon"]],
            radius=radius,
            color="#3b2f22", weight=1.5,
            fill=True, fill_color=color, fill_opacity=0.85,
            popup=folium.Popup(build_card_html(row, company_name), max_width=340),
            tooltip=f"#{int(row['rank'])} {row['manager_name']}",
        ).add_to(sink)
    if not use_cluster:
        sink.add_to(m)

    n_mutual_pairs = 0
    mutual_panels = []  # deduped undirected mutual pairs for floating cards
    if lines:
        line_layer = folium.FeatureGroup(name=f"Cross-holdings ({len(lines)})", show=True)
        seen_mutual = set()  # frozenset({a,b}) so each pair once
        for ln in lines:
            is_mutual = bool(ln.get("mutual"))
            tip = f"{ln['from_name']} holds {_fmt_value(ln['value'])} of {ln['to_name']}"
            if is_mutual:
                tip += f"  ·  MUTUAL (counter {_fmt_value(ln.get('mutual_value'))})"
            add_arrowed_line(
                line_layer,
                from_latlon=ln["from_latlon"],
                to_latlon=ln["to_latlon"],
                color=ln["color"],
                weight=2.5,
                opacity=0.9,
                tooltip=tip,
            )
            if is_mutual:
                key = frozenset([ln["from_name"], ln["to_name"]])
                if key not in seen_mutual:
                    seen_mutual.add(key)
                    mid = _point_along(*ln["from_latlon"], *ln["to_latlon"], 0.50)
                    hz = mutual_heuristics(
                        ln["value"], ln.get("mutual_value"),
                        ln.get("portfolio"), ln.get("mutual_portfolio"),
                    )
                    mutual_panels.append({
                        "id": f"mp{len(mutual_panels)}",
                        "lat": mid[0], "lon": mid[1],
                        "a_name": ln["from_name"],
                        "b_name": ln["to_name"],
                        "a_holds_b": ln["value"],
                        "b_holds_a": ln.get("mutual_value"),
                        "a_pct": hz["a_pct"],
                        "b_pct": hz["b_pct"],
                        "ratio": hz["ratio"],
                        "flags": hz["flags"],
                    })
                    # $$ anchor marker at midpoint
                    dollar_html = (
                        '<div class="ch-dollar" style="font-size:14px;font-weight:bold;'
                        'color:#1a7a1a;text-shadow:0 0 3px #fff,0 0 2px #fff;'
                        'line-height:1;letter-spacing:-1px;">$$</div>'
                    )
                    folium.Marker(
                        location=list(mid),
                        icon=folium.DivIcon(
                            html=dollar_html,
                            icon_size=(22, 14),
                            icon_anchor=(11, 7),
                            class_name="crosshold-mutual",
                        ),
                        interactive=False,
                    ).add_to(line_layer)
        n_mutual_pairs = len(mutual_panels)
        line_layer.add_to(m)

        vals = [ln["value"] or 0 for ln in lines]
        vmax, vmin = max(vals), min(vals)
        cycles = analysis.get("cycles") or []
        ratio_stats = analysis.get("ratio_stats") or {}
        m.get_root().html.add_child(folium.Element(
            build_legend_html(vmin, vmax, len(lines), n_mutual_pairs,
                              ratio_stats=ratio_stats, n_cycles=len(cycles))))
        print(f"[NOTE] cross-holding lines drawn: {len(lines)} "
              f"(red = highest → magenta = lowest; "
              f"{n_mutual_pairs} mutual $$ pairs; "
              f"{len(cycles)} closed chains; "
              f"arrows point at the held company)")
        if ratio_stats.get("n_mutual"):
            print(f"[NOTE] mutual buckets: near={ratio_stats.get('near_sym',0)} "
                  f"mod={ratio_stats.get('mod_asym',0)} "
                  f"high={ratio_stats.get('high_asym',0)} "
                  f"extreme={ratio_stats.get('extreme_asym',0)} "
                  f"B-vs-HM={ratio_stats.get('billions_vs_hm',0)} "
                  f"both_light={ratio_stats.get('both_light',0)}")

    # Layer control top-right (basemaps + overlays), matches GNSS layout
    folium.LayerControl(position="topright", collapsed=False).add_to(m)

    m.get_root().html.add_child(folium.Element(CARD_CSS))
    m.get_root().html.add_child(folium.Element(f"""
    <div style="position:fixed;top:12px;left:50%;transform:translateX(-50%);
                z-index:1001;background:#f4ecd8;border:2px solid #3b2f22;
                padding:6px 18px;font-family:Georgia,serif;font-weight:bold;
                text-transform:uppercase;letter-spacing:2px;font-size:14px;
                box-shadow:0 2px 6px rgba(0,0,0,.3);">
      {company_name} &mdash; {label} &mdash; {quarter_label}
    </div>
    """))
    m.get_root().html.add_child(folium.Element(CLICK_PANEL_HTML))
    m.get_root().script.add_child(folium.Element(
        CLICK_PANEL_JS.replace("__MAP__", m.get_name())))

    # Mutual holdings floating cards (draggable, minimizable, tethered to $$)
    import json
    if mutual_panels or (analysis.get("cycles")):
        m.get_root().html.add_child(folium.Element(MUTUAL_PANEL_CSS))
        if analysis.get("cycles"):
            m.get_root().html.add_child(folium.Element(CHAIN_CONSOLE_CSS))
        m.get_root().html.add_child(folium.Element(
            f'<div id="mutual-root"></div>'
            f'<svg id="mutual-tethers" style="position:fixed;inset:0;width:100%;height:100%;'
            f'pointer-events:none;z-index:1003;"></svg>'
        ))
    if mutual_panels:
        panels_json = json.dumps(mutual_panels)
        m.get_root().script.add_child(folium.Element(
            MUTUAL_PANEL_JS
            .replace("__MAP__", m.get_name())
            .replace("__PANELS__", panels_json)
        ))

    # Closed holding chains (cycles len ≥ 3)
    cycles = analysis.get("cycles") or []
    if cycles:
        cycle_payload = []
        for i, c in enumerate(cycles):
            if c.get("lat") is None:
                continue
            cycle_payload.append({
                "id": f"cyc{i}",
                "lat": c["lat"], "lon": c["lon"],
                "length": c["length"],
                "nodes": c["nodes"],
                "edges": c["edges"],
                "min_value": c["min_value"],
                "total_value": c["total_value"],
            })
            # ⟳ marker at cycle centroid
            folium.Marker(
                location=[c["lat"], c["lon"]],
                icon=folium.DivIcon(
                    html=('<div style="font-size:16px;font-weight:bold;color:#4a3060;'
                          'text-shadow:0 0 3px #fff,0 0 2px #fff;line-height:1;">⟳</div>'),
                    icon_size=(18, 18),
                    icon_anchor=(9, 9),
                    class_name="crosshold-mutual",
                ),
                interactive=False,
            ).add_to(m)
        if cycle_payload:
            m.get_root().script.add_child(folium.Element(
                CYCLE_PANEL_JS
                .replace("__MAP__", m.get_name())
                .replace("__CYCLES__", json.dumps(cycle_payload))
            ))
            print(f"[NOTE] closed chains shown: {len(cycle_payload)}")
            for c in cycle_payload[:8]:
                chain = " → ".join(
                    (n[:22] + "…") if len(n) > 22 else n for n in c["nodes"]
                ) + " → (back)"
                print(f"  len={c['length']}  min={_fmt_value(c['min_value'])}  "
                      f"sum={_fmt_value(c['total_value'])}  {chain}")

    unresolved = len(df) - len(geocoded)
    if unresolved:
        print(f"[WARN] {unresolved} holder(s) had no HQ coordinates and are "
              f"listed below but not on the map.")
    return m, df[["rank", "manager_name", "city", "state_or_country", "value", "sshprnamt"]]
def main():
    ap = argparse.ArgumentParser(description="Query 13F master DB, render trading-card map")
    ap.add_argument("--db", default=str(DB_PATH))
    ap.add_argument("--find-cusip", metavar="TEXT")
    ap.add_argument("--ticker")
    ap.add_argument("--cusip")
    ap.add_argument("--name")
    ap.add_argument("--top", type=int, default=0,
                     help="0 = map ALL holders (default). Set a number to cap it.")
    ap.add_argument("--max-lines", type=int, default=300,
                     help="Cap on cross-holding lines drawn (performance).")
    ap.add_argument("--no-lines", action="store_true",
                     help="Skip cross-holding line detection entirely.")
    ap.add_argument("--preset", choices=list(PRESETS.keys()),
                     help="Run a preset instead of --ticker/--cusip. "
                          "'company'/'market' presets need --cusip too; "
                          "'manager' presets need --manager-name.")
    ap.add_argument("--manager-name", help="Exact manager_name for --preset reverse")
    ap.add_argument("--no-serve", action="store_true")
    ap.add_argument("--port", type=int, default=8766)
    args = ap.parse_args()
    if args.preset:
        db_path = Path(args.db)
        if not db_path.exists():
            sys.exit(f"[ERROR] DB not found: {db_path}")
        conn = sqlite3.connect(db_path)
        kind, payload, label = run_preset(
            conn, args.preset, search_cusip=args.cusip,
            search_manager=args.manager_name)
        print(f"[NOTE] Preset: {label} (kind={kind})")
        if kind == "table":
            print(payload.to_string(index=False) if not payload.empty else "(no rows)")
        elif kind == "company":
            df, lines, analysis = payload
            print(df.to_string(index=False) if not df.empty else "(no rows)")
            print(f"[NOTE] lines: {len(lines)}")
            rs = analysis.get("ratio_stats") or {}
            if rs:
                print(f"[NOTE] mutual buckets: n={rs.get('n_mutual',0)} "
                      f"near={rs.get('near_sym',0)} mod={rs.get('mod_asym',0)} "
                      f"high={rs.get('high_asym',0)} extreme={rs.get('extreme_asym',0)} "
                      f"B-vs-HM={rs.get('billions_vs_hm',0)} both_light={rs.get('both_light',0)}")
            print(f"[NOTE] cycles: {len(analysis.get('cycles') or [])}")
        elif kind == "relationship":
            markers, lines = payload
            print(markers.to_string(index=False) if not markers.empty else "(no rows)")
            print(f"[NOTE] lines: {len(lines)}")
        conn.close()
        return
    db_path = Path(args.db)
    if not db_path.exists():
        sys.exit(f"[ERROR] DB not found: {db_path}\nRun build_13f_db.py first.")
    conn = sqlite3.connect(db_path)
    if args.find_cusip:
        find_cusip(conn, args.find_cusip)
        return
    if args.cusip:
        cusip, name = args.cusip, (args.name or args.cusip)
    elif args.ticker:
        entry = COMPANIES.get(args.ticker.upper())
        if not entry:
            sys.exit(f"[ERROR] {args.ticker} not in COMPANIES. Run --find-cusip first.")
        cusip, name = entry["cusip"], entry["name"]
    else:
        sys.exit("[ERROR] Provide --ticker, --cusip, or --find-cusip.")
    df = load_holdings(conn, cusip, args.top)
    if args.no_lines:
        lines, analysis = [], {}
    else:
        lines, analysis = find_cross_holdings(conn, df, max_lines=args.max_lines)
    m, table = build_map(df, args.ticker or cusip, name, args.top,
                         lines=lines, analysis=analysis)
    print(table.to_string(index=False))
    out_dir = db_path.parent
    out_path = out_dir / f"holders_{(args.ticker or cusip)}.html"
    m.save(str(out_path))
    print(f"\n[NOTE] Map saved: {out_path}")
    if args.no_serve:
        webbrowser.open(out_path.as_uri())
    else:
        os.chdir(out_dir)
        class Handler(http.server.SimpleHTTPRequestHandler):
            def log_message(self, *a):
                pass
        httpd = socketserver.TCPServer(("127.0.0.1", args.port), Handler)
        threading.Thread(target=httpd.serve_forever, daemon=True).start()
        url = f"http://127.0.0.1:{args.port}/{out_path.name}"
        print(f"Serving {url}")
        webbrowser.open(url)
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            httpd.shutdown()
if __name__ == "__main__":
    main()
