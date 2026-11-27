# Makes totals/world.json, the country shapes for the world map on the page
# of totals, from Natural Earth's countries at 1:110 million (public domain),
# as the npm package world-atlas 2.0.2 has them (TopoJSON):
#   https://cdn.jsdelivr.net/npm/world-atlas@2.0.2/countries-110m.json
# Download that file, then run (by hand, once; the result is committed):
#
#   python scripts/make_world_map.py countries-110m.json
#
# The shapes are drawn in the Equal Earth projection (Šavrič, Patterson and
# Jenny 2018), which keeps the areas of countries in proportion, and stored
# as SVG paths, so the page draws the map without loading anything from other
# websites. Antarctica is left out. Each country has its Natural Earth name
# and the name the participants' answers have after scripts/extract_files.py
# (lower case, "united states", "czech republic").

import json
import math
import os
import sys

WIDTH = 960
# Natural Earth's name -> the answer's name, where they differ
ANSWER_NAME = {
    "United States of America": "united states", "Czechia": "czech republic",
    "Dem. Rep. Congo": "democratic republic of the congo", "Congo": "republic of the congo",
    "Bosnia and Herz.": "bosnia and herzegovina", "Dominican Rep.": "dominican republic",
    "Central African Rep.": "central african republic", "Côte d'Ivoire": "ivory coast",
    "Eq. Guinea": "equatorial guinea", "S. Sudan": "south sudan", "Macedonia": "north macedonia",
    "eSwatini": "eswatini", "W. Sahara": "western sahara", "Solomon Is.": "solomon islands",
    "Falkland Is.": "falkland islands", "N. Cyprus": "northern cyprus",
    "Fr. S. Antarctic Lands": "french southern and antarctic lands",
}


def equal_earth(lon, lat):
    a1, a2, a3, a4 = 1.340264, -0.081106, 0.000893, 0.003796
    m = math.sqrt(3) / 2
    lam, phi = math.radians(lon), math.radians(lat)
    t = math.asin(m * math.sin(phi))
    t2, t6 = t * t, t ** 6
    x = 2 * math.sqrt(3) * lam * math.cos(t) / (3 * (9 * a4 * t6 * t2 + 7 * a3 * t6 + 3 * a2 * t2 + a1))
    y = t * (a4 * t6 * t2 + a3 * t6 + a2 * t2 + a1)
    return x, y


def main():
    topo = json.load(open(sys.argv[1], encoding="utf-8"))
    sx, sy = topo["transform"]["scale"]
    tx, ty = topo["transform"]["translate"]
    # the arcs: delta-encoded whole numbers -> longitude and latitude
    arcs = []
    for arc in topo["arcs"]:
        x = y = 0
        pts = []
        for dx, dy in arc:
            x += dx
            y += dy
            pts.append((x * sx + tx, y * sy + ty))
        arcs.append(pts)

    def ring(indices):
        pts = []
        for i in indices:
            a = arcs[i] if i >= 0 else arcs[~i][::-1]
            pts.extend(a if not pts else a[1:])      # arcs share their end points
        return pts

    xmax, ymax = equal_earth(180, 0)[0], equal_earth(0, 90)[1]
    scale = WIDTH / (2 * xmax)
    height = round(2 * ymax * scale)

    def to_svg(lon, lat):
        x, y = equal_earth(lon, lat)
        return (x + xmax) * scale, (ymax - y) * scale

    def pieces(pts):
        # an outline that crosses the 180th meridian (Russia, Fiji) jumps
        # from +180 to -180 longitude; drawn as one outline, its edge would
        # run across the whole map. It is split into its eastern and its
        # western part, each closed along the meridian.
        if not any(abs(a[0] - b[0]) > 180 for a, b in zip(pts, pts[1:])):
            return [pts]
        east = [p for p in pts if p[0] >= 0]
        west = [p for p in pts if p[0] < 0]
        return [q for q in (east, west) if len(q) >= 3]

    out = []
    for g in topo["objects"]["countries"]["geometries"]:
        name = g["properties"]["name"]
        if name == "Antarctica" or g.get("type") not in ("Polygon", "MultiPolygon"):
            continue
        polys = [g["arcs"]] if g["type"] == "Polygon" else g["arcs"]
        d = []
        for poly in polys:
            for r in (piece for r_ in poly for piece in pieces(ring(r_))):
                last, part = None, []
                for lon, lat in r:
                    p = to_svg(lon, lat)
                    if last and abs(p[0] - last[0]) + abs(p[1] - last[1]) < 0.6:
                        continue                     # closer than about half a pixel
                    part.append("%.1f %.1f" % p)
                    last = p
                if len(part) >= 3:
                    d.append("M" + "L".join(part) + "Z")
        out.append({"name": name, "key": ANSWER_NAME.get(name, name.lower()), "d": "".join(d)})
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "totals", "world.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump({"w": WIDTH, "h": height, "source": "Natural Earth 1:110m (public domain), via world-atlas 2.0.2",
                   "countries": out}, f, ensure_ascii=False, separators=(",", ":"))
    print("%s: %d countries, %d KB" % (os.path.normpath(path), len(out), os.path.getsize(path) // 1024))


if __name__ == "__main__":
    main()
