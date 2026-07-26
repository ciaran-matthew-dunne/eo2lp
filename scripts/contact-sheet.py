#!/usr/bin/env python3
"""Render a page range of a PDF into a labelled contact sheet.

Built for reviewing slide decks: renders pages, draws a page number and
a hairline border on each, and tiles them into one PNG that can be
eyeballed in a single view.

usage:
    contact-sheet.py FILE.pdf [-p RANGE] [-c COLS] [-d DPI] [-o OUT]

RANGE is like "1-8", "3", or "all" (default).
"""
import argparse
import glob
import os
import shutil
import subprocess
import sys
import tempfile

try:
    from PIL import Image, ImageDraw
except ImportError:
    sys.exit("needs Pillow: pip install --user Pillow")

GUTTER = 10
LABEL = 16
BG = (136, 136, 136)


def page_count(pdf):
    out = subprocess.run(["pdfinfo", pdf], capture_output=True, text=True).stdout
    for line in out.splitlines():
        if line.startswith("Pages:"):
            return int(line.split()[1])
    sys.exit(f"could not read page count from {pdf}")


def parse_range(spec, total):
    if spec in (None, "all"):
        return 1, total
    if "-" in spec:
        a, _, b = spec.partition("-")
        return int(a), min(int(b), total)
    n = int(spec)
    return n, n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pdf")
    ap.add_argument("-p", "--pages", default="all")
    ap.add_argument("-c", "--cols", type=int, default=2)
    ap.add_argument("-d", "--dpi", type=int, default=80)
    ap.add_argument("-o", "--out", default="contact-sheet.png")
    args = ap.parse_args()

    if not os.path.exists(args.pdf):
        sys.exit(f"no such file: {args.pdf}")

    total = page_count(args.pdf)
    first, last = parse_range(args.pages, total)
    if first > last:
        sys.exit(f"empty page range: {args.pages}")

    tmp = tempfile.mkdtemp(prefix="sheet-")
    try:
        subprocess.run(
            ["pdftoppm", "-f", str(first), "-l", str(last),
             "-r", str(args.dpi), "-png", args.pdf, os.path.join(tmp, "p")],
            check=True,
        )
        files = sorted(glob.glob(os.path.join(tmp, "p-*.png")))
        if not files:
            sys.exit("pdftoppm produced nothing")

        tiles = []
        for n, f in enumerate(files, start=first):
            im = Image.open(f).convert("RGB")
            canvas = Image.new("RGB", (im.width, im.height + LABEL), BG)
            canvas.paste(im, (0, LABEL))
            d = ImageDraw.Draw(canvas)
            d.text((3, 3), f"p.{n}", fill=(255, 255, 255))
            d.rectangle([0, LABEL, im.width - 1, im.height + LABEL - 1],
                        outline=(60, 60, 60))
            tiles.append(canvas)

        cols = max(1, min(args.cols, len(tiles)))
        rows = (len(tiles) + cols - 1) // cols
        tw = max(t.width for t in tiles)
        th = max(t.height for t in tiles)
        sheet = Image.new(
            "RGB",
            (cols * tw + (cols + 1) * GUTTER, rows * th + (rows + 1) * GUTTER),
            BG,
        )
        for i, t in enumerate(tiles):
            r, c = divmod(i, cols)
            sheet.paste(t, (GUTTER + c * (tw + GUTTER), GUTTER + r * (th + GUTTER)))
        sheet.save(args.out)
        print(f"{args.out}  pages {first}-{last}  {sheet.width}x{sheet.height}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
