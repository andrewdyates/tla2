# Large Format Printing

Instructions for printing SVG/PDF diagrams to the HP DesignJet Z5200 PostScript (44" roll printer, USB).

## Printer Setup

The Z5200 connects via USB. CUPS detects it automatically but the **Generic PostScript PPD does not support custom page sizes** — it forces Letter/Legal/Tabloid regardless of `-o media=Custom.*` options.

### Add the printer (one-time)

```bash
# Verify USB detection
lpinfo -v | grep -i hp

# Add with generic PostScript driver (only option on macOS)
lpadmin -p HP_Z5200 \
  -v "usb://Hewlett-Packard/HP%20Designjet%20Z5200%20PostScript?serial=CN32F4K012" \
  -m "drv:///sample.drv/generic.ppd" \
  -E

# Set as default
lpadmin -d HP_Z5200
```

## Printing Large Format

**The key insight:** CUPS re-filters PDFs through the PPD, which strips custom page sizes. The only reliable method is to send **raw PostScript** with `setpagedevice` embedded, so the Z5200's built-in PostScript RIP handles page sizing directly.

### Step 1: Install dependencies

```bash
pip3 install --break-system-packages cairosvg fonttools brotli
```

### Step 2: Embed fonts in SVG (if using web fonts)

SVG `@import url()` for Google Fonts won't resolve in offline renderers. Subset and embed as base64 woff2:

```python
from fontTools.subset import Subsetter
from fontTools.ttLib import TTFont
import base64, io, re

def subset_and_embed(ttf_path, svg_text):
    """Subset font to only characters used in SVG, return base64 woff2."""
    chars = set(re.sub(r'<[^>]+>', ' ', svg_text))
    font = TTFont(ttf_path)
    sub = Subsetter()
    sub.populate(unicodes={ord(c) for c in chars})
    sub.subset(font)
    buf = io.BytesIO()
    font.flavor = 'woff2'
    font.save(buf)
    return base64.b64encode(buf.getvalue()).decode('ascii')

# Then in SVG <style>:
# @font-face {
#   font-family: 'Inter';
#   src: url(data:font/woff2;base64,<BASE64>) format('woff2');
# }
```

### Step 3: Convert SVG to PostScript with correct page size

```python
import cairosvg

# Target size in points (1 inch = 72 points)
# Common large format sizes:
#   ARCH D: 24" x 36" = 1728 x 2592 pts
#   ARCH E: 36" x 48" = 2592 x 3456 pts
#   Custom: calculate from SVG aspect ratio

WIDTH_INCHES = 36
SVG_ASPECT = 4400 / 3200  # height / width from viewBox
HEIGHT_INCHES = WIDTH_INCHES * SVG_ASPECT
WIDTH_PTS = int(WIDTH_INCHES * 72)
HEIGHT_PTS = int(HEIGHT_INCHES * 72)

cairosvg.svg2ps(
    url='diagram.svg',
    write_to='/tmp/print.ps',
    dpi=72,
    output_width=WIDTH_PTS,
    output_height=HEIGHT_PTS,
)
```

### Step 4: Inject setpagedevice into PostScript

```python
with open('/tmp/print.ps', 'r') as f:
    ps = f.read()

# Insert after %%EndComments — the Z5200 RIP reads this
page_setup = f"""%%BeginSetup
<< /PageSize [{WIDTH_PTS} {HEIGHT_PTS}] /ImagingBBox null >> setpagedevice
%%EndSetup
"""
ps = ps.replace('%%EndComments\n', '%%EndComments\n' + page_setup)

with open('/tmp/print-final.ps', 'w') as f:
    f.write(ps)
```

### Step 5: Print as raw PostScript

```bash
lp -d HP_Z5200 -o raw /tmp/print-final.ps
```

The `-o raw` flag is critical — it bypasses CUPS filtering so `setpagedevice` reaches the printer.

### Verify job status

```bash
lpstat -t          # Overall status
lpstat -o HP_Z5200 # Pending jobs
cancel -a HP_Z5200 # Cancel all jobs
```

## What does NOT work

| Method | Why it fails |
|--------|-------------|
| `lp -o media=Custom.WxH file.pdf` | Generic PPD ignores custom sizes, defaults to Letter |
| `lp -o fit-to-page=false file.pdf` | CUPS still re-filters through PPD page size |
| `lpadmin -o PageSize=Custom.WxH` | PPD doesn't define custom size support |
| `lpadmin -m raw` | macOS no longer supports raw queues |
| PDF with correct MediaBox | CUPS re-filters, strips page size, uses PPD default |

## Quick Reference

```bash
# One-liner: SVG to large format print (36" wide, aspect-preserving)
python3 -c "
import cairosvg
w, h = 2592, 3564
cairosvg.svg2ps(url='INPUT.svg', write_to='/tmp/p.ps', dpi=72, output_width=w, output_height=h)
ps = open('/tmp/p.ps').read()
ps = ps.replace('%%EndComments\n', '%%EndComments\n%%BeginSetup\n<< /PageSize [%d %d] /ImagingBBox null >> setpagedevice\n%%EndSetup\n' % (w, h))
open('/tmp/p.ps', 'w').write(ps)
" && lp -d HP_Z5200 -o raw /tmp/p.ps
```

## Troubleshooting

- **Prints tiny on letter paper:** You sent PDF or PS without `-o raw`. The PPD forced Letter.
- **Z5200 front panel prompts for media:** Accept it. The printer is confirming the custom size.
- **Blank page:** Check `lpstat -t` for errors. The Z5200 needs PostScript Language Level 3.
- **Fonts wrong:** Embed fonts in SVG before converting. See Step 2.
- **Roll too narrow:** The Z5200 max width is 44". Keep content width ≤ 42" for margins.
