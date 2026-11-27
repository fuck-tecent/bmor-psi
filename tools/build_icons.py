#!/usr/bin/env python3
"""Compile assets/brand-icons/*.svg into a single deduplicated SVG sprite at deploy/agent-icons.svg."""

import argparse
import gzip
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC_DIR = ROOT / "assets" / "brand-icons"
OUT_FILE = ROOT / "deploy" / "agent-icons.svg"
SVG_NS = "http://www.w3.org/2000/svg"
XLINK_NS = "http://www.w3.org/1999/xlink"
KEY_RE = re.compile(r"^[a-z0-9][a-z0-9-]{0,31}$")
URL_REF_RE = re.compile(r"url\(#([^)]+)\)")
PRESENTATION_ATTRS = (
    "fill",
    "fill-rule",
    "clip-rule",
    "stroke",
    "stroke-width",
    "stroke-linecap",
    "stroke-linejoin",
    "stroke-miterlimit",
)

ET.register_namespace("", SVG_NS)
ET.register_namespace("xlink", XLINK_NS)


def _local(tag):
    return tag.rsplit("}", 1)[-1] if "}" in tag else tag


def _rewrite_ids(element, prefix, id_map):
    # First pass: collect all ids.
    for node in element.iter():
        old_id = node.attrib.get("id")
        if old_id:
            new_id = f"{prefix}{old_id}"
            id_map[old_id] = new_id
            node.attrib["id"] = new_id
    # Second pass: rewrite references in attributes.
    if not id_map:
        return
    for node in element.iter():
        for attr, val in list(node.attrib.items()):
            if attr == "id":
                continue
            new_val = URL_REF_RE.sub(
                lambda m: f"url(#{id_map[m.group(1)]})" if m.group(1) in id_map else m.group(0),
                val,
            )
            if attr in ("href", f"{{{XLINK_NS}}}href") and new_val.startswith("#"):
                ref = new_val[1:]
                if ref in id_map:
                    new_val = "#" + id_map[ref]
            if new_val != val:
                node.attrib[attr] = new_val


def _strip_noise(element):
    for parent in list(element.iter()):
        for child in list(parent):
            local = _local(child.tag)
            if local in ("title", "desc", "metadata"):
                parent.remove(child)


def _validate_safe_svg(element, path):
    for node in element.iter():
        local = _local(node.tag)
        if local in ("script", "foreignObject", "iframe", "object", "embed", "image"):
            raise ValueError(f"Disallowed SVG element <{local}> in {path.name}")
        for attr, val in node.attrib.items():
            if attr.lower().startswith("on"):
                raise ValueError(f"Disallowed SVG event handler {attr} in {path.name}")
            if "javascript:" in val.lower():
                raise ValueError(f"Disallowed javascript: URI in {path.name}")


def compile_sprite(src_dir=SRC_DIR):
    sprite = ET.Element(f"{{{SVG_NS}}}svg", {
        "aria-hidden": "true",
        "style": "position:absolute;width:0;height:0;overflow:hidden",
    })
    top_defs = ET.SubElement(sprite, f"{{{SVG_NS}}}defs")
    keys = []

    for svg_path in sorted(src_dir.glob("*.svg")):
        key = svg_path.stem
        if not KEY_RE.fullmatch(key):
            raise ValueError(f"Invalid icon key filename: {svg_path.name}")
        root = ET.fromstring(svg_path.read_text(encoding="utf-8"))
        if _local(root.tag) != "svg":
            raise ValueError(f"Root element is not <svg> in {svg_path.name}")
        _validate_safe_svg(root, svg_path)
        _strip_noise(root)
        _rewrite_ids(root, f"bi-{key}-", {})

        view_box = root.attrib.get("viewBox", "0 0 24 24")
        symbol = ET.SubElement(sprite, f"{{{SVG_NS}}}symbol", {
            "id": f"brand-{key}",
            "viewBox": view_box,
        })
        root_style_attrs = {
            attr: root.attrib[attr]
            for attr in PRESENTATION_ATTRS
            if attr in root.attrib
        }
        target = ET.SubElement(symbol, f"{{{SVG_NS}}}g", root_style_attrs) if root_style_attrs else symbol

        for child in list(root):
            if _local(child.tag) == "defs":
                for def_item in list(child):
                    top_defs.append(def_item)
            else:
                target.append(child)
        keys.append(key)

    if len(top_defs) == 0:
        sprite.remove(top_defs)

    # Compact deterministic serialization and strict XML round-trip validation.
    raw = ET.tostring(sprite, encoding="unicode")
    raw = re.sub(r">\s+<", "><", raw) + "\n"
    ET.fromstring(raw)
    return raw, keys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify deploy/agent-icons.svg matches assets/brand-icons/")
    args = parser.parse_args()

    compiled, keys = compile_sprite(SRC_DIR)
    if args.check:
        if not OUT_FILE.is_file() or OUT_FILE.read_text(encoding="utf-8") != compiled:
            raise SystemExit("deploy/agent-icons.svg is out of date; run `python3 tools/build_icons.py`.")
        print(f"OK: {OUT_FILE.relative_to(ROOT)} matches {len(keys)} source icons.")
        return

    OUT_FILE.write_text(compiled, encoding="utf-8")
    raw_bytes = compiled.encode("utf-8")
    gz_bytes = gzip.compress(raw_bytes, compresslevel=6)
    print(f"Wrote {OUT_FILE.relative_to(ROOT)}: {len(keys)} icons, raw={len(raw_bytes)} B, gzip={len(gz_bytes)} B")


if __name__ == "__main__":
    main()
