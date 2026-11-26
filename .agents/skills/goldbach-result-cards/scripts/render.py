"""Render a reviewed research report to self-contained HTML and PNG."""

import argparse
import base64
from html import escape
from io import BytesIO
import json
from pathlib import Path
from string import Template
from urllib.parse import urlsplit

from playwright.sync_api import sync_playwright
import qrcode


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
DEFAULT_URL = "https://www.goldbach.tech/"


def https_url(value):
    parsed = urlsplit(value)
    if (
        parsed.scheme != "https"
        or not parsed.hostname
        or parsed.username is not None
        or any(char.isspace() or char == "\\" for char in value)
    ):
        raise ValueError(f"Expected an HTTPS URL without credentials: {value!r}")
    return parsed


def data_image(mime, content):
    return f"data:{mime};base64,{base64.b64encode(content).decode('ascii')}"


def render_card(card):
    sources = []
    for source in card["sources"]:
        https_url(source["url"])
        sources.append(
            f'<a href="{escape(source["url"])}">{escape(source["label"])}</a>'
        )
    links = " · ".join(sources)
    return f"""
    <article>
      <div class="track">{escape(card["track"])}</div>
      <h2>{escape(card["title"])}</h2>
      <p>{escape(card["body"])}</p>
      <p class="scope">{escape(card["scope"])}</p>
      <div class="sources">{links}</div>
    </article>"""


def render_html(report, url):
    https_url(url)
    if not report["cards"] or any(not card["sources"] for card in report["cards"]):
        raise ValueError("Provide at least one card and cite a source for every card.")

    qr = qrcode.QRCode(box_size=5, border=4)
    qr.add_data(url)
    pixels = BytesIO()
    qr.make_image(fill_color="black", back_color="white").save(pixels, format="PNG")
    note = report.get("note")
    template = Template((HERE / "card.html").read_text(encoding="utf-8"))
    return template.substitute(
        title=escape(report["title"]),
        date=escape(report["date"]),
        summary=escape(report["summary"]),
        cards="".join(map(render_card, report["cards"])),
        note=f'<p class="note">{escape(note)}</p>' if note else "",
        logo=data_image("image/svg+xml", (ROOT / "deploy/goldbach-icon.svg").read_bytes()),
        qr=data_image("image/png", pixels.getvalue()),
        url=escape(url),
    )


def export(html, output, channel):
    output.parent.mkdir(parents=True, exist_ok=True)
    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(channel=channel)
        try:
            page = browser.new_page(viewport={"width": 1080, "height": 900})
            page.set_content(html)
            page.evaluate("Promise.all([...document.images].map(image => image.decode()))")
            page.locator(".report").screenshot(path=f"{output}.png", animations="disabled")
        finally:
            browser.close()
    Path(f"{output}.html").write_text(html, encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, help="UTF-8 report JSON")
    parser.add_argument("output", type=Path, help="output path without extension")
    parser.add_argument("--url", default=DEFAULT_URL)
    parser.add_argument("--channel", choices=["msedge", "chrome"])
    args = parser.parse_args()
    report = json.loads(args.report.read_text(encoding="utf-8-sig"))
    export(render_html(report, args.url), args.output, args.channel)


if __name__ == "__main__":
    main()
