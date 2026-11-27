# Brand Icon Sources

Vector icons in this directory are compiled into `deploy/agent-icons.svg` by `python3 tools/build_icons.py`.

- Brand and coding-tool SVGs are sourced from [`@lobehub/icons-static-svg`](https://github.com/lobehub/lobe-icons) (MIT License) and the respective trademark owners' public brand marks.
- `nex-agi.svg` is traced from Nex-AGI's official geometric mark (`github.com/nex-agi`).
- `tool-other.svg` and `provider-unknown.svg` are minimal platform fallback icons.

To add or update an icon:
1. Add or edit `assets/brand-icons/<icon-key>.svg` (square `viewBox`, clean SVG without scripts or external links).
2. Run `python3 tools/build_icons.py` to regenerate `deploy/agent-icons.svg`.
3. Reference `<icon-key>` in `deploy/desk.py` (`MODEL_REGISTRY` or `HARNESS_ICONS`).
