# Agent Instructions

@/Users/luoliwei/.codex/RTK.md

## Lean Workflow

- Check a single Lean file with `rtk lake env lean path/to/File.lean`.
- Run the mathlib style linter with `rtk lake env lake exe lint-style path/to/File.lean`.
- `lint-style` may warn that `scripts/nolints-style.txt` is missing; treat that as an empty
  exception list, not a lint failure.
