#!/usr/bin/env bash
# Reset the repo to the state before running any of the demo skills.
# Removes the generated Lean sources and build outputs; keeps the Mathlib packages
# (.lake/packages) so the next run doesn't have to re-download them.
set -euo pipefail
cd "$(dirname "$0")"

# Generated mechanization (tracked or untracked)
git checkout HEAD -- MaxFlowMinCut 2>/dev/null || true
git clean -fdxq -- MaxFlowMinCut
rm -rf MaxFlowMinCut

# Project files a skill may have touched during setup
git checkout HEAD -- lakefile.toml lake-manifest.json lean-toolchain

# Build outputs of the project itself (not of Mathlib)
rm -rf .lake/build

# Scratch files used by the skills
rm -rf /tmp/scrutiny /tmp/check.lean

echo "Demo reset. Remaining changes vs HEAD (should be empty):"
git status --short
