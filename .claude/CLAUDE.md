# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Purpose

A teaching demo of AI auto-formalization: the Max-Flow Min-Cut theorem from the
Stanford CS161 Lecture 16 notes (`notes/*.pdf`) is mechanized in Lean 4 + Mathlib.
The Lean sources under `MaxFlowMinCut/` are **generated live in class** by the
project skills. They're not hand-maintained, and the repo is routinely reset with
git between runs.

## Skills

The demo is driven by project skills in `.claude/skills/`. Invoke a skill only
when the user names it, and follow its instructions; they take precedence over
general habits. Don't read the files of skills other than the one invoked. Skills
don't commit; the instructor manages git and resets with `./reset-demo.sh`.

## Layout of the mechanization

```
MaxFlowMinCut/Definitions.lean   -- only what's needed to state the theorems; imports only Mathlib
MaxFlowMinCut/Theorems.lean      -- headline theorems; each proof is a one-term call into Proofs/
MaxFlowMinCut/Proofs/*.lean      -- all internal lemmas and auxiliary definitions
```

Import only the specific Mathlib modules needed (never `import Mathlib`), to keep
compile times low. Mathlib has no max-flow/min-cut material, but reuse its
generic infrastructure (`Finset.sum`, `Relation.ReflTransGen`, compactness, ...).

## Commands

- Build everything: `lake build`. `lakefile.toml` uses `globs = ["MaxFlowMinCut.+"]`,
  so every file under `MaxFlowMinCut/` is built; there's no root module file.
- Build one module: `lake build MaxFlowMinCut.Proofs.<Name>`
- Run a scratch file against the built project: `lake env lean /tmp/foo.lean`
  (local modules must be built first; `lake env lean` on a library file that
  imports unbuilt local modules fails with "unknown module prefix").
- Fetch Mathlib oleans after a fresh clone or a toolchain bump: `lake exe cache get`
  (never build Mathlib from source).
- Read the notes: `pdftotext -layout notes/stanford-cs161-lecture16-notes.pdf -` (poppler-utils).

## Toolchain notes

- Lean `v4.35.0` (`lean-toolchain`), Mathlib pinned to tag `v4.35.0`. `autoImplicit = false`.
- Reals are imported from `Mathlib.Basic.Real.Basic` (`Mathlib.Data.Real.Basic` is deprecated).
- Warnings that Mathlib "is designed for use with the module system" are harmless.
- To find a lemma's module: `grep -rn "theorem <name>" .lake/packages/mathlib/Mathlib`
  (e.g. `Finset.sum_comm` lives in `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`).
