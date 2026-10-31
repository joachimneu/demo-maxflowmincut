---
name: my-mechanize-srsly
description: Faithfully auto-formalize the Max-Flow Min-Cut theorem from notes/ in Lean 4 + Mathlib, laid out as MaxFlowMinCut/{Definitions,Theorems}.lean + MaxFlowMinCut/Proofs/. No sorry, no axioms, no vacuous statements.
disable-model-invocation: true
---

# Mechanize Max-Flow Min-Cut — for real

Auto-formalize the max-flow min-cut theorem from the lecture notes in `notes/`
in Lean 4 using Mathlib. The result must be **faithful** (definitions match the
notes, theorem statements mean what the notes say, nothing is vacuous) and
**complete** (no `sorry`, no `admit`, no new `axiom`, no tricks). Expect it to be
audited afterwards with `/my-scrutinize-mechanization`.

Work autonomously until `lake build` is clean. Do not commit.

## 0. Read the source

Extract the notes with `pdftotext -layout notes/stanford-cs161-lecture16-notes.pdf -`
(install `poppler-utils` with apt if it's missing). The relevant parts are Sec. 2
(flows), Sec. 4 (cuts), Sec. 5 (Lemma 2 = weak duality, Theorem 4 = MFMC),
and Sec. 6 (residual graph, Lemmas 5 and 6). Keep the notes' numbering in docstrings.

## 1. Project setup (skip whatever already exists)

- `lean-toolchain` pins Lean. `lakefile.toml` requires Mathlib at the tag that
  matches the toolchain (e.g. `v4.35.0`), and uses `globs = ["MaxFlowMinCut.+"]`
  so `lake build` builds every file under `MaxFlowMinCut/`. If it's missing, create it,
  then run `lake update` and `lake exe cache get` (never build Mathlib from source).
- Build with `lake build` (`lake env lean` can't see local modules until they're built).

## 2. Layout (strict)

```
MaxFlowMinCut/Definitions.lean   -- ONLY what's needed to STATE the theorems
MaxFlowMinCut/Theorems.lean      -- the headline theorems; each proof is ONE line
MaxFlowMinCut/Proofs/*.lean      -- all internal lemmas/defs, the actual proofs
```

- `Definitions.lean` imports only Mathlib. Never import `Proofs` here.
- `Proofs/*` import `Definitions` (and each other). `Theorems.lean` imports
  `Definitions` and the `Proofs` files it needs.
- Every theorem in `Theorems.lean` is `:= <one term>`, e.g. `:= Proofs.foo N`.
- Import only the Mathlib modules you need (e.g. `Mathlib.Algebra.BigOperators...`,
  `Mathlib.Topology...`). **Never** `import Mathlib`. When a lemma name is
  "unknown", find its module with grep in `.lake/packages/mathlib/Mathlib` and
  add that import (e.g. `Finset.sum_comm` is in `...BigOperators.Group.Finset.Sigma`).
- Reuse Mathlib (`Finset.sum`, `Relation.ReflTransGen`, `IsCompact`, ...) and don't
  re-prove what exists. Mathlib has **no** max-flow/min-cut material.
- Everything goes in `namespace MaxFlowMinCut`. Keep `autoImplicit` off.

## 3. Definitions (must match the notes)

Recommended encoding: complete digraph on a finite vertex type where non-edges
have capacity 0. This is equivalent to the notes' `G = (V, E), c : E → ℝ≥0`
because the capacity constraint forces flow 0 on non-edges. State this in the
module docstring.

- `FlowNetwork V` (`[Fintype V]`): `cap : V → V → ℝ`, `cap_nonneg : ∀ u v, 0 ≤ cap u v`,
  `s t : V`, `s_ne_t : s ≠ t`. Add **no other** assumptions. In particular, don't
  add the "no antiparallel edges" simplification of Sec. 6, integer capacities, etc.
- `Flow N`: `f : V → V → ℝ` with `0 ≤ f u v`, `f u v ≤ N.cap u v` for **all** `u v`, and
  conservation `∀ v, v ≠ N.s → v ≠ N.t → ∑ u, f u v = ∑ w, f v w`
  (in-flow = out-flow, at every vertex other than both `s` and `t`).
- `Flow.value F := ∑ v, F.f N.s v - ∑ u, F.f u N.s`. This is the general definition
  from the notes (out of s **minus** into s), not the simplified one.
- `Cut N`: `S : Finset V`, `s_mem : N.s ∈ S`, `t_not_mem : N.t ∉ S` (then `T = Sᶜ`).
- `Cut.capacity C := ∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, N.cap u v`. Only edges from `S` to `T`, with
  the argument order `cap u v`, u ∈ S, v ∈ T.
- `IsMaxFlow F := ∀ G : Flow N, G.value ≤ F.value` (non-strict `≤`!).
- `IsMinCut C := ∀ D : Cut N, C.capacity ≤ D.capacity`.

For every definition, double-check the quantifiers, `∧` vs `∨`, `→` direction,
`≤` vs `<`, argument order, and summation ranges against the notes.

## 4. Theorems.lean (headline statements)

```lean
/-- Lemma 2 (weak duality). -/
theorem weak_duality (F : Flow N) (C : Cut N) : F.value ≤ C.capacity := ...
/-- Theorem 4 (Max-Flow Min-Cut): a maximum flow and a minimum cut exist, and
their values coincide. -/
theorem max_flow_min_cut (N : FlowNetwork V) :
    ∃ F : Flow N, ∃ C : Cut N, IsMaxFlow F ∧ IsMinCut C ∧ F.value = C.capacity := ...
```

You may add a corollary that is a direct consequence (e.g.
`∀ F C, IsMaxFlow F → IsMinCut C → F.value = C.capacity`), but the **existential**
form above is mandatory. On its own, the universal form would be vacuous if
no max flow existed.

## 5. Proof roadmap (Proofs/)

A route known to work cleanly:

1. **`Proofs/CutFlow.lean`.** Define the excess `∑ v, f u v - ∑ v, f v u`. Show
   value = Σ_{u∈S} excess u (conservation; `t ∉ S`) = Σ_{u∈S} Σ_{v∉S} (f u v − f v u)
   (split with `Finset.sum_add_sum_compl`; the S×S part cancels via `Finset.sum_comm`).
   Weak duality follows.
2. **`Proofs/Existence.lean`.** A max flow exists by compactness. The set of
   flows is a closed subset of the compact box `Set.pi univ (fun u => Set.pi univ (fun v => Icc 0 (cap u v)))`
   (`isCompact_univ_pi`, `isCompact_Icc`, `IsCompact.of_isClosed_subset`; closedness
   via `isClosed_le`, `isClosed_eq`, `isClosed_iInter`, continuity of finite sums).
   Then `IsCompact.exists_isMaxOn` with continuous `value`. It's nonempty because of the zero flow.
3. **`Proofs/Residual.lean`.** Residual capacity `cf u v := cap u v - f u v + f v u`
   (this handles antiparallel edges without the Sec. 6 assumption). Residual edge iff
   `0 < cf u v`; reachability = `Relation.ReflTransGen`.
4. **`Proofs/Augment.lean`** (Lemma 6). Avoid simple paths entirely: by induction
   on `ReflTransGen`, a reachable `x` yields `d : V → V → ℕ` (edge multiplicities of a
   walk), supported on residual edges, with in(d) − out(d) = [v = x] − [v = s] at each
   vertex. Work with **net flow** `g u v = f u v − f v u`: set `g' = g + δ·(d − dᵀ)`,
   rebuild the flow as `f' u v := max 0 (g' u v)`, and choose `δ > 0` small
   (`Filter.eventually_all` over the finite type plus `nhdsWithin 0 (Ioi 0)`). Capacity,
   conservation and value depend only on net flow, so `value f' = value f + δ`.
5. **`Proofs/Main.lean`** (Lemma 5 + Theorem 4). Take a max flow; `t` isn't
   residual-reachable (else Lemma 6 contradicts maximality). `S` = the reachable set
   is a cut; across it `f u v = cap u v` and `f v u = 0`, so value = capacity. Weak
   duality makes that cut minimal.

You may deviate, but the statements in `Definitions.lean`/`Theorems.lean` stay as
specified. Never weaken a statement to make a proof go through.

## 6. Finish

1. `lake build` with **full output** visible: no errors, no `declaration uses 'sorry'`.
2. `grep -rnE "sorry|admit|axiom|native_decide|implemented_by|extern|#exit" MaxFlowMinCut`
   returns nothing.
3. In a scratch file outside the library (e.g. `/tmp/check.lean`, run with
   `lake env lean`), `#print axioms MaxFlowMinCut.max_flow_min_cut` (and the other
   theorems) shows only `propext`, `Classical.choice`, `Quot.sound`. Delete the
   scratch file afterwards.
4. Report: the file tree, the statements in `Definitions.lean` and `Theorems.lean`
   (quoted verbatim), how each maps to the notes, and the outputs of the checks above.
