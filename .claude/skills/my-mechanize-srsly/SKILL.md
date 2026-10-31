---
name: my-mechanize-srsly
description: Auto-formalize the Max-Flow Min-Cut theorem and the Ford-Fulkerson algorithm from notes/ in Lean 4 + Mathlib, laid out as MaxFlowMinCut/{Definitions,Theorems}.lean + MaxFlowMinCut/Proofs/. Use only when the user explicitly names this skill.
---

# Mechanize Max-Flow Min-Cut + Ford–Fulkerson — for real

Auto-formalize, from the lecture notes in `notes/`, in Lean 4 with Mathlib:
1. the **Max-Flow Min-Cut theorem** (Theorem 4), and
2. **correctness of the Ford–Fulkerson algorithm** (Algorithm 1): it returns a maximum flow.

We work with **integer capacities only** (as in the notes' running-time analysis).
The result must be **faithful** (definitions match the notes, statements mean what
the notes say, nothing is vacuous) and **complete** (no `sorry`, no `admit`, no new
`axiom`, no tricks). It will be audited afterwards with `/my-scrutinize-mechanization`.

Work autonomously until `lake build` is clean. Do not commit.

## 0. Read the source

`pdftotext -layout notes/stanford-cs161-lecture16-notes.pdf -` (apt-install
`poppler-utils` if missing). Relevant: Sec. 2 (flows), Sec. 4 (cuts), Sec. 5 (Lemma 2
= weak duality, Corollary 3, Theorem 4 = MFMC), Sec. 6 (residual graph, Lemma 5,
Lemma 6, Algorithm 1 and the integer-capacity termination argument). Cite the
notes' numbering in docstrings.

## 1. Project setup (skip whatever already exists)

`lean-toolchain` pins Lean. `lakefile.toml` requires Mathlib at the matching tag
(e.g. `v4.35.0`) with `globs = ["MaxFlowMinCut.+"]`. If it's missing, create it and run
`lake update && lake exe cache get` (never build Mathlib). Build with `lake build`;
`lake env lean` can't see local modules until they're built.

## 2. Layout (strict)

```
MaxFlowMinCut/Definitions.lean   -- everything needed to STATE the theorems, incl. the algorithm
MaxFlowMinCut/Theorems.lean      -- the headline theorems; each proof is ONE term
MaxFlowMinCut/Proofs/*.lean      -- all internal lemmas, the actual proofs
```

- `Definitions.lean` imports only Mathlib/Batteries and contains **no theorems or
  proofs**, only definitions (plus `Decidable` instances needed to run the algorithm).
- `Proofs/*` import `Definitions` (and each other). `Theorems.lean` imports
  `Definitions` and the `Proofs` files it needs, and each proof is `:= Proofs.foo …`.
- Import only the Mathlib modules you need, **never** `import Mathlib`. If a lemma is
  "unknown", grep `.lake/packages/mathlib/Mathlib` (and `.lake/packages/batteries`) for
  its module. Mathlib has **no** max-flow material; reuse generic infrastructure.
- `namespace MaxFlowMinCut`, `autoImplicit` off.

## 3. Definitions (must match the notes)

Vertices are `Fin n`. Any finite graph can be labelled `0, …, n-1`, and it gives a
canonical computable vertex list (`List.finRange n`) for the algorithm. Encode the
graph as a complete digraph whose non-edges have capacity 0. This is equivalent to the
notes' `G = (V, E), c : E → ℤ≥0` because the capacity constraint forces flow 0 on
non-edges. Say so in the module docstring. Flows are plain functions; properties are predicates.

- `structure FlowNetwork (n : ℕ)`: `cap : Fin n → Fin n → ℤ`, `cap_nonneg : ∀ u v, 0 ≤ cap u v`,
  `s t : Fin n`, `s_ne_t : s ≠ t`. **No other assumptions.** In particular, don't add
  the Sec. 6 "no antiparallel edges" simplification.
- `IsFlow N f` for `f : Fin n → Fin n → ℤ`: `∀ u v, 0 ≤ f u v`, `∀ u v, f u v ≤ N.cap u v`, and
  `∀ v, v ≠ N.s → v ≠ N.t → ∑ u, f u v = ∑ w, f v w`.
- `value N f : ℤ := ∑ v, f N.s v - ∑ u, f u N.s` (out of s **minus** into s).
- `IsCut N (S : Finset (Fin n)) := N.s ∈ S ∧ N.t ∉ S`.
- `cutCapacity N S : ℤ := ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v`. Only the forward edges S → T,
  argument order `cap u v` with u ∈ S, v ∈ T.
- `IsMaxFlow N f := IsFlow N f ∧ ∀ g, IsFlow N g → value N g ≤ value N f` (non-strict).
- `IsMinCut N S := IsCut N S ∧ ∀ T, IsCut N T → cutCapacity N S ≤ cutCapacity N T` (non-strict).

**Ford–Fulkerson (Algorithm 1).** Use the generic method (any augmenting path),
the easiest variant to mechanize. Here the path is found by exhaustive search over
simple paths, which is trivially correct. All of these are computable definitions:
- `residualCap N f u v : ℤ := N.cap u v - f u v + f v u`. This is the notes' `c_f`
  generalized to allow antiparallel edges; it coincides with the notes' formula
  under their Sec. 6 assumption. Docstring it.
- `pathEdges (p : List (Fin n)) := p.zip p.tail`.
- `IsAugmentingPath N f p`: `p.head? = some N.s ∧ p.getLast? = some N.t ∧ p.Nodup ∧
  p.IsChain (fun u v => 0 < residualCap N f u v)` (a simple s–t path in `G_f`;
  `List.IsChain` is the current name of the old `List.Chain'`). Provide a `Decidable`
  instance (e.g. `by unfold IsAugmentingPath; infer_instance`).
- `findAugmentingPath N f : Option (List (Fin n))`: the first `p` in
  `(List.finRange n).sublists.flatMap List.permutations` with `IsAugmentingPath N f p`
  (via `List.find?`). Exponential, but fine for a demo.
- `bottleneck N f p : ℤ`: the minimum of `residualCap` over `pathEdges p`.
- `augment N f p`: push `δ := bottleneck N f p` along `p`. Recommended generalization
  of the notes' `f'` that is robust with antiparallel edges, working with **net flow**:
  `augment N f p u v := max 0 (f u v - f v u + δ * ((pathEdges p).count (u, v) - (pathEdges p).count (v, u)))`.
  Docstring why this matches the notes (same net flow change; reduces to f ± F
  under the no-antiparallel assumption).
- `ffLoop N : ℕ → (Fin n → Fin n → ℤ) → (Fin n → Fin n → ℤ)` with
  `ffLoop N 0 f = f`, and `ffLoop N (k+1) f = match findAugmentingPath N f with | none => f | some p => ffLoop N k (augment N f p)`.
- `fordFulkerson N := ffLoop N (∑ v, N.cap N.s v).toNat (fun _ _ => 0)`: start
  from the zero flow, and loop while an augmenting path exists. The round budget is the
  notes' integer argument (each round adds ≥ 1 to the value, which never exceeds the
  total capacity out of `s`). Docstring it.

Double-check every definition against the notes: quantifiers, `∧` vs `∨`, `→`
direction, `≤` vs `<`, argument order, summation ranges.

## 4. Theorems.lean (headline statements)

```lean
/-- Lemma 2 (weak duality). -/
theorem weak_duality (N : FlowNetwork n) {f} {S} (hf : IsFlow N f) (hS : IsCut N S) :
    value N f ≤ cutCapacity N S := …
/-- Algorithm 1 is correct: Ford–Fulkerson returns a maximum flow. -/
theorem fordFulkerson_isMaxFlow (N : FlowNetwork n) : IsMaxFlow N (fordFulkerson N) := …
/-- Lemma 5 / Corollary 3: a minimum cut exists, with capacity equal to the value of the flow found by Ford–Fulkerson. -/
theorem exists_minCut_eq_fordFulkerson (N : FlowNetwork n) :
    ∃ S, IsMinCut N S ∧ cutCapacity N S = value N (fordFulkerson N) := …
/-- Theorem 4 (Max-Flow Min-Cut): the value of any max flow equals the capacity of any min cut. -/
theorem max_flow_min_cut (N : FlowNetwork n) {f} {S} (hf : IsMaxFlow N f) (hS : IsMinCut N S) :
    value N f = cutCapacity N S := …
```

On its own, `max_flow_min_cut` would be vacuous if no max flow or no min cut existed. The
other two theorems show both exist, so all four are mandatory.

## 5. Proof roadmap (Proofs/)

1. **`Proofs/CutFlow.lean`.** Excess `∑ v, f u v - ∑ v, f v u`. Value = Σ_{u∈S} excess u
   (conservation; `t ∉ S`) = Σ_{u∈S} Σ_{v∉S} (f u v − f v u) (split with
   `Finset.sum_add_sum_compl`; the S×S part cancels via `Finset.sum_comm`, which is in
   `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`). Weak duality follows.
2. **`Proofs/PathSearch.lean`.** Soundness: `findAugmentingPath N f = some p →
   IsAugmentingPath N f p` (`List.find?_some`). Completeness:
   `findAugmentingPath N f = none → ∀ p, ¬ IsAugmentingPath N f p`. A nodup `p` satisfies
   `p ⊆ List.finRange n` (`List.mem_finRange`), so `List.subperm_of_subset` gives
   `l ~ p`, `l <+ finRange n`. Then use `List.mem_sublists`, `List.mem_permutations`
   and `List.find?_eq_none`.
3. **`Proofs/Augment.lean`** (Lemma 6). For a list `p` forming a chain from `x` to `y`:
   `∑ w, count (v,w) − ∑ w, count (w,v) = [v = x] − [v = y]` (induction on `p`).
   For nodup `p`: each count ≤ 1, and `(u,v)` and `(v,u)` are never both edges. The
   bottleneck is ≥ 1 and ≤ every residual capacity on the path. Hence `augment` is a
   flow (capacity via the net-flow bounds `−cap v u ≤ net ≤ cap u v`; conservation and
   value depend only on net flow) and `value (augment …) = value f + bottleneck`.
4. **`Proofs/ResidualCut.lean`** (Lemma 5). `R :=` the set of `v` with a simple
   residual path from `s` (classical `Finset.filter`). It's closed under residual edges:
   if `w` already occurs on the path to `v`, take the prefix up to `w`; otherwise append `w`.
   No augmenting path ⇒ `t ∉ R` ⇒ `R` is a cut with `f u v = cap u v` and `f v u = 0` across it,
   so `value = cutCapacity R`.
5. **`Proofs/FordFulkerson.lean`.** The zero flow is a flow. `ffLoop` preserves `IsFlow`.
   By induction on `k`, `ffLoop N k f` either has no augmenting path, or its value is
   ≥ `value f + k`. In the first case Lemma 5 + weak duality give maximality. In the
   second, the value reaches the bound `∑ v, cap s v`, which bounds every flow.
6. **`Proofs/Main.lean`.** Theorem 4: any two max flows have equal value. Combine the
   Ford–Fulkerson cut with minimality of `S` and weak duality.

You may deviate in the proofs, but the statements in `Definitions.lean`/`Theorems.lean`
stay as specified. Never weaken a statement to make a proof go through.

## 6. Finish

1. `lake build` with **full output** visible: no errors, no `declaration uses 'sorry'`.
2. `grep -rnE "sorry|admit|axiom|native_decide|implemented_by|extern|partial|#exit" MaxFlowMinCut`
   returns nothing.
3. In a scratch file `/tmp/check.lean` (run with `lake env lean`; delete it afterwards):
   - `#print axioms` for each headline theorem shows only `propext`, `Classical.choice`, `Quot.sound`.
   - Run the algorithm on the notes' Fig. 1 example with `Fin 5`, `s=0, a=1, b=2, c=3, t=4`,
     capacities `s→a 10, s→c 11, a→b 5, a→c 12, c→b 3, b→t 100, c→t 10`:
     `#eval value fig1 (fordFulkerson fig1)` must print `18`.
4. Report: the file tree, the statements of `Definitions.lean` and `Theorems.lean`
   (quoted verbatim), how each maps to the notes, and the outputs of the checks above.
