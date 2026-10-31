---
name: my-scrutinize-mechanization
description: Audit the Lean mechanization in MaxFlowMinCut/ against the notes. Runs Lean-side checks (sorry, axioms, cheats, statement provenance) and semantic checks (definition and algorithm faithfulness, sanity tests on concrete examples, non-vacuity, mutation tests), explaining each check and its result. Use only when the user explicitly names this skill.
---

# Scrutinize the mechanization

You are an independent, skeptical auditor. A green `lake build` proves only that
*some* statements were proven, not that they are the *right* statements or that
the proofs are honest. And an algorithm printing the right number on an example
proves nothing about its correctness. Your job is to find every way the
mechanization in `MaxFlowMinCut/` might fail to establish what the notes in
`notes/` claim (the Max-Flow Min-Cut theorem and correctness of Ford–Fulkerson),
and to explain each check to a seminar audience.

Rules:
- **Audit, don't fix.** Never edit files under `MaxFlowMinCut/`. Put all experiments
  in a scratch dir, `/tmp/scrutiny/`, and run them with `lake env lean /tmp/scrutiny/X.lean`
  from the repo root (after `lake build`, so the project's `.olean`s exist).
- **Be independent.** Judge only the code and the notes. Don't read other skills
  in `.claude/skills/`, and don't trust docstrings or comments: a docstring saying
  "edges from S to T" proves nothing about the code under it.
- **Evidence for every verdict.** Quote the command or Lean snippet and its output.
  Run checks for real; never predict an outcome.
- When a check fails, keep going and run all checks; flaws can mask each other.

Work through the checks below in order. For each one, briefly tell the audience
**what** the check is, **why** it matters (what can go wrong), **how** you ran it,
and the **result** (✅ pass / ❌ fail / ⚠️ warning) with evidence.

---

## Part A: Lean-side checks (is the proof real?)

**A1. Clean build, full log.**
Run `lake build 2>&1 | tee /tmp/scrutiny/build.log` and read *all* of it. Truncated
output (`| tail`) can hide warnings. Look for `error`, `declaration uses 'sorry'`,
and other warnings. *Why:* `sorry` only produces a **warning**, so a project with
holes still "builds successfully".

**A2. Textual red-flag scan.**
`grep -rnE '\bsorry\b|\badmit\b|\baxiom\b|\bopaque\b|native_decide|implemented_by|@\[extern|\bunsafe\b|\bpartial\b|decreasing_by|#exit|set_option|macro|syntax|elab|notation|instance|attribute \[|local |open .* in|run_cmd|run_tac|Lean\.Elab|decide := true' MaxFlowMinCut`
Explain each hit:
- `sorry`/`admit`: unproven holes.
- `axiom`: an unproven assumption, maybe inconsistent (`axiom oops : False`).
- `opaque`: an uninterpretable "definition", so statements about it say nothing.
- `partial def`: the algorithm becomes opaque to the logic, so nothing about it can
  honestly be proven (or `decreasing_by sorry` hides a termination hole).
- `native_decide`/`implemented_by`/`extern`: trust compiled code instead of the kernel.
  With `implemented_by`, the code that `#eval` runs may differ from the definition the
  theorems are about.
- `#exit`: silently stops elaboration, so the rest of the file is never checked.
- `macro`/`syntax`/`elab`/`notation`: can redefine what familiar syntax means.
- `instance`/`attribute [-instance]`/`local`: a custom `LE ℤ` or `Fintype` instance could
  change the meaning of the statement. (`Decidable` instances to run the algorithm are fine.)
- `set_option`: e.g. `debug.skipKernelTC` skips kernel checking (`maxHeartbeats` is harmless).
A hit isn't automatically a failure; judge each one.

**A3. Axiom audit (decisive for holes).**
In `/tmp/scrutiny/Axioms.lean`: `import MaxFlowMinCut.Theorems`, then
`#print axioms MaxFlowMinCut.<thm>` for **every** theorem in `Theorems.lean`.
Allowed: `propext`, `Classical.choice`, `Quot.sound`. Anything else is a failure:
`sorryAx` means a hole somewhere in the transitive dependencies (however well
hidden), `Lean.ofReduceBool` means `native_decide`, and custom names are axioms.
*Why:* this catches holes regardless of macros, renames or file placement.

**A4. Layout and dependency discipline.**
- `Definitions.lean` imports only Mathlib/Batteries/core (never `Proofs`) and contains
  definitions only (no theorems).
- `Theorems.lean` contains only headline theorems, each with a one-term proof
  invoking `Proofs`.
- No `import Mathlib` (whole library). List the imports.

**A5. Statement provenance (no shadowing).**
Every constant in a headline **statement** must come from `MaxFlowMinCut.Definitions`
or from Mathlib/core, never from `Proofs/`. (Otherwise `Proofs` could quietly
redefine `IsFlow` or `fordFulkerson` with a weaker meaning.) Run this in `/tmp/scrutiny/Deps.lean`:
```lean
import MaxFlowMinCut.Theorems
open Lean Elab Command in
elab "#stmt_deps " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some ci := env.find? n | throwError "unknown {n}"
  for c in ci.type.getUsedConstants.toList.eraseDups do
    let mod := match env.getModuleIdxFor? c with
      | some i => env.header.moduleNames[i.toNat]!
      | none => `current_file
    logInfo m!"{c}  ←  {mod}"
#stmt_deps MaxFlowMinCut.max_flow_min_cut   -- repeat for each headline theorem
```
Also flag any *instance* in that list that comes from a project module.

**A6. Elaborated statement.**
`set_option pp.explicit true in #check @MaxFlowMinCut.<thm>` (and `#print` each
definition). Look for surprises hidden by notation: unexpected coercions (`ℕ`
subtraction truncates, `Int.toNat` clamps negatives to 0, `ℕ → ℤ` casts), implicit
arguments fixed to odd values, `Decidable`/`Fintype` instance mismatches.

---

## Part B: Semantic checks (is it the right theorem / the right algorithm?)

Extract the notes: `pdftotext -layout notes/stanford-cs161-lecture16-notes.pdf -`
(install `poppler-utils` if needed). Relevant: Sec. 2, 4, 5 (Lemma 2, Cor. 3,
Theorem 4), 6 (residual graph, Lemmas 5–6, Algorithm 1).

**B1. Definition-by-definition comparison with the notes.**
Make a table: notes' definition | Lean definition (verbatim) | match? Check the
usual error sources explicitly:
- **Network.** Capacities `≥ 0` (integers here), distinguished `s`, `t`, `s ≠ t`, and
  the encoding of non-edges (capacity 0 is fine). **Extra fields** (no antiparallel
  edges, `cap u u = 0`, ...) are added assumptions: are they justified, and are they *satisfiable*?
- **Flow.** `0 ≤ f ≤ cap` for all pairs; conservation **in = out** at **every**
  `v ∉ {s, t}`. Check the connective (`v ≠ s → v ≠ t → …` is right; `v ≠ s ∨ v ≠ t → …`
  is wrong), the summation index, and the orientation `f u v` vs `f v u`.
- **Value.** Out of `s` **minus** into `s` (the simplified "out of s" formula is only
  valid without edges into `s`).
- **Cut.** `s ∈ S`, `t ∉ S`, `T = V \ S`.
- **Cut capacity.** Sum over `u ∈ S`, `v ∈ T` of `cap u v`: **forward edges only,
  argument order u→v.** Swapped arguments (`cap v u`) or summing over all `v` are classic slips.
- **Max/min predicates.** `IsMaxFlow` and `IsMinCut` with **non-strict** `≤`. A strict
  `<` makes a predicate unsatisfiable.

**B2. Algorithm faithfulness (Algorithm 1).**
Compare each algorithm definition with Sec. 6:
- **Residual capacity** `c_f` (with antiparallel edges, `cap u v − f u v + f v u` is the right generalization).
- **Augmenting path.** A simple path from `s` to `t` using only edges with `c_f > 0`.
- **Path search.** It must find a path **whenever one exists** (otherwise the loop may
  stop early with a non-max flow); this should be proven.
- **Bottleneck.** The minimum of `c_f` along the path.
- **Augmentation.** Matches `f'` from Lemma 6 (net change `+F` along the path).
- **Loop.** Starts from the zero flow and repeats until no augmenting path is left. If
  there's a round budget/fuel, is it justified, and does the theorem cover the case where
  the budget runs out? (A too-small budget silently returns a non-max flow.)
- Is the algorithm **computable** (it should `#eval`), and is the theorem about **this**
  definition, unconditionally (no hypothesis like "assume the loop terminated")?

**B3. Sanity tests on the notes' worked example (Fig. 1).**
These are "unit tests for definitions". In `/tmp/scrutiny/Example.lean`, model Fig. 1 on
`Fin 5` with `s=0, a=1, b=2, c=3, t=4` and capacities
`s→a 10, s→c 11, a→b 5, a→c 12, c→b 3, b→t 100, c→t 10` (all others 0), e.g. via
`![![…], …]`. Adapt to the actual names. Use `#eval` to compute numbers, and
`decide` (after unfolding definitions) or `norm_num`/`simp [Fin.sum_univ_five]` to prove them.
Practical notes, so the file compiles on the first try:
- `![…]` needs `import Mathlib.Data.Fin.VecNotation` (the project may not import it;
  without it `!` parses as boolean negation and every matrix fails to elaborate).
- Predicates without a `Decidable` instance (e.g. `IsCut`, `IsFlow`, `IsMinCut`) must be
  unfolded first: `by unfold IsCut; decide`, `by unfold IsMinCut IsCut cutCapacity; decide`.
- `decide`/`decide +kernel` usually **cannot** reduce the algorithm itself: e.g. Mathlib's
  `List.permutations` is defined by well-founded recursion and gets stuck. Don't spend time
  on it, and never fall back to `native_decide`. Check the algorithm's output with `#eval`
  (fine, provided A2 found no `implemented_by`), and obtain a kernel-checked proof of the
  same fact *via the headline theorems* (see the first bullet).

Tests:
- The algorithm: `#eval value fig1 (fordFulkerson fig1)` prints **18** (also `#eval` the flow
  matrix). Kernel-checked version: `IsFlow` is `(fordFulkerson_isMaxFlow fig1).1`, and the
  value follows from `max_flow_min_cut fig1 (fordFulkerson_isMaxFlow fig1) hmin` with
  `hmin : IsMinCut fig1 {0, 1, 3}` (by `decide`, see B4) and `cutCapacity fig1 {0,1,3} = 18`
  (by `decide`), closed with `omega`. Also check an explicit flow of value 18 by `decide`
  (e.g. the `#eval`ed matrix, copied in as a literal): it's reused in B4.
- The sample flow (`s→a 5, s→c 11, a→b 5, a→c 0, c→b 1, b→t 6, c→t 10`) is a flow of value **16**.
- The cut `S = {s, a, c}` has capacity **18**, and `S = {s, c}` has capacity **23** (the notes
  stress that the backward edge `a→c` is not counted).
- A non-flow is rejected: changing `c→b` to 2 in the sample flow breaks conservation at `c`,
  so `¬ IsFlow` must be provable.
- Extra stress test for the general definitions: a tiny network with an edge **into**
  `s` and a pair of **antiparallel** edges. Check that the value and the algorithm's result
  match a hand computation (`#eval`, plus the theorem-based proof as above with a min cut
  found by hand). E.g. `Fin 3`, `s=0, x=1, t=2`, `s→x 3, x→s 2, x→t 2, s→t 1`: max flow 3,
  min cut `{s, x}`; the flow `s→x 3, x→s 2, x→t 1` has value `3 − 2 = 1` (out minus in).
If any expected number fails, find what the definition computes instead
(`#eval` it) and report the discrepancy.

**B4. Non-vacuity: are the hypotheses satisfiable?**
A theorem `H → P` with unsatisfiable `H` is "true" and worthless. For **each**
headline theorem, exhibit concrete objects satisfying **all** its hypotheses at once
(using Fig. 1). `IsMaxFlow` is witnessed by the Ford–Fulkerson flow (if that theorem
holds). For `IsMinCut fig1 {0,1,3}`, everything is finite, so try
`by unfold IsMinCut IsCut cutCapacity; decide` (or prove it via weak duality). If you
can't find a witness, try to prove the **negation** (e.g. `¬ IsMinCut fig1 {0,1,3}`, or
`∀ S, ¬ IsMinCut N S`); success is a definitive ❌.

**B5. Mutation test: is the proof too easy?**
Copy a headline statement into the scratch file with a **deliberately wrong
conclusion**, e.g. `value N f = cutCapacity N S + 1`, or simply `False`, keeping the
hypotheses. Try to prove it (the project's own proof route, `simp_all`, `linarith [...]`
with facts derived from the hypotheses, `exact?`). If a wrong conclusion is provable,
the hypotheses are contradictory and the original theorem is vacuous ❌.

**B6. Statement faithfulness and strength.**
Compare each headline theorem with the notes:
- **Theorem 4** says the max-flow value **equals** the min-cut capacity. The universal
  form "`∀ f S, IsMaxFlow f → IsMinCut S → value f = cap S`" is only meaningful together
  with proofs that a max flow **and** a min cut exist. Flag ⚠️/❌ if either existence is
  missing from `Theorems.lean`.
- **Lemma 2** (weak duality) should be stated for **every** flow and **every** cut, without
  maximality hypotheses. Is it there at all?
- **Ford–Fulkerson** must be stated as: the algorithm's output is a max flow, for
  **every** network, with no extra hypotheses.
- Look for **extra hypotheses** not in the notes, **swapped quantifiers**
  (`∃ C, ∀ F` vs `∀ F, ∃ C`), and `≤` where the notes have `=`.
- Note legitimate modelling choices (integer capacities, vertices `Fin n`,
  complete-digraph encoding, brute-force path search) as ℹ️, not failures.

**B7. Proof spot check.**
Skim `Proofs/` for suspicious patterns that A3 can't see: a key step closed by
deriving `False` from the theorem's own hypotheses (e.g. `linarith [hS.2 S hS.1]`,
`absurd`, `lt_irrefl`, `exfalso`), case splits where the hard case is discharged "too
easily", lemmas that are stated but never used, and proofs that reason about an
inlined expression instead of the definition named in the statement (e.g. an explicit
sum instead of `cutCapacity`). Mismatches there are where definitional bugs hide.

---

## Report

End with:
1. A summary table: check | result | one-line finding.
2. For each ❌/⚠️: the exact location (`file:line`), what is wrong, why it matters,
   evidence, and the minimal fix (described, not applied).
3. A verdict: does the mechanization faithfully and completely prove (a) the
   Max-Flow Min-Cut theorem and (b) correctness of Ford–Fulkerson as in the notes?
   (Yes / No / Yes with caveats, for each.)

Leave `/tmp/scrutiny/` in place so the audience can inspect the experiments.
