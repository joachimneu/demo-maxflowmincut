---
name: my-scrutinize-mechanization
description: Audit the Lean mechanization in MaxFlowMinCut/ against the notes. Runs Lean-side checks (sorry, axioms, cheats, statement provenance) and semantic checks (definition faithfulness, sanity tests on concrete examples, non-vacuity, mutation tests), explaining each check and its result. Use only when the user explicitly names this skill.
---

# Scrutinize the mechanization

You are an independent, skeptical auditor. A green `lake build` proves only that
*some* statements were proven, not that they are the *right* statements or that
the proofs are honest. Your job is to find every way the mechanization in
`MaxFlowMinCut/` might fail to establish the Max-Flow Min-Cut theorem as stated in
`notes/`, and to explain each check to a seminar audience.

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
`grep -rnE '\bsorry\b|\badmit\b|\baxiom\b|\bopaque\b|native_decide|implemented_by|@\[extern|\bunsafe\b|\bpartial\b|#exit|set_option|macro|syntax|elab|notation|instance|attribute \[|local |open .* in|run_cmd|run_tac|Lean\.Elab|decide := true' MaxFlowMinCut`
Explain each hit:
- `sorry`/`admit`: unproven holes.
- `axiom`: an unproven assumption, maybe inconsistent (`axiom oops : False`).
- `opaque`: an uninterpretable "definition", so statements about it say nothing.
- `native_decide`/`implemented_by`/`extern`: trust compiled code instead of the kernel.
- `#exit`: silently stops elaboration, so the rest of the file is never checked.
- `macro`/`syntax`/`elab`/`notation`: can redefine what familiar syntax means, e.g. a
  tactic that expands to `sorry`, or `≤` meaning something else.
- `instance`/`attribute [-instance]`/`local`: a custom `LE ℝ` or `Fintype` instance
  could change the meaning of the statement.
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
- `Definitions.lean` imports only Mathlib/core (never `Proofs`).
- `Theorems.lean` contains only headline theorems, each with a one-term proof
  invoking `Proofs`.
- No `import Mathlib` (whole library). List the imports.
- The theorems in `Theorems.lean` use the definitions from `Definitions.lean`.

**A5. Statement provenance (no shadowing).**
Every constant in a headline **statement** must come from `MaxFlowMinCut.Definitions`
or from Mathlib/core, never from `Proofs/`. (Otherwise `Proofs` could
quietly redefine `Flow` or `IsMaxFlow` with a weaker meaning.) Run this in
`/tmp/scrutiny/Deps.lean`:
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
definition). Look for surprises hidden by notation: unexpected coercions (ℕ
subtraction truncates, `ℕ → ℝ` casts), implicit arguments fixed to odd values,
`Decidable`/`Fintype` instance mismatches, `Set` vs `Finset` confusion.

---

## Part B: Semantic checks (is it the right theorem?)

Extract the notes: `pdftotext -layout notes/stanford-cs161-lecture16-notes.pdf -`
(install `poppler-utils` if needed). Relevant: Sec. 2, 4, 5 (Lemma 2, Theorem 4), 6.

**B1. Definition-by-definition comparison with the notes.**
Make a table: notes' definition | Lean definition (verbatim) | match? For each
one, explicitly check the usual error sources:
- **Network.** Capacities `≥ 0`, distinguished `s`, `t`, `s ≠ t`. Encoding of
  non-edges (capacity 0 is fine). **Extra fields** (no antiparallel edges, integer
  capacities, `cap u u = 0`, ...) are added assumptions: are they justified, and
  are they *satisfiable*?
- **Flow.** `0 ≤ f ≤ cap` for all pairs; conservation **in = out** at **every**
  `v ∉ {s, t}`. Check the connective (`v ≠ s → v ≠ t → …` is right; `v ≠ s ∨ v ≠ t → …`
  is wrong), that sums run over the right index, and that `f u v` vs `f v u` is
  oriented correctly.
- **Value.** Out of `s` **minus** into `s` (the simplified "out of s" formula is
  only valid without edges into `s`).
- **Cut.** `s ∈ S`, `t ∉ S`, `T = V \ S`.
- **Cut capacity.** Sum over `u ∈ S`, `v ∈ T` of `cap u v`: **forward edges only,
  argument order u→v.** Swapped arguments (`cap v u`) or summing over all `v` are classic slips.
- **Max/min predicates.** `IsMaxFlow F := ∀ G, G.value ≤ F.value` with **non-strict
  `≤`**; `IsMinCut` analogous. A strict `<` makes the predicate unsatisfiable.

**B2. Sanity tests on the notes' worked example (Fig. 1).**
These are "unit tests for definitions". Model Fig. 1 in `/tmp/scrutiny/Example.lean`
with `V := Fin 5`, `s=0, a=1, b=2, c=3, t=4` and capacities
`s→a 10, s→c 11, a→b 5, a→c 12, c→b 3, b→t 100, c→t 10` (all others 0), e.g. via
`![![…], …]` or a `match`. Adapt to the actual structure and field names. Prove with
`decide`/`norm_num [Fin.sum_univ_five, …]`/`simp`:
- The sample flow (`s→a 5, s→c 11, a→b 5, a→c 0, c→b 1, b→t 6, c→t 10`) **is** a
  `Flow` and has value **16**.
- The flow `s→a 7, s→c 11, a→b 5, a→c 2, c→b 3, b→t 8, c→t 10` is a `Flow` with value **18**.
- Cut `S = {s, a, c}` has capacity **18**; cut `S = {s, c}` has capacity **23**
  (the notes stress that the backward edge `a→c` is not counted).
- A non-flow is rejected: changing `c→b` to 2 breaks conservation at `c`, so
  constructing that `Flow` must be **impossible** (prove the conservation field is false).
If any expected number can't be proven, find what the definition computes
instead (e.g. `norm_num` the capacity to a value), and report the discrepancy.

**B3. Non-vacuity: are the hypotheses satisfiable?**
A theorem `H → P` with unsatisfiable `H` is "true" and worthless. For **each**
headline theorem, exhibit concrete objects satisfying **all** its hypotheses at
once (using the Fig. 1 example). In particular prove `IsMaxFlow F18` (e.g.
`∀ G, G.value ≤ 18` via the project's weak duality with the 18-cut, if available)
and `IsMinCut` of the 18-cut. Also check that the structures themselves are
inhabited (`FlowNetwork`, `Flow` via the zero flow, `Cut`). If you can't find a
witness, try to prove the **negation** (e.g. `∀ F, ¬ IsMaxFlow F`); success
is a definitive ❌.

**B4. Mutation test: is the proof too easy?**
Copy a headline statement into the scratch file with a **deliberately wrong
conclusion**, e.g. `F.value = C.capacity + 1`, or simply `False`, keeping the
hypotheses. Try to prove it (use the project's own proof route, `simp_all`,
`linarith [...]`, `exact?`, contradiction from hypotheses). If a wrong conclusion
is provable, the hypotheses are contradictory and the original theorem is vacuous ❌.
Also try the strengthened original statements: a correct development usually makes them easy.

**B5. Statement faithfulness and strength.**
Compare each headline theorem with the notes:
- **Theorem 4** says the max-flow value **equals** the min-cut capacity. A faithful
  form is `∃ F C, IsMaxFlow F ∧ IsMinCut C ∧ F.value = C.capacity` (or `sSup = sInf`
  with attainment). The form "`∀ F C, IsMaxFlow F → IsMinCut C → …`" alone is
  weaker: it says nothing unless a max flow exists. Flag it ⚠️ unless existence
  is proven elsewhere in `Theorems.lean`.
- **Lemma 2** (weak duality) should hold for **every** flow and **every** cut, without
  maximality hypotheses.
- Look for **extra hypotheses** on the theorems that aren't in the notes,
  **swapped quantifiers** (`∃ C, ∀ F` vs `∀ F, ∃ C`), and conclusions with `≤`
  where the notes have `=`.
- Note legitimate modelling choices (ℝ capacities, so no infinite capacities from
  Remark 1; finite `V`; complete-digraph encoding) as ℹ️, not failures.

**B6. Proof spot check.**
Skim `Proofs/` for suspicious patterns that A3 can't see: a key step closed by
deriving `False` from the theorem's own hypotheses (e.g. `linarith [hF F]`,
`absurd`, `lt_irrefl`, `exfalso`), case splits where the hard case is discharged
"too easily", lemmas that are stated but never used, and proofs that never use the
definitions they claim to reason about.

---

## Report

End with:
1. A summary table: check | result | one-line finding.
2. For each ❌/⚠️: the exact location (`file:line`), what is wrong, why it matters,
   evidence, and the minimal fix (described, not applied).
3. A verdict: does the mechanization faithfully and completely prove the
   Max-Flow Min-Cut theorem of the notes? (Yes / No / Yes with caveats.)

Leave `/tmp/scrutiny/` in place so the audience can inspect the experiments.
