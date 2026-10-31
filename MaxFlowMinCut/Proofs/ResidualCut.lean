import MaxFlowMinCut.Proofs.CutFlow
import MaxFlowMinCut.Proofs.PathSearch
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix

/-!
# The residual-reachability cut (Lemma 5)

If there is no augmenting path, the set `R` of vertices reachable from `s` in the
residual network `G_f` is an `s`-`t` cut whose capacity equals `|f|`.
-/

namespace MaxFlowMinCut.Proofs

variable {n : ℕ}

/-- `p` is a simple path from `s` to `v` in the residual network `G_f`. -/
def IsResPath (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (v : Fin n) (p : List (Fin n)) :
    Prop :=
  p.head? = some N.s ∧ p.getLast? = some v ∧ p.Nodup ∧
    p.IsChain (fun a b => 0 < residualCap N f a b)

/-- The set of vertices reachable from `s` in `G_f` (Lemma 5's `S`). -/
noncomputable def reachSet (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Finset (Fin n) :=
  @Finset.filter _ (fun v => ∃ p, IsResPath N f v p) (Classical.decPred _) Finset.univ

lemma mem_reachSet {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {v : Fin n} :
    v ∈ reachSet N f ↔ ∃ p, IsResPath N f v p := by
  simp [reachSet]

lemma s_mem_reachSet (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : N.s ∈ reachSet N f :=
  mem_reachSet.2 ⟨[N.s], rfl, rfl, List.nodup_singleton _, List.isChain_singleton _⟩

/-- `R` is closed under residual edges. -/
lemma reachSet_closed {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {v w : Fin n}
    (hv : v ∈ reachSet N f) (hvw : 0 < residualCap N f v w) : w ∈ reachSet N f := by
  obtain ⟨p, hs, hl, hnd, hc⟩ := mem_reachSet.1 hv
  rw [mem_reachSet]
  by_cases hw : w ∈ p
  · -- take the prefix of `p` ending at `w`
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hw
    have hpre : l₁ ++ [w] <+: l₁ ++ w :: l₂ := ⟨l₂, by simp⟩
    refine ⟨l₁ ++ [w], ?_, by simp, hnd.sublist hpre.sublist, hc.infix hpre.isInfix⟩
    cases l₁ <;> simp_all
  · -- append `w`
    have hne : p ≠ [] := by rintro rfl; simp at hs
    refine ⟨p ++ [w], ?_, by simp, ?_, ?_⟩
    · rw [List.head?_append, hs]; rfl
    · rw [List.nodup_append]
      simp only [List.nodup_singleton, List.mem_singleton, true_and]
      exact ⟨hnd, fun a ha b hb => by rintro rfl; exact hw (hb ▸ ha)⟩
    · refine hc.append (List.isChain_singleton _) ?_
      intro x hx y hy
      rw [hl, Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hx hy
      exact hvw

/-- Lemma 5: if `G_f` has no augmenting path, then `R` is an `s`-`t` cut with
`|f| = c(R, Rᶜ)`. -/
theorem reachSet_cut (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} (hf : IsFlow N f)
    (hnone : ∀ p, ¬ IsAugmentingPath N f p) :
    IsCut N (reachSet N f) ∧ value N f = cutCapacity N (reachSet N f) := by
  have hcut : IsCut N (reachSet N f) := by
    refine ⟨s_mem_reachSet N f, fun ht => ?_⟩
    obtain ⟨p, hp⟩ := mem_reachSet.1 ht
    exact hnone p hp
  refine ⟨hcut, ?_⟩
  rw [value_eq_net_across_cut N hf.2.2 hcut, cutCapacity]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
  have hres : residualCap N f u v ≤ 0 := by
    by_contra h
    exact Finset.mem_compl.1 hv (reachSet_closed hu (lt_of_not_ge h))
  unfold residualCap at hres
  linarith [hf.1 v u, hf.2.1 u v]

end MaxFlowMinCut.Proofs
