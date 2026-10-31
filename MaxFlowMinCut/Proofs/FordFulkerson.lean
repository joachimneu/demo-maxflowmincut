import MaxFlowMinCut.Proofs.Augment
import MaxFlowMinCut.Proofs.ResidualCut

/-!
# Correctness of Algorithm 1 (Ford–Fulkerson)

Invariant of the main loop: the current function is a flow, and after `k` iterations
either the search found no augmenting path, or each of the `k` augmentations increased the
value by at least `1` (integer capacities, Sec. 6). With `k = ∑ₓ c(s, x)`, the second case
means the value has reached the trivial upper bound, so in both cases the result is a
maximum flow (Lemma 5).
-/

namespace MaxFlowMinCut

variable {n : ℕ}

theorem ffLoop_spec (N : FlowNetwork n) :
    ∀ (k : ℕ) {f : Fin n → Fin n → ℤ}, IsFlow N f →
      IsFlow N (ffLoop N k f) ∧
        (findAugmentingPath N (ffLoop N k f) = none ∨ value N f + k ≤ value N (ffLoop N k f))
  | 0, f, hf => ⟨hf, Or.inr (by simp [ffLoop])⟩
  | k + 1, f, hf => by
    unfold ffLoop
    split
    · next h => exact ⟨hf, Or.inl h⟩
    · next p h =>
      have hp := findAugmentingPath_sound N h
      obtain ⟨hflow, hrest⟩ := ffLoop_spec N k (augment_isFlow hf hp)
      refine ⟨hflow, hrest.imp_right fun hk => ?_⟩
      have := value_augment hp
      have := one_le_bottleneck hp
      push_cast
      linarith

/-- Algorithm 1 returns a maximum flow. -/
theorem fordFulkerson_isMaxFlow' (N : FlowNetwork n) : IsMaxFlow N (fordFulkerson N) := by
  obtain ⟨hflow, h⟩ := ffLoop_spec N (∑ v, N.cap N.s v).toNat (isFlow_zero N)
  rcases h with h | h
  · exact isMaxFlow_of_no_augmentingPath hflow (findAugmentingPath_complete N h)
  · refine ⟨hflow, fun g hg => ?_⟩
    have hcap : 0 ≤ ∑ v, N.cap N.s v := Finset.sum_nonneg fun v _ => N.cap_nonneg _ _
    rw [value_zero, Int.toNat_of_nonneg hcap, zero_add] at h
    exact (value_le_sum_cap_source N hg).trans h

/-- A maximum flow admits no augmenting path (contrapositive of Lemma 6). -/
theorem no_augmentingPath_of_isMaxFlow {N : FlowNetwork n} {f : Fin n → Fin n → ℤ}
    (hf : IsMaxFlow N f) (p : List (Fin n)) : ¬ IsAugmentingPath N f p := fun hp => by
  have h1 := hf.2 _ (augment_isFlow hf.1 hp)
  have h2 := value_augment hp
  have h3 := one_le_bottleneck hp
  linarith

end MaxFlowMinCut
