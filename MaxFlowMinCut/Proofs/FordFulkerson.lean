import MaxFlowMinCut.Proofs.Augment
import MaxFlowMinCut.Proofs.ResidualCut

/-!
# Correctness of Ford–Fulkerson (Algorithm 1)
-/

namespace MaxFlowMinCut.Proofs

variable {n : ℕ}

/-- The all-zeroes flow is a flow. -/
lemma zero_isFlow (N : FlowNetwork n) : IsFlow N (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun u v => N.cap_nonneg u v, fun _ _ _ => by simp⟩

lemma value_zero (N : FlowNetwork n) : value N (fun _ _ => 0) = 0 := by
  simp [value]

/-- Each round of the loop preserves being a flow. -/
lemma ffLoop_isFlow (N : FlowNetwork n) :
    ∀ (k : ℕ) {f : Fin n → Fin n → ℤ}, IsFlow N f → IsFlow N (ffLoop N k f)
  | 0, _, hf => hf
  | k + 1, f, hf => by
    rw [ffLoop]
    split
    · exact hf
    · next p hp => exact ffLoop_isFlow N k (augment_isFlow N hf (findAugmentingPath_sound N f hp))

/-- After `k` rounds, either the loop stopped (no augmenting path), or the value grew by
at least `k` (integer capacities: each augmentation adds at least `1`). -/
lemma ffLoop_progress (N : FlowNetwork n) :
    ∀ (k : ℕ) {f : Fin n → Fin n → ℤ}, IsFlow N f →
      findAugmentingPath N (ffLoop N k f) = none ∨ value N f + k ≤ value N (ffLoop N k f)
  | 0, _, _ => Or.inr (by simp [ffLoop])
  | k + 1, f, hf => by
    rw [ffLoop]
    split
    · next h => exact Or.inl h
    · next p hp =>
      have hpa := findAugmentingPath_sound N f hp
      rcases ffLoop_progress N k (augment_isFlow N hf hpa) with h | h
      · exact Or.inl h
      · right
        have := value_augment_ge N hpa
        push_cast
        linarith

/-- The total capacity out of `s` is at least the capacity of the cut `{s}`. -/
lemma cutCapacity_singleton_le (N : FlowNetwork n) :
    cutCapacity N {N.s} ≤ ∑ v, N.cap N.s v := by
  rw [cutCapacity, Finset.sum_singleton]
  exact Finset.sum_le_univ_sum_of_nonneg fun v => N.cap_nonneg _ _

lemma isCut_singleton (N : FlowNetwork n) : IsCut N {N.s} :=
  ⟨Finset.mem_singleton_self _, fun h => N.s_ne_t (Finset.mem_singleton.1 h).symm⟩

/-- Ford–Fulkerson returns a flow together with a cut of equal capacity. -/
theorem fordFulkerson_spec (N : FlowNetwork n) :
    IsFlow N (fordFulkerson N) ∧
      ∃ S, IsCut N S ∧ cutCapacity N S = value N (fordFulkerson N) := by
  have hflow := ffLoop_isFlow N (∑ v, N.cap N.s v).toNat (zero_isFlow N)
  refine ⟨hflow, ?_⟩
  rcases ffLoop_progress N (∑ v, N.cap N.s v).toNat (zero_isFlow N) with h | h
  · -- the loop stopped: Lemma 5
    have hnone := findAugmentingPath_complete N _ h
    obtain ⟨hcut, heq⟩ := reachSet_cut N hflow hnone
    exact ⟨_, hcut, heq.symm⟩
  · -- the budget was exhausted: the value reached `Σ_v c(s,v) ≥ c({s}, V - {s})`
    refine ⟨{N.s}, isCut_singleton N, le_antisymm ?_ (weak_duality N hflow (isCut_singleton N))⟩
    rw [value_zero, zero_add, Int.toNat_of_nonneg
      (Finset.sum_nonneg fun v _ => N.cap_nonneg _ _)] at h
    exact (cutCapacity_singleton_le N).trans h

/-- Algorithm 1 is correct: it returns a maximum flow. -/
theorem fordFulkerson_isMaxFlow (N : FlowNetwork n) : IsMaxFlow N (fordFulkerson N) := by
  obtain ⟨hf, S, hS, h⟩ := fordFulkerson_spec N
  exact (corollary3 N hf hS h.symm).1

/-- A minimum cut exists, with capacity equal to the value of the Ford–Fulkerson flow. -/
theorem exists_minCut_eq_fordFulkerson (N : FlowNetwork n) :
    ∃ S, IsMinCut N S ∧ cutCapacity N S = value N (fordFulkerson N) := by
  obtain ⟨hf, S, hS, h⟩ := fordFulkerson_spec N
  exact ⟨S, (corollary3 N hf hS h.symm).2, h⟩

end MaxFlowMinCut.Proofs
