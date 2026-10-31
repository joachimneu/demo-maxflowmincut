import MaxFlowMinCut.Proofs.FordFulkerson

/-!
# The Max-Flow Min-Cut theorem (Theorem 4)

Following the notes, Theorem 4 is proved via the algorithm: any max flow `f` has the same
value as the Ford–Fulkerson flow, which has no augmenting path, so (Lemma 5) its value is
attained by the residual cut; minimality of `S` then pins down `c(S, T)`.
-/

namespace MaxFlowMinCut

variable {n : ℕ}

/-- Every maximum flow is witnessed by a cut of equal forward capacity (Lemma 5 +
Corollary 3). -/
theorem exists_cut_forwardCap_eq_value {N : FlowNetwork n} {f : Fin n → Fin n → ℤ}
    (hf : IsMaxFlow N f) : ∃ R, IsCut N R ∧ value N f = forwardCap N R :=
  ⟨residualReach N f, isCut_residualReach (no_augmentingPath_of_isMaxFlow hf),
    value_eq_forwardCap_residualReach hf.1 (no_augmentingPath_of_isMaxFlow hf)⟩

theorem max_flow_min_cut' (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {S : Finset (Fin n)}
    (hf : IsMaxFlow N f) (hS : IsMinCut N S) : value N f = cutCapacity N S := by
  -- `f` and the Ford–Fulkerson flow are both maximum, so they have the same value.
  have hff := fordFulkerson_isMaxFlow' N
  have key₁ : value N f = value N (fordFulkerson N) :=
    le_antisymm (hff.2 f hf.1) (hf.2 _ hff.1)
  -- That value is the forward capacity of the residual cut `R` (Lemma 5).
  obtain ⟨R, hR, key₂⟩ := exists_cut_forwardCap_eq_value hff
  -- Lemma 2 for the cut `S`.
  have key₃ : value N f ≤ forwardCap N S := value_le_forwardCap N hf.1 hS.1
  -- Minimality of `S`.
  linarith [hS.2 S hS.1, key₁, key₂, key₃]

end MaxFlowMinCut
