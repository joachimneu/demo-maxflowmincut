import MaxFlowMinCut.Proofs.FordFulkerson

/-!
# The Max-Flow Min-Cut theorem (Theorem 4)
-/

namespace MaxFlowMinCut.Proofs

variable {n : ℕ}

/-- Theorem 4: the value of any maximum flow equals the capacity of any minimum cut. -/
theorem max_flow_min_cut (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {S : Finset (Fin n)}
    (hf : IsMaxFlow N f) (hS : IsMinCut N S) : value N f = cutCapacity N S := by
  obtain ⟨hff, S₀, hS₀, h₀⟩ := fordFulkerson_spec N
  refine le_antisymm (weak_duality N hf.1 hS.1) ?_
  calc cutCapacity N S ≤ cutCapacity N S₀ := hS.2 S₀ hS₀
    _ = value N (fordFulkerson N) := h₀
    _ ≤ value N f := hf.2 _ hff

end MaxFlowMinCut.Proofs
