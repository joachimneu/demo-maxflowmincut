import MaxFlowMinCut.Definitions
import MaxFlowMinCut.Proofs.CutFlow
import MaxFlowMinCut.Proofs.FordFulkerson
import MaxFlowMinCut.Proofs.Main

/-!
# Max-Flow Min-Cut and correctness of Ford–Fulkerson: headline theorems

Stanford CS161 Lecture 16, integer capacities. All proofs live in `MaxFlowMinCut/Proofs/`.
-/

namespace MaxFlowMinCut

variable {n : ℕ}

/-- Lemma 2 (weak duality): for any flow `f` and any `s`-`t` cut `(S, T)`, `|f| ≤ c(S, T)`. -/
theorem weak_duality (N : FlowNetwork n) {f} {S} (hf : IsFlow N f) (hS : IsCut N S) :
    value N f ≤ cutCapacity N S :=
  Proofs.weak_duality N hf hS

/-- Algorithm 1 is correct: Ford–Fulkerson returns a maximum flow. -/
theorem fordFulkerson_isMaxFlow (N : FlowNetwork n) : IsMaxFlow N (fordFulkerson N) :=
  Proofs.fordFulkerson_isMaxFlow N

/-- Lemma 5 / Corollary 3: a minimum cut exists, with capacity equal to the value of the
flow found by Ford–Fulkerson. -/
theorem exists_minCut_eq_fordFulkerson (N : FlowNetwork n) :
    ∃ S, IsMinCut N S ∧ cutCapacity N S = value N (fordFulkerson N) :=
  Proofs.exists_minCut_eq_fordFulkerson N

/-- Theorem 4 (Max-Flow Min-Cut): the value of any max flow equals the capacity of any
min cut. -/
theorem max_flow_min_cut (N : FlowNetwork n) {f} {S} (hf : IsMaxFlow N f) (hS : IsMinCut N S) :
    value N f = cutCapacity N S :=
  Proofs.max_flow_min_cut N hf hS

end MaxFlowMinCut
