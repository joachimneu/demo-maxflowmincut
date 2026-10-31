import MaxFlowMinCut.Definitions
import MaxFlowMinCut.Proofs.Main

/-!
# Max-Flow Min-Cut and Ford–Fulkerson: main theorems

Stanford CS161, Lecture 16. All proofs live in `MaxFlowMinCut/Proofs/`.
-/

namespace MaxFlowMinCut

variable {n : ℕ}

/-- Algorithm 1 is correct: Ford–Fulkerson returns a maximum flow (Lemmas 5 and 6 and the
integer termination argument of Sec. 6). -/
theorem fordFulkerson_isMaxFlow (N : FlowNetwork n) : IsMaxFlow N (fordFulkerson N) :=
  fordFulkerson_isMaxFlow' N

/-- Theorem 4 (Max-Flow Min-Cut): the value of any max flow equals the capacity of any min cut. -/
theorem max_flow_min_cut (N : FlowNetwork n) {f} {S} (hf : IsMaxFlow N f) (hS : IsMinCut N S) :
    value N f = cutCapacity N S :=
  max_flow_min_cut' N hf hS

end MaxFlowMinCut
