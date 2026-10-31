import MaxFlowMinCut.Definitions

/-!
# Correctness of the augmenting-path search

`findAugmentingPath` returns only augmenting paths (soundness), and returns `none` only
if no augmenting path exists (completeness): every simple path is a permutation of a
sublist of the vertex list.
-/

namespace MaxFlowMinCut

variable {n : ℕ}

/-- Soundness of the search. -/
theorem findAugmentingPath_sound (N : FlowNetwork n) {f : Fin n → Fin n → ℤ}
    {p : List (Fin n)} (h : findAugmentingPath N f = some p) : IsAugmentingPath N f p := by
  unfold findAugmentingPath at h
  simpa using List.find?_some h

/-- Every duplicate-free list of vertices is among the search candidates. -/
theorem mem_candidates {p : List (Fin n)} (hp : p.Nodup) :
    p ∈ (List.finRange n).sublists.flatMap List.permutations := by
  obtain ⟨l, hperm, hsub⟩ := List.subperm_of_subset hp (fun x _ => List.mem_finRange x)
  exact List.mem_flatMap.2 ⟨l, List.mem_sublists.2 hsub, List.mem_permutations.2 hperm.symm⟩

/-- Completeness of the search. -/
theorem findAugmentingPath_complete (N : FlowNetwork n) {f : Fin n → Fin n → ℤ}
    (h : findAugmentingPath N f = none) (p : List (Fin n)) : ¬ IsAugmentingPath N f p := by
  intro hp
  unfold findAugmentingPath at h
  have := List.find?_eq_none.1 h p (mem_candidates hp.2.2.1)
  simp [hp] at this

end MaxFlowMinCut
