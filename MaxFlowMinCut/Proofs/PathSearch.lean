import MaxFlowMinCut.Definitions
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Permutation

/-!
# The exhaustive augmenting-path search is sound and complete
-/

namespace MaxFlowMinCut.Proofs

variable {n : ℕ}

/-- Soundness: a returned path is augmenting. -/
theorem findAugmentingPath_sound (N : FlowNetwork n) (f : Fin n → Fin n → ℤ)
    {p : List (Fin n)} (h : findAugmentingPath N f = some p) : IsAugmentingPath N f p := by
  unfold findAugmentingPath at h
  simpa using List.find?_some h

/-- Every duplicate-free vertex list is among the searched candidates. -/
lemma mem_candidates {p : List (Fin n)} (hp : p.Nodup) :
    p ∈ (List.finRange n).sublists.flatMap List.permutations := by
  obtain ⟨l, hl, hsub⟩ := List.subperm_of_subset hp (fun x _ => List.mem_finRange x)
  exact List.mem_flatMap.2 ⟨l, List.mem_sublists.2 hsub, List.mem_permutations.2 hl.symm⟩

/-- Completeness: if the search fails, there is no augmenting path. -/
theorem findAugmentingPath_complete (N : FlowNetwork n) (f : Fin n → Fin n → ℤ)
    (h : findAugmentingPath N f = none) (p : List (Fin n)) : ¬ IsAugmentingPath N f p := by
  intro hp
  unfold findAugmentingPath at h
  have := List.find?_eq_none.1 h p (mem_candidates hp.2.2.1)
  simp [hp] at this

end MaxFlowMinCut.Proofs
