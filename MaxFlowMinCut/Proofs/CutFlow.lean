import MaxFlowMinCut.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Flows across cuts (Lemma 2)

The value of a flow equals the net flow across any `s`-`t` cut, and hence is bounded by
the total capacity of the edges leaving the source side.
-/

namespace MaxFlowMinCut

open Finset

variable {n : ℕ}

/-- Total capacity of the edges from `S` to `Sᶜ`. -/
def forwardCap (N : FlowNetwork n) (S : Finset (Fin n)) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v

/-- The value of a flow equals the net flow across any cut (proof of Lemma 2). -/
theorem value_eq_netFlow (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} (hf : IsFlow N f)
    {S : Finset (Fin n)} (hS : IsCut N S) :
    value N f = ∑ u ∈ S, ∑ v ∈ Sᶜ, (f u v - f v u) := by
  -- Step 1: by conservation, `|f| = ∑_{u ∈ S} (net flow out of u)`.
  have h1 : value N f = ∑ u ∈ S, ∑ v, (f u v - f v u) := by
    rw [Finset.sum_eq_single_of_mem N.s hS.1]
    · simp [value, Finset.sum_sub_distrib]
    · intro u hu hne
      have hut : u ≠ N.t := fun h => hS.2 (h ▸ hu)
      rw [Finset.sum_sub_distrib, hf.2.2 u hne hut, sub_self]
  -- Step 2: the flow inside `S` cancels.
  have h2 : ∑ u ∈ S, ∑ v ∈ S, (f u v - f v u) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := S) (t := S) (f := fun u v => f v u), sub_self]
  rw [h1]
  have h3 : ∀ u, ∑ v, (f u v - f v u) =
      ∑ v ∈ S, (f u v - f v u) + ∑ v ∈ Sᶜ, (f u v - f v u) :=
    fun u => (Finset.sum_add_sum_compl S _).symm
  simp only [h3, Finset.sum_add_distrib, h2, zero_add]

/-- Lemma 2 (with the forward capacity): `|f| ≤ ∑_{u ∈ S, v ∉ S} c(u, v)`. -/
theorem value_le_forwardCap (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} (hf : IsFlow N f)
    {S : Finset (Fin n)} (hS : IsCut N S) : value N f ≤ forwardCap N S := by
  rw [value_eq_netFlow N hf hS, forwardCap]
  refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
  linarith [hf.1 v u, hf.2.1 u v]

/-- The value of any flow is at most the total capacity out of the source. -/
theorem value_le_sum_cap_source (N : FlowNetwork n) {f : Fin n → Fin n → ℤ}
    (hf : IsFlow N f) : value N f ≤ ∑ v, N.cap N.s v := by
  have h1 : 0 ≤ ∑ u, f u N.s := Finset.sum_nonneg fun u _ => hf.1 u N.s
  have h2 : ∑ v, f N.s v ≤ ∑ v, N.cap N.s v := Finset.sum_le_sum fun v _ => hf.2.1 _ _
  unfold value; linarith

/-- The all-zeroes flow. -/
theorem isFlow_zero (N : FlowNetwork n) : IsFlow N (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun u v => N.cap_nonneg u v, fun _ _ _ => by simp⟩

@[simp] theorem value_zero (N : FlowNetwork n) : value N (fun _ _ => 0) = 0 := by
  simp [value]

end MaxFlowMinCut
