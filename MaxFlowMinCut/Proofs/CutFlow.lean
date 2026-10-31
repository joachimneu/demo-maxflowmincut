import MaxFlowMinCut.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Flow across a cut and weak duality (Lemma 2, Corollary 3)
-/

namespace MaxFlowMinCut.Proofs

variable {n : ℕ}

/-- Excess of `u`: flow out of `u` minus flow into `u`. -/
def excess (f : Fin n → Fin n → ℤ) (u : Fin n) : ℤ :=
  ∑ v, f u v - ∑ v, f v u

lemma excess_eq_sum_net (f : Fin n → Fin n → ℤ) (u : Fin n) :
    excess f u = ∑ v, (f u v - f v u) := by
  simp [excess, Finset.sum_sub_distrib]

/-- Conservation in terms of net flow. -/
lemma excess_eq_zero (N : FlowNetwork n) {f : Fin n → Fin n → ℤ}
    (hcons : ∀ v, v ≠ N.s → v ≠ N.t → ∑ u, f u v = ∑ w, f v w)
    {v : Fin n} (hs : v ≠ N.s) (ht : v ≠ N.t) : excess f v = 0 := by
  simp [excess, hcons v hs ht]

lemma value_eq_excess (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) :
    value N f = excess f N.s := rfl

/-- The value of a flow equals the net flow across any cut (proof of Lemma 2). Only
conservation is used. -/
lemma value_eq_net_across_cut (N : FlowNetwork n) {f : Fin n → Fin n → ℤ}
    (hcons : ∀ v, v ≠ N.s → v ≠ N.t → ∑ u, f u v = ∑ w, f v w)
    {S : Finset (Fin n)} (hS : IsCut N S) :
    value N f = ∑ u ∈ S, ∑ v ∈ Sᶜ, (f u v - f v u) := by
  have h1 : value N f = ∑ u ∈ S, excess f u := by
    rw [value_eq_excess, Finset.sum_eq_single_of_mem N.s hS.1]
    intro b hb hbs
    exact excess_eq_zero N hcons hbs (fun h => hS.2 (h ▸ hb))
  have h2 : ∀ u, excess f u = ∑ v ∈ S, (f u v - f v u) + ∑ v ∈ Sᶜ, (f u v - f v u) := by
    intro u
    rw [excess_eq_sum_net, Finset.sum_add_sum_compl]
  have h3 : ∑ u ∈ S, ∑ v ∈ S, (f u v - f v u) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := S) (t := S) (f := fun u v => f v u)]
    simp
  rw [h1]
  simp only [h2, Finset.sum_add_distrib, h3, zero_add]

/-- Lemma 2 (weak duality). -/
theorem weak_duality (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {S : Finset (Fin n)}
    (hf : IsFlow N f) (hS : IsCut N S) : value N f ≤ cutCapacity N S := by
  rw [value_eq_net_across_cut N hf.2.2 hS, cutCapacity]
  refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
  linarith [hf.1 v u, hf.2.1 u v]

/-- Corollary 3: a flow and a cut with `|f| = c(S, T)` are a max flow and a min cut. -/
theorem corollary3 (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {S : Finset (Fin n)}
    (hf : IsFlow N f) (hS : IsCut N S) (h : value N f = cutCapacity N S) :
    IsMaxFlow N f ∧ IsMinCut N S :=
  ⟨⟨hf, fun _ hg => h ▸ weak_duality N hg hS⟩,
   ⟨hS, fun _ hT => h ▸ weak_duality N hf hT⟩⟩

end MaxFlowMinCut.Proofs
