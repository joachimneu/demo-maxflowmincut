import MaxFlowMinCut.Proofs.CutFlow
import MaxFlowMinCut.Proofs.PathSearch
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic

/-!
# The residual cut (Lemma 5)

Let `S` be the set of vertices reachable from `s` in the residual network `G_f`. If `G_f`
has no augmenting path, then `(S, V \ S)` is an `s`-`t` cut, every edge from `S` to `V \ S`
is saturated and every edge back carries no flow, so `|f|` equals the forward capacity of
the cut, and `f` is a maximum flow.
-/

namespace MaxFlowMinCut

open Finset

variable {n : ℕ}

/-- The edge relation of the residual network `G_f`. -/
def ResidualEdge (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (u v : Fin n) : Prop :=
  0 < residualCap N f u v

/-- Reachability in any relation is witnessed by a simple path (shortcut at repeated
vertices). -/
theorem exists_simple_path {R : Fin n → Fin n → Prop} {a b : Fin n}
    (h : Relation.ReflTransGen R a b) :
    ∃ p : List (Fin n), p.head? = some a ∧ p.getLast? = some b ∧ p.Nodup ∧ p.IsChain R := by
  induction h with
  | refl => exact ⟨[a], rfl, rfl, List.nodup_singleton a, List.isChain_singleton a⟩
  | @tail b c _ hbc ih =>
    obtain ⟨p, hpa, hpb, hnd, hch⟩ := ih
    have hne : p ≠ [] := by rintro rfl; simp at hpa
    by_cases hc : c ∈ p
    · -- shortcut: the prefix of `p` ending at `c`
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hc
      refine ⟨l₁ ++ [c], ?_, by simp, ?_, ?_⟩
      · cases l₁ <;> simp_all
      · exact (List.sublist_append_left (l₁ ++ [c]) l₂).nodup (by simpa using hnd)
      · exact List.IsChain.left_of_append (l₂ := l₂) (by simpa using hch)
    · -- extend `p` by the edge `b → c`
      refine ⟨p ++ [c], ?_, by simp, ?_, ?_⟩
      · rw [List.head?_append, hpa]; rfl
      · exact List.nodup_append.2 ⟨hnd, List.nodup_singleton c, by simp; grind⟩
      · refine hch.append (List.isChain_singleton c) ?_
        intro x hx y hy
        rw [hpb] at hx
        simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
        subst hx hy
        exact hbc

open Classical in
/-- The set of vertices reachable from `s` in `G_f`. -/
noncomputable def residualReach (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun v => Relation.ReflTransGen (ResidualEdge N f) N.s v

theorem mem_residualReach {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {v : Fin n} :
    v ∈ residualReach N f ↔ Relation.ReflTransGen (ResidualEdge N f) N.s v := by
  classical
  simp [residualReach]

/-- If there is no augmenting path, the residual-reachable set is an `s`-`t` cut. -/
theorem isCut_residualReach {N : FlowNetwork n} {f : Fin n → Fin n → ℤ}
    (h : ∀ p, ¬ IsAugmentingPath N f p) : IsCut N (residualReach N f) := by
  refine ⟨mem_residualReach.2 Relation.ReflTransGen.refl, fun ht => ?_⟩
  obtain ⟨p, h₁, h₂, h₃, h₄⟩ := exists_simple_path (mem_residualReach.1 ht)
  exact h p ⟨h₁, h₂, h₃, h₄⟩

/-- No residual edge leaves the reachable set. -/
theorem residualCap_nonpos {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {u v : Fin n}
    (hu : u ∈ residualReach N f) (hv : v ∉ residualReach N f) : residualCap N f u v ≤ 0 := by
  by_contra hpos
  exact hv (mem_residualReach.2 ((mem_residualReach.1 hu).tail (lt_of_not_ge hpos)))

/-- Lemma 5 (main computation): with no augmenting path, `|f|` equals the forward capacity
of the residual cut. -/
theorem value_eq_forwardCap_residualReach {N : FlowNetwork n} {f : Fin n → Fin n → ℤ}
    (hf : IsFlow N f) (h : ∀ p, ¬ IsAugmentingPath N f p) :
    value N f = forwardCap N (residualReach N f) := by
  rw [value_eq_netFlow N hf (isCut_residualReach h), forwardCap]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
  have h0 := residualCap_nonpos hu (Finset.mem_compl.1 hv)
  unfold residualCap at h0
  -- cases 1 and 2 of the notes: `f(u,v) = c(u,v)` and `f(v,u) = 0`
  linarith [hf.1 v u, hf.2.1 u v]

/-- Lemma 5: if `t` is not reachable from `s` in `G_f`, then `f` is a maximum flow. -/
theorem isMaxFlow_of_no_augmentingPath {N : FlowNetwork n} {f : Fin n → Fin n → ℤ}
    (hf : IsFlow N f) (h : ∀ p, ¬ IsAugmentingPath N f p) : IsMaxFlow N f :=
  ⟨hf, fun _ hg => (value_eq_forwardCap_residualReach hf h).symm ▸
    value_le_forwardCap N hg (isCut_residualReach h)⟩

end MaxFlowMinCut
