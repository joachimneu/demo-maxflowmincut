import MaxFlowMinCut.Proofs.PathSearch
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Augmenting along a path (Lemma 6)

If `p` is an augmenting path for a flow `f`, then `augment N f p` is again a flow, and its
value is `|f| + F` where `F ≥ 1` is the bottleneck of `p`.

The conservation argument of the notes (a simple path uses either `0` or `2` edges at an
inner vertex) is phrased via edge counts: for a path from `a` to `b`, the number of path
edges entering `v` minus the number leaving `v` is `[v = b] - [v = a]`.
-/

namespace MaxFlowMinCut

open Finset

variable {n : ℕ}

/-! ### Edges of a path -/

@[simp] theorem pathEdges_nil : pathEdges ([] : List (Fin n)) = [] := rfl

@[simp] theorem pathEdges_singleton (a : Fin n) : pathEdges [a] = [] := rfl

@[simp] theorem pathEdges_cons_cons (a b : Fin n) (l : List (Fin n)) :
    pathEdges (a :: b :: l) = (a, b) :: pathEdges (b :: l) := rfl

/-- The heads of the edges of a path are all its vertices but the last. -/
theorem map_fst_pathEdges : ∀ p : List (Fin n), (pathEdges p).map Prod.fst = p.dropLast
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [pathEdges_cons_cons, List.map_cons, map_fst_pathEdges (b :: l)]
    rfl

/-- The tails of the edges of a path are all its vertices but the first. -/
theorem map_snd_pathEdges : ∀ p : List (Fin n), (pathEdges p).map Prod.snd = p.tail
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [pathEdges_cons_cons, List.map_cons, map_snd_pathEdges (b :: l)]
    rfl

/-- Every edge of a chain satisfies the chain relation. -/
theorem rel_of_mem_pathEdges {R : Fin n → Fin n → Prop} :
    ∀ {p : List (Fin n)}, p.IsChain R → ∀ {e}, e ∈ pathEdges p → R e.1 e.2
  | [], _, _, he => by simp at he
  | [_], _, _, he => by simp at he
  | a :: b :: l, hp, e, he => by
    rw [List.isChain_cons_cons] at hp
    rw [pathEdges_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact hp.1
    · exact rel_of_mem_pathEdges hp.2 he

/-- A simple path traverses each edge at most once. -/
theorem nodup_pathEdges {p : List (Fin n)} (hp : p.Nodup) : (pathEdges p).Nodup := by
  have : ((pathEdges p).map Prod.fst).Nodup := by
    rw [map_fst_pathEdges]; exact hp.sublist (List.dropLast_sublist p)
  exact this.of_map _

/-! ### Edge counts at a vertex -/

/-- Number of edges in `E` entering `v`. -/
theorem sum_count_in (E : List (Fin n × Fin n)) (v : Fin n) :
    ∑ u, (E.count (u, v) : ℤ) = ((E.map Prod.snd).count v : ℤ) := by
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [List.count_cons, List.map_cons, Nat.cast_add, Finset.sum_add_distrib, ih,
      beq_iff_eq]
    congr 1
    obtain ⟨a, b⟩ := e
    by_cases hb : b = v
    · subst hb
      rw [Finset.sum_eq_single a] <;> simp_all [eq_comm]
    · simp [Prod.ext_iff, hb]

/-- Number of edges in `E` leaving `v`. -/
theorem sum_count_out (E : List (Fin n × Fin n)) (v : Fin n) :
    ∑ w, (E.count (v, w) : ℤ) = ((E.map Prod.fst).count v : ℤ) := by
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [List.count_cons, List.map_cons, Nat.cast_add, Finset.sum_add_distrib, ih,
      beq_iff_eq]
    congr 1
    obtain ⟨a, b⟩ := e
    by_cases ha : a = v
    · subst ha
      rw [Finset.sum_eq_single b] <;> simp_all [eq_comm]
    · sorry

/-- For a path from `a` to `b`: (edges into `v`) − (edges out of `v`) = `[v = b] - [v = a]`. -/
theorem count_tail_sub_count_dropLast {p : List (Fin n)} {a b : Fin n}
    (ha : p.head? = some a) (hb : p.getLast? = some b) (v : Fin n) :
    (p.tail.count v : ℤ) - p.dropLast.count v =
      (if v = b then 1 else 0) - (if v = a then 1 else 0) := by
  have hne : p ≠ [] := by rintro rfl; simp at ha
  have h1 : p.count v = p.tail.count v + if v = a then 1 else 0 := by
    obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [List.count_cons, List.tail_cons]
    rcases eq_or_ne v x with h | h
    · simp [h]
    · simp [h, h.symm]
  have h2 : p.count v = p.dropLast.count v + if v = b then 1 else 0 := by
    have hl : p.getLast hne = b := by
      rw [List.getLast?_eq_some_getLast hne] at hb; exact Option.some.inj hb
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.count_append, hl]
    rcases eq_or_ne v b with h | h
    · simp [h]
    · simp [h, h.symm]
  have h1' : (p.count v : ℤ) = p.tail.count v + if v = a then 1 else 0 := by
    rw [h1]; push_cast; split_ifs <;> simp
  have h2' : (p.count v : ℤ) = p.dropLast.count v + if v = b then 1 else 0 := by
    rw [h2]; push_cast; split_ifs <;> simp
  linarith

/-! ### The bottleneck -/

theorem bottleneck_le {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    {e : Fin n × Fin n} (he : e ∈ pathEdges p) : bottleneck N f p ≤ residualCap N f e.1 e.2 := by
  set L := (pathEdges p).map fun e => residualCap N f e.1 e.2
  obtain ⟨m, hm⟩ : ∃ m, L.min? = some m :=
    Option.isSome_iff_exists.1 (List.isSome_min?_of_mem (List.mem_map_of_mem he))
  have : bottleneck N f p = m := by simp [bottleneck, L, hm]
  rw [this]
  exact (List.min?_eq_some_iff.1 hm).2 _ (List.mem_map_of_mem he)

/-- An augmenting path has at least one edge. -/
theorem pathEdges_ne_nil {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hp : IsAugmentingPath N f p) : pathEdges p ≠ [] := by
  match p, hp with
  | [], hp => simp [IsAugmentingPath] at hp
  | [a], hp =>
    obtain ⟨h1, h2, -⟩ := hp
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    exact absurd (h1.symm.trans h2) N.s_ne_t
  | a :: b :: l, _ => simp

/-- With integer capacities the bottleneck of an augmenting path is at least `1`. -/
theorem one_le_bottleneck {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hp : IsAugmentingPath N f p) : 1 ≤ bottleneck N f p := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (pathEdges_ne_nil hp)
  set L := (pathEdges p).map fun e => residualCap N f e.1 e.2
  obtain ⟨m, hm⟩ : ∃ m, L.min? = some m :=
    Option.isSome_iff_exists.1 (List.isSome_min?_of_mem (List.mem_map_of_mem he))
  have : bottleneck N f p = m := by simp [bottleneck, L, hm]
  rw [this]
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 (List.min?_mem hm)
  exact rel_of_mem_pathEdges hp.2.2.2 he'

/-! ### The augmented flow -/

section Augment

variable {N : FlowNetwork n} {f : Fin n → Fin n → ℤ} {p : List (Fin n)}

/-- The net flow of `augment N f p` on `(u, v)`. -/
private def netAug (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n))
    (u v : Fin n) : ℤ :=
  f u v - f v u +
    bottleneck N f p * (((pathEdges p).count (u, v) : ℤ) - (pathEdges p).count (v, u))

private theorem augment_sub_augment (u v : Fin n) :
    augment N f p u v - augment N f p v u = netAug N f p u v := by
  unfold augment netAug
  have h : f v u - f u v + bottleneck N f p *
      (((pathEdges p).count (v, u) : ℤ) - (pathEdges p).count (u, v)) =
      -(f u v - f v u + bottleneck N f p *
      (((pathEdges p).count (u, v) : ℤ) - (pathEdges p).count (v, u))) := by ring
  rw [h]
  generalize f u v - f v u + _ = x
  omega

/-- Net flow of `augment N f p` out of `x`. -/
private theorem sum_augment_sub (ha : p.head? = some N.s) (hb : p.getLast? = some N.t)
    (x : Fin n) :
    ∑ v, (augment N f p x v - augment N f p v x) =
      ∑ v, (f x v - f v x) +
        bottleneck N f p * ((if x = N.s then 1 else 0) - (if x = N.t then 1 else 0)) := by
  simp only [augment_sub_augment, netAug, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, sum_count_out, sum_count_in, map_fst_pathEdges,
    map_snd_pathEdges]
  have := count_tail_sub_count_dropLast ha hb x
  congr 2
  linarith

theorem augment_nonneg (u v : Fin n) : 0 ≤ augment N f p u v := le_max_left _ _

theorem augment_le_cap (hf : IsFlow N f) (hp : IsAugmentingPath N f p) (u v : Fin n) :
    augment N f p u v ≤ N.cap u v := by
  refine max_le (N.cap_nonneg u v) ?_
  have hδ := one_le_bottleneck hp
  have hcnt : (pathEdges p).count (u, v) ≤ 1 :=
    List.nodup_iff_count_le_one.1 (nodup_pathEdges hp.2.2.1) _
  have h0 : 0 ≤ bottleneck N f p * ((pathEdges p).count (v, u) : ℤ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hfu := hf.1 v u
  have hfc := hf.2.1 u v
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcnt with h | h
  · rw [h]; push_cast; linarith
  · have hmem : (u, v) ∈ pathEdges p := List.count_pos_iff.1 (by omega)
    have := bottleneck_le (N := N) (f := f) hmem
    simp only [residualCap] at this
    rw [h]; push_cast; linarith

theorem augment_conservation (hf : IsFlow N f) (hp : IsAugmentingPath N f p) (v : Fin n)
    (hs : v ≠ N.s) (ht : v ≠ N.t) :
    ∑ u, augment N f p u v = ∑ w, augment N f p v w := by
  have h := sum_augment_sub (N := N) (f := f) (p := p) hp.1 hp.2.1 v
  simp only [hs, ht, ↓reduceIte, sub_self, mul_zero, add_zero, Finset.sum_sub_distrib,
    hf.2.2 v hs ht] at h
  linarith

/-- Lemma 6, first part: augmenting along an augmenting path yields a flow. -/
theorem augment_isFlow (hf : IsFlow N f) (hp : IsAugmentingPath N f p) :
    IsFlow N (augment N f p) :=
  ⟨augment_nonneg, augment_le_cap hf hp, augment_conservation hf hp⟩

/-- Lemma 6, second part: augmenting increases the value by the bottleneck. -/
theorem value_augment (hp : IsAugmentingPath N f p) :
    value N (augment N f p) = value N f + bottleneck N f p := by
  have h := sum_augment_sub (N := N) (f := f) (p := p) hp.1 hp.2.1 N.s
  simp only [N.s_ne_t, ↓reduceIte, sub_zero, mul_one, Finset.sum_sub_distrib] at h
  unfold value
  linarith

end Augment

end MaxFlowMinCut
