import MaxFlowMinCut.Proofs.CutFlow
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Augmenting along a path (Lemma 6)

Augmenting a flow `f` along an augmenting path `p` by its bottleneck `δ` yields a flow
of value `|f| + δ`, and `δ ≥ 1` (integer capacities).
-/

namespace MaxFlowMinCut.Proofs

variable {n : ℕ}

@[simp] lemma pathEdges_nil : pathEdges ([] : List (Fin n)) = [] := rfl
@[simp] lemma pathEdges_singleton (a : Fin n) : pathEdges [a] = [] := rfl
@[simp] lemma pathEdges_cons_cons (a b : Fin n) (l : List (Fin n)) :
    pathEdges (a :: b :: l) = (a, b) :: pathEdges (b :: l) := rfl

lemma isChain_iff_pathEdges {R : Fin n → Fin n → Prop} :
    ∀ {p : List (Fin n)}, p.IsChain R ↔ ∀ e ∈ pathEdges p, R e.1 e.2
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    rw [List.isChain_cons_cons, isChain_iff_pathEdges (p := b :: l)]
    simp

lemma mem_of_mem_pathEdges {p : List (Fin n)} {e : Fin n × Fin n} (h : e ∈ pathEdges p) :
    e.1 ∈ p ∧ e.2 ∈ p := by
  have := List.of_mem_zip (a := e.1) (b := e.2) (l₁ := p) (l₂ := p.tail) h
  exact ⟨this.1, List.mem_of_mem_tail this.2⟩

lemma nodup_pathEdges : ∀ {p : List (Fin n)}, p.Nodup → (pathEdges p).Nodup
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    rw [pathEdges_cons_cons, List.nodup_cons]
    have h' := List.nodup_cons.1 h
    exact ⟨fun hm => h'.1 (mem_of_mem_pathEdges hm).1, nodup_pathEdges h'.2⟩

/-- Net number of times the path traverses `(u, v)` (forwards minus backwards). -/
def pathNet (p : List (Fin n)) (u v : Fin n) : ℤ :=
  ((pathEdges p).count (u, v) : ℤ) - ((pathEdges p).count (v, u) : ℤ)

lemma pathNet_le_one {p : List (Fin n)} (hp : p.Nodup) (u v : Fin n) : pathNet p u v ≤ 1 := by
  have h1 := List.nodup_iff_count_le_one.1 (nodup_pathEdges hp) (u, v)
  unfold pathNet
  omega

lemma mem_of_pathNet_pos {p : List (Fin n)} {u v : Fin n} (h : 0 < pathNet p u v) :
    (u, v) ∈ pathEdges p := by
  apply List.count_pos_iff.1
  unfold pathNet at h
  omega

lemma sum_count_cons_fst (e : Fin n × Fin n) (L : List (Fin n × Fin n)) (v : Fin n) :
    ∑ w, ((e :: L).count (v, w) : ℤ) = ∑ w, (L.count (v, w) : ℤ) + if e.1 = v then 1 else 0 := by
  obtain ⟨a, b⟩ := e
  simp only [List.count_cons, beq_iff_eq, Prod.mk.injEq, Nat.cast_add, Finset.sum_add_distrib]
  congr 1
  by_cases h : a = v
  · subst h; simp [Finset.sum_ite_eq]
  · simp [h]

lemma sum_count_cons_snd (e : Fin n × Fin n) (L : List (Fin n × Fin n)) (v : Fin n) :
    ∑ w, ((e :: L).count (w, v) : ℤ) = ∑ w, (L.count (w, v) : ℤ) + if e.2 = v then 1 else 0 := by
  obtain ⟨a, b⟩ := e
  simp only [List.count_cons, beq_iff_eq, Prod.mk.injEq, Nat.cast_add, Finset.sum_add_distrib]
  congr 1
  by_cases h : b = v
  · subst h; simp [Finset.sum_ite_eq]
  · simp [h]

/-- Net out-degree of a vertex along a path from `x` to `y`: `[v = x] - [v = y]`. -/
lemma sum_pathNet : ∀ (p : List (Fin n)) {x y : Fin n} (v : Fin n),
    p.head? = some x → p.getLast? = some y →
    ∑ w, pathNet p v w = (if v = x then 1 else 0) - (if v = y then 1 else 0)
  | [], _, _, _, hx, _ => by simp at hx
  | [a], x, y, v, hx, hy => by
    simp at hx hy; subst hx hy; simp [pathNet]
  | a :: b :: l, x, y, v, hx, hy => by
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    rw [List.getLast?_cons_cons] at hy
    have ih := sum_pathNet (b :: l) v rfl hy
    simp only [pathNet, Finset.sum_sub_distrib] at ih ⊢
    rw [pathEdges_cons_cons, sum_count_cons_fst, sum_count_cons_snd]
    simp only [eq_comm (a := a) (b := v), eq_comm (a := b) (b := v)]
    split_ifs at ih ⊢ <;> linarith

/-- Net flow `g(u,v) - g(v,u)`. -/
lemma augment_net (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) (u v : Fin n) :
    augment N f p u v - augment N f p v u = f u v - f v u + bottleneck N f p * pathNet p u v := by
  unfold augment pathNet
  generalize bottleneck N f p = δ
  have : f v u - f u v + δ * (((pathEdges p).count (v, u) : ℤ) - (pathEdges p).count (u, v)) =
      -(f u v - f v u + δ * (((pathEdges p).count (u, v) : ℤ) - (pathEdges p).count (v, u))) := by
    ring
  rw [this]
  generalize f u v - f v u + δ * (((pathEdges p).count (u, v) : ℤ) - (pathEdges p).count (v, u)) = x
  omega

lemma pathEdges_ne_nil (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hp : IsAugmentingPath N f p) : pathEdges p ≠ [] := by
  obtain ⟨hs, ht, -, -⟩ := hp
  match p, hs, ht with
  | [], hs, _ => simp at hs
  | [a], hs, ht => simp at hs ht; exact absurd (hs.symm.trans ht) N.s_ne_t
  | a :: b :: l, _, _ => simp

lemma bottleneck_spec (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hp : IsAugmentingPath N f p) :
    1 ≤ bottleneck N f p ∧ ∀ e ∈ pathEdges p, bottleneck N f p ≤ residualCap N f e.1 e.2 := by
  set L := (pathEdges p).map (fun e => residualCap N f e.1 e.2) with hL
  have hne : L ≠ [] := by simpa [hL] using pathEdges_ne_nil N hp
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (List.isSome_min?_of_ne_nil hne)
  have hb : bottleneck N f p = m := by simp [bottleneck, ← hL, hm]
  obtain ⟨hmem, hle⟩ := List.min?_eq_some_iff.1 hm
  rw [hb]
  refine ⟨?_, fun e he => hle _ (List.mem_map_of_mem he)⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
  exact isChain_iff_pathEdges.1 hp.2.2.2 e he

/-- Conservation at `v` in terms of net flow. -/
lemma cons_iff_net (g : Fin n → Fin n → ℤ) (v : Fin n) :
    (∑ u, g u v = ∑ w, g v w) ↔ ∑ w, (g v w - g w v) = 0 := by
  rw [← excess_eq_sum_net, excess, sub_eq_zero, eq_comm]

lemma value_eq_net (N : FlowNetwork n) (g : Fin n → Fin n → ℤ) :
    value N g = ∑ w, (g N.s w - g w N.s) := by
  rw [value_eq_excess, excess_eq_sum_net]

lemma sum_net_augment (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hp : IsAugmentingPath N f p) (v : Fin n) :
    ∑ w, (augment N f p v w - augment N f p w v) = ∑ w, (f v w - f w v) +
      bottleneck N f p * ((if v = N.s then 1 else 0) - (if v = N.t then 1 else 0)) := by
  simp only [augment_net, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_pathNet p v hp.1 hp.2.1]

/-- Lemma 6: augmenting along an augmenting path gives a flow. -/
theorem augment_isFlow (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hf : IsFlow N f) (hp : IsAugmentingPath N f p) : IsFlow N (augment N f p) := by
  obtain ⟨hδ1, hδ⟩ := bottleneck_spec N hp
  refine ⟨fun u v => le_max_left _ _, fun u v => ?_, fun v hs ht => ?_⟩
  · refine max_le (N.cap_nonneg u v) ?_
    have hd := pathNet_le_one hp.2.2.1 u v
    change f u v - f v u + bottleneck N f p * pathNet p u v ≤ N.cap u v
    have h1 := hf.1 v u
    have h2 := hf.2.1 u v
    rcases le_or_gt (pathNet p u v) 0 with h | h
    · nlinarith
    · have he := hδ _ (mem_of_pathNet_pos h)
      have : pathNet p u v = 1 := by omega
      rw [this]
      simp only [residualCap] at he
      linarith
  · rw [cons_iff_net, sum_net_augment N hp, (cons_iff_net f v).1 (hf.2.2 v hs ht)]
    simp [hs, ht]

/-- Lemma 6: augmenting increases the value by the bottleneck. -/
theorem value_augment (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hp : IsAugmentingPath N f p) :
    value N (augment N f p) = value N f + bottleneck N f p := by
  rw [value_eq_net, value_eq_net, sum_net_augment N hp]
  simp [N.s_ne_t]

/-- Lemma 6: augmenting strictly increases the value, by at least `1`. -/
theorem value_augment_ge (N : FlowNetwork n) {f : Fin n → Fin n → ℤ} {p : List (Fin n)}
    (hp : IsAugmentingPath N f p) : value N f + 1 ≤ value N (augment N f p) := by
  rw [value_augment N hp]
  linarith [(bottleneck_spec N hp).1]

end MaxFlowMinCut.Proofs
