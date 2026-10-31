import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Defs
import Batteries.Data.List.Basic

/-!
# Max-Flow Min-Cut and Ford–Fulkerson: definitions

Definitions needed to *state* the results of Stanford CS161 Lecture 16
("Max Flow, Min Cut and Ford-Fulkerson"), restricted to **integer capacities**.

## Encoding of the graph

The notes work with a directed graph `G = (V, E)` and capacities `c : E → ℝ≥0`
(integer-valued for the termination argument of Sec. 6). We label the vertices
`0, …, n-1`, i.e. `V = Fin n`, and encode `G` as a *complete* digraph whose
capacity function `cap : Fin n → Fin n → ℤ` is `0` on non-edges `(u, v) ∉ E`.
This is equivalent to the notes' setting: on a non-edge the capacity
constraint `0 ≤ f u v ≤ cap u v = 0` forces `f u v = 0`, so flows, flow values and
cut capacities are exactly the notes' ones (non-edges contribute `0` to every sum).
Self-loops and pairs of antiparallel edges are allowed; we do **not** make the
Sec. 6 "no antiparallel edges" simplification.

Flows are plain functions `Fin n → Fin n → ℤ`; being a flow is a predicate.
-/

namespace MaxFlowMinCut

/-- A flow network (Sec. 2): `n` vertices `Fin n`, nonnegative integer capacities
`cap u v` on every ordered pair (`0` meaning "no edge"), a source `s` and a sink `t`
with `s ≠ t`. -/
structure FlowNetwork (n : ℕ) where
  /-- Capacity `c(u, v)`; `0` for pairs that are not edges of `G`. -/
  cap : Fin n → Fin n → ℤ
  /-- Capacities are nonnegative: `c : E → ℤ≥0`. -/
  cap_nonneg : ∀ u v, 0 ≤ cap u v
  /-- The source. -/
  s : Fin n
  /-- The sink (destination). -/
  t : Fin n
  /-- Source and sink are distinct. -/
  s_ne_t : s ≠ t

variable {n : ℕ}

/-- `f` is a flow (Sec. 2): (1) capacity constraints `0 ≤ f(u,v) ≤ c(u,v)`, and
(2) flow conservation at every `v ∈ V - {s, t}`: flow into `v` equals flow out of `v`.
(Sums range over all vertices; non-neighbours contribute `0`.) -/
def IsFlow (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧ (∀ u v, f u v ≤ N.cap u v) ∧
    (∀ v, v ≠ N.s → v ≠ N.t → ∑ u, f u v = ∑ w, f v w)

/-- The value `|f| = Σ_x f(s, x) - Σ_y f(y, s)` of a flow (Sec. 2): flow out of `s`
minus flow into `s`. -/
def value (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : ℤ :=
  ∑ v, f N.s v - ∑ u, f u N.s

/-- An `s`-`t` cut (Sec. 4): a partition `V = S ∪ T` (with `T = Sᶜ`) with `s ∈ S`, `t ∈ T`. -/
def IsCut (N : FlowNetwork n) (S : Finset (Fin n)) : Prop :=
  N.s ∈ S ∧ N.t ∉ S

/-- The capacity `c(S, T) = Σ_{x ∈ S, y ∈ T} c(x, y)` of a cut (Sec. 4), with `T = Sᶜ`:
only edges from `S` to `T` are counted. -/
def cutCapacity (N : FlowNetwork n) (S : Finset (Fin n)) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v

/-- `f` is a maximum flow: a flow whose value is at least that of every flow. -/
def IsMaxFlow (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Prop :=
  IsFlow N f ∧ ∀ g, IsFlow N g → value N g ≤ value N f

/-- `S` is a minimum `s`-`t` cut: a cut whose capacity is at most that of every cut. -/
def IsMinCut (N : FlowNetwork n) (S : Finset (Fin n)) : Prop :=
  IsCut N S ∧ ∀ T, IsCut N T → cutCapacity N S ≤ cutCapacity N T

/-! ## The Ford–Fulkerson method (Sec. 6, Algorithm 1) -/

/-- Residual capacity `c_f(u, v) = c(u, v) - f(u, v) + f(v, u)` (Sec. 6).

This is the notes' `c_f` generalized to allow antiparallel edges: under the notes'
assumption that `(u,v)` and `(v,u)` are never both edges, if `(u, v) ∈ E` then
`f(v,u) = 0` and this is `c(u,v) - f(u,v)`; if `(v, u) ∈ E` then `c(u,v) = f(u,v) = 0`
and this is `f(v,u)`; otherwise it is `0` — exactly the notes' three cases. -/
def residualCap (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (u v : Fin n) : ℤ :=
  N.cap u v - f u v + f v u

/-- The edges `(x₀,x₁), (x₁,x₂), …` of a path given as its vertex list `[x₀, x₁, …]`. -/
def pathEdges (p : List (Fin n)) : List (Fin n × Fin n) :=
  p.zip p.tail

/-- An augmenting path (Sec. 6): a simple path `s = x₀ → x₁ → ⋯ → x_k = t` in the
residual network `G_f`, i.e. consecutive vertices have positive residual capacity. -/
def IsAugmentingPath (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) : Prop :=
  p.head? = some N.s ∧ p.getLast? = some N.t ∧ p.Nodup ∧
    p.IsChain (fun u v => 0 < residualCap N f u v)

instance (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) :
    Decidable (IsAugmentingPath N f p) := by
  unfold IsAugmentingPath; infer_instance

/-- Find an augmenting path, if one exists, by exhaustive search over all simple paths
(all permutations of all sublists of the vertex list `[0, …, n-1]`). Exponential, but
trivially correct; the notes allow any method of choosing the path ("DFS, BFS, or any
other method"). -/
def findAugmentingPath (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Option (List (Fin n)) :=
  ((List.finRange n).sublists.flatMap List.permutations).find?
    (fun p => decide (IsAugmentingPath N f p))

/-- The bottleneck `F = min_i c_f(x_i, x_{i+1})` of a path (Lemma 6): the minimum residual
capacity over its edges (`0` for a path without edges, which never occurs for an
augmenting path since `s ≠ t`). -/
def bottleneck (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) : ℤ :=
  ((pathEdges p).map (fun e => residualCap N f e.1 e.2)).min?.getD 0

/-- Augment `f` along `p` by `δ = bottleneck N f p` (Lemma 6, the flow `f'`).

We work with net flow: the new net flow `f'(u,v) - f'(v,u)` is the old net flow plus
`δ` if `(u,v)` is an edge of `p`, minus `δ` if `(v,u)` is an edge of `p`; the new flow on
`(u,v)` is the positive part of the new net flow. This changes net flows exactly as the
notes' `f'` does (`f(u,v) + F` if `(u,v) ∈ P`, `f(u,v) - F` if `(v,u) ∈ P`), and under the
notes' no-antiparallel-edges assumption it coincides with `f'` on every edge; unlike the
literal formula it stays a flow when antiparallel edges are present. -/
def augment (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) :
    Fin n → Fin n → ℤ :=
  fun u v => max 0 (f u v - f v u + bottleneck N f p *
    (((pathEdges p).count (u, v) : ℤ) - ((pathEdges p).count (v, u) : ℤ)))

/-- The main loop of Algorithm 1, run for at most `k` rounds: while an augmenting path
exists, augment along it. -/
def ffLoop (N : FlowNetwork n) : ℕ → (Fin n → Fin n → ℤ) → (Fin n → Fin n → ℤ)
  | 0, f => f
  | k + 1, f =>
    match findAugmentingPath N f with
    | none => f
    | some p => ffLoop N k (augment N f p)

/-- Algorithm 1 (Ford–Fulkerson): start from the all-zeroes flow and augment while an
augmenting path exists. The round budget `Σ_v c(s, v)` is the notes' integer-capacity
termination argument: each round increases the value by at least `1`, and no flow has
value exceeding the total capacity out of `s`, so the loop stops (no augmenting path
left) within the budget. -/
def fordFulkerson (N : FlowNetwork n) : Fin n → Fin n → ℤ :=
  ffLoop N (∑ v, N.cap N.s v).toNat (fun _ _ => 0)

end MaxFlowMinCut
