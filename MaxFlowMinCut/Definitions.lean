import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Chain

/-!
# Max-Flow Min-Cut and Ford–Fulkerson: definitions

Definitions following Stanford CS161, Lecture 16 ("Max Flow, Min Cut and Ford–Fulkerson").

## Encoding

* Vertices are `Fin n`; the canonical computable vertex list is `List.finRange n`.
* We use the *complete-digraph encoding*: a network is a capacity function
  `cap : Fin n → Fin n → ℤ` on all ordered pairs, and a pair `(u, v)` with `cap u v = 0`
  is a non-edge. Since a flow satisfies `0 ≤ f u v ≤ cap u v`, flows vanish on non-edges,
  so sums over `N_out(v)` / `N_in(v)` in the notes become sums over all vertices.
  This also removes the need for the notes' "no antiparallel edges" assumption (Sec. 6):
  the residual capacity below is the standard generalisation `c(u,v) - f(u,v) + f(v,u)`.
* Capacities are integers (the setting in which Sec. 6 proves termination).
-/

namespace MaxFlowMinCut

open Finset

/-- A flow network (Sec. 2): integer capacities `c(u, v) ≥ 0` on ordered pairs of vertices,
a source `s` and a sink `t ≠ s`. -/
structure FlowNetwork (n : ℕ) where
  /-- The capacity `c(u, v)`; `0` encodes a non-edge. -/
  cap : Fin n → Fin n → ℤ
  cap_nonneg : ∀ u v, 0 ≤ cap u v
  /-- The source. -/
  s : Fin n
  /-- The sink (destination). -/
  t : Fin n
  s_ne_t : s ≠ t

variable {n : ℕ}

/-- `f` is a flow (Sec. 2): capacity constraints `0 ≤ f(u,v) ≤ c(u,v)` and flow
conservation at every vertex other than `s` and `t`. -/
def IsFlow (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧ (∀ u v, f u v ≤ N.cap u v) ∧
    ∀ v, v ≠ N.s → v ≠ N.t → ∑ u, f u v = ∑ w, f v w

/-- The value `|f| = ∑ₓ f(s, x) - ∑_y f(y, s)` of a flow (Sec. 2). -/
def value (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : ℤ :=
  ∑ v, f N.s v - ∑ u, f u N.s

/-- An `s`-`t` cut (Sec. 4), given by its source side `S`; the sink side is `T = Sᶜ`. -/
def IsCut (N : FlowNetwork n) (S : Finset (Fin n)) : Prop :=
  N.s ∈ S ∧ N.t ∉ S

/-- The capacity `c(S, T)` of a cut: total capacity of the edges from `S` to `T = V \ S`. -/
def cutCapacity (N : FlowNetwork n) (S : Finset (Fin n)) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap v u

/-- `f` is a maximum flow: a flow whose value is at least that of every flow. -/
def IsMaxFlow (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Prop :=
  IsFlow N f ∧ ∀ g, IsFlow N g → value N g ≤ value N f

/-- `S` is a minimum cut: no cut has a smaller capacity. -/
def IsMinCut (N : FlowNetwork n) (S : Finset (Fin n)) : Prop :=
  IsCut N S ∧ ∀ T, IsCut N T → cutCapacity N S < cutCapacity N T

instance (N : FlowNetwork n) (S : Finset (Fin n)) : Decidable (IsCut N S) := by
  unfold IsCut; infer_instance

/-! ### Algorithm 1 (Ford–Fulkerson), Sec. 6 -/

/-- Residual capacity `c_f(u, v) = c(u, v) - f(u, v) + f(v, u)` (Sec. 6): how much more flow
can be sent from `u` to `v`, by using spare capacity on `(u, v)` or by undoing flow on
`(v, u)`. -/
def residualCap (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (u v : Fin n) : ℤ :=
  N.cap u v - f u v + f v u

/-- The edges `(x₀, x₁), (x₁, x₂), …` of a path given as its vertex list `[x₀, x₁, …]`. -/
def pathEdges (p : List (Fin n)) : List (Fin n × Fin n) :=
  p.zip p.tail

/-- An augmenting path (Sec. 6): a simple path `s = x₀ → ⋯ → x_k = t` in the residual
network `G_f`, i.e. every step has positive residual capacity. -/
def IsAugmentingPath (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) : Prop :=
  p.head? = some N.s ∧ p.getLast? = some N.t ∧ p.Nodup ∧
    p.IsChain (fun u v => 0 < residualCap N f u v)

instance (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) :
    Decidable (IsAugmentingPath N f p) := by
  unfold IsAugmentingPath; infer_instance

/-- Search for an augmenting path in `G_f` ("check if `t` is reachable from `s` in `G_f`").
The notes allow any search method; we search exhaustively through all simple paths, i.e.
all permutations of all sublists of the vertex list, and return the first augmenting one. -/
def findAugmentingPath (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) : Option (List (Fin n)) :=
  ((List.finRange n).sublists.flatMap List.permutations).find?
    (fun p => decide (IsAugmentingPath N f p))

/-- The bottleneck `F = minᵢ c_f(xᵢ, xᵢ₊₁)` of a path (Lemma 6). -/
def bottleneck (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) : ℤ :=
  (((pathEdges p).map fun e => residualCap N f e.1 e.2).min?).getD 0

/-- Augmenting `f` along `p` by its bottleneck `F` (Lemma 6): `F` is pushed along every
edge of `p`, where pushing along `(u, v)` first undoes flow on `(v, u)`. We write this in
net-flow form: the new flow on `(u, v)` is the positive part of the new net flow
`f(u,v) - f(v,u) ± F`. -/
def augment (N : FlowNetwork n) (f : Fin n → Fin n → ℤ) (p : List (Fin n)) :
    Fin n → Fin n → ℤ := fun u v =>
  max 0 (f u v - f v u +
    bottleneck N f p * (((pathEdges p).count (u, v) : ℤ) - (pathEdges p).count (v, u)))

/-- The main loop of Algorithm 1 with an iteration budget: while an augmenting path exists,
augment along it. -/
def ffLoop (N : FlowNetwork n) : ℕ → (Fin n → Fin n → ℤ) → (Fin n → Fin n → ℤ)
  | 0, f => f
  | k + 1, f =>
    match findAugmentingPath N f with
    | none => f
    | some p => ffLoop N k (augment N f p)

/-- Algorithm 1 (Ford–Fulkerson), started from the all-zeroes flow. With integer capacities
each augmentation increases the value by at least `1` (Sec. 6), and the value is at most
`∑ₓ c(s, x)`, so this many iterations suffice. -/
def fordFulkerson (N : FlowNetwork n) : Fin n → Fin n → ℤ :=
  ffLoop N (∑ v, N.cap N.s v).toNat (fun _ _ => 0)

end MaxFlowMinCut
