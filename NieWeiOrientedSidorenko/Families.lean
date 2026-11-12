import NieWeiOrientedSidorenko.Basic

/-!
# Named directed graphs and families

The two orientations `O₁, O₂` of `C₄` (Section 1.2, Figure 1), the directed edge, the directed
two-edge path, the family `D_t` (Definition 3), oriented stars, paths and cycles (Section 1.4.3,
convention C11), and the girth cycles and orientation imbalance of Section 6.3.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace NieWeiOrientedSidorenko

namespace OrientedGraph

/-- An oriented graph given by a finite list of arcs on `Fin n`; loops and antiparallel pairs
are excluded by the two decidable side conditions. -/
def ofArcs {n : ℕ} (A : Finset (Fin n × Fin n)) (h1 : ∀ v, (v, v) ∉ A)
    (h2 : ∀ u v, (u, v) ∈ A → (v, u) ∉ A) : OrientedGraph (Fin n) where
  Adj u v := (u, v) ∈ A
  irrefl v := h1 v
  asymm u v h := h2 u v h

/-- `O₁ : 1 ← 2 → 3 → 4 → 1` (Section 1.2), with vertices `1, 2, 3, 4` relabelled `0, 1, 2, 3`:
arcs `2→1, 2→3, 3→4, 4→1`. -/
def O₁ : OrientedGraph (Fin 4) :=
  ofArcs {(1, 0), (1, 2), (2, 3), (3, 0)} (by decide) (by decide)

/-- `O₂ : 1 ← 2 → 3 ← 4 → 1` (Section 1.2), with vertices `1, 2, 3, 4` relabelled `0, 1, 2, 3`:
arcs `2→1, 2→3, 4→3, 4→1`. -/
def O₂ : OrientedGraph (Fin 4) :=
  ofArcs {(1, 0), (1, 2), (3, 2), (3, 0)} (by decide) (by decide)

/-- The directed edge `0 → 1`. -/
def dirEdge : OrientedGraph (Fin 2) :=
  ofArcs {(0, 1)} (by decide) (by decide)

/-- The directed two-edge path `1 → 2 → 3`, relabelled `0 → 1 → 2`. -/
def dirPath3 : OrientedGraph (Fin 3) :=
  ofArcs {(0, 1), (1, 2)} (by decide) (by decide)

/-- **Definition 3.** For `t ≥ 2`, `D_t` is the orientation of `K_{t, 2^t}` with parts
`X = {u_1, …, u_t}` (here `Fin t`) and `{v_ε : ε ∈ {-1, 1}^t}` (here `ε : Fin t → Bool`, with
`true` for `1` and `false` for `-1`): the edge between `u_i` and `v_ε` is `u_i → v_ε` if
`ε_i = 1` and `v_ε → u_i` if `ε_i = -1`. (The definition makes sense for every `t`; the paper
uses it for `t ≥ 2`.) -/
def Dt (t : ℕ) : OrientedGraph (Fin t ⊕ (Fin t → Bool)) where
  Adj a b := match a, b with
    | Sum.inl i, Sum.inr ε => ε i = true
    | Sum.inr ε, Sum.inl i => ε i = false
    | _, _ => False
  irrefl v := by cases v <;> simp
  asymm u v h := by
    cases u <;> cases v <;> simp_all

/-- `D` is **homomorphic to a directed edge** (Theorem 4.1(a)): there is a map `f : V → Fin 2`
sending every arc to the arc `0 → 1`. -/
def HomToDirEdge {V : Type*} (D : OrientedGraph V) : Prop :=
  ∃ f : V → Fin 2, ∀ u v, D.Adj u v → f u = 0 ∧ f v = 1

variable {V : Type*} [Fintype V]

/-- In-degree of a vertex. -/
noncomputable def inDeg (D : OrientedGraph V) (c : V) : ℕ := by
  classical exact (Finset.univ.filter fun u => D.Adj u c).card

/-- Out-degree of a vertex. -/
noncomputable def outDeg (D : OrientedGraph V) (c : V) : ℕ := by
  classical exact (Finset.univ.filter fun v => D.Adj c v).card

/-- `D` is an **oriented star with center `c`**: its underlying graph is the star whose edges are
exactly the pairs `{c, u}`, `u ≠ c` (a star has at least one edge, C11; the number of edges is
`e(D)`). -/
def IsOrientedStar (D : OrientedGraph V) (c : V) : Prop :=
  (∀ u v, D.underlying.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c)) ∧ 1 ≤ D.numArcs

/-- `D` is an **oriented path**: its underlying graph is isomorphic to a path with
`|V(D)|` vertices and at least one edge (C11). -/
def IsOrientedPath (D : OrientedGraph V) : Prop :=
  Nonempty (D.underlying ≃g SimpleGraph.pathGraph (Fintype.card V)) ∧ 2 ≤ Fintype.card V

/-- `D` is an **oriented cycle**: its underlying graph is isomorphic to a cycle of length
`|V(D)| ≥ 3` (C11). -/
def IsOrientedCycle (D : OrientedGraph V) : Prop :=
  Nonempty (D.underlying ≃g SimpleGraph.cycleGraph (Fintype.card V)) ∧ 3 ≤ Fintype.card V

/-- An **alternating orientation**: every vertex is a source or a sink. -/
def IsAlternating (D : OrientedGraph V) : Prop :=
  ∀ v, (∀ u, ¬ D.Adj u v) ∨ (∀ u, ¬ D.Adj v u)

/-! ### Girth cycles and orientation imbalance (Section 6.3) -/

/-- The orientation imbalance of a walk in `\bar D`: the number of its steps that follow the
orientation of `D` minus the number that go against it. -/
noncomputable def walkImbalance (D : OrientedGraph V) {u v : V} (w : D.underlying.Walk u v) :
    ℤ := by
  classical exact (w.darts.map fun d => if D.Adj d.fst d.snd then (1 : ℤ) else -1).sum

/-- `𝒞_g(D)`: the cycles of length `g` of `\bar D`, each given by its edge set. -/
noncomputable def cyclesOfLength (D : OrientedGraph V) (g : ℕ) : Finset (Finset (Sym2 V)) := by
  classical
  exact Finset.univ.filter fun C =>
    ∃ (v : V) (w : D.underlying.Walk v v), w.IsCycle ∧ w.length = g ∧ w.edges.toFinset = C

/-- `cos(ω_D(C) θ)` for a cycle `C` given by its edge set: `ω_D(C) = f_D(C) - b_D(C)` is read
along a cycle walk traversing `C` in one of its two cyclic directions (chosen arbitrarily; the
cosine does not depend on the choice); `0` for a set that is not a cycle's edge set. -/
noncomputable def cosImbalance (D : OrientedGraph V) (θ : ℝ) (C : Finset (Sym2 V)) : ℝ := by
  classical
  exact if h : ∃ (v : V) (w : D.underlying.Walk v v), w.IsCycle ∧ w.edges.toFinset = C then
    Real.cos ((walkImbalance D (Classical.choose (Classical.choose_spec h)) : ℝ) * θ)
  else 0

end OrientedGraph

end NieWeiOrientedSidorenko
