import NieWeiOrientedSidorenko.Common

/-!
# Basic definitions

The definitions of Section 1 (finite hosts and sequences) and Section 2 (kernels and
digraphons) of J. Nie and F. Wei, *Sidorenko inequalities and symmetry-forcing for graph
orientations* (unpublished manuscript, 11 November 2026).

Conventions (authors' answer key, Part C):
* C1: a directed graph is an orientation of a finite simple graph: no loops and no
  antiparallel arcs; isolated vertices are allowed; finite hosts are nonempty.
* C2: connectivity refers to the underlying undirected graph.
* C3: any measurable `[0,1]`-valued function on `[0,1]²` is a digraphon.
* C4: kernel equality and distinctness are almost everywhere.
* C5: the ambient space is `[0,1]` with Lebesgue measure; the densities are also defined over a
  general probability space, for the auxiliary spaces the proofs use.
* C9: step Sidorenko and step forcing use (a.e. symmetric) graphons and finite measurable
  partitions into parts of positive measure.
* C10: measure-preserving bijections are measurable equivalences that preserve the measure (their
  inverses are then measurable and measure-preserving).
* C12: a finite step digraphon comes with its partition into positive-measure parts.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal

namespace NieWeiOrientedSidorenko

/-! ## Directed graphs -/

/-- A **directed graph** in the sense of the paper (Section 2, "Directed graphs"): an orientation
of a finite simple graph, i.e. an irreflexive relation with no antiparallel pairs. Finiteness is
a `Fintype` instance on the vertex type wherever it is needed. -/
structure OrientedGraph (V : Type*) where
  /-- `Adj u v` means that `(u, v)` is an arc, directed from `u` to `v`. -/
  Adj : V → V → Prop
  /-- No loops. -/
  irrefl : ∀ v, ¬ Adj v v
  /-- No antiparallel arcs. -/
  asymm : ∀ u v, Adj u v → ¬ Adj v u

namespace OrientedGraph

variable {V W : Type*}

/-- The transpose `D^T`: every arc reversed. -/
def transpose (D : OrientedGraph V) : OrientedGraph V where
  Adj u v := D.Adj v u
  irrefl v := D.irrefl v
  asymm u v h := D.asymm v u h

/-- The underlying undirected simple graph `\bar D`. -/
def underlying (D : OrientedGraph V) : SimpleGraph V := SimpleGraph.fromRel D.Adj

/-- The arc set `E(D)` as a finset of ordered pairs. -/
noncomputable def arcs [Fintype V] (D : OrientedGraph V) : Finset (V × V) := by
  classical exact Finset.univ.filter fun p => D.Adj p.1 p.2

/-- The number of arcs `e(D)`. -/
noncomputable def numArcs [Fintype V] (D : OrientedGraph V) : ℕ := D.arcs.card

/-- An isomorphism of directed graphs: a bijection of vertex sets preserving and reflecting arcs
together with their directions. -/
structure Iso (D : OrientedGraph V) (D' : OrientedGraph W) extends V ≃ W where
  /-- Arcs and their directions are preserved and reflected. -/
  map_adj_iff : ∀ u v, D'.Adj (toEquiv u) (toEquiv v) ↔ D.Adj u v

/-- `D` is connected: its underlying undirected graph is connected (convention C2). -/
def IsConnected (D : OrientedGraph V) : Prop := D.underlying.Connected

/-- A **one-direction orientation** (Theorem 1.2(a)): the vertex set has a bipartition `A ∪ B`
(with `B` the complement of `A`) such that every arc is directed from `A` to `B`. -/
def IsOneDirection (D : OrientedGraph V) : Prop :=
  ∃ A : Set V, ∀ u v, D.Adj u v → u ∈ A ∧ v ∉ A

/-- `D` is isomorphic to its transpose `D^T` (Theorem 1.2(b)). -/
def IsSelfConverse (D : OrientedGraph V) : Prop := Nonempty (D.Iso D.transpose)

/-! ### Discrete homomorphism densities (Section 1 and Section 2) -/

/-- The number of homomorphisms of directed graphs from `D` to `G`: maps of vertex sets sending
every arc `(u, v)` of `D` to an arc `(f u, f v)` of `G`. -/
noncomputable def homCount [Fintype V] [Fintype W] (D : OrientedGraph V) (G : OrientedGraph W) :
    ℕ := by
  classical exact (Finset.univ.filter fun f : V → W => ∀ u v, D.Adj u v → G.Adj (f u) (f v)).card

/-- The directed homomorphism density `t(D, G) = |Hom(D, G)| / |V(G)|^{v(D)}`. -/
noncomputable def homDensity [Fintype V] [Fintype W] (D : OrientedGraph V)
    (G : OrientedGraph W) : ℝ :=
  (homCount D G : ℝ) / (Fintype.card W : ℝ) ^ Fintype.card V

end OrientedGraph

/-- The number of homomorphisms of simple graphs from `H` to `G`. -/
noncomputable def simpleHomCount {V W : Type*} [Fintype V] [Fintype W] (H : SimpleGraph V)
    (G : SimpleGraph W) : ℕ := by
  classical exact (Finset.univ.filter fun f : V → W => ∀ u v, H.Adj u v → G.Adj (f u) (f v)).card

/-- The homomorphism density `t(H, G)` of simple graphs: the probability that a uniformly random
map `V(H) → V(G)` sends every edge to an edge. -/
noncomputable def simpleHomDensity {V W : Type*} [Fintype V] [Fintype W] (H : SimpleGraph V)
    (G : SimpleGraph W) : ℝ :=
  (simpleHomCount H G : ℝ) / (Fintype.card W : ℝ) ^ Fintype.card V

namespace OrientedGraph

variable {V W : Type*}

/-- The symmetrized finite density `t(D, (G + G^T)/2) := 2^{-e(D)} t(\bar D, \bar G)` of
Section 1.2 (the exact finite baseline, answer key B2). -/
noncomputable def symmDensity [Fintype V] [Fintype W] (D : OrientedGraph V)
    (G : OrientedGraph W) : ℝ :=
  (2 : ℝ)⁻¹ ^ D.numArcs * simpleHomDensity D.underlying G.underlying

/-- **Definition 1 (OS), finite form.** `D` has the oriented Sidorenko property if
`t(D, G) ≥ t(D, (G + G^T)/2)` for every (finite, nonempty) directed graph `G`. -/
def IsOS [Fintype V] (D : OrientedGraph V) : Prop :=
  ∀ (W : Type) [Fintype W] [Nonempty W] (G : OrientedGraph W), symmDensity D G ≤ homDensity D G

/-- **Definition 1 (OAS), finite form.** `D` has the oriented anti-Sidorenko property if
`t(D, G) ≤ t(D, (G + G^T)/2)` for every (finite, nonempty) directed graph `G`. -/
def IsOAS [Fintype V] (D : OrientedGraph V) : Prop :=
  ∀ (W : Type) [Fintype W] [Nonempty W] (G : OrientedGraph W), homDensity D G ≤ symmDensity D G

/-- `e_G(A, B)`: the number of arcs of `G` directed from `A` to `B` (Section 1.2). -/
noncomputable def arcsFromTo [Fintype W] (G : OrientedGraph W) (A B : Finset W) : ℕ := by
  classical exact (G.arcs.filter fun p => p.1 ∈ A ∧ p.2 ∈ B).card

/-- A sequence of directed graphs `G n` on `Fin (N n)` is **quasi-random in its orientations**
(Section 1.2): `max_{A,B} |e(A,B) - e(B,A)| = o(|V(G_n)|²)`, the vertex sets `A, B` being
arbitrary, possibly overlapping (convention C8). -/
def IsOrientQuasirandom (N : ℕ → ℕ) (G : ∀ n, OrientedGraph (Fin (N n))) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ A B : Finset (Fin (N n)),
    |((G n).arcsFromTo A B : ℝ) - (G n).arcsFromTo B A| ≤ ε * (N n : ℝ) ^ 2

/-- **Definition 2 (symmetry-forcing), sequence form.** For every sequence of directed graphs
`G n` with `|V(G n)| → ∞`, `t(D, G n) = t(D, (G n + (G n)^T)/2) + o(1)` holds if and only if
the sequence is quasi-random in its orientations. Hosts are taken on the vertex sets
`Fin (N n)`; densities are invariant under relabelling. -/
def IsSymmetryForcing [Fintype V] (D : OrientedGraph V) : Prop :=
  ∀ (N : ℕ → ℕ) (G : ∀ n, OrientedGraph (Fin (N n))), Tendsto N atTop atTop →
    (Tendsto (fun n => homDensity D (G n) - symmDensity D (G n)) atTop (𝓝 0) ↔
      IsOrientQuasirandom N G)

end OrientedGraph

/-! ## Kernels and digraphons (Section 2) -/

section Kernels

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A (directed) **kernel**: a bounded measurable function `Ω × Ω → ℝ`, not necessarily
symmetric. -/
def IsKernel (U : Ω → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry U) ∧ ∃ M : ℝ, ∀ x y, |U x y| ≤ M

/-- A **digraphon**: a measurable kernel with values in `[0, 1]` (convention C3). -/
def IsDigraphon (U : Ω → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry U) ∧ ∀ x y, U x y ∈ Icc (0 : ℝ) 1

/-- The transpose `W^T(x, y) = W(y, x)`. -/
def kTranspose (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => U y x

/-- The symmetrization `(W + W^T)/2`. -/
noncomputable def symmetrize (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => (U x y + U y x) / 2

/-- Two kernels agree almost everywhere (kernels are identified up to null sets, C4). -/
def AEEq (μ : Measure Ω) (U U' : Ω → Ω → ℝ) : Prop :=
  ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = U' p.1 p.2

/-- A **graphon** is a symmetric digraphon: `W(x, y) = W(y, x)` for almost all `(x, y)`. -/
def IsGraphon (μ : Measure Ω) (U : Ω → Ω → ℝ) : Prop :=
  IsDigraphon U ∧ AEEq μ U (kTranspose U)

/-- The directed homomorphism density over a probability space `(Ω, μ)`:
`t(D, W) = ∫ ∏_{(u, w) ∈ E(D)} W(x_u, x_w) ∏_v dx_v`. -/
noncomputable def tDir (μ : Measure Ω) [SigmaFinite μ] {V : Type*} [Fintype V]
    (D : OrientedGraph V) (U : Ω → Ω → ℝ) : ℝ :=
  ∫ x : V → Ω, ∏ p ∈ D.arcs, U (x p.1) (x p.2) ∂(Measure.pi fun _ => μ)

/-- The homomorphism density of an undirected graph `H` in a kernel over `(Ω, μ)`. Each edge is
read in a fixed (arbitrary) order of its endpoints; for (a.e.) symmetric kernels, the only ones it
is applied to, the order does not matter. -/
noncomputable def tUndir (μ : Measure Ω) [SigmaFinite μ] {V : Type*} [Fintype V]
    (H : SimpleGraph V) (U : Ω → Ω → ℝ) : ℝ := by
  classical
  exact ∫ x : V → Ω, ∏ e ∈ H.edgeFinset, U (x (Quot.out e).1) (x (Quot.out e).2)
    ∂(Measure.pi fun _ => μ)

/-- The **bipartite homomorphism density** `t_bi(H, W)` of a bipartite graph with a fixed
bipartition `X ∪ Y` and edge set `E ⊆ X × Y`: vertices of `X` are mapped to the first coordinate
and vertices of `Y` to the second. -/
noncomputable def tBi (μ : Measure Ω) [SigmaFinite μ] {X Y : Type*} [Fintype X] [Fintype Y]
    (E : Finset (X × Y)) (U : Ω → Ω → ℝ) : ℝ :=
  ∫ z : (X → Ω) × (Y → Ω), ∏ p ∈ E, U (z.1 p.1) (z.2 p.2)
    ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))

/-- The **decorated** homomorphism density `t_bi(H; (U_e)_e)`: edge `e` is read in `U e`. -/
noncomputable def tBiDec (μ : Measure Ω) [SigmaFinite μ] {X Y : Type*} [Fintype X] [Fintype Y]
    (E : Finset (X × Y)) (U : X × Y → Ω → Ω → ℝ) : ℝ :=
  ∫ z : (X → Ω) × (Y → Ω), ∏ p ∈ E, U p (z.1 p.1) (z.2 p.2)
    ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))

end Kernels

/-! ### On `[0, 1]` -/

/-- `t(D, W)` on `[0, 1]` with Lebesgue measure. -/
noncomputable abbrev t {V : Type*} [Fintype V] (D : OrientedGraph V) (U : I → I → ℝ) : ℝ :=
  tDir volume D U

/-- `t(H, W)` of an undirected graph on `[0, 1]`. -/
noncomputable abbrev tU {V : Type*} [Fintype V] (H : SimpleGraph V) (U : I → I → ℝ) : ℝ :=
  tUndir volume H U

/-- `t_bi(H, W)` on `[0, 1]`. -/
noncomputable abbrev tb {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (U : I → I → ℝ) : ℝ :=
  tBi volume E U

namespace OrientedGraph

variable {V : Type*} [Fintype V]

/-- **OS in digraphon language** (Section 2): `t(D, W) ≥ t(D, (W + W^T)/2)` for every
digraphon `W`. -/
def IsOSK (D : OrientedGraph V) : Prop :=
  ∀ U : I → I → ℝ, IsDigraphon U → t D (symmetrize U) ≤ t D U

/-- **OAS in digraphon language** (Section 2): `t(D, W) ≤ t(D, (W + W^T)/2)` for every
digraphon `W`. -/
def IsOASK (D : OrientedGraph V) : Prop :=
  ∀ U : I → I → ℝ, IsDigraphon U → t D U ≤ t D (symmetrize U)

/-- **Symmetry-forcing in digraphon language** (Section 2): for every digraphon `W`,
`t(D, W) = t(D, (W + W^T)/2)` implies `W = W^T` almost everywhere. -/
def IsSymmetryForcingK (D : OrientedGraph V) : Prop :=
  ∀ U : I → I → ℝ, IsDigraphon U → t D U = t D (symmetrize U) →
    AEEq volume U (kTranspose U)

end OrientedGraph

/-! ## Norming and weakly norming (Section 2) -/

section Norming

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `‖W‖_{r(H)} = t_bi(H, |W|)^{1/e(H)}`. -/
noncomputable def rNorm (E : Finset (X × Y)) (U : I → I → ℝ) : ℝ :=
  tb E (fun x y => |U x y|) ^ ((1 : ℝ) / E.card)

/-- `‖W‖_H = |t_bi(H, W)|^{1/e(H)}`. -/
noncomputable def hNorm (E : Finset (X × Y)) (U : I → I → ℝ) : ℝ :=
  |tb E U| ^ ((1 : ℝ) / E.card)

/-- A functional `N` on kernels is a **norm on the space of all kernels** (kernels identified up to
null sets): absolutely homogeneous, subadditive, and zero only at the a.e.-zero kernel. -/
def IsKernelNorm (N : (I → I → ℝ) → ℝ) : Prop :=
  (∀ U, IsKernel U → ∀ c : ℝ, N (fun x y => c * U x y) = |c| * N U) ∧
  (∀ U V, IsKernel U → IsKernel V → N (fun x y => U x y + V x y) ≤ N U + N V) ∧
  (∀ U, IsKernel U → N U = 0 → AEEq volume U (fun _ _ => 0))

/-- A bipartite graph with a fixed bipartition is **weakly norming** if `‖·‖_{r(H)}` is a norm on
the space of all kernels (full-kernel convention). -/
def IsWeaklyNorming (E : Finset (X × Y)) : Prop := IsKernelNorm (rNorm E)

/-- A bipartite graph with a fixed bipartition is **norming** if `‖·‖_H` is a norm on the space
of all kernels. -/
def IsNorming (E : Finset (X × Y)) : Prop := IsKernelNorm (hNorm E)

/-- The undirected graph on `X ⊕ Y` underlying a bipartite edge set. -/
def bipGraph (E : Finset (X × Y)) : SimpleGraph (X ⊕ Y) :=
  SimpleGraph.fromRel fun a b => ∃ x y, a = Sum.inl x ∧ b = Sum.inr y ∧ (x, y) ∈ E

end Norming

section GraphNorming

variable {V : Type*} [Fintype V]

/-- The bipartite edge set of a simple graph `H` with respect to a side predicate `s`: pairs
`(x, y)` with `s x`, `¬ s y` and `x ~ y`. -/
noncomputable def sideEdges (H : SimpleGraph V) (s : V → Prop) :
    Finset ({v // s v} × {v // ¬ s v}) := by
  classical exact Finset.univ.filter fun p => H.Adj p.1 p.2

/-- `s` is a bipartition of `H`: every edge joins a vertex with `s` to one without. -/
def IsBipartition (H : SimpleGraph V) (s : V → Prop) : Prop :=
  ∀ u v, H.Adj u v → (s u ↔ ¬ s v)

/-- An undirected graph is **weakly norming** (full-kernel convention) if it has a bipartition for
which the resulting bipartite graph is weakly norming. -/
def IsWeaklyNormingGraph (H : SimpleGraph V) : Prop :=
  ∃ s : V → Prop, IsBipartition H s ∧
    letI := Classical.decPred s
    IsWeaklyNorming (sideEdges H s)

/-- An undirected graph is **norming** (full-kernel convention) if it has a bipartition for which
the resulting bipartite graph is norming. -/
def IsNormingGraph (H : SimpleGraph V) : Prop :=
  ∃ s : V → Prop, IsBipartition H s ∧
    letI := Classical.decPred s
    IsNorming (sideEdges H s)

/-- **Weakly norming in the symmetric convention**: `W ↦ t(H, |W|)^{1/e(H)}` is a norm on the
space of (a.e.) symmetric kernels. -/
def IsWeaklyNormingSymm (H : SimpleGraph V) : Prop :=
  letI := Classical.decRel H.Adj
  let N : (I → I → ℝ) → ℝ := fun U => tU H (fun x y => |U x y|) ^ ((1 : ℝ) / H.edgeFinset.card)
  let Sym : (I → I → ℝ) → Prop := fun U => IsKernel U ∧ AEEq volume U (kTranspose U)
  (∀ U, Sym U → ∀ c : ℝ, N (fun x y => c * U x y) = |c| * N U) ∧
  (∀ U V, Sym U → Sym V → N (fun x y => U x y + V x y) ≤ N U + N V) ∧
  (∀ U, Sym U → N U = 0 → AEEq volume U (fun _ _ => 0))

end GraphNorming

/-! ## Step averaging, envelopes and the cut distance (Section 2) -/

section Step

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite measurable partition of `Ω` into parts of positive measure (convention C9). -/
structure PosPartition (μ : Measure Ω) where
  /-- The number of parts. -/
  k : ℕ
  /-- The parts. -/
  part : Fin k → Set Ω
  measurableSet_part : ∀ i, MeasurableSet (part i)
  pos : ∀ i, 0 < μ (part i)
  disjoint : Pairwise fun i j => Disjoint (part i) (part j)
  cover : (⋃ i, part i) = univ

/-- The step average `W^𝒫 = W_𝒫`: on `P_i × P_j` it is the average of `W` over `P_i × P_j`. -/
noncomputable def stepAvg {μ : Measure Ω} (P : PosPartition μ) (U : Ω → Ω → ℝ) : Ω → Ω → ℝ :=
  fun x y => ∑ i, ∑ j, (P.part i).indicator (fun _ => (1 : ℝ)) x *
    (P.part j).indicator (fun _ => (1 : ℝ)) y *
    ((∫ p in P.part i ×ˢ P.part j, U p.1 p.2 ∂(μ.prod μ)) /
      ((μ (P.part i)).toReal * (μ (P.part j)).toReal))

end Step

/-- A measure-preserving bijection of `[0, 1]` (convention C10). -/
def MPBij : Type := {φ : I ≃ᵐ I // MeasurePreserving φ volume volume}

/-- The version `W^φ(x, y) = W(φ x, φ y)`. -/
def pullback (φ : I → I) (U : I → I → ℝ) : I → I → ℝ := fun x y => U (φ x) (φ y)

/-- Weak* convergence of kernels on `[0, 1]`: `∫_{A×B} W_n → ∫_{A×B} W` for all measurable
`A, B`. -/
def WeakStarTendsto (Un : ℕ → I → I → ℝ) (U : I → I → ℝ) : Prop :=
  ∀ A B : Set I, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n => ∫ p in A ×ˢ B, Un n p.1 p.2) atTop (𝓝 (∫ p in A ×ˢ B, U p.1 p.2))

/-- The **envelope** `⟨W⟩`: the graphons that are weak* limits of sequences of versions
`W^{φ_n}`, `φ_n` measure-preserving bijections. -/
def envelope (U : I → I → ℝ) : Set (I → I → ℝ) :=
  {U' | IsGraphon volume U' ∧ ∃ φ : ℕ → MPBij, WeakStarTendsto (fun n => pullback (φ n).1 U) U'}

/-- `U ⪯ W`: `⟨U⟩ ⊆ ⟨W⟩`. -/
def StructLE (U W : I → I → ℝ) : Prop := envelope U ⊆ envelope W

/-- `U ≺ W`: `⟨U⟩ ⊊ ⟨W⟩`. -/
def StructLT (U W : I → I → ℝ) : Prop := envelope U ⊂ envelope W

/-- A graphon parameter is **cut distance compatible** if `U ⪯ W` implies `θ(U) ≤ θ(W)`. -/
def CutDistCompatible (θ : (I → I → ℝ) → ℝ) : Prop :=
  ∀ U W, IsGraphon volume U → IsGraphon volume W → StructLE U W → θ U ≤ θ W

/-- A graphon parameter is **cut distance identifying** if `U ≺ W` implies `θ(U) < θ(W)`. -/
def CutDistIdentifying (θ : (I → I → ℝ) → ℝ) : Prop :=
  ∀ U W, IsGraphon volume U → IsGraphon volume W → StructLT U W → θ U < θ W

/-- The **cut norm** `‖F‖_□ = sup_{S,T} |∫_{S×T} F|` over measurable `S, T ⊆ [0,1]`. -/
noncomputable def cutNorm (F : I → I → ℝ) : ℝ :=
  sSup {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧ r = |∫ p in S ×ˢ T, F p.1 p.2|}

/-- The **cut distance** of the paper, `δ_□(U, W) = inf_φ ‖U - W^φ‖_□` over measure-preserving
bijections `φ`. -/
noncomputable def cutDist (U W : I → I → ℝ) : ℝ :=
  sInf {r | ∃ φ : MPBij, r = cutNorm fun x y => U x y - pullback φ.1 W x y}

/-- The map-based cut distance `δ_□^{map}(U, W) = inf_φ ‖U - W^φ‖_□` over measure-preserving maps
`φ : [0,1] → [0,1]` (Fox–Himwich–Mani–Zhou, Definition 12). -/
noncomputable def cutDistMap (U W : I → I → ℝ) : ℝ :=
  sInf {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
    r = cutNorm fun x y => U x y - pullback φ W x y}

/-! ## Step Sidorenko and step forcing (Section 2) -/

section StepProps

variable {V : Type*} [Fintype V]

/-- `H` is **step Sidorenko**: `t(H, W^𝒫) ≤ t(H, W)` for every graphon `W` and every finite
partition `𝒫` of `[0, 1]` into measurable parts of positive measure. -/
def IsStepSidorenko (H : SimpleGraph V) : Prop :=
  ∀ U : I → I → ℝ, IsGraphon volume U → ∀ P : PosPartition (volume : Measure I),
    tU H (stepAvg P U) ≤ tU H U

/-- `H` is **step forcing**: `t(H, W^𝒫) < t(H, W)` whenever `W` and `W^𝒫` differ on a set of
positive measure. -/
def IsStepForcing (H : SimpleGraph V) : Prop :=
  ∀ U : I → I → ℝ, IsGraphon volume U → ∀ P : PosPartition (volume : Measure I),
    ¬ AEEq volume U (stepAvg P U) → tU H (stepAvg P U) < tU H U

end StepProps

/-! ## Convexity on kernels (Section 1.4.2 and Lemma 2.3) -/

section Convexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `t_bi(H, ·)` is convex on nonnegative (bounded measurable) kernels. -/
def ConvexOnNonnegKernels (E : Finset (X × Y)) : Prop :=
  ∀ U V : I → I → ℝ, IsKernel U → IsKernel V → (∀ x y, 0 ≤ U x y) → (∀ x y, 0 ≤ V x y) →
    ∀ a : ℝ, a ∈ Icc (0 : ℝ) 1 →
      tb E (fun x y => a * U x y + (1 - a) * V x y) ≤ a * tb E U + (1 - a) * tb E V

/-- `t_bi(H, ·)` is strictly convex on nonnegative kernels (convention C7: all bounded
nonnegative kernels): strict inequality for distinct (not a.e. equal) kernels. -/
def StrictConvexOnNonnegKernels (E : Finset (X × Y)) : Prop :=
  ∀ U V : I → I → ℝ, IsKernel U → IsKernel V → (∀ x y, 0 ≤ U x y) → (∀ x y, 0 ≤ V x y) →
    ¬ AEEq volume U V → ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
      tb E (fun x y => a * U x y + (1 - a) * V x y) < a * tb E U + (1 - a) * tb E V

/-- `t_bi(H, ·)` is strictly convex on real-valued (bounded measurable) kernels. -/
def StrictConvexOnKernels (E : Finset (X × Y)) : Prop :=
  ∀ U V : I → I → ℝ, IsKernel U → IsKernel V → ¬ AEEq volume U V →
    ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
      tb E (fun x y => a * U x y + (1 - a) * V x y) < a * tb E U + (1 - a) * tb E V

end Convexity

end NieWeiOrientedSidorenko
