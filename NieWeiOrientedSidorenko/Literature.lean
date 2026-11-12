import NieWeiOrientedSidorenko.Basic

/-!
# Literature hypotheses

The published results that `paper/SOURCES.md` (Part 1) permits as named hypotheses. Each is a
`Prop` definition, taken as an explicit argument wherever it is used; none is an axiom or a
theorem. Each states what SOURCES.md Part 1 lists under "What may be assumed in Lean" for its
entry. Every reduction, transfer and bridge around these statements (SOURCES.md Part 1 "What must
be PROVED instead", and Part 2) is not part of any hypothesis here.

Auxiliary notions used by the sources but not (or differently) in `Basic.lean` are defined first:
* everywhere-symmetric kernels and graphons (the spaces `𝒲`, `𝒲₀` of Lovász and DGHRR, and
  `F_ℝ^sym` of Lee–Sidorenko), `IsSymmKernel`, `IsSymmGraphon`;
* seminorms and norms on a class of kernels, `IsSeminormOn`, `IsNormOn`;
* the weak-norming functional `W ↦ t(H, |W|)^{1/e(H)}` and the symmetric-convention notions built
  on it;
* step Sidorenko over everywhere-symmetric graphons;
* `[k]`-graphons, `d_{□_k}` and `δ_{□_k}` (Falgas-Ravry–Hancock–Strömberg–Uzzell);
* the step digraphon `W_G` of a finite directed graph on `[n]` (Fox–Himwich–Mani–Zhou);
* the cut-metric topologies used to state the two compactness assertions.

Conventions (SOURCES.md, general conventions): "maps" are measure-preserving maps `[0,1] → [0,1]`
(`MeasurePreserving φ volume volume`), "bijections" are `MPBij`; kernel equality is a.e.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace NieWeiOrientedSidorenko

/-! ## Auxiliary notions -/

/-- A **symmetric kernel** in the sense of Lovász (*Large Networks and Graph Limits*, Ch. 7, p.115:
`𝒲` is "the space of all bounded symmetric measurable functions W : [0,1]² → ℝ"), DGHRR (§2.3,
p.6) and Lee–Sidorenko (`F_ℝ^sym`, §3, p.8: "f(x,y) = f(y,x) for every (x,y)"): a bounded
measurable kernel (`IsKernel`) that is symmetric **everywhere**.

Relation to `Basic.lean`: `IsWeaklyNormingSymm` ranges over the larger class of
kernels that are symmetric only almost everywhere. -/
def IsSymmKernel (U : I → I → ℝ) : Prop :=
  IsKernel U ∧ ∀ x y, U x y = U y x

/-- A **symmetric graphon** in the sense of DGHRR (`𝒲₀`, §2.3, p.6: "the space of all graphons,
that is, symmetric measurable functions from Ω² to [0, 1]", here with `Ω = [0,1]`) and Lovász
(`𝒲₀`): a digraphon (`IsDigraphon`) that is symmetric **everywhere**.

Relation to `Basic.lean`: every `IsSymmGraphon` is an `IsGraphon volume` (which only asks for
a.e. symmetry); the converse holds up to modification on a null set. -/
def IsSymmGraphon (U : I → I → ℝ) : Prop :=
  IsDigraphon U ∧ ∀ x y, U x y = U y x

/-- `N` is a **seminorm** on the class `K` of kernels: absolutely homogeneous and subadditive on
`K` (Lovász §14.1, p.239: "subadditive, but could be 0 even if W is not identically 0;
homogeneity is trivial"). -/
def IsSeminormOn (K : (I → I → ℝ) → Prop) (N : (I → I → ℝ) → ℝ) : Prop :=
  (∀ U, K U → ∀ c : ℝ, N (fun x y => c * U x y) = |c| * N U) ∧
  (∀ U V, K U → K V → N (fun x y => U x y + V x y) ≤ N U + N V)

/-- `N` is a **norm** on the class `K` of kernels, kernels being identified up to null sets
(convention C4): a seminorm on `K` that vanishes only at the a.e.-zero kernel. With `K = IsKernel`
this is exactly `IsKernelNorm` of `Basic.lean`. -/
def IsNormOn (K : (I → I → ℝ) → Prop) (N : (I → I → ℝ) → ℝ) : Prop :=
  IsSeminormOn K N ∧ (∀ U, K U → N U = 0 → AEEq volume U (fun _ _ => 0))

/-- The weak-norming functional `W ↦ t(H, |W|)^{1/e(H)}` of an undirected graph `H` (DGHRR §2.4,
p.12; Lovász §14.1). It is the functional of `Basic.lean`'s `IsWeaklyNormingSymm`. -/
noncomputable def weakNormFn {V : Type*} [Fintype V] (H : SimpleGraph V)
    (U : I → I → ℝ) : ℝ := by
  classical
  exact tU H (fun x y => |U x y|) ^ ((1 : ℝ) / H.edgeFinset.card)

/-- **Weakly norming in the sense of DGHRR** (§2.4, p.12: "We say that a graph H is weakly norming,
if the function ‖W‖_H := t(H,|W|)^{1/e(H)} is a seminorm on 𝒲"): `W ↦ t(H,|W|)^{1/e(H)}` is a
**seminorm** on the everywhere-symmetric bounded measurable kernels.

Relation to `Basic.lean`: `IsWeaklyNormingSymm H` (a norm on a.e.-symmetric kernels)
implies this notion by restriction and by forgetting definiteness; the converse (seminorm ⇒ norm,
Lovász Ex. 14.9, and the passage to a.e.-symmetric kernels) is not assumed anywhere. -/
def IsWeaklySeminormingSymm {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  IsSeminormOn IsSymmKernel (weakNormFn H)

/-- **Weakly norming for symmetric functions in the sense of Lee–Sidorenko** (pp.2–3, p.8:
replacing `f` by `|f|`, the functional `|t_H(|f|)|^{1/e(H)} = t(H,|f|)^{1/e(H)}` "defines a norm",
on the class `F_ℝ^sym` of bounded measurable symmetric functions): `W ↦ t(H,|W|)^{1/e(H)}` is a
**norm** on the everywhere-symmetric bounded measurable kernels (definiteness a.e.).

Relation to `Basic.lean`: `IsWeaklyNormingSymm H` implies this notion by restriction
to everywhere-symmetric kernels. -/
def IsWeaklyNormingSymmFn {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  IsNormOn IsSymmKernel (weakNormFn H)

/-- **Step Sidorenko over symmetric graphons** (DGHRR (3.17), pp.38–39, restricted as permitted by
SOURCES.md A2/A3 to finite partitions of `[0,1]` into measurable parts of positive measure):
`t(H, W^𝒫) ≤ t(H, W)` for every everywhere-symmetric graphon `W` and every `𝒫 : PosPartition`.

Relation to `Basic.lean`: `IsStepSidorenko H` (which ranges over a.e.-symmetric
graphons) implies this notion by restriction. -/
def IsStepSidorenkoSymm {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  ∀ U : I → I → ℝ, IsSymmGraphon U → ∀ P : PosPartition (volume : Measure I),
    tU H (stepAvg P U) ≤ tU H U

/-! ### `[k]`-graphons (Falgas-Ravry–Hancock–Strömberg–Uzzell, §4.1) -/

/-- A **`[k]`-graphon** (FRHSU, J. Graph Theory 104 (2023), pp.124–125: "symmetric measurable
functions W:[0,1]²→𝒫([k])"; arXiv p.17: `W_i(x,y) := W(x,y)(i)`), written by its coordinates
`W i = W_i`: each `W_i` is measurable, nonnegative and symmetric (everywhere), and
`∑_i W_i(x,y) = 1` for every `(x,y)`. (Measurability into the simplex `𝒫([k]) ⊆ ℝ^k` is
measurability of every coordinate.) -/
def IsKGraphon (k : ℕ) (W : Fin k → I → I → ℝ) : Prop :=
  (∀ i, Measurable (Function.uncurry (W i))) ∧ (∀ i x y, 0 ≤ W i x y) ∧
    (∀ x y, ∑ i, W i x y = 1) ∧ (∀ i x y, W i x y = W i y x)

/-- The bundled type `𝒲_k` of `[k]`-graphons. It is a structure (not a subtype of the function
space) so that it carries no topology other than the one given explicitly below. -/
structure KGraphon (k : ℕ) where
  /-- The colour coordinates `W_1, …, W_k`. -/
  toFun : Fin k → I → I → ℝ
  isKGraphon : IsKGraphon k toFun

/-- `d_{□_k}(U, W) := sup_{S,T ⊆ [0,1]} ∑_{i=1}^k |∫_{S×T} (U_i − W_i)|` (FRHSU §4.1, p.18): one
common pair of measurable sets `(S, T)`, the **sum** over colours inside the supremum. -/
noncomputable def kCutNormDist (k : ℕ) (U W : Fin k → I → I → ℝ) : ℝ :=
  sSup {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧
    r = ∑ i, |∫ p in S ×ˢ T, (U i p.1 p.2 - W i p.1 p.2)|}

/-- `δ_{□_k}(U, W) := inf_φ d_{□_k}(U, W^φ)` over measure-preserving **maps** `φ : [0,1] → [0,1]`
(FRHSU §4.1, p.18, "analogously to the definition for graphons": there
`δ_□(U,W) := inf_φ d_□(U,W^φ)` over all measure-preserving transformations), with one map acting on
all `k` colours at once: `(W^φ)_i = (W_i)^φ`. -/
noncomputable def kCutDist (k : ℕ) (U W : Fin k → I → I → ℝ) : ℝ :=
  sInf {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
    r = kCutNormDist k U (fun i => pullback φ (W i))}

/-- The topology on `𝒲_k` generated by the open `δ_{□_k}`-balls `{W | δ_{□_k}(U, W) < r}`. When
`δ_{□_k}` is a pseudometric (which FRHSU leave implicit, "mutatis mutandis") this is its
pseudometric topology; no pseudometric property is assumed here. -/
@[instance_reducible]
def kCutTopology (k : ℕ) : TopologicalSpace (KGraphon k) :=
  TopologicalSpace.generateFrom
    {B | ∃ (U : KGraphon k) (r : ℝ), B = {W | kCutDist k U.toFun W.toFun < r}}

/-! ### Directed graphons and the step digraphon of FHMZ -/

/-- The bundled type of digraphons on `[0,1]` (the graphons of FHMZ, Definition 11: "a measurable
function W : [0,1]² → [0,1]", asymmetric in general). A structure, so that it carries no topology
other than the one given explicitly below. -/
structure Digraphon where
  /-- The underlying function. -/
  toFun : I → I → ℝ
  isDigraphon : IsDigraphon toFun

/-- The topology on digraphons generated by the open balls `{W | δ_□^{map}(U, W) < r}` of the
map-based cut distance `cutDistMap` (FHMZ Definition 12). When `δ_□^{map}` is a pseudometric
(implicit in FHMZ's "cut metric") this is its pseudometric topology; no pseudometric property is
assumed here. -/
@[instance_reducible]
def cutMapTopology : TopologicalSpace Digraphon :=
  TopologicalSpace.generateFrom
    {B | ∃ (U : Digraphon) (r : ℝ), B = {W | cutDistMap U.toFun W.toFun < r}}

/-- The index of the equal-length interval of `[0,1] = I₁ ⊔ ⋯ ⊔ I_n` containing `x` (0-based):
`I_i = [i/n, (i+1)/n)` for `i < n - 1` and `I_{n-1} = [(n-1)/n, 1]`. -/
noncomputable def equipartIdx (n : ℕ) (hn : 0 < n) (x : I) : Fin n :=
  ⟨min (⌊(x : ℝ) * n⌋₊) (n - 1), by omega⟩

/-- The **associated directed graphon** `W_G` of a directed graph `G = ([n], E)` (FHMZ, EJC 32(3)
#P3.38, Definition 11, p.5: "obtained by equipartitioning [0,1] = I₁ ⊔ ⋯ ⊔ I_n into equal length
intervals, and letting W_G(x,y) = 1{(i,j) ∈ E} for x ∈ I_i, y ∈ I_j"), for `G` an oriented graph on
`Fin n` (vertex `i` of `Fin n` is FHMZ's vertex `i + 1`). The endpoints of the intervals are a null
set. For `n = 0` (no vertices, no partition) it is set to `0`.

Relation to `Basic.lean`: `Basic.lean` has no step digraphon of a finite directed graph. -/
noncomputable def stepDigraphonOf {n : ℕ} (G : OrientedGraph (Fin n)) : I → I → ℝ := by
  classical
  exact fun x y =>
    if hn : 0 < n then (if G.Adj (equipartIdx n hn x) (equipartIdx n hn y) then 1 else 0) else 0

/-! ## A1 -/

/-- **A1 — Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
Proposition 5.44(c)** (near-final text, §5.5, p.73; AMS numbering not confirmed).

If `F₁, …, F_k` are pairwise nonisomorphic finite simple graphs without isolated vertices, then
there are finite simple graphs `G₁, …, G_k` such that the `k × k` real matrix `[t(F_i, G_j)]` is
nonsingular (`t` = `simpleHomDensity`).

Modelling choices: the `F_i` are taken with nonempty vertex sets (Lovász's graphs; this only
narrows the hypothesis); the `G_j` are not required to be nonempty (this only widens the
conclusion's witnesses). Vertex types live in an arbitrary universe `u`. -/
def LovaszProp544cHyp.{u} : Prop :=
  ∀ (k : ℕ) (V : Fin k → Type u) [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (F : ∀ i, SimpleGraph (V i)),
    (∀ i j, i ≠ j → IsEmpty (F i ≃g F j)) →
    (∀ i (v : V i), ∃ w, (F i).Adj v w) →
    ∃ (W : Fin k → Type u) (hW : ∀ j, Fintype (W j)) (G : ∀ j, SimpleGraph (W j)),
      (Matrix.of fun i j => @simpleHomDensity (V i) (W j) _ (hW j) (F i) (G j)).det ≠ 0

/-! ## A2 and A3 -/

/-- **A2 — M. Doležal, J. Grebík, J. Hladký, I. Rocha, V. Rozhoň, *Cut distance identifying
graphon parameters over weak\* limits*, J. Combin. Theory Ser. A 189 (2022) 105615
(arXiv:1809.03797), Corollary 3.24** (arXiv v5 numbering; journal numbering not checked).

A finite graph `H` that is weakly norming in the symmetric convention (DGHRR: `W ↦ t(H,|W|)^{1/e(H)}`
is a seminorm on bounded symmetric measurable kernels on `[0,1]²`) satisfies
`t(H, W^𝒫) ≤ t(H, W)` for every symmetric graphon `W` on `[0,1]` and every finite partition `𝒫` of
`[0,1]` into measurable parts of positive measure.

Modelling choices: the premise is DGHRR's seminorm notion (`IsWeaklySeminormingSymm`;
SOURCES.md A2 allows "the seminorm notion as in the source"), on everywhere-symmetric kernels as in
DGHRR's `𝒲`; the conclusion ranges over everywhere-symmetric graphons (DGHRR's `𝒲₀`) and over
`PosPartition`s (the permitted form; DGHRR allow null parts). No connectedness hypothesis. -/
def DGHRRCor324Hyp.{u} : Prop :=
  ∀ (V : Type u) [Fintype V] (H : SimpleGraph V),
    IsWeaklySeminormingSymm H → IsStepSidorenkoSymm H

/-- **A3 — DGHRR (as in A2), Theorem 3.25 together with Theorem 2.14** (Hatami's Theorem 2.8 as
restated by DGHRR; arXiv v5 numbering; journal numbering not checked), **with `e(H) > 0` stated**.

A connected finite graph `H` with at least one edge, such that `t(H, W^𝒫) ≤ t(H, W)` for every
symmetric graphon `W` on `[0,1]` and every finite partition `𝒫` of `[0,1]` into measurable parts of
positive measure, is weakly norming in the symmetric convention: `W ↦ t(H,|W|)^{1/e(H)}` is a
seminorm on bounded symmetric measurable kernels on `[0,1]²`.

Modelling choices: the premise is step Sidorenko in the positive-measure form, stated directly as
SOURCES.md A3 permits (`IsStepSidorenkoSymm`, over everywhere-symmetric graphons as in
DGHRR's `𝒲₀`); the conclusion is DGHRR's seminorm notion (`IsWeaklySeminormingSymm`,
"(semi)norm" in SOURCES.md), on everywhere-symmetric kernels. The norm form and the passage to the
full-kernel convention (through A4) are not part of this hypothesis. -/
def DGHRRThm325Hyp.{u} : Prop :=
  ∀ (V : Type u) [Fintype V] (H : SimpleGraph V), H.Connected → H.edgeSet.Nonempty →
    IsStepSidorenkoSymm H → IsWeaklySeminormingSymm H

/-! ## A4 -/

/-- **A4 — J. Lee and A. Sidorenko, *On graph norms for complex-valued functions*, J. London Math.
Soc. 106(2) (2022) 1501–1538 (arXiv:2101.12145), Theorem 1.3** (weakly norming half; arXiv v2
numbering; journal numbering not checked).

If `H` is a connected finite bipartite graph with `e(H) > 0` and `W ↦ t(H,|W|)^{1/e(H)}` is a norm
on the bounded symmetric measurable kernels on `[0,1]²`, then for a bipartition `X ∪ Y` of `H` the
functional `W ↦ t_bi(H,|W|)^{1/e(H)}` is a norm on all bounded measurable kernels on `[0,1]²`, not
necessarily symmetric (`IsWeaklyNormingGraph H` of `Basic.lean`).

Modelling choices: the premise is a norm on everywhere-symmetric kernels
(`IsWeaklyNormingSymmFn`, Lee–Sidorenko's `F_ℝ^sym`); the conclusion asserts
full-kernel weak norming for **some** bipartition (`IsWeaklyNormingGraph` is existential), so the
independence of the choice of side (SOURCES.md A4, KEY C6) is left to be proved. Lee–Sidorenko's
standing assumptions "nonempty" and "no isolated vertices" follow from connected and `e(H) > 0`.
The real-norming half is not included. -/
def LeeSidorenkoThm13Hyp.{u} : Prop :=
  ∀ (V : Type u) [Fintype V] (H : SimpleGraph V), H.Connected → H.edgeSet.Nonempty →
    (∃ s : V → Prop, IsBipartition H s) →
    IsWeaklyNormingSymmFn H → IsWeaklyNormingGraph H

/-! ## A5 -/

/-- **A5 (first fact) — DGHRR (as in A2), Fact 2.17** (arXiv v5 numbering), quoted there from the
companion paper, Doležal–Grebík–Hladký–Rocha–Rozhoň, *Relating the cut distance and the weak\*
topology for graphons*, J. Combin. Theory Ser. B 147 (2021), Lemma 4.2(b). Provenance: taken as
DGHRR restate it; the companion paper is not in the manuscript's bibliography.

For every symmetric graphon `W` on `[0,1]` and every finite measurable partition `𝒫` of `[0,1]`,
`W^𝒫` lies in the envelope `⟨W⟩` (weak\* limits of versions `W^{π_n}` with `π_n`
measure-preserving bijections; `envelope` of `Basic.lean`).

Modelling choices: `W` ranges over everywhere-symmetric graphons (DGHRR's `𝒲₀`); the partitions are
`PosPartition`s (positive-measure parts), which only narrows the source's "every finite partition"
(null parts allowed), and are the partitions `stepAvg` of `Basic.lean` is defined for. -/
def DGHRRFact217Hyp : Prop :=
  ∀ U : I → I → ℝ, IsSymmGraphon U → ∀ P : PosPartition (volume : Measure I),
    stepAvg P U ∈ envelope U

/-- **A5 (second fact) — DGHRR (as in A2), Fact 2.18** (arXiv v5 numbering), quoted there from the
companion paper (as in `DGHRRFact217Hyp`), Corollary 4.24. Provenance: taken as DGHRR restate it.

For symmetric graphons `U, W` on `[0,1]` with `⟨U⟩ ⊆ ⟨W⟩` (`StructLE U W`): `⟨W⟩ ⊆ ⟨U⟩` if and
only if `δ_□(U, W) = 0`, with `δ_□` the infimum over measure-preserving **bijections** (`cutDist`
of `Basic.lean`).

Modelling choice: `U, W` range over everywhere-symmetric graphons (DGHRR's `𝒲₀`). The conditional
form is stated (it requires `U ⪯ W`); the companion paper's unconditional Corollary 4.24 is not
assumed. -/
def DGHRRFact218Hyp : Prop :=
  ∀ U W : I → I → ℝ, IsSymmGraphon U → IsSymmGraphon W → StructLE U W →
    (StructLE W U ↔ cutDist U W = 0)

/-! ## A9 -/

/-- **A9 — Lovász, *Large Networks and Graph Limits* (as in A1), Proposition 14.2(a)** (near-final
text, p.241; AMS numbering not confirmed): "Even cycles are norming".

For every `q ≥ 2`, `W ↦ |t(C_{2q}, W)|^{1/(2q)}` is a norm on the bounded symmetric measurable
kernels on `[0,1]²` (Lovász's `𝒲`).

Modelling choices: the absolute value of Lovász's definition (§14.1, p.239) is kept, as the NOTE in
SOURCES.md A9 allows; `C_{2q}` is Mathlib's `SimpleGraph.cycleGraph (2 * q)`; the norm is on
everywhere-symmetric kernels with definiteness a.e. (`IsNormOn IsSymmKernel`). The transfer to
weak norming and to the full-kernel convention (through A4) is not part of this hypothesis. -/
def LovaszProp142aHyp : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    IsNormOn IsSymmKernel
      (fun U => |tU (SimpleGraph.cycleGraph (2 * q)) U| ^ ((1 : ℝ) / (2 * q)))

/-! ## FRHSU Theorem 4.3 -/

/-- **FRHSU — V. Falgas-Ravry, R. Hancock, J. Strömberg, A. Uzzell, *Rectilinear approximation and
volume estimates for hereditary bodies via [0,1]-decorated containers*, J. Graph Theory 104(1)
(2023) 104–132, Theorem 4.3, p.125** (arXiv:2107.00550v2, Theorem 4.3, p.19): "The space
`(𝒲̃_k, δ_{□_k})` is compact."

For every `k ≥ 1`, the quotient of the `[k]`-graphons by `δ_{□_k} = 0` (`δ_{□_k}` the infimum over
measure-preserving **maps**, one map acting on all colours, of the sum-over-colours `d_{□_k}`),
with the topology of `δ_{□_k}`, is compact.

Modelling choices: the most literal form (SOURCES.md), compactness of the quotient, is stated:
`Quot` by the relation `δ_{□_k}(U, W) = 0` (Lean's `Quot` takes its equivalence closure), with the
quotient topology of `kCutTopology` (generated by `δ_{□_k}`-balls). That `δ_{□_k}` is a
pseudometric, and any sequential form, are not assumed; they are to be proved from this form or
raised as an open point. The source's form, every `k ≥ 1`, is stated; the run uses `k = 4`. -/
def FRHSUThm43Hyp : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    letI : TopologicalSpace (KGraphon k) := kCutTopology k
    CompactSpace (Quot fun U W : KGraphon k => kCutDist k U.toFun W.toFun = 0)

/-! ## FHMZ -/

/-- **FHMZ Theorem 13 (oriented part) — J. Fox, Z. Himwich, N. Mani, Y. Zhou, *A note on directed
analogues of the Sidorenko and forcing conjectures*, Electron. J. Combin. 32(3) (2025) #P3.38,
Theorem 13, p.6** (arXiv:2210.16971v1, Theorem 2.7).

If `W : [0,1]² → [0,1]` is measurable and `W(x,y) + W(y,x) ≤ 1` for **all** `x, y`, then there are
finite oriented graphs `G_n` (on `[N_n]`) with `δ_□^{map}(W, W_{G_n}) → 0`, where `δ_□^{map}` is
`cutDistMap` (FHMZ Definition 12, measure-preserving maps) and `W_{G_n}` is `stepDigraphonOf`.

Modelling choices: the bipartite part of Theorem 13 is not included (SOURCES.md: not needed); the
vertex counts `N_n` may be `0` (where `W_G = 0`), which only widens the conclusion's witnesses. -/
def FHMZThm13Hyp : Prop :=
  ∀ U : I → I → ℝ, IsDigraphon U → (∀ x y, U x y + U y x ≤ 1) →
    ∃ (N : ℕ → ℕ) (G : ∀ n, OrientedGraph (Fin (N n))),
      Tendsto (fun n => cutDistMap U (stepDigraphonOf (G n))) atTop (𝓝 0)

/-- **FHMZ Theorem 18 (oriented part) — FHMZ (as in `FHMZThm13Hyp`), Theorem 18, p.8**
(arXiv:2210.16971v1, Theorem 2.12).

For digraphons `U, W` on `[0,1]` and every finite oriented graph `B`,
`|t(B, W) − t(B, U)| ≤ e(B) · δ_□^{map}(U, W)`, with `δ_□^{map}` = `cutDistMap` (FHMZ Definition 12,
measure-preserving maps).

Modelling choice: the bipartite part of Theorem 18 is not included (SOURCES.md: optional). -/
def FHMZThm18Hyp.{u} : Prop :=
  ∀ (V : Type u) [Fintype V] (B : OrientedGraph V) (U W : I → I → ℝ),
    IsDigraphon U → IsDigraphon W →
      |t B W - t B U| ≤ (B.numArcs : ℝ) * cutDistMap U W

/-- **FHMZ p.6 assertion — FHMZ (as in `FHMZThm13Hyp`), unnumbered, printed p.6 (top)** (arXiv v1,
p.4): "The space of graphons is compact under the cut metric, given by identifying graphons with
cut distance zero". **Asserted without proof or citation in the source.**

The quotient of the space of (asymmetric) digraphons on `[0,1]` by `δ_□^{map} = 0`, with the
topology of `δ_□^{map}` (`cutDistMap`, FHMZ Definition 12), is compact.

Modelling choices: as for `FRHSUThm43Hyp`, `Quot` by `δ_□^{map}(U, W) = 0` with the quotient
topology of `cutMapTopology` (generated by `δ_□^{map}`-balls). That `δ_□^{map}` is a pseudometric,
and any sequential form, are not assumed. FHMZ's p.7 identification of a.e.-equal graphons is not
used. -/
def FHMZCompactHyp : Prop :=
  letI : TopologicalSpace Digraphon := cutMapTopology
  CompactSpace (Quot fun U W : Digraphon => cutDistMap U.toFun W.toFun = 0)

end NieWeiOrientedSidorenko
