import NieWeiOrientedSidorenko

/-!
# Certificate: the main theorems, as checked by Lean

Each `example` below restates one main result of J. Nie and F. Wei, *Sidorenko inequalities and
symmetry-forcing for graph orientations* (unpublished manuscript, version of 11 November 2026),
with its full Lean statement, and has Lean confirm that the library proves exactly that statement.
The definitions these statements use are listed in `CERTIFICATE.md`, each next to the manuscript's
wording. Every proof in the library is checked by Lean's kernel.

Arguments named `hA1`, `hA2`, …, `h13`, `h18`, `hcpt`, `hF217`, `hF218`, `hFR` whose types end in
`Hyp` are published results the authors authorised as assumptions
(`NieWeiOrientedSidorenko/Literature.lean`). They are hypotheses of the statements, not axioms:
each statement holds whenever the cited results hold as worded there.

Check with:  `lake build && lake env lean Certificate.lean`
The `#print axioms` lines must show only `propext`, `Classical.choice`, `Quot.sound`
(Lean's standard axioms): no `sorry`, no additional axiom.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

/-! ## Undirected results: Theorems 1.4 and 1.6, Corollary 1.5, B4(i) -/

/-- **Theorem 1.4.** A weakly norming graph `H` containing a cycle: `t(H, ·)` is cut distance
identifying, and `H` is step forcing. Assumes DGHRR Cor. 3.24, Facts 2.17 (unused) and 2.18, and
FRHSU Thm 4.3. -/
example {V : Type u} [Fintype V] (hA2 : DGHRRCor324Hyp.{u}) (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp)
    (H : SimpleGraph V) (hH : IsWeaklyNormingGraph H) (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H :=
  thm_1_4 hA2 hF217 hF218 hFR H hH hcyc

/-- **Theorem 1.4, "for every bipartition" reading** (derived from `thm_1_4`). -/
example {V : Type u} [Fintype V] (hA2 : DGHRRCor324Hyp.{u}) (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) (H : SimpleGraph V)
    (hbip : ∃ s : V → Prop, IsBipartition H s)
    (hH : ∀ s : V → Prop, IsBipartition H s →
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges H s))
    (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H :=
  thm_1_4_every_bipartition hA2 hF217 hF218 hFR H hbip hH hcyc

/-- **Theorem 1.4, connected symmetric-convention form** (answer key B1). Also assumes
Lee–Sidorenko Thm 1.3. -/
example {V : Type u} [Fintype V] (hA2 : DGHRRCor324Hyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) (hbip : ∃ s : V → Prop, IsBipartition H s)
    (he : 0 < H.edgeFinset.card) (hH : IsWeaklyNormingSymm H) (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H :=
  thm_1_4_symm hA2 hA4 hF217 hF218 hFR H hconn hbip he hH hcyc

/-- **Corollary 1.5.** A connected graph is step forcing if and only if it is step Sidorenko and
contains a cycle. Assumes DGHRR Cor. 3.24, Thm 3.25, Facts 2.17 (forwarded only) and 2.18,
Lee–Sidorenko Thm 1.3 and FRHSU Thm 4.3. -/
example {V : Type u} [Fintype V] (hA2 : DGHRRCor324Hyp.{u}) (hA3 : DGHRRThm325Hyp.{u})
    (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hF217 : DGHRRFact217Hyp) (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp)
    (H : SimpleGraph V) (hconn : H.Connected) :
    IsStepForcing H ↔ IsStepSidorenko H ∧ ¬ H.IsAcyclic :=
  cor_1_5 hA2 hA3 hA4 hF217 hF218 hFR H hconn

/-- **Theorem 1.6.** A bipartite graph with a fixed bipartition and at least one edge is weakly
norming and contains a cycle if and only if `t_bi(H, ·)` is strictly convex on nonnegative kernels.
No assumed result. -/
example {X Y : Type u} [Fintype X] [Fintype Y] (E : Finset (X × Y)) (hE : 0 < E.card) :
    IsWeaklyNorming E ∧ ¬ (bipGraph E).IsAcyclic ↔ StrictConvexOnNonnegKernels E :=
  thm_1_6 E hE

/-- **B4(i).** `K_{2,3}` is weakly norming and step forcing, but not norming. Assumes DGHRR
Cor. 3.24 (the other three hypotheses are unused). -/
example (hA2 : DGHRRCor324Hyp.{0})
    (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) :
    IsWeaklyNorming (Finset.univ : Finset (Fin 2 × Fin 3)) ∧
    IsStepForcing (completeBipartiteGraph (Fin 2) (Fin 3)) ∧
    ¬ IsNormingGraph (completeBipartiteGraph (Fin 2) (Fin 3)) :=
  k23_weaklyNorming_stepForcing_not_norming hA2 hF217 hF218 hFR

/-- **B4(i), "not norming" in the symmetric convention.** No assumed result. -/
example :
    ¬ IsNormOn IsSymmKernel
      (fun U => |tU (completeBipartiteGraph (Fin 2) (Fin 3)) U| ^ ((1 : ℝ) / 6)) :=
  k23_not_norming_symm

namespace OrientedGraph

/-! ## Question 1(c): finite and sequence definitions ⇔ digraphon definitions -/

/-- **Question 1(c), OS bridge.** No assumed result. -/
example {V : Type u} [Fintype V] (D : OrientedGraph V) : D.IsOS ↔ D.IsOSK :=
  isOS_iff_isOSK D

/-- **Question 1(c), OAS bridge.** No assumed result. -/
example {V : Type u} [Fintype V] (D : OrientedGraph V) : D.IsOAS ↔ D.IsOASK :=
  isOAS_iff_isOASK D

/-- **Question 1(c), symmetry-forcing bridge.** Assumes FHMZ Thms 13, 18 and the p. 6
compactness assertion. -/
example {V : Type u} [Fintype V] (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u})
    (hcpt : FHMZCompactHyp) (D : OrientedGraph V) :
    D.IsSymmetryForcing ↔ D.IsSymmetryForcingK :=
  isSymmetryForcing_iff_isSymmetryForcingK h13 h18 hcpt D

/-! ## Theorems 1.1–1.3, B4(ii) -/

/-- **Theorem 1.1 (Griffiths).** `O₁` is OAS and symmetry-forcing; `O₂` is OS and
symmetry-forcing. Assumes Lovász 5.44(c), 14.2(a), Lee–Sidorenko Thm 1.3 and FHMZ (Thm 13 not
needed). -/
example (hA1 : LovaszProp544cHyp.{0}) (hA4 : LeeSidorenkoThm13Hyp.{0})
    (hA9 : LovaszProp142aHyp) (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0})
    (hcpt : FHMZCompactHyp) :
    (O₁.IsOAS ∧ O₁.IsSymmetryForcing) ∧ (O₂.IsOS ∧ O₂.IsSymmetryForcing) :=
  thm_1_1 hA1 hA4 hA9 h13 h18 hcpt

/-- **Theorem 1.2.** A connected directed graph `D` with at least one arc is OS if and only if
(a) it is a one-direction orientation, (b) `D ≅ Dᵀ`, (c) its underlying graph is weakly norming.
Assumes Lovász 5.44(c). -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (he : 1 ≤ D.numArcs) :
    D.IsOS ↔ D.IsOneDirection ∧ D.IsSelfConverse ∧ IsWeaklyNormingGraph D.underlying :=
  thm_1_2 hA1 D hconn he

/-- **Theorem 1.2**, digraphon form. Assumes Lovász 5.44(c). -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (he : 1 ≤ D.numArcs) :
    D.IsOSK ↔ D.IsOneDirection ∧ D.IsSelfConverse ∧ IsWeaklyNormingGraph D.underlying :=
  thm_1_2_kernel hA1 D hconn he

/-- **Theorem 1.3.** A connected OS directed graph is symmetry-forcing if and only if its
underlying graph contains a cycle. Assumes Lovász 5.44(c) and the three FHMZ items. -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (h13 : FHMZThm13Hyp)
    (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp) (D : OrientedGraph V)
    (hconn : D.IsConnected) (hD : D.IsOS) :
    D.IsSymmetryForcing ↔ ¬ D.underlying.IsAcyclic :=
  thm_1_3 hA1 h13 h18 hcpt D hconn hD

/-- **Theorem 1.3**, digraphon form. Assumes Lovász 5.44(c). -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (hD : D.IsOSK) :
    D.IsSymmetryForcingK ↔ ¬ D.underlying.IsAcyclic :=
  thm_1_3_kernel hA1 D hconn hD

/-- **B4(ii).** A connected one-direction orientation `D ≅ Dᵀ` with at least one arc is OS if and
only if its underlying graph is step Sidorenko. Assumes Lovász 5.44(c), DGHRR Cor. 3.24 and
Thm 3.25, and Lee–Sidorenko Thm 1.3. -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (hA2 : DGHRRCor324Hyp.{u})
    (hA3 : DGHRRThm325Hyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected)
    (hone : D.IsOneDirection) (hsc : D.IsSelfConverse) (he : 1 ≤ D.numArcs) :
    D.IsOS ↔ IsStepSidorenko D.underlying :=
  isOS_iff_isStepSidorenko hA1 hA2 hA3 hA4 D hconn hone hsc he

/-! ## Theorem 1.7, Propositions 1.8 and 1.12 -/

/-- **Theorem 1.7.** For every `t ≥ 2`, `D_t` is OAS and symmetry-forcing. Assumes the three FHMZ
items (Thm 13 not needed). -/
example (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0}) (hcpt : FHMZCompactHyp)
    (t : ℕ) (ht : 2 ≤ t) :
    (Dt t).IsOAS ∧ (Dt t).IsSymmetryForcing :=
  thm_1_7 h13 h18 hcpt t ht

/-- **Proposition 1.8.** There is an OAS directed graph whose underlying graph contains a
triangle. No assumed result. -/
example : ∃ (n : ℕ) (D : OrientedGraph (Fin n)), D.IsOAS ∧
    ∃ a b c : Fin n, D.underlying.Adj a b ∧ D.underlying.Adj b c ∧ D.underlying.Adj a c :=
  prop_1_8

/-- **Proposition 1.12.** A symmetry-forcing directed graph is OS or OAS. Assumes FHMZ Thms 13 and
18 (the p. 6 assertion not needed). -/
example {V : Type u} [Fintype V] (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u})
    (hcpt : FHMZCompactHyp)
    (D : OrientedGraph V) (hD : D.IsSymmetryForcing) : D.IsOS ∨ D.IsOAS :=
  prop_1_12 h13 h18 hcpt D hD

/-! ## Theorems 1.9–1.11: stars, paths, cycles -/

/-- **Theorem 1.9** (oriented stars). Assumes Lovász 5.44(c). -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (c : V) (hstar : D.IsOrientedStar c) :
    (D.numArcs = 1 → D.IsOS ∧ D.IsOAS) ∧
    (2 ≤ D.numArcs → ¬ D.IsOS ∧ (D.IsOAS ↔ D.inDeg c = D.outDeg c)) :=
  thm_1_9 hA1 D c hstar

/-- **Theorem 1.10** (oriented paths). Assumes Lovász 5.44(c). -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hpath : D.IsOrientedPath) :
    (D.numArcs = 1 → D.IsOS ∧ D.IsOAS) ∧
    (2 ≤ D.numArcs → ¬ D.IsOS ∧ (D.IsOAS ↔ Nonempty (D.Iso dirPath3))) :=
  thm_1_10 hA1 D hpath

/-- **Theorem 1.11** (oriented cycles). Assumes Lovász 5.44(c), 14.2(a) and Lee–Sidorenko
Thm 1.3. -/
example {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hA9 : LovaszProp142aHyp) (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) :
    (D.IsOS ↔ Even (Fintype.card V) ∧ D.IsAlternating) ∧ (D.IsOAS ↔ Nonempty (D.Iso O₁)) :=
  thm_1_11 hA1 hA4 hA9 D hcyc

/-! ## Theorem 4.1 and Lemma 6.1, digraphon and finite-host forms -/

/-- **Theorem 4.1** (digraphon form). (a) `D` is homomorphic to a directed edge; (b) `D ≅ Dᵀ`;
(c) `\bar D` is weakly norming for a bipartition under which every arc goes from the first part to
the second. Then `D` is OS. No assumed result. -/
example {V : Type u} [Fintype V] (D : OrientedGraph V) (ha : D.HomToDirEdge)
    (hb : D.IsSelfConverse)
    (hc : ∃ s : V → Prop, (∀ u v, D.Adj u v → s u ∧ ¬ s v) ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges D.underlying s)) :
    D.IsOSK :=
  thm_4_1 D ha hb hc

/-- **Theorem 4.1, finite hosts.** The same, with the conclusion OS for finite hosts
(Definition 1). No assumed result. -/
example {V : Type u} [Fintype V] (D : OrientedGraph V) (ha : D.HomToDirEdge)
    (hb : D.IsSelfConverse)
    (hc : ∃ s : V → Prop, (∀ u v, D.Adj u v → s u ∧ ¬ s v) ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges D.underlying s)) :
    D.IsOS :=
  thm_4_1_finite D ha hb hc

/-- **Lemma 6.1** (digraphon form). If `\bar D` contains a cycle, `g` is its girth and `D` is OAS,
then `∑_{C ∈ 𝒞_g(D)} cos(ω_D(C) θ) ≤ |𝒞_g(D)| cos^g θ` for `θ ∈ [0, 2π)`. No assumed result. -/
example {V : Type u} [Fintype V] (D : OrientedGraph V) (hcyc : ¬ D.underlying.IsAcyclic)
    (hD : D.IsOASK) (θ : ℝ) (hθ : θ ∈ Ico 0 (2 * Real.pi)) :
    ∑ C ∈ D.cyclesOfLength D.underlying.girth, D.cosImbalance θ C ≤
      (D.cyclesOfLength D.underlying.girth).card * Real.cos θ ^ D.underlying.girth :=
  lemma_6_1 D hcyc hD θ hθ

/-- **Lemma 6.1, finite hosts.** The same, with the hypothesis OAS for finite hosts
(Definition 1). No assumed result. -/
example {V : Type u} [Fintype V] (D : OrientedGraph V) (hcyc : ¬ D.underlying.IsAcyclic)
    (hD : D.IsOAS) (θ : ℝ) (hθ : θ ∈ Ico 0 (2 * Real.pi)) :
    ∑ C ∈ D.cyclesOfLength D.underlying.girth, D.cosImbalance θ C ≤
      (D.cyclesOfLength D.underlying.girth).card * Real.cos θ ^ D.underlying.girth :=
  lemma_6_1_finite D hcyc hD θ hθ

end OrientedGraph

end NieWeiOrientedSidorenko

#print axioms NieWeiOrientedSidorenko.thm_1_4
#print axioms NieWeiOrientedSidorenko.thm_1_4_every_bipartition
#print axioms NieWeiOrientedSidorenko.thm_1_4_symm
#print axioms NieWeiOrientedSidorenko.cor_1_5
#print axioms NieWeiOrientedSidorenko.thm_1_6
#print axioms NieWeiOrientedSidorenko.k23_weaklyNorming_stepForcing_not_norming
#print axioms NieWeiOrientedSidorenko.k23_not_norming_symm
#print axioms NieWeiOrientedSidorenko.OrientedGraph.isOS_iff_isOSK
#print axioms NieWeiOrientedSidorenko.OrientedGraph.isOAS_iff_isOASK
#print axioms NieWeiOrientedSidorenko.OrientedGraph.isSymmetryForcing_iff_isSymmetryForcingK
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_1
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_2
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_2_kernel
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_3
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_3_kernel
#print axioms NieWeiOrientedSidorenko.OrientedGraph.isOS_iff_isStepSidorenko
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_7
#print axioms NieWeiOrientedSidorenko.OrientedGraph.prop_1_8
#print axioms NieWeiOrientedSidorenko.OrientedGraph.prop_1_12
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_9
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_10
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_1_11
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_4_1
#print axioms NieWeiOrientedSidorenko.OrientedGraph.thm_4_1_finite
#print axioms NieWeiOrientedSidorenko.OrientedGraph.lemma_6_1
#print axioms NieWeiOrientedSidorenko.OrientedGraph.lemma_6_1_finite
