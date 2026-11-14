import NieWeiOrientedSidorenko.Section1Aux
import NieWeiOrientedSidorenko.S1Bridges
import NieWeiOrientedSidorenko.S1CutDist
import NieWeiOrientedSidorenko.S1Families
import NieWeiOrientedSidorenko.S1P112
import NieWeiOrientedSidorenko.S1Dt

/-!
# Section 1: the main results

Each result of Section 1 about OS, OAS or symmetry-forcing is stated twice: with the finite and
sequence definitions of the Introduction (Definitions 1 and 2), the paper's statement, and, with
suffix `_kernel`, with the digraphon definitions of Section 2. The two are bridged by
`isOS_iff_isOSK`, `isOAS_iff_isOASK` and `isSymmetryForcing_iff_isSymmetryForcingK` (the two
Question 1(c) equivalences of the authors' answer key).

Also: Conjecture 1 as a stated, unproved `Prop` (not a result), and the answer key's additions
B1 (the connected symmetric-convention form of Theorem 1.4) and B4 (i), (ii).
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

/-! ## Conjecture 1 (stated, not a result) -/

/-- `e_G(A, B)` for a finite simple graph: the number of ordered pairs `(x, y) ∈ A × B` with
`xy` an edge. -/
noncomputable def simpleEdgesBetween {W : Type*} [Fintype W] (G : SimpleGraph W)
    (A B : Finset W) : ℕ := by
  classical exact ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card

/-- **Conjecture 1 (Sidorenko and forcing conjectures)**, recorded as a proposition; it is neither
assumed nor proved. For a bipartite graph `H`: `t(H, G) ≥ t(K₂, G)^{e(H)}` for every graph `G`;
and if `H` contains a cycle, then for every `p ∈ (0, 1)` every sequence `G_n` with
`|V(G_n)| → ∞`, `t(K₂, G_n) = p + o(1)` and `t(H, G_n) = p^{e(H)} + o(1)` is quasi-random:
`e_{G_n}(A, B) = p|A||B| + o(|V(G_n)|²)` uniformly over `A, B`.
The hypotheses of the forcing half can all hold: `KConj1.conj1_forcing_antecedent` gives H = C₄,
p = 1/2 and the inner-product graphs on F₂^k, and `KConj1.ipSeq_quasirandom` shows that sequence
is quasi-random. -/
def SidorenkoForcingConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (H : SimpleGraph V), H.Colorable 2 →
    letI := Classical.decRel H.Adj
    (∀ (W : Type) [Fintype W] [Nonempty W] (G : SimpleGraph W),
      simpleHomDensity (⊤ : SimpleGraph (Fin 2)) G ^ H.edgeFinset.card ≤ simpleHomDensity H G) ∧
    (¬ H.IsAcyclic → ∀ p ∈ Ioo (0 : ℝ) 1, ∀ (N : ℕ → ℕ) (G : ∀ n, SimpleGraph (Fin (N n))),
      Tendsto N atTop atTop →
      Tendsto (fun n => simpleHomDensity (⊤ : SimpleGraph (Fin 2)) (G n)) atTop (𝓝 p) →
      Tendsto (fun n => simpleHomDensity H (G n)) atTop (𝓝 (p ^ H.edgeFinset.card)) →
      ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ A B : Finset (Fin (N n)),
        |(simpleEdgesBetween (G n) A B : ℝ) - p * A.card * B.card| ≤ ε * (N n : ℝ) ^ 2)


namespace OrientedGraph

variable {V : Type u} [Fintype V]

/-! ## Question 1(c): finite/sequence definitions ⇔ digraphon definitions -/

/-- **Question 1(c), finite-host bridge (OS).** `D` is OS for all finite hosts (Definition 1) if
and only if it is OS for all digraphons (Section 2). -/
theorem isOS_iff_isOSK (D : OrientedGraph V) : D.IsOS ↔ D.IsOSK :=
  S1Bridges.isOS_iff_isOSK_proof D

/-- **Question 1(c), finite-host bridge (OAS).** `D` is OAS for all finite hosts (Definition 1) if
and only if it is OAS for all digraphons (Section 2). -/
theorem isOAS_iff_isOASK (D : OrientedGraph V) : D.IsOAS ↔ D.IsOASK :=
  S1Bridges.isOAS_iff_isOASK_proof D

/-- **Question 1(c), sequence bridge (symmetry-forcing).** `D` is symmetry-forcing for sequences
of finite hosts (Definition 2) if and only if it is symmetry-forcing for digraphons
(Section 2). -/
theorem isSymmetryForcing_iff_isSymmetryForcingK (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u})
    (hcpt : FHMZCompactHyp) (D : OrientedGraph V) :
    D.IsSymmetryForcing ↔ D.IsSymmetryForcingK :=
  S1Bridges.isSymmetryForcing_iff_isSymmetryForcingK_proof h13 h18 hcpt D

/-! ## Theorem 1.1 -/

/-- **Theorem 1.1 (Griffiths).** `O₁` is OAS and symmetry-forcing, while `O₂` is OS and
symmetry-forcing.
The hypothesis h13 (FHMZ Theorem 13) is not used by the proof: only the digraphon-to-sequence
half of the symmetry-forcing bridge is needed (`S1Bridges.sfk_to_sf`, which takes h18 and hcpt);
it is kept because the statement was approved with it. -/
theorem thm_1_1 (hA1 : LovaszProp544cHyp.{0}) (hA4 : LeeSidorenkoThm13Hyp.{0})
    (hA9 : LovaszProp142aHyp) (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0})
    (hcpt : FHMZCompactHyp) :
    (O₁.IsOAS ∧ O₁.IsSymmetryForcing) ∧ (O₂.IsOS ∧ O₂.IsSymmetryForcing) :=
  S1Families.thm_1_1_proof hA1 hA4 hA9 h13 h18 hcpt

/-- **Theorem 1.1**, digraphon form. -/
theorem thm_1_1_kernel (hA1 : LovaszProp544cHyp.{0}) (hA4 : LeeSidorenkoThm13Hyp.{0})
    (hA9 : LovaszProp142aHyp) :
    (O₁.IsOASK ∧ O₁.IsSymmetryForcingK) ∧ (O₂.IsOSK ∧ O₂.IsSymmetryForcingK) :=
  S1Families.thm_1_1_kernel_proof hA1 hA4 hA9

/-! ## Theorems 1.2 and 1.3 (the goal results) -/

/-- **Theorem 1.2.** Let `D` be a connected directed graph with at least one arc. Then `D` is OS
if and only if (a) `D` is a one-direction orientation, (b) `D ≅ D^T`, and (c) the underlying graph
`\bar D` is weakly norming. -/
theorem thm_1_2 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (he : 1 ≤ D.numArcs) :
    D.IsOS ↔ D.IsOneDirection ∧ D.IsSelfConverse ∧ IsWeaklyNormingGraph D.underlying := by
  exact (isOS_iff_isOSK D).trans (Section1Aux.osk_char hA1 D hconn he)

/-- **Theorem 1.2**, digraphon form. -/
theorem thm_1_2_kernel (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (he : 1 ≤ D.numArcs) :
    D.IsOSK ↔ D.IsOneDirection ∧ D.IsSelfConverse ∧ IsWeaklyNormingGraph D.underlying := by
  exact Section1Aux.osk_char hA1 D hconn he

/-- **Theorem 1.3.** A connected OS directed graph is symmetry-forcing if and only if its
underlying graph contains a cycle. -/
theorem thm_1_3 (hA1 : LovaszProp544cHyp.{u}) (h13 : FHMZThm13Hyp)
    (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp) (D : OrientedGraph V)
    (hconn : D.IsConnected) (hD : D.IsOS) :
    D.IsSymmetryForcing ↔ ¬ D.underlying.IsAcyclic := by
  exact (isSymmetryForcing_iff_isSymmetryForcingK h13 h18 hcpt D).trans
    (Section1Aux.thm13k hA1 D hconn ((isOS_iff_isOSK D).mp hD))

/-- **Theorem 1.3**, digraphon form. -/
theorem thm_1_3_kernel (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (hD : D.IsOSK) :
    D.IsSymmetryForcingK ↔ ¬ D.underlying.IsAcyclic := by
  exact Section1Aux.thm13k hA1 D hconn hD

end OrientedGraph

/-! ## Theorems 1.4 and 1.6, Corollary 1.5 (undirected) -/

section Undirected

variable {V : Type u} [Fintype V]

/-- **Theorem 1.4.** Let `H` be a weakly norming graph containing a cycle. Then `t(H, ·)` is a cut
distance identifying graphon parameter, and hence `H` is step forcing.
The hypothesis hF217 (DGHRR Fact 2.17) is not used by the proof; it is kept because the
statement was approved with it. -/
theorem thm_1_4 (hA2 : DGHRRCor324Hyp.{u}) (hF217 : DGHRRFact217Hyp) (hF218 : DGHRRFact218Hyp)
    (hFR : FRHSUThm43Hyp)
    (H : SimpleGraph V) (hH : IsWeaklyNormingGraph H) (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H :=
  S1CutDist.thm_1_4_proof hA2 hF218 hFR H hH hcyc

/-- **Theorem 1.4, reading "for every bipartition".** The paper's "weakly norming graph" does not
fix a bipartition; `thm_1_4` reads it as "weakly norming for some bipartition" (the stronger
theorem). This is the other reading: if `H` is bipartite, weakly norming for every one of its
bipartitions, and contains a cycle, then `t(H, ·)` is cut distance identifying and `H` is step
forcing. It follows from `thm_1_4`; the two readings differ only for disconnected `H`.
The hypothesis hF217 (DGHRR Fact 2.17) is not used by the proof; it is kept because the
statement was approved with it. -/
theorem thm_1_4_every_bipartition (hA2 : DGHRRCor324Hyp.{u}) (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) (H : SimpleGraph V)
    (hbip : ∃ s : V → Prop, IsBipartition H s)
    (hH : ∀ s : V → Prop, IsBipartition H s →
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges H s))
    (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H := by
  obtain ⟨s, hs⟩ := hbip
  exact thm_1_4 hA2 hF217 hF218 hFR H ⟨s, hs, hH s hs⟩ hcyc

/-- **Theorem 1.4, connected symmetric-convention form** (answer key B1). Let `H` be a connected
bipartite graph with at least one edge that is weakly norming in the symmetric convention and
contains a cycle. Then `t(H, ·)` is cut distance identifying and `H` is step forcing.
The hypothesis hF217 (DGHRR Fact 2.17) is not used by the proof; it is kept because the
statement was approved with it. -/
theorem thm_1_4_symm (hA2 : DGHRRCor324Hyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) (hbip : ∃ s : V → Prop, IsBipartition H s)
    (he : 0 < H.edgeFinset.card) (hH : IsWeaklyNormingSymm H) (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H := by
  have hne : H.edgeSet.Nonempty := by
    obtain ⟨e, he'⟩ := Finset.card_pos.mp he
    exact ⟨e, (SimpleGraph.mem_edgeFinset).mp he'⟩
  have hfn : IsWeaklyNormingSymmFn H := by
    obtain ⟨h1, h2, h3⟩ := hH
    refine ⟨⟨fun U hU c => ?_, fun U W hU hW => ?_⟩, fun U hU h0 => ?_⟩
    · exact h1 U ⟨hU.1, Filter.Eventually.of_forall fun p => hU.2 p.1 p.2⟩ c
    · exact h2 U W ⟨hU.1, Filter.Eventually.of_forall fun p => hU.2 p.1 p.2⟩
        ⟨hW.1, Filter.Eventually.of_forall fun p => hW.2 p.1 p.2⟩
    · exact h3 U ⟨hU.1, Filter.Eventually.of_forall fun p => hU.2 p.1 p.2⟩ h0
  exact thm_1_4 hA2 hF217 hF218 hFR H (hA4 V H hconn hne hbip hfn) hcyc

/-- **Corollary 1.5.** A connected graph is step forcing if and only if it is step Sidorenko and
contains a cycle.
The hypothesis hF217 (DGHRR Fact 2.17) is not used by the proof; it is kept because the
statement was approved with it. -/
theorem cor_1_5 (hA2 : DGHRRCor324Hyp.{u}) (hA3 : DGHRRThm325Hyp.{u})
    (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hF217 : DGHRRFact217Hyp) (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp)
    (H : SimpleGraph V) (hconn : H.Connected) :
    IsStepForcing H ↔ IsStepSidorenko H ∧ ¬ H.IsAcyclic := by
  constructor
  · intro h
    exact ⟨Section1Aux.stepSid_of_stepForcing h, Section1Aux.not_acyclic_of_stepForcing h⟩
  · rintro ⟨h, hcyc⟩
    exact (thm_1_4 hA2 hF217 hF218 hFR H (Section1Aux.wnGraph_of_stepSid hA3 hA4 hconn
      (Section1Aux.edgeSet_nonempty_of_cycle hcyc) h) hcyc).2

end Undirected

/-- **Theorem 1.6.** Let `H = (X ∪ Y, E)` be a bipartite graph with a fixed bipartition and at
least one edge. Then `H` is weakly norming and contains a cycle if and only if `t_bi(H, ·)` is
strictly convex on nonnegative kernels. -/
theorem thm_1_6 {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y)) (hE : 0 < E.card) :
    IsWeaklyNorming E ∧ ¬ (bipGraph E).IsAcyclic ↔ StrictConvexOnNonnegKernels E := by
  exact ⟨fun h => Section1Aux.thm16_forward E hE h.1 h.2, Section1Aux.thm16_backward E hE⟩

/-! ## Answer key B4 -/

/-- **B4(i).** `K_{2,3}` is weakly norming (for its bipartition into the parts of sizes 2 and 3)
and step forcing, but not norming (for any bipartition): a negative answer to Problem 3.29 of
Doležal–Grebík–Hladký–Rocha–Rozhoň.
The hypotheses hF217, hF218 and hFR are not used by the proof (only A2 is); they are kept
because the statement was approved with them. -/
theorem k23_weaklyNorming_stepForcing_not_norming (hA2 : DGHRRCor324Hyp.{0})
    (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) :
    IsWeaklyNorming (Finset.univ : Finset (Fin 2 × Fin 3)) ∧
    IsStepForcing (completeBipartiteGraph (Fin 2) (Fin 3)) ∧
    ¬ IsNormingGraph (completeBipartiteGraph (Fin 2) (Fin 3)) :=
  S1CutDist.k23_weaklyNorming_stepForcing_not_norming_proof hA2

/-- **B4(i), "not norming" in the symmetric convention.**
`k23_weaklyNorming_stepForcing_not_norming` reads "`K_{2,3}` is not norming" in the paper's full-kernel convention. This is the other
reading, the convention of Doležal–Grebík–Hladký–Rocha–Rozhoň's Problem 3.29: the functional
`W ↦ |t(K_{2,3}, W)|^{1/6}` is not a norm on the (everywhere) symmetric bounded measurable
kernels. The paper's odd-degree argument (tex l.612–614) uses the symmetric test kernel
`f(x) f(y)`, so it proves this reading. -/
theorem k23_not_norming_symm :
    ¬ IsNormOn IsSymmKernel
      (fun U => |tU (completeBipartiteGraph (Fin 2) (Fin 3)) U| ^ ((1 : ℝ) / 6)) := by
  exact Section1Aux.k23_not_norming_symm'

namespace OrientedGraph

variable {V : Type u} [Fintype V]

/-- **B4(ii).** For a connected one-direction orientation `D ≅ D^T` with at least one arc,
`D` is OS if and only if its underlying graph `\bar D` is step Sidorenko. -/
theorem isOS_iff_isStepSidorenko (hA1 : LovaszProp544cHyp.{u}) (hA2 : DGHRRCor324Hyp.{u})
    (hA3 : DGHRRThm325Hyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected)
    (hone : D.IsOneDirection) (hsc : D.IsSelfConverse) (he : 1 ≤ D.numArcs) :
    D.IsOS ↔ IsStepSidorenko D.underlying := by
  exact (isOS_iff_isOSK D).trans (Section1Aux.osk_iff_stepSid hA1 hA2 hA3 hA4 D hconn hone hsc he)

/-! ## Theorem 1.7, Proposition 1.8 -/

/-- **Theorem 1.7.** For every `t ≥ 2`, `D_t` is OAS and symmetry-forcing.
The hypothesis h13 (FHMZ Theorem 13) is not used by the proof: only the digraphon-to-sequence
half of the symmetry-forcing bridge is needed (`S1Bridges.sfk_to_sf`, which takes h18 and hcpt);
it is kept because the statement was approved with it. -/
theorem thm_1_7 (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0}) (hcpt : FHMZCompactHyp)
    (t : ℕ) (ht : 2 ≤ t) :
    (Dt t).IsOAS ∧ (Dt t).IsSymmetryForcing :=
  S1Dt.thm_1_7_proof h13 h18 hcpt t ht

/-- **Theorem 1.7**, digraphon form. -/
theorem thm_1_7_kernel (t : ℕ) (ht : 2 ≤ t) : (Dt t).IsOASK ∧ (Dt t).IsSymmetryForcingK :=
  S1Dt.thm_1_7_kernel_proof t ht

/-- **Proposition 1.8.** There is an OAS directed graph whose underlying graph contains a
triangle. -/
theorem prop_1_8 : ∃ (n : ℕ) (D : OrientedGraph (Fin n)), D.IsOAS ∧
    ∃ a b c : Fin n, D.underlying.Adj a b ∧ D.underlying.Adj b c ∧ D.underlying.Adj a c :=
  S1Dt.prop_1_8_proof

/-- **Proposition 1.8**, digraphon form. -/
theorem prop_1_8_kernel : ∃ (n : ℕ) (D : OrientedGraph (Fin n)), D.IsOASK ∧
    ∃ a b c : Fin n, D.underlying.Adj a b ∧ D.underlying.Adj b c ∧ D.underlying.Adj a c :=
  S1Dt.prop_1_8_kernel_proof

/-! ## Theorems 1.9–1.11: stars, paths, cycles -/

/-- **Theorem 1.9.** Let `D` be an oriented star with center `c`. (1) If `D` has one edge, then
`D` is both OS and OAS. (2) If `D` has at least two edges, then `D` is not OS, and `D` is OAS if
and only if its center has equal in-degree and out-degree. -/
theorem thm_1_9 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (c : V) (hstar : D.IsOrientedStar c) :
    (D.numArcs = 1 → D.IsOS ∧ D.IsOAS) ∧
    (2 ≤ D.numArcs → ¬ D.IsOS ∧ (D.IsOAS ↔ D.inDeg c = D.outDeg c)) := by
  obtain ⟨k1, k2⟩ := Section1Aux.star_kernel hA1 D c hstar
  exact ⟨fun h => ⟨(isOS_iff_isOSK D).mpr (k1 h).1, (isOAS_iff_isOASK D).mpr (k1 h).2⟩,
    fun h => ⟨fun hD => (k2 h).1 ((isOS_iff_isOSK D).mp hD), (isOAS_iff_isOASK D).trans (k2 h).2⟩⟩

/-- **Theorem 1.9**, digraphon form. -/
theorem thm_1_9_kernel (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (c : V) (hstar : D.IsOrientedStar c) :
    (D.numArcs = 1 → D.IsOSK ∧ D.IsOASK) ∧
    (2 ≤ D.numArcs → ¬ D.IsOSK ∧ (D.IsOASK ↔ D.inDeg c = D.outDeg c)) := by
  exact Section1Aux.star_kernel hA1 D c hstar

/-- **Theorem 1.10.** Let `P` be an oriented path. (1) If `P` has one edge, then `P` is both OS
and OAS. (2) If `P` has at least two edges, then `P` is not OS, and `P` is OAS if and only if it
is (isomorphic to) the directed two-edge path `1 → 2 → 3`. -/
theorem thm_1_10 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V) (hpath : D.IsOrientedPath) :
    (D.numArcs = 1 → D.IsOS ∧ D.IsOAS) ∧
    (2 ≤ D.numArcs → ¬ D.IsOS ∧ (D.IsOAS ↔ Nonempty (D.Iso dirPath3))) :=
  S1Families.thm_1_10_proof hA1 D hpath

/-- **Theorem 1.10**, digraphon form. -/
theorem thm_1_10_kernel (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hpath : D.IsOrientedPath) :
    (D.numArcs = 1 → D.IsOSK ∧ D.IsOASK) ∧
    (2 ≤ D.numArcs → ¬ D.IsOSK ∧ (D.IsOASK ↔ Nonempty (D.Iso dirPath3))) :=
  S1Families.thm_1_10_kernel_proof hA1 D hpath

/-- **Theorem 1.11.** An oriented cycle is OS if and only if it is an alternating orientation of
an even cycle, and it is OAS if and only if it is isomorphic to `O₁`. -/
theorem thm_1_11 (hA1 : LovaszProp544cHyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hA9 : LovaszProp142aHyp) (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) :
    (D.IsOS ↔ Even (Fintype.card V) ∧ D.IsAlternating) ∧ (D.IsOAS ↔ Nonempty (D.Iso O₁)) :=
  S1Families.thm_1_11_proof hA1 hA4 hA9 D hcyc

/-- **Theorem 1.11**, digraphon form. -/
theorem thm_1_11_kernel (hA1 : LovaszProp544cHyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hA9 : LovaszProp142aHyp) (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) :
    (D.IsOSK ↔ Even (Fintype.card V) ∧ D.IsAlternating) ∧ (D.IsOASK ↔ Nonempty (D.Iso O₁)) :=
  S1Families.thm_1_11_kernel_proof hA1 hA4 hA9 D hcyc

/-! ## Proposition 1.12 -/

/-- **Proposition 1.12.** If a directed graph `D` is symmetry-forcing, then `D` is OS or OAS.
The hypothesis hcpt (the FHMZ p.6 compactness assertion) is not used by the proof: only the
sequence-to-digraphon half of the symmetry-forcing bridge is needed (`S1Bridges.sf_to_sfk`,
which takes h13 and h18); it is kept because the statement was approved with it. -/
theorem prop_1_12 (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp)
    (D : OrientedGraph V) (hD : D.IsSymmetryForcing) : D.IsOS ∨ D.IsOAS :=
  S1P112.prop_1_12_proof h13 h18 hcpt D hD

/-- **Proposition 1.12**, digraphon form. -/
theorem prop_1_12_kernel (D : OrientedGraph V) (hD : D.IsSymmetryForcingK) :
    D.IsOSK ∨ D.IsOASK :=
  S1P112.prop_1_12_kernel_proof D hD

end OrientedGraph

end NieWeiOrientedSidorenko
