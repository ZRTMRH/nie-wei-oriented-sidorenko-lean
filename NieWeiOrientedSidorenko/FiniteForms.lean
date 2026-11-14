import NieWeiOrientedSidorenko.Section1

/-!
# Finite-host forms of Lemma 6.1 and Theorem 4.1

The paper defines OS and OAS for finite hosts (Definition 1, tex l.140) and gives the
equivalent digraphon formulation (tex l.144-146, l.497). Lemma 6.1 (`OrientedGraph.lemma_6_1`)
and Theorem 4.1 (`OrientedGraph.thm_4_1`) are stated in the digraphon form. The author asked
(final-delivery answers, §2) that both host classes be represented explicitly: these are the
finite-host instances of the same results. They are not new mathematical claims. They are
derived from the proved finite–kernel equivalences of Question 1(c)
(`OrientedGraph.isOAS_iff_isOASK`, `OrientedGraph.isOS_iff_isOSK`) and take no published
assumption. The printed restriction `0 ≤ θ < 2π` and conditions (a)–(c) are kept, and no
connectedness hypothesis is added.
-/

namespace NieWeiOrientedSidorenko

open Set

namespace OrientedGraph

variable {V : Type*} [Fintype V]

/-- **Lemma 6.1, finite hosts.** Let `D` be a directed graph whose underlying graph contains a
cycle, and let `g` be the girth of `\bar D`. If `D` is OAS for finite hosts (Definition 1), then
`∑_{C ∈ 𝒞_g(D)} cos(ω_D(C) θ) ≤ |𝒞_g(D)| cos^g(θ)` for every `θ ∈ [0, 2π)` (tex l.1368-1377).
The same statement as `lemma_6_1`, whose hypothesis is OAS for digraphons; the two hypotheses are
equivalent by `isOAS_iff_isOASK`. The range restriction `hθ` is the paper's. -/
theorem lemma_6_1_finite (D : OrientedGraph V) (hcyc : ¬ D.underlying.IsAcyclic) (hD : D.IsOAS)
    (θ : ℝ) (hθ : θ ∈ Ico 0 (2 * Real.pi)) :
    ∑ C ∈ D.cyclesOfLength D.underlying.girth, D.cosImbalance θ C ≤
      (D.cyclesOfLength D.underlying.girth).card * Real.cos θ ^ D.underlying.girth :=
  lemma_6_1 D hcyc ((isOAS_iff_isOASK D).mp hD) θ hθ

/-- **Theorem 4.1, finite hosts.** Let `D` be a directed graph such that (a) `D` is homomorphic to
a directed edge; (b) `D ≅ D^T`; (c) `\bar D` is weakly norming with respect to a bipartition under
which all arcs of `D` go from the first part to the second (tex l.694-697). Then `D` is oriented
Sidorenko for finite hosts (Definition 1): `t(D, G) ≥ 2^{-e(D)} t(\bar D, \bar G)` for every finite
nonempty oriented host `G`. The same statement as `thm_4_1`, whose conclusion is OS for digraphons;
the two conclusions are equivalent by `isOS_iff_isOSK`. Hypothesis (a) is the paper's; it follows
from (c). -/
theorem thm_4_1_finite (D : OrientedGraph V) (ha : D.HomToDirEdge) (hb : D.IsSelfConverse)
    (hc : ∃ s : V → Prop, (∀ u v, D.Adj u v → s u ∧ ¬ s v) ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges D.underlying s)) :
    D.IsOS :=
  (isOS_iff_isOSK D).mpr (thm_4_1 D ha hb hc)

end OrientedGraph

end NieWeiOrientedSidorenko
