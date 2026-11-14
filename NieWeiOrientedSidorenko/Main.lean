import NieWeiOrientedSidorenko.Common
import NieWeiOrientedSidorenko.Examples

/-!
# Index

J. Nie and F. Wei, *Sidorenko inequalities and symmetry-forcing for graph orientations*
(unpublished manuscript, 11 November 2026). All names are in the namespace
`NieWeiOrientedSidorenko`. Results of Section 1 about OS, OAS or symmetry-forcing are stated with
the finite and sequence definitions of the Introduction and, with suffix `_kernel`, with the
digraphon definitions of Section 2; the two Question 1(c) rows bridge them.

| result | Lean |
|---|---|
| Definition (directed graph, tex l.130, tex l.400–401) | `OrientedGraph`, `OrientedGraph.arcs`, `OrientedGraph.numArcs`, `OrientedGraph.underlying`, `OrientedGraph.transpose`, `OrientedGraph.Iso`, `OrientedGraph.IsConnected` |
| Definition (homomorphism density of finite graphs, tex l.408–410) | `OrientedGraph.homCount`, `OrientedGraph.homDensity`, `simpleHomCount`, `simpleHomDensity` |
| Definition (symmetrized finite density, tex l.130) | `OrientedGraph.symmDensity` |
| Definition (quasi-random in its orientations, tex l.132) | `OrientedGraph.arcsFromTo`, `OrientedGraph.IsOrientQuasirandom` |
| Definition 1 | `OrientedGraph.IsOS`, `OrientedGraph.IsOAS` |
| Definition 2 | `OrientedGraph.IsSymmetryForcing` |
| Definition (orientations O₁ and O₂ of C₄, tex l.134) | `OrientedGraph.ofArcs`, `OrientedGraph.O₁`, `OrientedGraph.O₂` |
| Definition (kernel, digraphon, graphon, transpose, symmetrization, tex l.415) | `IsKernel`, `IsDigraphon`, `IsGraphon`, `AEEq`, `kTranspose`, `symmetrize` |
| Definition (homomorphism density in a kernel, tex l.417–421) | `tDir`, `tUndir`, `t`, `tU` |
| Definition (bipartite homomorphism density, tex l.429–432) | `tBi`, `tb`, `bipGraph` |
| Definition (norming, weakly norming, tex l.434–437) | `rNorm`, `hNorm`, `IsKernelNorm`, `IsWeaklyNorming`, `IsNorming`, `sideEdges`, `IsBipartition`, `IsWeaklyNormingGraph`, `IsNormingGraph` |
| Definition (symmetric convention, tex l.442–444) | `IsWeaklyNormingSymm`, `IsSymmKernel`, `IsSeminormOn`, `IsNormOn` |
| Definition (step average, step Sidorenko, step forcing, tex l.476–487) | `PosPartition`, `stepAvg`, `IsStepSidorenko`, `IsStepForcing` |
| Definition (envelope, cut distance compatible and identifying, cut norm, cut distance, tex l.489–493) | `MPBij`, `pullback`, `WeakStarTendsto`, `envelope`, `StructLE`, `StructLT`, `CutDistCompatible`, `CutDistIdentifying`, `cutNorm`, `cutDist` |
| Definition (map-based cut distance of Fox–Himwich–Mani–Zhou, tex l.380) | `cutDistMap` |
| Definition (OS, OAS and symmetry-forcing in digraphon language, tex l.497) | `OrientedGraph.IsOSK`, `OrientedGraph.IsOASK`, `OrientedGraph.IsSymmetryForcingK` |
| Definition (finite step digraphon, doubled host, paired partition, tex l.505) | `StepDigraphon`, `StepDigraphon.toFun`, `halfCount`, `twoCopies`, `doubled`, `pairedPartition` |
| Definition (decorated homomorphism density, tex l.543–547) | `tBiDec` |
| Definition (convexity on kernels, tex l.312, tex l.578–580) | `ConvexOnNonnegKernels`, `StrictConvexOnNonnegKernels`, `StrictConvexOnKernels` |
| Definition (one-direction orientation, self-converse, tex l.218–223) | `OrientedGraph.IsOneDirection`, `OrientedGraph.IsSelfConverse` |
| Definition (homomorphic to a directed edge, tex l.694) | `OrientedGraph.dirEdge`, `OrientedGraph.HomToDirEdge` |
| Definition (oriented stars, paths and cycles, tex l.352–375) | `OrientedGraph.IsOrientedStar`, `OrientedGraph.inDeg`, `OrientedGraph.outDeg`, `OrientedGraph.IsOrientedPath`, `OrientedGraph.dirPath3`, `OrientedGraph.IsOrientedCycle`, `OrientedGraph.IsAlternating` |
| Definition 3 | `OrientedGraph.Dt` |
| Definition (girth cycles and orientation imbalance, tex l.1360–1365) | `OrientedGraph.walkImbalance`, `OrientedGraph.cyclesOfLength`, `OrientedGraph.cosImbalance` |
| Conjecture 1 | `SidorenkoForcingConjecture` (stated as a definition only; not a result, neither assumed nor proved), `simpleEdgesBetween` |
| Question 1(c) (finite-host OS bridge) | `OrientedGraph.isOS_iff_isOSK` |
| Question 1(c) (finite-host OAS bridge) | `OrientedGraph.isOAS_iff_isOASK` |
| Question 1(c) (sequence symmetry-forcing bridge) | `OrientedGraph.isSymmetryForcing_iff_isSymmetryForcingK` |
| Theorem 1.1 | `OrientedGraph.thm_1_1`, `OrientedGraph.thm_1_1_kernel` |
| Theorem 1.2 | `OrientedGraph.thm_1_2`, `OrientedGraph.thm_1_2_kernel` |
| Theorem 1.3 | `OrientedGraph.thm_1_3`, `OrientedGraph.thm_1_3_kernel` |
| Theorem 1.4 | `thm_1_4` |
| Theorem 1.4 (reading: weakly norming for every bipartition) | `thm_1_4_every_bipartition` |
| Theorem 1.4 (answer key B1, connected symmetric-convention form) | `thm_1_4_symm` |
| Corollary 1.5 | `cor_1_5` |
| Theorem 1.6 | `thm_1_6` |
| Theorem 1.7 | `OrientedGraph.thm_1_7`, `OrientedGraph.thm_1_7_kernel` |
| Proposition 1.8 | `OrientedGraph.prop_1_8`, `OrientedGraph.prop_1_8_kernel` |
| Theorem 1.9 | `OrientedGraph.thm_1_9`, `OrientedGraph.thm_1_9_kernel` |
| Theorem 1.10 | `OrientedGraph.thm_1_10`, `OrientedGraph.thm_1_10_kernel` |
| Theorem 1.11 | `OrientedGraph.thm_1_11`, `OrientedGraph.thm_1_11_kernel` |
| Proposition 1.12 | `OrientedGraph.prop_1_12`, `OrientedGraph.prop_1_12_kernel` |
| Theorem B4(i) (answer key: K₂,₃ weakly norming, step forcing, not norming) | `k23_weaklyNorming_stepForcing_not_norming` |
| Theorem B4(i) (reading: K₂,₃ not norming in the symmetric convention) | `k23_not_norming_symm` |
| Theorem B4(ii) (answer key: OS iff the underlying graph is step Sidorenko) | `OrientedGraph.isOS_iff_isStepSidorenko` |
| Claim 2.1 | `claim_2_1` |
| Lemma 2.2 | `lemma_2_2` |
| Lemma 2.3 | `lemma_2_3_1`, `lemma_2_3_2` |
| Theorem 4.1 | `OrientedGraph.thm_4_1` |
| Lemma 4.2 | `OrientedGraph.lemma_4_2` |
| Lemma 4.3 | `OrientedGraph.lemma_4_3` |
| Lemma 4.4 | `OrientedGraph.lemma_4_4` |
| Lemma 4.5 | `OrientedGraph.lemma_4_5` |
| Lemma 4.6 | `lemma_4_6` |
| Lemma 6.1 | `OrientedGraph.lemma_6_1` |
| Lemma 6.1 (finite hosts, final-delivery answers §2) | `OrientedGraph.lemma_6_1_finite` |
| Theorem 4.1 (finite hosts, final-delivery answers §2) | `OrientedGraph.thm_4_1_finite` |
-/

namespace NieWeiOrientedSidorenko

end NieWeiOrientedSidorenko
