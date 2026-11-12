import NieWeiOrientedSidorenko.Section1

/-!
# Examples

Tests of the definitions against the paper's examples and against degenerate cases, and named
witnesses for the statements of the formalization.
-/

open MeasureTheory Set
open scoped unitInterval

namespace NieWeiOrientedSidorenko
namespace OrientedGraph

example : O₁.numArcs = 4 := by
  simp only [numArcs, arcs, O₁, ofArcs]
  convert (by decide : (Finset.univ.filter fun p : Fin 4 × Fin 4 =>
    (p.1, p.2) ∈ ({(1, 0), (1, 2), (2, 3), (3, 0)} : Finset (Fin 4 × Fin 4))).card = 4)
  ext; simp

example : O₂.numArcs = 4 := by
  simp only [numArcs, arcs, O₂, ofArcs]
  convert (by decide : (Finset.univ.filter fun p : Fin 4 × Fin 4 =>
    (p.1, p.2) ∈ ({(1, 0), (1, 2), (3, 2), (3, 0)} : Finset (Fin 4 × Fin 4))).card = 4)
  ext; simp

example : dirEdge.homCount dirEdge = 1 := by
  simp only [homCount, dirEdge, ofArcs]
  convert (by decide : (Finset.univ.filter fun f : Fin 2 → Fin 2 =>
    ∀ u v, (u, v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)) →
      (f u, f v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2))).card = 1)
  ext; simp

example : simpleHomCount dirEdge.underlying dirEdge.underlying = 2 := by
  simp only [simpleHomCount, underlying, dirEdge, ofArcs, SimpleGraph.fromRel_adj]
  convert (by decide : (Finset.univ.filter fun f : Fin 2 → Fin 2 =>
    ∀ u v : Fin 2, u ≠ v ∧ ((u, v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)) ∨
      (v, u) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2))) →
      f u ≠ f v ∧ ((f u, f v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)) ∨
        (f v, f u) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)))).card = 2)

/-- One arc: `t(D, G) = 1/4` and the baseline `2^{-1} t(K₂, K₂) = 1/4` agree. -/
example : dirEdge.homDensity dirEdge = 1 / 4 ∧ dirEdge.symmDensity dirEdge = 1 / 4 := by
  have h1 : dirEdge.homCount dirEdge = 1 := by
    simp only [homCount, dirEdge, ofArcs]
    convert (by decide : (Finset.univ.filter fun f : Fin 2 → Fin 2 =>
      ∀ u v, (u, v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)) →
        (f u, f v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2))).card = 1)
    ext; simp
  have h2 : simpleHomCount dirEdge.underlying dirEdge.underlying = 2 := by
    simp only [simpleHomCount, underlying, dirEdge, ofArcs, SimpleGraph.fromRel_adj]
    convert (by decide : (Finset.univ.filter fun f : Fin 2 → Fin 2 =>
      ∀ u v : Fin 2, u ≠ v ∧ ((u, v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)) ∨
        (v, u) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2))) →
        f u ≠ f v ∧ ((f u, f v) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)) ∨
          (f v, f u) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)))).card = 2)
  have h3 : dirEdge.numArcs = 1 := by
    simp only [numArcs, arcs, dirEdge, ofArcs]
    convert (by decide : (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      (p.1, p.2) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2))).card = 1)
    ext; simp
  refine ⟨?_, ?_⟩
  · simp only [homDensity, h1]; norm_num
  · simp only [symmDensity, simpleHomDensity, h2, h3]; norm_num

example : dirEdge.IsOneDirection := ⟨{0}, by
  intro u v h
  simp [dirEdge, ofArcs] at h
  simp [h]⟩

example : ¬ dirPath3.IsOneDirection := by
  rintro ⟨A, hA⟩
  have h1 := hA 0 1 (by simp [dirPath3, ofArcs])
  have h2 := hA 1 2 (by simp [dirPath3, ofArcs])
  exact h1.2 h2.1

example : (Dt 2).Adj (Sum.inl 0) (Sum.inr fun _ => true) ∧
    (Dt 2).Adj (Sum.inr fun _ => false) (Sum.inl 1) ∧
    ¬ (Dt 2).Adj (Sum.inl 0) (Sum.inl 1) := by
  simp [Dt]

/-- A directed graph with no arcs is trivially OS in the digraphon sense: both densities are `1`. -/
example : (⟨fun _ _ => False, fun _ h => h, fun _ _ h => h.elim⟩ : OrientedGraph (Fin 1)).IsOSK := by
  intro U _
  classical
  simp [tDir, arcs]

end OrientedGraph

/-- The empty bipartite graph is not weakly norming: its functional is constantly `1`, which is
not homogeneous. -/
example : ¬ IsWeaklyNorming (∅ : Finset (Unit × Unit)) := by
  rintro ⟨hhom, -, -⟩
  have h := hhom (fun _ _ => 0) ⟨measurable_const, 0, fun _ _ => by simp⟩ 0
  simp [rNorm, tBi] at h



end NieWeiOrientedSidorenko
