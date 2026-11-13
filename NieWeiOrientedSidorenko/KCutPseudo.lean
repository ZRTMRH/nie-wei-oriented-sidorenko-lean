import NieWeiOrientedSidorenko.Mixing

/-!
# Cut-distance pseudometrics and the compactness hypotheses (Checkpoint B, Q3)

Auxiliary lemmas (no new results of the paper) identifying the formal compactness hypotheses
`FRHSUThm43Hyp` and `FHMZCompactHyp` of `Literature.lean` with the published statements:

1. pullback contraction of the cut norm and of `d_{□_k}` under measure-preserving maps
   (`cutNorm_pullback_le`, `kCutNormDist_pullback_le`);
2. the pseudometric facts other than symmetry for `δ_□^{map}` (`cutDistMap`) and `δ_{□_k}`
   (`kCutDist`): nonnegativity, `δ(U,U) = 0`, the triangle inequality, boundedness;
3. generic topology: the one-sided-ball topology of a pseudometric is the pseudometric topology
   (`ballTopology_eq`), `Quot (d = 0)` is homeomorphic to `SeparationQuotient`
   (`quotHomeomorph`), and the compactness equivalences;
4. conditional on symmetry, `fhmzCompactHyp_iff_of_symm` and `frhsu_iff_of_symm`.

Symmetry of the distances is not proved here; it enters only as the explicit hypothesis `hsymm`.
No literature hypothesis is used.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace KCutPseudo

open S1CutDist

/-- One-sided extremal step: for a bounded measurable `G` and finite measures `μ ≤ λ`, `ν`, there
is a measurable `S` with `∫ G d(μ × ν) ≤ ∫ G d(λ|_S × ν)` (take `S = {u | ∫ G(u, ·) dν > 0}`). -/
lemma one_side (G : I × I → ℝ) (hG : Measurable G) {M : ℝ} (hM : ∀ p, |G p| ≤ M)
    (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≤ volume) :
    ∃ S : Set I, MeasurableSet S ∧
      ∫ p, G p ∂(μ.prod ν) ≤ ∫ p, G p ∂(((volume : Measure I).restrict S).prod ν) := by
  set h : I → ℝ := fun u => ∫ v, G (u, v) ∂ν with hh
  have hhm : Measurable h := (hG.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hhb : ∀ u, |h u| ≤ M * ν.real univ := fun u => by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun v => G (u, v)) (C := M)
      (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hM _)
    rw [Real.norm_eq_abs] at this
    simpa [mul_comm] using this
  set S := {u | 0 < h u} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hhm
  refine ⟨S, hSm, ?_⟩
  have hGi : ∀ (ρ : Measure I) [IsFiniteMeasure ρ], Integrable G (ρ.prod ν) := fun ρ _ =>
    integrable_bdd hG M hM
  rw [integral_prod G (hGi μ), integral_prod G (hGi _)]
  change ∫ u, h u ∂μ ≤ ∫ u, h u ∂((volume : Measure I).restrict S)
  have hind : Integrable (S.indicator h) (volume : Measure I) :=
    (integrable_bdd hhm _ hhb).indicator hSm
  calc ∫ u, h u ∂μ ≤ ∫ u, S.indicator h u ∂μ := by
        refine integral_mono (integrable_bdd hhm _ hhb) (integrable_bdd (hhm.indicator hSm) (M * ν.real univ)
          fun u => ?_) fun u => ?_
        · by_cases hu : u ∈ S
          · rw [indicator_of_mem hu]; exact hhb u
          · rw [indicator_of_notMem hu, abs_zero]; exact (abs_nonneg _).trans (hhb u)
        · by_cases hu : u ∈ S
          · rw [indicator_of_mem hu]
          · rw [indicator_of_notMem hu]; exact not_lt.mp hu
    _ ≤ ∫ u, S.indicator h u ∂(volume : Measure I) := by
        refine integral_mono_measure hμ (Eventually.of_forall fun u => ?_) hind
        by_cases hu : u ∈ S
        · rw [indicator_of_mem hu]; exact (le_of_lt hu)
        · rw [indicator_of_notMem hu]; rfl
    _ = ∫ u in S, h u := integral_indicator hSm

/-- The bilinear form over two sub-probability measures dominated by Lebesgue measure is at most
the integral over some rectangle. -/
lemma integral_le_rect (G : I × I → ℝ) (hG : Measurable G) {M : ℝ} (hM : ∀ p, |G p| ≤ M)
    (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≤ volume)
    (hν : ν ≤ volume) :
    ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧
      ∫ p, G p ∂(μ.prod ν) ≤ ∫ p in S ×ˢ T, G p := by
  obtain ⟨S, hS, h1⟩ := one_side G hG hM μ ν hμ
  obtain ⟨T, hT, h2⟩ := one_side (fun p => G p.swap) (hG.comp measurable_swap)
    (fun p => hM _) ν ((volume : Measure I).restrict S) hν
  refine ⟨S, T, hS, hT, h1.trans ?_⟩
  rw [integral_prod_swap G, integral_prod_swap G] at h2
  refine h2.trans (le_of_eq ?_)
  rw [Measure.prod_restrict]
  rfl


/-- The pushforward of `λ|_S` under a measure-preserving map is dominated by `λ`. -/
lemma map_restrict_le {φ : I → I} (hφ : MeasurePreserving φ volume volume) (S : Set I) :
    ((volume : Measure I).restrict S).map φ ≤ volume := by
  calc ((volume : Measure I).restrict S).map φ ≤ (volume : Measure I).map φ :=
        Measure.map_mono Measure.restrict_le_self hφ.measurable
    _ = volume := hφ.map_eq

/-- `∫_{S×T} G(φx, φy) = ∫ G d(φ_*(λ|_S) × φ_*(λ|_T))`. -/
lemma setIntegral_comp_eq (G : I × I → ℝ) (hG : Measurable G) {φ : I → I}
    (hφ : MeasurePreserving φ volume volume) (S T : Set I) :
    ∫ p in S ×ˢ T, G (φ p.1, φ p.2) =
      ∫ p, G p ∂((((volume : Measure I).restrict S).map φ).prod
        (((volume : Measure I).restrict T).map φ)) := by
  rw [Measure.map_prod_map _ _ hφ.measurable hφ.measurable,
    integral_map (hφ.measurable.prodMap hφ.measurable).aemeasurable hG.aestronglyMeasurable,
    Measure.prod_restrict]
  rfl

/-- One-sided pullback bound: the integral of `G ∘ (φ × φ)` over a rectangle is at most the
integral of `G` over some rectangle. -/
lemma setIntegral_comp_le (G : I × I → ℝ) (hG : Measurable G) {M : ℝ} (hM : ∀ p, |G p| ≤ M)
    {φ : I → I} (hφ : MeasurePreserving φ volume volume) (S T : Set I) :
    ∃ S' T' : Set I, MeasurableSet S' ∧ MeasurableSet T' ∧
      ∫ p in S ×ˢ T, G (φ p.1, φ p.2) ≤ ∫ p in S' ×ˢ T', G p := by
  rw [setIntegral_comp_eq G hG hφ S T]
  exact integral_le_rect G hG hM _ _ (map_restrict_le hφ S) (map_restrict_le hφ T)

/-- `‖−F‖_□ = ‖F‖_□`. -/
lemma cutNorm_neg (F : I → I → ℝ) : cutNorm (fun x y => -F x y) = cutNorm F := by
  unfold cutNorm
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, integral_neg, abs_neg]

/-- **Pullback contraction of the cut norm.** For a bounded measurable `F` and a
measure-preserving map `φ`, `‖F^φ‖_□ ≤ ‖F‖_□`. -/
theorem cutNorm_pullback_le {F : I → I → ℝ} (hF : Measurable (Function.uncurry F)) {M : ℝ}
    (hM : ∀ x y, |F x y| ≤ M) {φ : I → I} (hφ : MeasurePreserving φ volume volume) :
    cutNorm (fun x y => F (φ x) (φ y)) ≤ cutNorm F := by
  refine cutNorm_le fun S T hS hT => abs_le.mpr ⟨?_, ?_⟩
  · obtain ⟨S', T', hS', hT', h⟩ := setIntegral_comp_le (fun p => -F p.1 p.2) hF.neg
      (fun p => by rw [abs_neg]; exact hM _ _) hφ S T
    rw [integral_neg, integral_neg] at h
    have := le_cutNorm hM hS' hT'
    linarith [neg_abs_le (∫ p in S' ×ˢ T', F p.1 p.2)]
  · obtain ⟨S', T', hS', hT', h⟩ := setIntegral_comp_le (fun p => F p.1 p.2) hF
      (fun p => hM _ _) hφ S T
    have := le_cutNorm hM hS' hT'
    linarith [le_abs_self (∫ p in S' ×ˢ T', F p.1 p.2)]


/-- The set whose supremum is `d_{□_k}`. -/
def kSet (k : ℕ) (U W : Fin k → I → I → ℝ) : Set ℝ :=
  {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧
    r = ∑ i, |∫ p in S ×ˢ T, (U i p.1 p.2 - W i p.1 p.2)|}

/-- `d_{□_k}` is the supremum of `kSet`. -/
lemma kCutNormDist_eq (k : ℕ) (U W : Fin k → I → I → ℝ) :
    kCutNormDist k U W = sSup (kSet k U W) := rfl

/-- `kSet` is nonempty. -/
lemma kSet_nonempty (k : ℕ) (U W : Fin k → I → I → ℝ) : (kSet k U W).Nonempty :=
  ⟨_, ∅, ∅, MeasurableSet.empty, MeasurableSet.empty, rfl⟩

/-- `kSet` is bounded above for colour families bounded by `M`. -/
lemma kSet_bdd {k : ℕ} {U W : Fin k → I → I → ℝ} {M : ℝ} (hU : ∀ i x y, |U i x y| ≤ M)
    (hW : ∀ i x y, |W i x y| ≤ M) : BddAbove (kSet k U W) := by
  refine ⟨∑ _i : Fin k, 2 * M, ?_⟩
  rintro _ ⟨S, T, -, -, rfl⟩
  refine Finset.sum_le_sum fun i _ =>
    abs_setIntegral_le (F := fun x y => U i x y - W i x y) (M := 2 * M) (fun x y => ?_) _
  calc |U i x y - W i x y| ≤ |U i x y| + |W i x y| := abs_sub _ _
    _ ≤ 2 * M := by linarith [hU i x y, hW i x y]

/-- Each rectangle sum is at most `d_{□_k}`, for bounded colours. -/
lemma le_kCutNormDist {k : ℕ} {U W : Fin k → I → I → ℝ} {M : ℝ} (hU : ∀ i x y, |U i x y| ≤ M)
    (hW : ∀ i x y, |W i x y| ≤ M) {S T : Set I} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∑ i, |∫ p in S ×ˢ T, (U i p.1 p.2 - W i p.1 p.2)| ≤ kCutNormDist k U W :=
  le_csSup (kSet_bdd hU hW) ⟨S, T, hS, hT, rfl⟩

/-- `d_{□_k}(U, W) ≤ c` when every rectangle sum is at most `c`. -/
lemma kCutNormDist_le {k : ℕ} {U W : Fin k → I → I → ℝ} {c : ℝ}
    (h : ∀ S T : Set I, MeasurableSet S → MeasurableSet T →
      ∑ i, |∫ p in S ×ˢ T, (U i p.1 p.2 - W i p.1 p.2)| ≤ c) :
    kCutNormDist k U W ≤ c :=
  csSup_le (kSet_nonempty k U W) (by rintro r ⟨S, T, hS, hT, rfl⟩; exact h S T hS hT)

/-- `d_{□_k} ≥ 0`, for every `k`. -/
theorem kCutNormDist_nonneg' (k : ℕ) (U W : Fin k → I → I → ℝ) : 0 ≤ kCutNormDist k U W :=
  Real.sSup_nonneg fun _ ⟨_, _, _, _, hr⟩ => hr ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The sign `±1` of a real number (`+1` at `0`). -/
noncomputable def sgn (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

/-- `sgn a · a = |a|`. -/
lemma sgn_mul (a : ℝ) : sgn a * a = |a| := by
  unfold sgn; split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]; ring

/-- `sgn a · b ≤ |b|`. -/
lemma sgn_mul_le (a b : ℝ) : sgn a * b ≤ |b| := by
  unfold sgn; split_ifs
  · rw [one_mul]; exact le_abs_self b
  · rw [neg_one_mul]; exact neg_le_abs b

/-- `|sgn a| = 1`. -/
lemma abs_sgn (a : ℝ) : |sgn a| = 1 := by unfold sgn; split_ifs <;> simp

/-- **Pullback contraction of `d_{□_k}`.** For bounded measurable colours and a
measure-preserving map `φ` acting on all colours, `d_{□_k}(U^φ, W^φ) ≤ d_{□_k}(U, W)`. -/
theorem kCutNormDist_pullback_le {k : ℕ} {U W : Fin k → I → I → ℝ}
    (hUm : ∀ i, Measurable (Function.uncurry (U i))) (hWm : ∀ i, Measurable (Function.uncurry (W i)))
    {M : ℝ} (hU : ∀ i x y, |U i x y| ≤ M) (hW : ∀ i x y, |W i x y| ≤ M)
    {φ : I → I} (hφ : MeasurePreserving φ volume volume) :
    kCutNormDist k (fun i => pullback φ (U i)) (fun i => pullback φ (W i)) ≤
      kCutNormDist k U W := by
  refine kCutNormDist_le fun S T hS hT => ?_
  set a : Fin k → ℝ := fun i => ∫ p in S ×ˢ T, (pullback φ (U i) p.1 p.2 - pullback φ (W i) p.1 p.2)
    with ha
  set G : I × I → ℝ := fun p => ∑ i, sgn (a i) * (U i p.1 p.2 - W i p.1 p.2) with hGdef
  have hdm : ∀ i, Measurable (fun p : I × I => U i p.1 p.2 - W i p.1 p.2) := fun i =>
    (hUm i).sub (hWm i)
  have hdb : ∀ i (p : I × I), |U i p.1 p.2 - W i p.1 p.2| ≤ 2 * M := fun i p => by
    calc _ ≤ |U i p.1 p.2| + |W i p.1 p.2| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hU i p.1 p.2, hW i p.1 p.2]
  have hGm : Measurable G := Finset.measurable_sum _ fun i _ => (hdm i).const_mul _
  have hGb : ∀ p, |G p| ≤ ∑ _i : Fin k, 2 * M := fun p => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_sgn, one_mul]; exact hdb i p
  -- integrals of signed sums
  have hsum : ∀ (ρ : Measure (I × I)) [IsFiniteMeasure ρ] (ψ : I × I → I × I), Measurable ψ →
      ∫ p, G (ψ p) ∂ρ = ∑ i, sgn (a i) * ∫ p, (U i (ψ p).1 (ψ p).2 - W i (ψ p).1 (ψ p).2) ∂ρ := by
    intro ρ _ ψ hψ
    simp only [hGdef]
    rw [integral_finsetSum (f := fun i p => sgn (a i) * (U i (ψ p).1 (ψ p).2 - W i (ψ p).1 (ψ p).2))
      _ fun i _ => ((integrable_bdd ((hdm i).comp hψ) (2 * M) fun p => hdb i (ψ p)).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  obtain ⟨S', T', hS', hT', hle⟩ := setIntegral_comp_le G hGm hGb hφ S T
  have e1 : ∑ i, |a i| = ∫ p in S ×ˢ T, G (φ p.1, φ p.2) := by
    rw [hsum _ (fun p => (φ p.1, φ p.2)) (hφ.measurable.prodMap hφ.measurable)]
    exact Finset.sum_congr rfl fun i _ => (sgn_mul _).symm
  have e2 : ∫ p in S' ×ˢ T', G p = ∑ i, sgn (a i) * ∫ p in S' ×ˢ T', (U i p.1 p.2 - W i p.1 p.2) :=
    hsum _ id measurable_id
  calc ∑ i, |a i| ≤ ∫ p in S' ×ˢ T', G p := e1 ▸ hle
    _ ≤ ∑ i, |∫ p in S' ×ˢ T', (U i p.1 p.2 - W i p.1 p.2)| := by
        rw [e2]; exact Finset.sum_le_sum fun i _ => sgn_mul_le _ _
    _ ≤ kCutNormDist k U W := le_kCutNormDist hU hW hS' hT'


/-! ## Target 2: pseudometric facts (all but symmetry) -/

section MapDist

/-- A digraphon is a bounded measurable kernel. -/
lemma isKernel_of_isDigraphon {U : I → I → ℝ} (hU : IsDigraphon U) : IsKernel U :=
  ⟨hU.1, 1, fun x y => by rw [abs_le]; constructor <;> linarith [(hU.2 x y).1, (hU.2 x y).2]⟩

/-- The set defining `δ_□^{map}` is nonempty (`φ = id`). -/
lemma cutDistMap_set_nonempty (U W : I → I → ℝ) :
    {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = cutNorm fun x y => U x y - pullback φ W x y}.Nonempty :=
  ⟨_, id, MeasurePreserving.id _, rfl⟩

/-- The set defining `δ_□^{map}` is bounded below by `0`. -/
lemma cutDistMap_set_bdd (U W : I → I → ℝ) :
    BddBelow {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = cutNorm fun x y => U x y - pullback φ W x y} :=
  ⟨0, fun _ ⟨_, _, hr⟩ => hr ▸ cutNorm_nonneg' _⟩

/-- `δ_□^{map}(U, W) ≤ ‖U − W^φ‖_□` for every measure-preserving map `φ`. -/
theorem cutDistMap_le (U W : I → I → ℝ) {φ : I → I} (hφ : MeasurePreserving φ volume volume) :
    cutDistMap U W ≤ cutNorm fun x y => U x y - pullback φ W x y :=
  csInf_le (cutDistMap_set_bdd U W) ⟨φ, hφ, rfl⟩

/-- **Nonnegativity** of `δ_□^{map}`, for arbitrary functions. -/
theorem cutDistMap_nonneg (U W : I → I → ℝ) : 0 ≤ cutDistMap U W :=
  Real.sInf_nonneg fun _ ⟨_, _, hr⟩ => hr ▸ cutNorm_nonneg' _

/-- `δ_□^{map}(U, U) = 0`, for every function `U`. -/
theorem cutDistMap_self (U : I → I → ℝ) : cutDistMap U U = 0 := by
  refine le_antisymm ((cutDistMap_le U U (MeasurePreserving.id volume)).trans ?_)
    (cutDistMap_nonneg U U)
  refine cutNorm_le fun S T _ _ => ?_
  simp [pullback]

/-- **Triangle inequality** for `δ_□^{map}` on bounded measurable kernels:
`δ(U, X) ≤ δ(U, W) + δ(W, X)` (via `‖U − X^{ψ∘φ}‖ ≤ ‖U − W^φ‖ + ‖(W − X^ψ)^φ‖` and the pullback
contraction `cutNorm_pullback_le`). -/
theorem cutDistMap_triangle {U W X : I → I → ℝ} (hU : IsKernel U) (hW : IsKernel W)
    (hX : IsKernel X) : cutDistMap U X ≤ cutDistMap U W + cutDistMap W X := by
  obtain ⟨hUm, A, hA⟩ := hU
  obtain ⟨hWm, B, hB⟩ := hW
  obtain ⟨hXm, C, hC⟩ := hX
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨_, ⟨φ, hφ, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (cutDistMap_set_nonempty U W)
    (show cutDistMap U W < cutDistMap U W + ε / 2 by linarith)
  obtain ⟨_, ⟨ψ, hψ, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (cutDistMap_set_nonempty W X)
    (show cutDistMap W X < cutDistMap W X + ε / 2 by linarith)
  have hψm := hψ.measurable
  have hφm := hφ.measurable
  -- the two pieces
  set F₁ : I → I → ℝ := fun x y => U x y - pullback φ W x y with hF₁
  set F : I → I → ℝ := fun x y => W x y - pullback ψ X x y with hF
  have hFm : Measurable (Function.uncurry F) := hWm.sub (hXm.comp (hψm.prodMap hψm))
  have hFb : ∀ x y, |F x y| ≤ B + C := fun x y => by
    calc |F x y| ≤ |W x y| + |X (ψ x) (ψ y)| := abs_sub _ _
      _ ≤ B + C := add_le_add (hB x y) (hC _ _)
  have hk₁ : BK F₁ := ⟨hUm.sub (hWm.comp (hφm.prodMap hφm)), A + B, fun x y => by
    calc |F₁ x y| ≤ |U x y| + |W (φ x) (φ y)| := abs_sub _ _
      _ ≤ A + B := add_le_add (hA x y) (hB _ _)⟩
  have hk₂ : BK (fun x y => F (φ x) (φ y)) :=
    ⟨hFm.comp (hφm.prodMap hφm), B + C, fun x y => hFb _ _⟩
  have hcomp : MeasurePreserving (ψ ∘ φ) volume volume := hψ.comp hφ
  have e : (fun x y => U x y - pullback (ψ ∘ φ) X x y) =
      fun x y => 1 * F₁ x y + 1 * F (φ x) (φ y) := by
    funext x y; simp only [hF₁, hF, pullback, Function.comp]; ring
  calc cutDistMap U X ≤ cutNorm fun x y => U x y - pullback (ψ ∘ φ) X x y :=
        cutDistMap_le U X hcomp
    _ = cutNorm fun x y => 1 * F₁ x y + 1 * F (φ x) (φ y) := by rw [e]
    _ ≤ |1| * cutNorm F₁ + |1| * cutNorm (fun x y => F (φ x) (φ y)) := cutNorm_lin_le hk₁ hk₂ 1 1
    _ ≤ cutNorm F₁ + cutNorm F := by
        rw [abs_one, one_mul, one_mul]
        exact add_le_add le_rfl (cutNorm_pullback_le hFm hFb hφ)
    _ < cutDistMap U W + ε / 2 + (cutDistMap W X + ε / 2) := add_lt_add h1 h2
    _ = cutDistMap U W + cutDistMap W X + ε := by ring

/-- **Boundedness** of `δ_□^{map}` on digraphons: `δ_□^{map}(U, W) ≤ 1`. -/
theorem cutDistMap_le_one {U W : I → I → ℝ} (hU : IsDigraphon U) (hW : IsDigraphon W) :
    cutDistMap U W ≤ 1 := by
  refine (cutDistMap_le U W (MeasurePreserving.id volume)).trans (cutNorm_le fun S T _ _ => ?_)
  refine abs_setIntegral_le (F := fun x y => U x y - pullback id W x y) (fun x y => ?_) _
  have h1 := hU.2 x y; have h2 := hW.2 x y
  simp only [pullback, id]
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Nonnegativity of `δ_□^{map}` on `Digraphon`. -/
theorem digraphon_cutDistMap_nonneg (U W : Digraphon) : 0 ≤ cutDistMap U.toFun W.toFun :=
  cutDistMap_nonneg _ _

/-- `δ_□^{map}(U, U) = 0` on `Digraphon`. -/
theorem digraphon_cutDistMap_self (U : Digraphon) : cutDistMap U.toFun U.toFun = 0 :=
  cutDistMap_self _

/-- The triangle inequality for `δ_□^{map}` on `Digraphon`. -/
theorem digraphon_cutDistMap_triangle (U W X : Digraphon) :
    cutDistMap U.toFun X.toFun ≤ cutDistMap U.toFun W.toFun + cutDistMap W.toFun X.toFun :=
  cutDistMap_triangle (isKernel_of_isDigraphon U.isDigraphon)
    (isKernel_of_isDigraphon W.isDigraphon) (isKernel_of_isDigraphon X.isDigraphon)

/-- Boundedness `δ_□^{map} ≤ 1` on `Digraphon`. -/
theorem digraphon_cutDistMap_le_one (U W : Digraphon) : cutDistMap U.toFun W.toFun ≤ 1 :=
  cutDistMap_le_one U.isDigraphon W.isDigraphon

end MapDist

section KDist

variable {k : ℕ}

/-- **Triangle inequality for `d_{□_k}`** on measurable colour families bounded by `M`. -/
theorem kCutNormDist_triangle {U W X : Fin k → I → I → ℝ}
    (hUm : ∀ i, Measurable (Function.uncurry (U i))) (hWm : ∀ i, Measurable (Function.uncurry (W i)))
    (hXm : ∀ i, Measurable (Function.uncurry (X i))) {M : ℝ} (hU : ∀ i x y, |U i x y| ≤ M)
    (hW : ∀ i x y, |W i x y| ≤ M) (hX : ∀ i x y, |X i x y| ≤ M) :
    kCutNormDist k U X ≤ kCutNormDist k U W + kCutNormDist k W X := by
  refine kCutNormDist_le fun S T hS hT => ?_
  have hint : ∀ (Y : Fin k → I → I → ℝ), (∀ i, Measurable (Function.uncurry (Y i))) →
      (∀ i x y, |Y i x y| ≤ M) → ∀ i,
        IntegrableOn (fun p : I × I => Y i p.1 p.2) (S ×ˢ T) (volume : Measure (I × I)) :=
    fun Y hm hb i => (integrable_bdd (hm i) M fun p => hb i p.1 p.2).integrableOn
  calc ∑ i, |∫ p in S ×ˢ T, (U i p.1 p.2 - X i p.1 p.2)|
      ≤ ∑ i, (|∫ p in S ×ˢ T, (U i p.1 p.2 - W i p.1 p.2)| +
          |∫ p in S ×ˢ T, (W i p.1 p.2 - X i p.1 p.2)|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [integral_sub (hint U hUm hU i) (hint X hXm hX i),
          integral_sub (hint U hUm hU i) (hint W hWm hW i),
          integral_sub (hint W hWm hW i) (hint X hXm hX i)]
        calc _ = |((∫ p in S ×ˢ T, U i p.1 p.2) - ∫ p in S ×ˢ T, W i p.1 p.2) +
              ((∫ p in S ×ˢ T, W i p.1 p.2) - ∫ p in S ×ˢ T, X i p.1 p.2)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ kCutNormDist k U W + kCutNormDist k W X :=
        add_le_add (le_kCutNormDist hU hW hS hT) (le_kCutNormDist hW hX hS hT)

/-- The set defining `δ_{□_k}` is nonempty (`φ = id`), for every `k`. -/
lemma kCutDist_set_nonempty' (U W : Fin k → I → I → ℝ) :
    {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = kCutNormDist k U (fun i => pullback φ (W i))}.Nonempty :=
  ⟨_, id, MeasurePreserving.id _, rfl⟩

/-- The set defining `δ_{□_k}` is bounded below by `0`. -/
lemma kCutDist_set_bdd (U W : Fin k → I → I → ℝ) :
    BddBelow {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = kCutNormDist k U (fun i => pullback φ (W i))} :=
  ⟨0, fun _ ⟨_, _, hr⟩ => hr ▸ kCutNormDist_nonneg' _ _ _⟩

/-- `δ_{□_k}(U, W) ≤ d_{□_k}(U, W^φ)` for every measure-preserving map `φ`. -/
theorem kCutDist_le (U W : Fin k → I → I → ℝ) {φ : I → I}
    (hφ : MeasurePreserving φ volume volume) :
    kCutDist k U W ≤ kCutNormDist k U (fun i => pullback φ (W i)) :=
  csInf_le (kCutDist_set_bdd U W) ⟨φ, hφ, rfl⟩

/-- **Nonnegativity** of `δ_{□_k}`, for arbitrary colour families. -/
theorem kCutDist_nonneg (U W : Fin k → I → I → ℝ) : 0 ≤ kCutDist k U W :=
  Real.sInf_nonneg fun _ ⟨_, _, hr⟩ => hr ▸ kCutNormDist_nonneg' _ _ _

/-- `δ_{□_k}(U, U) = 0`, for every colour family `U`. -/
theorem kCutDist_self (U : Fin k → I → I → ℝ) : kCutDist k U U = 0 := by
  refine le_antisymm ((kCutDist_le U U (MeasurePreserving.id volume)).trans ?_)
    (kCutDist_nonneg U U)
  refine kCutNormDist_le fun S T _ _ => ?_
  simp [pullback]

/-- **Triangle inequality** for `δ_{□_k}` on measurable colour families bounded by `M`:
`δ(U, X) ≤ δ(U, W) + δ(W, X)` (via `d(U, X^{ψ∘φ}) ≤ d(U, W^φ) + d(W^φ, (X^ψ)^φ)` and the pullback
contraction `kCutNormDist_pullback_le`). -/
theorem kCutDist_triangle {U W X : Fin k → I → I → ℝ}
    (hUm : ∀ i, Measurable (Function.uncurry (U i))) (hWm : ∀ i, Measurable (Function.uncurry (W i)))
    (hXm : ∀ i, Measurable (Function.uncurry (X i))) {M : ℝ} (hU : ∀ i x y, |U i x y| ≤ M)
    (hW : ∀ i x y, |W i x y| ≤ M) (hX : ∀ i x y, |X i x y| ≤ M) :
    kCutDist k U X ≤ kCutDist k U W + kCutDist k W X := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨_, ⟨φ, hφ, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (kCutDist_set_nonempty' U W)
    (show kCutDist k U W < kCutDist k U W + ε / 2 by linarith)
  obtain ⟨_, ⟨ψ, hψ, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (kCutDist_set_nonempty' W X)
    (show kCutDist k W X < kCutDist k W X + ε / 2 by linarith)
  have hψm := hψ.measurable
  have hφm := hφ.measurable
  have hpm : ∀ (Y : Fin k → I → I → ℝ), (∀ i, Measurable (Function.uncurry (Y i))) →
      ∀ {θ : I → I}, Measurable θ → ∀ i, Measurable (Function.uncurry (pullback θ (Y i))) :=
    fun Y hY θ hθ i => (hY i).comp (hθ.prodMap hθ)
  have hpb : ∀ (Y : Fin k → I → I → ℝ), (∀ i x y, |Y i x y| ≤ M) → ∀ (θ : I → I),
      ∀ i x y, |pullback θ (Y i) x y| ≤ M := fun Y hY θ i x y => hY i _ _
  calc kCutDist k U X ≤ kCutNormDist k U (fun i => pullback (ψ ∘ φ) (X i)) :=
        kCutDist_le U X (hψ.comp hφ)
    _ ≤ kCutNormDist k U (fun i => pullback φ (W i)) +
          kCutNormDist k (fun i => pullback φ (W i)) (fun i => pullback (ψ ∘ φ) (X i)) :=
        kCutNormDist_triangle hUm (hpm W hWm hφm) (hpm X hXm (hψm.comp hφm)) hU (hpb W hW φ)
          (hpb X hX _)
    _ ≤ kCutNormDist k U (fun i => pullback φ (W i)) +
          kCutNormDist k W (fun i => pullback ψ (X i)) := by
        refine add_le_add le_rfl ?_
        exact kCutNormDist_pullback_le (U := W) (W := fun i => pullback ψ (X i)) hWm
          (hpm X hXm hψm) hW (hpb X hX ψ) hφ
    _ < kCutDist k U W + ε / 2 + (kCutDist k W X + ε / 2) := add_lt_add h1 h2
    _ = kCutDist k U W + kCutDist k W X + ε := by ring

/-- Coordinates of a `[k]`-graphon lie in `[0, 1]`. -/
lemma kGraphon_mem {W : Fin k → I → I → ℝ} (hW : IsKGraphon k W) (i : Fin k) (x y : I) :
    W i x y ∈ Icc (0 : ℝ) 1 := by
  refine ⟨hW.2.1 i x y, ?_⟩
  rw [← hW.2.2.1 x y]
  exact Finset.single_le_sum (fun j _ => hW.2.1 j x y) (Finset.mem_univ i)

/-- Coordinates of a `[k]`-graphon are bounded by `1` in absolute value. -/
lemma kGraphon_abs_le {W : Fin k → I → I → ℝ} (hW : IsKGraphon k W) (i : Fin k) (x y : I) :
    |W i x y| ≤ 1 := by
  have := kGraphon_mem hW i x y
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

/-- **Boundedness** of `δ_{□_k}` on `[k]`-graphons: `δ_{□_k}(U, W) ≤ k`. -/
theorem kCutDist_le_card {U W : Fin k → I → I → ℝ} (hU : IsKGraphon k U) (hW : IsKGraphon k W) :
    kCutDist k U W ≤ k := by
  refine (kCutDist_le U W (MeasurePreserving.id volume)).trans (kCutNormDist_le fun S T _ _ => ?_)
  calc _ ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        abs_setIntegral_le (F := fun x y => U i x y - pullback id (W i) x y) (fun x y => by
          have h1 := kGraphon_mem hU i x y; have h2 := kGraphon_mem hW i x y
          simp only [pullback, id]
          rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]) _
    _ = k := by simp

/-- Nonnegativity of `δ_{□_k}` on `KGraphon k`. -/
theorem kGraphon_kCutDist_nonneg (U W : KGraphon k) : 0 ≤ kCutDist k U.toFun W.toFun :=
  kCutDist_nonneg _ _

/-- `δ_{□_k}(U, U) = 0` on `KGraphon k`. -/
theorem kGraphon_kCutDist_self (U : KGraphon k) : kCutDist k U.toFun U.toFun = 0 :=
  kCutDist_self _

/-- The triangle inequality for `δ_{□_k}` on `KGraphon k`. -/
theorem kGraphon_kCutDist_triangle (U W X : KGraphon k) :
    kCutDist k U.toFun X.toFun ≤ kCutDist k U.toFun W.toFun + kCutDist k W.toFun X.toFun :=
  kCutDist_triangle U.isKGraphon.1 W.isKGraphon.1 X.isKGraphon.1 (kGraphon_abs_le U.isKGraphon)
    (kGraphon_abs_le W.isKGraphon) (kGraphon_abs_le X.isKGraphon)

/-- Boundedness `δ_{□_k} ≤ k` on `KGraphon k`. -/
theorem kGraphon_kCutDist_le_card (U W : KGraphon k) : kCutDist k U.toFun W.toFun ≤ k :=
  kCutDist_le_card U.isKGraphon W.isKGraphon

end KDist

/-! ## Target 3: the topology of one-sided balls, the quotient, compactness -/

section Generic

variable {X : Type*}

/-- The topology generated by the one-sided balls `{W | d U W < r}`. -/
@[instance_reducible]
def ballTopology (d : X → X → ℝ) : TopologicalSpace X :=
  TopologicalSpace.generateFrom {B | ∃ (U : X) (r : ℝ), B = {W | d U W < r}}

/-- **(3a)** If `d` is the distance of a pseudometric space structure on `X`, the topology generated
by the one-sided balls `{W | d U W < r}` is the pseudometric topology. -/
theorem ballTopology_eq [PseudoMetricSpace X] (d : X → X → ℝ) (hd : ∀ x y, dist x y = d x y) :
    ballTopology d = (inferInstance : TopologicalSpace X) := by
  have hball : ∀ (U : X) (r : ℝ), {W | d U W < r} = Metric.ball U r := fun U r => by
    ext W; simp only [Set.mem_ofPred_eq, Metric.mem_ball, ← hd, dist_comm W U]
  refine le_antisymm ?_ ?_
  · intro s hs
    let _ : TopologicalSpace X := ballTopology d
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hs x hx
    refine ⟨Metric.ball x ε, hsub, ?_, Metric.mem_ball_self hε⟩
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨x, ε, (hball x ε).symm⟩
  · rw [ballTopology, TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨U, r, rfl⟩
    rw [hball]
    exact Metric.isOpen_ball

/-- **(3b)** The relation `d U W = 0` is an equivalence relation when `d` is the distance of a
pseudometric space structure. -/
theorem zero_equivalence [PseudoMetricSpace X] (d : X → X → ℝ) (hd : ∀ x y, dist x y = d x y) :
    Equivalence (fun U W : X => d U W = 0) := by
  refine ⟨fun x => by rw [← hd, dist_self], fun {x y} h => by rw [← hd, dist_comm, hd, h],
    fun {x y z} h₁ h₂ => ?_⟩
  rw [← hd] at h₁ h₂ ⊢
  exact le_antisymm (by linarith [dist_triangle x y z]) dist_nonneg

/-- **(3b)** `Quot (d · · = 0)`, with the quotient topology of the pseudometric topology, is
homeomorphic to the metric identification `SeparationQuotient X`. -/
noncomputable def quotHomeomorph [PseudoMetricSpace X] (d : X → X → ℝ)
    (hd : ∀ x y, dist x y = d x y) :
    Quot (fun U W : X => d U W = 0) ≃ₜ SeparationQuotient X where
  toFun := Quot.lift SeparationQuotient.mk fun a b h =>
    SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 (by rw [hd]; exact h))
  invFun := SeparationQuotient.lift (Quot.mk _) fun a b h =>
    Quot.sound (by rw [← hd]; exact Metric.inseparable_iff.1 h)
  left_inv := fun q => by induction q using Quot.ind; rfl
  right_inv := SeparationQuotient.surjective_mk.forall.2 fun _ => rfl
  continuous_toFun := continuous_quot_lift _ SeparationQuotient.continuous_mk
  continuous_invFun := SeparationQuotient.continuous_lift continuous_quot_mk

/-- **(3c)** A pseudometric space is compact iff its metric identification is. -/
theorem compactSpace_separationQuotient_iff [PseudoMetricSpace X] :
    CompactSpace (SeparationQuotient X) ↔ CompactSpace X := by
  constructor
  · intro h
    refine ⟨?_⟩
    have := (SeparationQuotient.isInducing_mk (X := X)).isCompact_preimage_iff
      (K := univ) (by rw [SeparationQuotient.range_mk]) |>.2 isCompact_univ
    simpa using this
  · intro h
    exact SeparationQuotient.surjective_mk.compactSpace SeparationQuotient.continuous_mk

/-- **(3c)** Compactness of `Quot (d · · = 0)` with the quotient topology of the one-sided-ball
topology `ballTopology d` is compactness of the metric identification `SeparationQuotient X`. -/
theorem compactSpace_quot_ballTopology_iff [PseudoMetricSpace X] (d : X → X → ℝ)
    (hd : ∀ x y, dist x y = d x y) :
    @CompactSpace (Quot fun U W : X => d U W = 0)
        (@instTopologicalSpaceQuot X _ (ballTopology d)) ↔
      CompactSpace (SeparationQuotient X) := by
  rw [ballTopology_eq d hd]
  exact ⟨fun h => (quotHomeomorph d hd).compactSpace,
    fun h => (quotHomeomorph d hd).symm.compactSpace⟩

/-- **(3c)** The same, with the pseudometric space itself. -/
theorem compactSpace_quot_ballTopology_iff' [PseudoMetricSpace X] (d : X → X → ℝ)
    (hd : ∀ x y, dist x y = d x y) :
    @CompactSpace (Quot fun U W : X => d U W = 0)
        (@instTopologicalSpaceQuot X _ (ballTopology d)) ↔ CompactSpace X :=
  (compactSpace_quot_ballTopology_iff d hd).trans compactSpace_separationQuotient_iff

/-- The topology of Mathlib's `MetricSpace (SeparationQuotient X)` (the metric identification) is
the quotient topology of the pseudometric topology (definitionally). -/
theorem separationQuotient_topology_eq [PseudoMetricSpace X] :
    (inferInstance : MetricSpace (SeparationQuotient X)).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (SeparationQuotient X)) := rfl

end Generic

/-! ## Target 4: the formal compactness hypotheses are the published statements -/

section Concrete

/-- `cutMapTopology` is the one-sided-ball topology of `δ_□^{map}`. -/
theorem cutMapTopology_eq_ballTopology :
    cutMapTopology = ballTopology (fun U W : Digraphon => cutDistMap U.toFun W.toFun) := rfl

/-- `kCutTopology k` is the one-sided-ball topology of `δ_{□_k}`. -/
theorem kCutTopology_eq_ballTopology (k : ℕ) :
    kCutTopology k = ballTopology (fun U W : KGraphon k => kCutDist k U.toFun W.toFun) := rfl

/-- The pseudometric space structure `(Digraphon, δ_□^{map})`, given the symmetry of
`δ_□^{map}` (the other pseudometric laws are `digraphon_cutDistMap_self` and
`digraphon_cutDistMap_triangle`). Not an instance. -/
@[instance_reducible]
noncomputable def digraphonPseudoMetric
    (hsymm : ∀ U W : Digraphon, cutDistMap U.toFun W.toFun = cutDistMap W.toFun U.toFun) :
    PseudoMetricSpace Digraphon where
  dist U W := cutDistMap U.toFun W.toFun
  dist_self U := digraphon_cutDistMap_self U
  dist_comm := hsymm
  dist_triangle := digraphon_cutDistMap_triangle

/-- The pseudometric space structure `(KGraphon k, δ_{□_k})`, given the symmetry of `δ_{□_k}`
(the other pseudometric laws are `kGraphon_kCutDist_self` and `kGraphon_kCutDist_triangle`). Not an
instance. -/
@[instance_reducible]
noncomputable def kGraphonPseudoMetric (k : ℕ)
    (hsymm : ∀ U W : KGraphon k, kCutDist k U.toFun W.toFun = kCutDist k W.toFun U.toFun) :
    PseudoMetricSpace (KGraphon k) where
  dist U W := kCutDist k U.toFun W.toFun
  dist_self U := kGraphon_kCutDist_self U
  dist_comm := hsymm
  dist_triangle := kGraphon_kCutDist_triangle

/-- **Target 4 (FHMZ).** Given the symmetry of `δ_□^{map}`, the formal hypothesis
`FHMZCompactHyp` (compactness of `Quot (δ_□^{map} = 0)` with the quotient of the ball topology)
is equivalent to the published statement (FHMZ p.6): the metric space obtained from
`(Digraphon, δ_□^{map})` by identifying distance zero, `SeparationQuotient Digraphon` with its
`MetricSpace` structure, is compact. -/
theorem fhmzCompactHyp_iff_of_symm
    (hsymm : ∀ U W : Digraphon, cutDistMap U.toFun W.toFun = cutDistMap W.toFun U.toFun) :
    FHMZCompactHyp ↔
      letI : PseudoMetricSpace Digraphon := digraphonPseudoMetric hsymm
      CompactSpace (SeparationQuotient Digraphon) := by
  let _ : PseudoMetricSpace Digraphon := digraphonPseudoMetric hsymm
  exact compactSpace_quot_ballTopology_iff (fun U W : Digraphon => cutDistMap U.toFun W.toFun)
    (fun _ _ => rfl)

/-- **Target 4 (FHMZ), second form.** Given symmetry, `FHMZCompactHyp` is equivalent to
compactness of the pseudometric space `(Digraphon, δ_□^{map})`. -/
theorem fhmzCompactHyp_iff_compactSpace_of_symm
    (hsymm : ∀ U W : Digraphon, cutDistMap U.toFun W.toFun = cutDistMap W.toFun U.toFun) :
    FHMZCompactHyp ↔
      letI : PseudoMetricSpace Digraphon := digraphonPseudoMetric hsymm
      CompactSpace Digraphon := by
  let _ : PseudoMetricSpace Digraphon := digraphonPseudoMetric hsymm
  exact compactSpace_quot_ballTopology_iff' (fun U W : Digraphon => cutDistMap U.toFun W.toFun)
    (fun _ _ => rfl)

/-- **Target 4 (FRHSU), one `k`.** Given the symmetry of `δ_{□_k}`, compactness of
`Quot (δ_{□_k} = 0)` with the quotient of `kCutTopology k` is equivalent to compactness of the
metric space `(𝒲̃_k, δ_{□_k})`, i.e. `SeparationQuotient (KGraphon k)`. -/
theorem kCut_compact_iff_of_symm (k : ℕ)
    (hsymm : ∀ U W : KGraphon k, kCutDist k U.toFun W.toFun = kCutDist k W.toFun U.toFun) :
    (letI : TopologicalSpace (KGraphon k) := kCutTopology k;
      CompactSpace (Quot fun U W : KGraphon k => kCutDist k U.toFun W.toFun = 0)) ↔
      letI : PseudoMetricSpace (KGraphon k) := kGraphonPseudoMetric k hsymm
      CompactSpace (SeparationQuotient (KGraphon k)) := by
  let _ : PseudoMetricSpace (KGraphon k) := kGraphonPseudoMetric k hsymm
  exact compactSpace_quot_ballTopology_iff (fun U W : KGraphon k => kCutDist k U.toFun W.toFun)
    (fun _ _ => rfl)

/-- **Target 4 (FRHSU).** Given the symmetry of every `δ_{□_k}`, the formal hypothesis
`FRHSUThm43Hyp` is equivalent to the published FRHSU Theorem 4.3: for every `k ≥ 1` the metric
space `(𝒲̃_k, δ_{□_k})` (the metric identification `SeparationQuotient (KGraphon k)` of the
pseudometric space `(KGraphon k, δ_{□_k})`) is compact. -/
theorem frhsu_iff_of_symm
    (hsymm : ∀ k, ∀ U W : KGraphon k, kCutDist k U.toFun W.toFun = kCutDist k W.toFun U.toFun) :
    FRHSUThm43Hyp ↔ ∀ k : ℕ, 1 ≤ k →
      letI : PseudoMetricSpace (KGraphon k) := kGraphonPseudoMetric k (hsymm k)
      CompactSpace (SeparationQuotient (KGraphon k)) :=
  forall_congr' fun k => imp_congr_right fun _ => kCut_compact_iff_of_symm k (hsymm k)

/-- **Target 4 (FRHSU), second form.** Given symmetry, `FRHSUThm43Hyp` is equivalent to
compactness of every pseudometric space `(KGraphon k, δ_{□_k})`, `k ≥ 1`. -/
theorem frhsu_iff_compactSpace_of_symm
    (hsymm : ∀ k, ∀ U W : KGraphon k, kCutDist k U.toFun W.toFun = kCutDist k W.toFun U.toFun) :
    FRHSUThm43Hyp ↔ ∀ k : ℕ, 1 ≤ k →
      letI : PseudoMetricSpace (KGraphon k) := kGraphonPseudoMetric k (hsymm k)
      CompactSpace (KGraphon k) :=
  (frhsu_iff_of_symm hsymm).trans <| forall_congr' fun k => imp_congr_right fun _ =>
    letI : PseudoMetricSpace (KGraphon k) := kGraphonPseudoMetric k (hsymm k)
    compactSpace_separationQuotient_iff

end Concrete

end KCutPseudo

end NieWeiOrientedSidorenko
