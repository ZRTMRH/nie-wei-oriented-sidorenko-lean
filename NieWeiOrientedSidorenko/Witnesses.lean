import NieWeiOrientedSidorenko.Section1

/-!
# Non-vacuity witnesses

Witnesses that the hypotheses of the norming-type definitions of `Basic.lean` can hold:

* `isNorming_K22`: `C₄ = K_{2,2}` (with its bipartition into two sides of size two) is
  norming, proved directly by the Cauchy–Schwarz argument for `t(C₄, ·)`;
* `isNormingGraph_K22`: the undirected graph `K_{2,2}` (the 4-cycle) is norming;
* `strictConvexOnKernels_K22`: `t_bi(K_{2,2}, ·)` is strictly convex on all kernels;
* `strict_to_norming_hyps_K22`: the full hypothesis bundle of `Section2Aux.strict_to_norming`;
* `structLT_const_avgW`, `exists_structLT`, `not_cutDistIdentifying_zero`: `StructLT` holds for
  the constant `∫ W` below `W(x, y) = (x + y)/2`, conditional on the literature hypothesis
  `DGHRRFact217Hyp`; `structLT_const_avgW_of_mixing` reduces them to a mixing sequence of
  measure-preserving bijections. The mixing sequence it needs is built in `Mixing.lean`, which proves
  the same three facts unconditionally (`structLT_const_avgW'`, `exists_structLT'`,
  `not_cutDistIdentifying_zero'`); the conditional versions here are superseded.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace NieWeiOrientedSidorenko

namespace Witnesses

/-! ## Cauchy–Schwarz for bounded measurable functions -/

lemma abs_mul_le_of {p q A B : ℝ} (hp : |p| ≤ A) (hq : |q| ≤ B) : |p * q| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp)

lemma integrable_mul_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) {C D : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hD : ∀ x, |g x| ≤ D) : Integrable (fun x => f x * g x) μ :=
  S1CutDist.integrable_bdd (hf.mul hg) (C * D) fun x => abs_mul_le_of (hC x) (hD x)

/-- Cauchy–Schwarz: `(∫ f g)² ≤ (∫ f²)(∫ g²)` for bounded measurable `f, g` on a finite measure
space. -/
lemma cs_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) {C D : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hD : ∀ x, |g x| ≤ D) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x * f x ∂μ) * (∫ x, g x * g x ∂μ) := by
  have iff : Integrable (fun x => f x * f x) μ := integrable_mul_of_bdd hf hf hC hC
  have igg : Integrable (fun x => g x * g x) μ := integrable_mul_of_bdd hg hg hD hD
  have ifg : Integrable (fun x => f x * g x) μ := integrable_mul_of_bdd hf hg hC hD
  have key : ∀ t : ℝ, 0 ≤ (∫ x, g x * g x ∂μ) * (t * t) + (-2 * ∫ x, f x * g x ∂μ) * t +
      ∫ x, f x * f x ∂μ := by
    intro t
    have e1 : (fun x => (f x - t * g x) ^ 2) =
        fun x => (t * t) * (g x * g x) + ((-2 * t) * (f x * g x) + f x * f x) := by
      funext x; ring
    have e : ∫ x, (f x - t * g x) ^ 2 ∂μ = (∫ x, g x * g x ∂μ) * (t * t) +
        (-2 * ∫ x, f x * g x ∂μ) * t + ∫ x, f x * f x ∂μ := by
      rw [e1, integral_add (igg.const_mul _) (by exact (ifg.const_mul _).add iff),
        integral_add (ifg.const_mul _) iff, integral_const_mul, integral_const_mul]
      ring
    rw [← e]; exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-! ## The two Gram kernels of `K_{2,2}` -/

/-- `k(F, G)(y, y') = ∫ F(x, y) G(x, y') dx`. -/
noncomputable def kk2 (F G : I → I → ℝ) (y y' : I) : ℝ := ∫ x, F x y * G x y'

/-- `g(F, G)(x, x') = ∫ F(x, y) G(x', y) dy`. -/
noncomputable def gT (F G : I → I → ℝ) (x x' : I) : ℝ := ∫ y, F x y * G x' y

/-- The product measure on `[0,1]²`. -/
noncomputable abbrev ν : Measure (I × I) := (volume : Measure I).prod volume

lemma kk2_meas {F G : I → I → ℝ} (hF : IsKernel F) (hG : IsKernel G) :
    Measurable (fun q : I × I => kk2 F G q.1 q.2) := by
  have hm : Measurable (fun r : I × (I × I) => F r.1 r.2.1 * G r.1 r.2.2) :=
    (S1CutDist.meas_app hF.1 measurable_fst (measurable_fst.comp measurable_snd)).mul
      (S1CutDist.meas_app hG.1 measurable_fst (measurable_snd.comp measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure I))).measurable

lemma gT_meas {F G : I → I → ℝ} (hF : IsKernel F) (hG : IsKernel G) :
    Measurable (fun q : I × I => gT F G q.1 q.2) := by
  have hm : Measurable (fun r : I × (I × I) => F r.2.1 r.1 * G r.2.2 r.1) :=
    (S1CutDist.meas_app hF.1 (measurable_fst.comp measurable_snd) measurable_fst).mul
      (S1CutDist.meas_app hG.1 (measurable_snd.comp measurable_snd) measurable_fst)
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure I))).measurable

lemma abs_integral_le_const {g : I → ℝ} {C : ℝ} (h : ∀ x, |g x| ≤ C) : |∫ x, g x| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure I)) (f := g) (C := C)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)
  simpa using this

lemma kk2_bound {F G : I → I → ℝ} {A B : ℝ} (hA : ∀ x y, |F x y| ≤ A) (hB : ∀ x y, |G x y| ≤ B)
    (y y' : I) : |kk2 F G y y'| ≤ A * B :=
  abs_integral_le_const fun _ => abs_mul_le_of (hA _ _) (hB _ _)

lemma gT_bound {F G : I → I → ℝ} {A B : ℝ} (hA : ∀ x y, |F x y| ≤ A) (hB : ∀ x y, |G x y| ≤ B)
    (x x' : I) : |gT F G x x'| ≤ A * B :=
  abs_integral_le_const fun _ => abs_mul_le_of (hA _ _) (hB _ _)

/-- The four-kernel density of `K_{2,2}`, grouped along the `Y` side. -/
noncomputable def Q (a b c d : I → I → ℝ) : ℝ := ∫ q, kk2 a b q.1 q.2 * kk2 c d q.1 q.2 ∂ν

/-- The same, grouped along the `X` side (for the pattern `Q a b a b`). -/
noncomputable def P (a b : I → I → ℝ) : ℝ := ∫ q, gT a a q.1 q.2 * gT b b q.1 q.2 ∂ν

/-- Fubini: `Q(a, b, a, b) = P(a, b)`. -/
lemma Q_eq_P {a b : I → I → ℝ} (ha : IsKernel a) (hb : IsKernel b) : Q a b a b = P a b := by
  obtain ⟨hma, A, hA⟩ := ha
  obtain ⟨hmb, B, hB⟩ := hb
  set H : I × I → I × I → ℝ := fun r s => a s.1 r.1 * b s.1 r.2 * (a s.2 r.1 * b s.2 r.2)
    with hH
  have h1 : ∀ r : I × I, kk2 a b r.1 r.2 * kk2 a b r.1 r.2 = ∫ s, H r s ∂ν := fun r => by
    simp only [hH, kk2]
    rw [← integral_prod_mul (fun x => a x r.1 * b x r.2) (fun x => a x r.1 * b x r.2)]
  have h2 : ∀ s : I × I, gT a a s.1 s.2 * gT b b s.1 s.2 = ∫ r, H r s ∂ν := fun s => by
    simp only [hH, gT]
    rw [← integral_prod_mul (fun y => a s.1 y * a s.2 y) (fun y' => b s.1 y' * b s.2 y')]
    congr 1; funext r; ring
  have hint : Integrable (Function.uncurry H) (ν.prod ν) := by
    refine S1CutDist.integrable_bdd ?_ (A * B * (A * B)) fun p => ?_
    · exact ((S1CutDist.meas_app hma measurable_snd.fst measurable_fst.fst).mul
        (S1CutDist.meas_app hmb measurable_snd.fst measurable_fst.snd)).mul
        ((S1CutDist.meas_app hma measurable_snd.snd measurable_fst.fst).mul
        (S1CutDist.meas_app hmb measurable_snd.snd measurable_fst.snd))
    · exact abs_mul_le_of (abs_mul_le_of (hA _ _) (hB _ _)) (abs_mul_le_of (hA _ _) (hB _ _))
  unfold Q P
  simp_rw [h1, h2]
  exact integral_integral_swap hint

lemma Q_self_nonneg (a b : I → I → ℝ) : 0 ≤ Q a b a b :=
  integral_nonneg fun _ => mul_self_nonneg _

/-- `C₄` as a bipartite graph: `K_{2,2}`. -/
abbrev E4 : Finset (Fin 2 × Fin 2) := Finset.univ

lemma card_E4 : E4.card = 4 := by
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

lemma tb_eq_Q {F : I → I → ℝ} (hF : IsKernel F) : tb E4 F = Q F F F F := by
  rw [S1CutDist.tb_K22 hF]
  unfold Q
  congr 1; funext q; rw [sq]; rfl

lemma tb_nonneg {F : I → I → ℝ} (hF : IsKernel F) : 0 ≤ tb E4 F := by
  rw [tb_eq_Q hF]; exact Q_self_nonneg _ _

lemma P_self {a : I → I → ℝ} (ha : IsKernel a) : P a a = tb E4 a := by
  rw [← Q_eq_P ha ha, tb_eq_Q ha]

lemma tb_eq_pow {F : I → I → ℝ} (hF : IsKernel F) : tb E4 F = hNorm E4 F ^ 4 := by
  rw [← card_E4, ← Section2Aux.abs_tb_eq_hNorm_pow E4 (by rw [card_E4]; norm_num),
    abs_of_nonneg (tb_nonneg hF)]

/-- The Cauchy–Schwarz–Hölder inequality for `K_{2,2}`:
`|Q(a,b,c,d)| ≤ ‖a‖‖b‖‖c‖‖d‖`. -/
lemma abs_Q_le {a b c d : I → I → ℝ} (ha : IsKernel a) (hb : IsKernel b) (hc : IsKernel c)
    (hd : IsKernel d) :
    |Q a b c d| ≤ hNorm E4 a * hNorm E4 b * hNorm E4 c * hNorm E4 d := by
  have hP : ∀ {a b : I → I → ℝ}, IsKernel a → IsKernel b →
      P a b ≤ hNorm E4 a ^ 2 * hNorm E4 b ^ 2 := by
    intro a b ha hb
    obtain ⟨A, hA⟩ := ha.2
    obtain ⟨B, hB⟩ := hb.2
    have hcs := cs_integral (μ := ν) (gT_meas ha ha) (gT_meas hb hb) (fun q => gT_bound hA hA q.1 q.2) (fun q => gT_bound hB hB q.1 q.2)
    change P a b ^ 2 ≤ P a a * P b b at hcs
    rw [P_self ha, P_self hb, tb_eq_pow ha, tb_eq_pow hb] at hcs
    have h0 : 0 ≤ P a b := by rw [← Q_eq_P ha hb]; exact Q_self_nonneg _ _
    have h1 : 0 ≤ hNorm E4 a ^ 2 * hNorm E4 b ^ 2 := by positivity
    refine (pow_le_pow_iff_left₀ h0 h1 two_ne_zero).1 ?_
    calc P a b ^ 2 ≤ hNorm E4 a ^ 4 * hNorm E4 b ^ 4 := hcs
      _ = _ := by ring
  obtain ⟨A, hA⟩ := ha.2
  obtain ⟨B, hB⟩ := hb.2
  obtain ⟨C, hC⟩ := hc.2
  obtain ⟨D, hD⟩ := hd.2
  have hcs := cs_integral (μ := ν) (kk2_meas ha hb) (kk2_meas hc hd)
    (fun q => kk2_bound hA hB q.1 q.2) (fun q => kk2_bound hC hD q.1 q.2)
  change Q a b c d ^ 2 ≤ Q a b a b * Q c d c d at hcs
  rw [Q_eq_P ha hb, Q_eq_P hc hd] at hcs
  have hab := hP ha hb
  have hcd := hP hc hd
  have h0 : 0 ≤ hNorm E4 a * hNorm E4 b * hNorm E4 c * hNorm E4 d := by
    have := Section2Aux.hNorm_nonneg E4 a; have := Section2Aux.hNorm_nonneg E4 b
    have := Section2Aux.hNorm_nonneg E4 c; have := Section2Aux.hNorm_nonneg E4 d
    positivity
  have hPab0 : 0 ≤ P a b := by rw [← Q_eq_P ha hb]; exact Q_self_nonneg _ _
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) h0 two_ne_zero).1 ?_
  rw [sq_abs]
  calc Q a b c d ^ 2 ≤ P a b * P c d := hcs
    _ ≤ (hNorm E4 a ^ 2 * hNorm E4 b ^ 2) * (hNorm E4 c ^ 2 * hNorm E4 d ^ 2) :=
        mul_le_mul hab hcd (by rw [← Q_eq_P hc hd]; exact Q_self_nonneg _ _)
          (by positivity)
    _ = _ := by ring

/-! ## The triangle inequality -/

lemma kk2_expand {U V : I → I → ℝ} (hU : IsKernel U) (hV : IsKernel V) (y y' : I) :
    kk2 (fun x y => U x y + V x y) (fun x y => U x y + V x y) y y' =
      ∑ i : Fin 4, kk2 (![U, U, V, V] i) (![U, V, U, V] i) y y' := by
  have hi : ∀ F G : I → I → ℝ, IsKernel F → IsKernel G →
      Integrable (fun x => F x y * G x y') volume := fun F G hF hG => by
    obtain ⟨M, hM⟩ := hF.2
    obtain ⟨N, hN⟩ := hG.2
    exact integrable_mul_of_bdd (S1CutDist.meas_app hF.1 measurable_id measurable_const)
      (S1CutDist.meas_app hG.1 measurable_id measurable_const) (fun _ => hM _ _) (fun _ => hN _ _)
  have hAk : ∀ i : Fin 4, IsKernel (![U, U, V, V] i) := by
    intro i; fin_cases i <;> simpa
  have hBk : ∀ i : Fin 4, IsKernel (![U, V, U, V] i) := by
    intro i; fin_cases i <;> simpa
  unfold kk2
  rw [← integral_finsetSum _ (fun i _ => hi _ _ (hAk i) (hBk i))]
  congr 1; funext x
  simp [Fin.sum_univ_four]
  ring

lemma tb_add_le {U V : I → I → ℝ} (hU : IsKernel U) (hV : IsKernel V) :
    tb E4 (fun x y => U x y + V x y) ≤ (hNorm E4 U + hNorm E4 V) ^ 4 := by
  set A : Fin 4 → I → I → ℝ := ![U, U, V, V] with hA
  set B : Fin 4 → I → I → ℝ := ![U, V, U, V] with hB
  have hAk : ∀ i : Fin 4, IsKernel (A i) := by
    intro i; fin_cases i <;> simpa [hA]
  have hBk : ∀ i : Fin 4, IsKernel (B i) := by
    intro i; fin_cases i <;> simpa [hB]
  set k : Fin 4 → I × I → ℝ := fun i q => kk2 (A i) (B i) q.1 q.2 with hk
  have hW := Section2Aux.isKernel_add hU hV
  rw [tb_eq_Q hW]
  have e : ∀ q : I × I, kk2 (fun x y => U x y + V x y) (fun x y => U x y + V x y) q.1 q.2 *
      kk2 (fun x y => U x y + V x y) (fun x y => U x y + V x y) q.1 q.2 =
      ∑ i, ∑ j, k i q * k j q := by
    intro q; rw [kk2_expand hU hV, Finset.sum_mul_sum]
  have hint : ∀ i j, Integrable (fun q => k i q * k j q) ν := by
    intro i j
    obtain ⟨Ma, hMa⟩ := (hAk i).2
    obtain ⟨Mb, hMb⟩ := (hBk i).2
    obtain ⟨Mc, hMc⟩ := (hAk j).2
    obtain ⟨Md, hMd⟩ := (hBk j).2
    exact integrable_mul_of_bdd (kk2_meas (hAk i) (hBk i)) (kk2_meas (hAk j) (hBk j))
      (fun q => kk2_bound hMa hMb q.1 q.2) (fun q => kk2_bound hMc hMd q.1 q.2)
  have hQ : Q (fun x y => U x y + V x y) (fun x y => U x y + V x y)
      (fun x y => U x y + V x y) (fun x y => U x y + V x y) =
      ∑ i, ∑ j, Q (A i) (B i) (A j) (B j) := by
    unfold Q
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
  rw [hQ]
  calc ∑ i, ∑ j, Q (A i) (B i) (A j) (B j)
      ≤ ∑ i, ∑ j, (hNorm E4 (A i) * hNorm E4 (B i)) * (hNorm E4 (A j) * hNorm E4 (B j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (le_abs_self _).trans ((abs_Q_le (hAk i) (hBk i) (hAk j) (hBk j)).trans_eq (by ring))
    _ = (∑ i, hNorm E4 (A i) * hNorm E4 (B i)) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ = _ := by simp [Fin.sum_univ_four, hA, hB]; ring

/-! ## `C₄ = K_{2,2}` is norming -/

/-- **Witness for `IsNorming`**: `C₄ = K_{2,2}`, with the bipartition into its two sides of size
two, is norming; `‖W‖_{C₄} = t_bi(C₄, W)^{1/4}` is a norm on all kernels. Proved directly by the
two Cauchy–Schwarz steps `Q(a,b,c,d)² ≤ Q(a,b,a,b) Q(c,d,c,d)` (grouping along `Y`) and
`Q(a,b,a,b)² ≤ t(a) t(b)` (grouping along `X`); definiteness from `|∫_{S×T} W|⁴ ≤ t_bi(C₄, W)`. -/
theorem isNorming_K22 : IsNorming (Finset.univ : Finset (Fin 2 × Fin 2)) := by
  have hne : 0 < E4.card := by rw [card_E4]; norm_num
  refine ⟨fun U _ c => Section2Aux.hNorm_smul E4 hne U c, fun U V hU hV => ?_, fun U hU h => ?_⟩
  · refine Section2Aux.hNorm_le_of E4 hne _
      (add_nonneg (Section2Aux.hNorm_nonneg E4 U) (Section2Aux.hNorm_nonneg E4 V)) ?_
    rw [card_E4, abs_of_nonneg (tb_nonneg (Section2Aux.isKernel_add hU hV))]
    exact tb_add_le hU hV
  · have ht : tb E4 U = 0 := by rw [tb_eq_pow hU, h]; norm_num
    have hrect : ∀ S T : Set I, MeasurableSet S → MeasurableSet T →
        ∫ p in S ×ˢ T, U p.1 p.2 = 0 := by
      intro S T hS hT
      have h4 := S1CutDist.rect_pow4_le hU hS hT
      rw [ht] at h4
      exact (pow_eq_zero_iff (n := 4) (by norm_num)).1 (le_antisymm h4 (by positivity))
    exact S1Bridges.ae_zero_of_rect hU hrect

/-- **Witness for `StrictConvexOnKernels`**: `t_bi(K_{2,2}, ·)` is strictly convex on all
(bounded measurable) kernels, via the proved Lemma 2.3(2) (`lemma_2_3_2`). -/
theorem strictConvexOnKernels_K22 : StrictConvexOnKernels (Finset.univ : Finset (Fin 2 × Fin 2)) :=
  (lemma_2_3_2 E4 (by rw [card_E4]; norm_num)).1 isNorming_K22

/-- **Witness for the hypotheses of `Section2Aux.strict_to_norming`** (`0 < E.card` and
`StrictConvexOnKernels E`): both hold for `E = K_{2,2}`. -/
theorem strict_to_norming_hyps_K22 :
    0 < (Finset.univ : Finset (Fin 2 × Fin 2)).card ∧
      StrictConvexOnKernels (Finset.univ : Finset (Fin 2 × Fin 2)) :=
  ⟨by rw [card_E4]; norm_num, strictConvexOnKernels_K22⟩

/-- The conclusion of `Section2Aux.strict_to_norming` on the witness bundle (consistency
check: it returns `isNorming_K22` again). -/
theorem strict_to_norming_applied_K22 : IsNorming (Finset.univ : Finset (Fin 2 × Fin 2)) :=
  Section2Aux.strict_to_norming _ strict_to_norming_hyps_K22.1 strict_to_norming_hyps_K22.2

/-! ## The 4-cycle as an undirected graph -/

lemma isNorming_map_equiv {X Y X' Y' : Type*} [Fintype X] [Fintype Y] [Fintype X']
    [Fintype Y'] (e1 : X ≃ X') (e2 : Y ≃ Y') (E : Finset (X × Y)) :
    IsNorming (E.map (e1.prodCongr e2).toEmbedding) ↔ IsNorming E := by
  have : hNorm (E.map (e1.prodCongr e2).toEmbedding) = hNorm E := by
    funext U
    simp only [hNorm, Section1Aux.tb_map_equiv, Finset.card_map]
  unfold IsNorming
  rw [this]

/-- The bipartition of `K_{2,2}` into its two sides. -/
def leftSide22 : Fin 2 ⊕ Fin 2 → Prop := fun v => v.isLeft = true

lemma isBipartition_leftSide22 :
    IsBipartition (completeBipartiteGraph (Fin 2) (Fin 2)) leftSide22 := by
  intro u v h
  simp only [completeBipartiteGraph_adj] at h
  simp only [leftSide22]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, Sum.isLeft_eq_false.mpr h2]
  · rw [Sum.isLeft_eq_false.mpr h1]; simp [h2]

/-- `Fin 2` is the left side. -/
def eL22 : Fin 2 ≃ {v : Fin 2 ⊕ Fin 2 // leftSide22 v} where
  toFun i := ⟨Sum.inl i, rfl⟩
  invFun v := v.1.getLeft v.2
  left_inv i := rfl
  right_inv := by
    rintro ⟨v, h⟩
    cases v with
    | inl i => rfl
    | inr j => simp [leftSide22] at h

/-- `Fin 2` is the right side. -/
def eR22 : Fin 2 ≃ {v : Fin 2 ⊕ Fin 2 // ¬ leftSide22 v} where
  toFun j := ⟨Sum.inr j, by simp [leftSide22]⟩
  invFun v := v.1.getRight (by have := v.2; simp only [leftSide22] at this; simpa using this)
  left_inv j := rfl
  right_inv := by
    rintro ⟨v, h⟩
    cases v with
    | inl i => simp [leftSide22] at h
    | inr j => rfl

/-- **Witness for `IsNormingGraph`**: the 4-cycle `C₄ = K_{2,2}` (as the undirected graph
`completeBipartiteGraph (Fin 2) (Fin 2)`) is norming, for the bipartition into its two sides. -/
theorem isNormingGraph_K22 : IsNormingGraph (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  refine ⟨leftSide22, isBipartition_leftSide22, ?_⟩
  let _ := Classical.decPred leftSide22
  have hE : sideEdges (completeBipartiteGraph (Fin 2) (Fin 2)) leftSide22 =
      (Finset.univ : Finset (Fin 2 × Fin 2)).map (eL22.prodCongr eR22).toEmbedding := by
    ext p
    rw [Section1Aux.mem_sideEdges]
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Equiv.coe_toEmbedding,
      Equiv.prodCongr_apply]
    constructor
    · intro _
      exact ⟨(eL22.symm p.1, eR22.symm p.2), by simp⟩
    · intro _
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
      simp only [leftSide22] at ha hb
      simp only [completeBipartiteGraph_adj]
      left
      exact ⟨ha, by simpa using hb⟩
  rw [hE, isNorming_map_equiv]
  exact isNorming_K22

/-- The parity bipartition of `cycleGraph 4` (vertices `0, 2` against `1, 3`). -/
def evenSide : Fin 4 → Prop := fun v => v.val % 2 = 0

lemma isBipartition_evenSide : IsBipartition (SimpleGraph.cycleGraph 4) evenSide := by
  intro u v h
  rw [SimpleGraph.cycleGraph_adj] at h
  unfold evenSide
  revert u v; decide

lemma card_evenSide : (letI := Classical.decPred evenSide; Fintype.card {v // evenSide v}) = 2 := by
  have : Fintype.card {v : Fin 4 // v.val % 2 = 0} = 2 := by decide
  convert this; rfl

lemma card_oddSide :
    (letI := Classical.decPred evenSide; Fintype.card {v // ¬ evenSide v}) = 2 := by
  have : Fintype.card {v : Fin 4 // ¬ v.val % 2 = 0} = 2 := by decide
  convert this; rfl

lemma sideEdges_cycle4 :
    (letI := Classical.decPred evenSide;
      sideEdges (SimpleGraph.cycleGraph 4) evenSide = Finset.univ) := by
  let _ := Classical.decPred evenSide
  ext p
  rw [Section1Aux.mem_sideEdges]
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  simp only [evenSide] at ha hb ⊢
  rw [SimpleGraph.cycleGraph_adj]
  revert a b; decide

/-- **Witness for `IsNormingGraph`** (Mathlib's cycle graph): the 4-cycle `cycleGraph 4` is
norming, for the parity bipartition `{0, 2} ∪ {1, 3}`. -/
theorem isNormingGraph_cycle4 : IsNormingGraph (SimpleGraph.cycleGraph 4) := by
  refine ⟨evenSide, isBipartition_evenSide, ?_⟩
  let _ := Classical.decPred evenSide
  show IsNorming (sideEdges (SimpleGraph.cycleGraph 4) evenSide)
  rw [sideEdges_cycle4]
  set e1 : Fin 2 ≃ {v // evenSide v} := (Fintype.equivFinOfCardEq card_evenSide).symm
  set e2 : Fin 2 ≃ {v // ¬ evenSide v} := (Fintype.equivFinOfCardEq card_oddSide).symm
  rw [← Finset.map_univ_equiv (e1.prodCongr e2), isNorming_map_equiv]
  exact isNorming_K22

/-! ## Target 2: `StructLT` is satisfiable (conditional on DGHRR Fact 2.17) -/

/-- The graphon `W(x, y) = (x + y)/2`. -/
noncomputable def avgW : I → I → ℝ := fun x y => ((x : ℝ) + (y : ℝ)) / 2

lemma isSymmGraphon_avgW : IsSymmGraphon avgW := by
  refine ⟨⟨?_, fun x y => ?_⟩, fun x y => by simp only [avgW]; ring⟩
  · exact ((continuous_subtype_val.measurable.comp measurable_fst).add
      (continuous_subtype_val.measurable.comp measurable_snd)).div_const _
  · have := x.2.1; have := x.2.2; have := y.2.1; have := y.2.2
    simp only [avgW, mem_Icc]; constructor <;> linarith

lemma isGraphon_of_symm {U : I → I → ℝ} (hU : IsSymmGraphon U) : IsGraphon volume U :=
  ⟨hU.1, Eventually.of_forall fun p => hU.2 p.1 p.2⟩

lemma isKernel_of_digraphon {U : I → I → ℝ} (hU : IsDigraphon U) : IsKernel U :=
  ⟨hU.1, 1, fun x y => by
    rw [abs_of_nonneg (hU.2 x y).1]; exact (hU.2 x y).2⟩

lemma not_ae_val_eq (c : ℝ) : ¬ ∀ᵐ y : I ∂volume, (y : ℝ) = c := by
  intro h3
  have hnull : (volume : Measure I) {x : I | (x : ℝ) = c} = 0 := by
    by_cases hc : ∃ x : I, (x : ℝ) = c
    · obtain ⟨x0, hx0⟩ := hc
      refine measure_mono_null (fun x (hx : (x : ℝ) = c) => ?_) (measure_singleton x0)
      exact Subtype.ext (hx.trans hx0.symm)
    · have : {x : I | (x : ℝ) = c} = ∅ := by
        ext x; simp only [mem_empty_iff_false, iff_false]; exact fun hx => hc ⟨x, hx⟩
      rw [this, measure_empty]
  have h4 : (volume : Measure I) {x : I | ¬ (x : ℝ) = c} = 0 := ae_iff.1 h3
  have : (volume : Measure I) univ = 0 := by
    refine measure_mono_null (fun x _ => ?_) (measure_union_null hnull h4)
    by_cases hx : (x : ℝ) = c
    · exact Or.inl hx
    · exact Or.inr hx
  simp at this

lemma avgW_not_const (c : ℝ) : ¬ ∀ᵐ p ∂(volume : Measure (I × I)), avgW p.1 p.2 = c := by
  intro h
  rw [Measure.volume_eq_prod] at h
  have h2 := Measure.ae_ae_of_ae_prod h
  obtain ⟨x, hx⟩ := h2.exists
  refine not_ae_val_eq (2 * c - x) ?_
  filter_upwards [hx] with y hy
  simp only [avgW] at hy
  linarith

/-- The trivial partition `{[0,1]}`. -/
noncomputable def trivPart : PosPartition (volume : Measure I) where
  k := 1
  part := fun _ => univ
  measurableSet_part := fun _ => MeasurableSet.univ
  pos := fun _ => by rw [measure_univ]; exact one_pos
  disjoint := fun i j h => absurd (Subsingleton.elim i j) h
  cover := Set.iUnion_const _

/-- The mean `∫ W` of `avgW`. -/
noncomputable def meanW : ℝ := ∫ p, avgW p.1 p.2 ∂((volume : Measure I).prod volume)

lemma stepAvg_trivPart (x y : I) : stepAvg trivPart avgW x y = meanW := by
  simp only [stepAvg, trivPart, meanW, Set.indicator_univ, Measure.restrict_univ,
    univ_prod_univ, measure_univ, ENNReal.toReal_one, mul_one, div_one, one_mul]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (@Finset.univ (Fin 1) (Fin.fintype trivPart.k)).card = 1 := rfl
  rw [hc]
  simp

lemma meanW_mem : meanW ∈ Icc (0 : ℝ) 1 := by
  have hk := isKernel_of_digraphon isSymmGraphon_avgW.1
  have hint : Integrable (fun p : I × I => avgW p.1 p.2) ((volume : Measure I).prod volume) := by
    obtain ⟨M, hM⟩ := hk.2
    exact S1CutDist.integrable_bdd hk.1 M fun p => hM _ _
  refine ⟨integral_nonneg fun p => (isSymmGraphon_avgW.1.2 _ _).1, ?_⟩
  calc meanW ≤ ∫ _p : I × I, (1 : ℝ) ∂((volume : Measure I).prod volume) :=
        integral_mono hint (integrable_const _) fun p => (isSymmGraphon_avgW.1.2 _ _).2
    _ = 1 := by simp

/-- The constant graphon with value `∫ W`. -/
noncomputable def constW : I → I → ℝ := fun _ _ => meanW

lemma isSymmGraphon_constW : IsSymmGraphon constW :=
  ⟨⟨measurable_const, fun _ _ => meanW_mem⟩, fun _ _ => rfl⟩

/-- Members of the envelope of the constant graphon have the rectangle integrals of the
constant. -/
lemma rect_of_mem_envelope_const {V : I → I → ℝ} (hV : V ∈ envelope constW) (A B : Set I)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ p in A ×ˢ B, V p.1 p.2 = ∫ p in A ×ˢ B, constW p.1 p.2 := by
  obtain ⟨-, φ, hφ⟩ := hV
  have := hφ A B hA hB
  have e : (fun n => ∫ p in A ×ˢ B, pullback (φ n).1 constW p.1 p.2) =
      fun _ => ∫ p in A ×ˢ B, constW p.1 p.2 := rfl
  rw [e] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

/-- `W = avgW` is not in the envelope of the constant: it is not a.e. constant. -/
lemma avgW_not_mem_envelope_const : avgW ∉ envelope constW := by
  intro h
  have hk : IsKernel (fun x y => avgW x y - constW x y) :=
    Section2Aux.isKernel_add (isKernel_of_digraphon isSymmGraphon_avgW.1)
      (Section2Aux.isKernel_neg (Section2Aux.isKernel_const meanW))
  have hrect : ∀ S T : Set I, MeasurableSet S → MeasurableSet T →
      ∫ p in S ×ˢ T, (avgW p.1 p.2 - constW p.1 p.2) = 0 := by
    intro S T hS hT
    rw [integral_sub (f := fun p : I × I => avgW p.1 p.2) (g := fun p : I × I => constW p.1 p.2)
      (S1Bridges.intOn (isKernel_of_digraphon isSymmGraphon_avgW.1) _)
      (S1Bridges.intOn (Section2Aux.isKernel_const meanW : IsKernel constW) _),
      rect_of_mem_envelope_const h S T hS hT, sub_self]
  have hae := S1Bridges.ae_zero_of_rect hk hrect
  refine avgW_not_const meanW ?_
  filter_upwards [hae] with p hp
  simp only [constW] at hp
  linarith

/-- If the constant lies in `⟨W⟩`, then `⟨const⟩ ⊆ ⟨W⟩`. -/
lemma envelope_const_subset (h : constW ∈ envelope avgW) : envelope constW ⊆ envelope avgW := by
  intro V hV
  obtain ⟨-, φ, hφ⟩ := h
  refine ⟨hV.1, φ, fun A B hA hB => ?_⟩
  rw [rect_of_mem_envelope_const hV A B hA hB]
  exact hφ A B hA hB

/-- The unconditional reduction: a single mixing sequence of measure-preserving bijections
(`W^{φ_n} → ∫ W` weak\*) gives `StructLT constW avgW`. This isolates exactly what the
conditional witness below takes from the literature. -/
theorem structLT_const_avgW_of_mixing
    (hmix : ∃ φ : ℕ → MPBij, WeakStarTendsto (fun n => pullback (φ n).1 avgW) constW) :
    StructLT constW avgW := by
  obtain ⟨φ, hφ⟩ := hmix
  have hmem : constW ∈ envelope avgW := ⟨isGraphon_of_symm isSymmGraphon_constW, φ, hφ⟩
  rw [StructLT, Set.ssubset_def]
  refine ⟨envelope_const_subset hmem, fun hsub => avgW_not_mem_envelope_const ?_⟩
  exact hsub (S1CutDist.mem_envelope_self (isGraphon_of_symm isSymmGraphon_avgW))

/-- **Witness that `StructLT` (hence the hypothesis of `CutDistIdentifying`) can hold**,
conditional on the literature fact `DGHRRFact217Hyp` (DGHRR Fact 2.17 = DGHRR companion paper
Lemma 4.2(b): `W^𝒫 ∈ ⟨W⟩`), applied to the trivial partition: the constant graphon
`∫ W` is strictly below `W(x, y) = (x + y)/2` in the structural order. -/
theorem structLT_const_avgW (hF : DGHRRFact217Hyp) : StructLT constW avgW := by
  have hmem : constW ∈ envelope avgW := by
    have h := hF avgW isSymmGraphon_avgW trivPart
    have e : stepAvg trivPart avgW = constW := by
      funext x y; exact stepAvg_trivPart x y
    rwa [e] at h
  obtain ⟨-, φ, hφ⟩ := hmem
  exact structLT_const_avgW_of_mixing ⟨φ, hφ⟩

/-- **Non-vacuity of `CutDistIdentifying`** (conditional on `DGHRRFact217Hyp`): there are
graphons `U, W` with `StructLT U W`, so `CutDistIdentifying θ` is a genuine constraint. -/
theorem exists_structLT (hF : DGHRRFact217Hyp) :
    ∃ U W : I → I → ℝ, IsGraphon volume U ∧ IsGraphon volume W ∧ StructLT U W :=
  ⟨constW, avgW, isGraphon_of_symm isSymmGraphon_constW,
    isGraphon_of_symm isSymmGraphon_avgW, structLT_const_avgW hF⟩

/-- **Non-vacuity of `CutDistIdentifying`** (conditional on `DGHRRFact217Hyp`): the constant
parameter `θ = 0` is not cut distance identifying. -/
theorem not_cutDistIdentifying_zero (hF : DGHRRFact217Hyp) :
    ¬ CutDistIdentifying (fun _ => (0 : ℝ)) := by
  intro h
  exact lt_irrefl (0 : ℝ) (h constW avgW (isGraphon_of_symm isSymmGraphon_constW)
    (isGraphon_of_symm isSymmGraphon_avgW) (structLT_const_avgW hF))

end Witnesses

end NieWeiOrientedSidorenko
