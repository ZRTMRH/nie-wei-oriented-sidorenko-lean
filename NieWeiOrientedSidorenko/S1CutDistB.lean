import NieWeiOrientedSidorenko.Section1Aux

/-!
# Tools for Theorem 1.4: step averages, the cut norm, the counting lemma

Generic material for `S1CutDist.lean` (which imports this file).
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace S1CutDist

lemma meas_app {β : Type*} [MeasurableSpace β] {f : I → I → ℝ}
    (hf : Measurable (Function.uncurry f)) {a b : β → I} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun z => f (a z) (b z)) := hf.comp (ha.prodMk hb)

lemma integrable_bdd {β : Type*} [MeasurableSpace β] {μ : Measure β} [IsFiniteMeasure μ]
    {φ : β → ℝ} (hφ : Measurable φ) (C : ℝ) (h : ∀ x, |φ x| ≤ C) : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact h x)

/-! ## Step averages -/

section StepAvg

variable (P : PosPartition (volume : Measure I))

/-- The value of `U^𝒫` on `P_i × P_j`. -/
noncomputable def avgV (U : I → I → ℝ) (i j : Fin P.k) : ℝ :=
  (∫ p in P.part i ×ˢ P.part j, U p.1 p.2 ∂((volume : Measure I).prod volume)) /
    (((volume : Measure I) (P.part i)).toReal * ((volume : Measure I) (P.part j)).toReal)

lemma stepAvg_eq_of_mem (U : I → I → ℝ) {x y : I} {i j : Fin P.k} (hx : x ∈ P.part i)
    (hy : y ∈ P.part j) : stepAvg P U x y = avgV P U i j := by
  unfold stepAvg
  have e : ∀ i', ∑ j', (P.part i').indicator (fun _ => (1 : ℝ)) x *
      (P.part j').indicator (fun _ => (1 : ℝ)) y * avgV P U i' j' =
      (P.part i').indicator (fun _ => (1 : ℝ)) x * avgV P U i' j := by
    intro i'
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, Section2Aux.indicator_sum P.part P.disjoint hy]
  change ∑ i', ∑ j', (P.part i').indicator (fun _ => (1 : ℝ)) x *
      (P.part j').indicator (fun _ => (1 : ℝ)) y * avgV P U i' j' = _
  simp_rw [e]
  exact Section2Aux.indicator_sum P.part P.disjoint hx _

lemma exists_part (x : I) : ∃ i, x ∈ P.part i := Section2Aux.pp_exists_mem P x

lemma measure_part_pos (i : Fin P.k) : 0 < ((volume : Measure I) (P.part i)).toReal :=
  ENNReal.toReal_pos (P.pos i).ne' (measure_ne_top _ _)

lemma measurable_stepAvg (U : I → I → ℝ) : Measurable (Function.uncurry (stepAvg P U)) := by
  unfold stepAvg
  have : Function.uncurry (fun x y => ∑ i, ∑ j, (P.part i).indicator (fun _ => (1 : ℝ)) x *
      (P.part j).indicator (fun _ => (1 : ℝ)) y *
      ((∫ p in P.part i ×ˢ P.part j, U p.1 p.2 ∂((volume : Measure I).prod volume)) /
        (((volume : Measure I) (P.part i)).toReal * ((volume : Measure I) (P.part j)).toReal))) =
      fun q : I × I => ∑ i, ∑ j, (P.part i).indicator (fun _ => (1 : ℝ)) q.1 *
      (P.part j).indicator (fun _ => (1 : ℝ)) q.2 *
      ((∫ p in P.part i ×ˢ P.part j, U p.1 p.2 ∂((volume : Measure I).prod volume)) /
        (((volume : Measure I) (P.part i)).toReal * ((volume : Measure I) (P.part j)).toReal)) := by
    funext q; rfl
  rw [this]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  refine Measurable.mul (Measurable.mul ?_ ?_) measurable_const
  · exact (measurable_const.indicator (P.measurableSet_part i)).comp measurable_fst
  · exact (measurable_const.indicator (P.measurableSet_part j)).comp measurable_snd

lemma integrableOn_of_digraphon {U : I → I → ℝ} (hU : IsDigraphon U) (s : Set (I × I)) :
    IntegrableOn (fun p : I × I => U p.1 p.2) s ((volume : Measure I).prod volume) := by
  refine Integrable.integrableOn ?_
  refine Integrable.of_bound hU.1.aestronglyMeasurable 1 (Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hU.2 _ _).1]; exact (hU.2 _ _).2

lemma integrable_of_kernel {U : I → I → ℝ} (hU : IsKernel U) :
    Integrable (fun p : I × I => U p.1 p.2) ((volume : Measure I).prod volume) := by
  obtain ⟨hm, M, hM⟩ := hU
  exact Integrable.of_bound hm.aestronglyMeasurable M
    (Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hM _ _)

lemma avgV_mem {U : I → I → ℝ} (hU : IsDigraphon U) (i j : Fin P.k) :
    avgV P U i j ∈ Icc (0 : ℝ) 1 := by
  unfold avgV
  have hpos := mul_pos (measure_part_pos P i) (measure_part_pos P j)
  have hrect : ((volume : Measure I).prod volume).real (P.part i ×ˢ P.part j) =
      ((volume : Measure I) (P.part i)).toReal * ((volume : Measure I) (P.part j)).toReal := by
    rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  constructor
  · refine div_nonneg (setIntegral_nonneg ((P.measurableSet_part i).prod (P.measurableSet_part j))
      fun q _ => (hU.2 _ _).1) hpos.le
  · rw [div_le_one hpos]
    calc ∫ p in P.part i ×ˢ P.part j, U p.1 p.2 ∂((volume : Measure I).prod volume)
        ≤ ∫ p in P.part i ×ˢ P.part j, (1 : ℝ) ∂((volume : Measure I).prod volume) :=
          setIntegral_mono (integrableOn_of_digraphon hU _) (integrableOn_const (measure_ne_top _ _))
            fun q => (hU.2 _ _).2
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one, hrect]

lemma isDigraphon_stepAvg {U : I → I → ℝ} (hU : IsDigraphon U) : IsDigraphon (stepAvg P U) := by
  refine ⟨measurable_stepAvg P U, fun x y => ?_⟩
  obtain ⟨i, hi⟩ := exists_part P x
  obtain ⟨j, hj⟩ := exists_part P y
  rw [stepAvg_eq_of_mem P U hi hj]
  exact avgV_mem P hU i j

lemma avgV_symm {U : I → I → ℝ} (hU : ∀ x y, U x y = U y x) (i j : Fin P.k) :
    avgV P U i j = avgV P U j i := by
  unfold avgV
  rw [mul_comm (((volume : Measure I) (P.part i)).toReal)]
  congr 1
  rw [← setIntegral_prod_swap (P.part j) (P.part i)]
  simp only [Prod.fst_swap, Prod.snd_swap]
  simp_rw [hU]

lemma stepAvg_symm {U : I → I → ℝ} (hU : ∀ x y, U x y = U y x) (x y : I) :
    stepAvg P U x y = stepAvg P U y x := by
  obtain ⟨i, hi⟩ := exists_part P x
  obtain ⟨j, hj⟩ := exists_part P y
  rw [stepAvg_eq_of_mem P U hi hj, stepAvg_eq_of_mem P U hj hi, avgV_symm P hU]

lemma avgV_lin {U V : I → I → ℝ} (hU : IsKernel U) (hV : IsKernel V) (a b : ℝ) (i j : Fin P.k) :
    avgV P (fun x y => a * U x y + b * V x y) i j = a * avgV P U i j + b * avgV P V i j := by
  unfold avgV
  rw [integral_add ((integrable_of_kernel hU).integrableOn.const_mul a)
      ((integrable_of_kernel hV).integrableOn.const_mul b), integral_const_mul,
    integral_const_mul]
  ring

lemma stepAvg_lin {U V : I → I → ℝ} (hU : IsKernel U) (hV : IsKernel V) (a b : ℝ) :
    stepAvg P (fun x y => a * U x y + b * V x y) =
      fun x y => a * stepAvg P U x y + b * stepAvg P V x y := by
  funext x y
  obtain ⟨i, hi⟩ := exists_part P x
  obtain ⟨j, hj⟩ := exists_part P y
  rw [stepAvg_eq_of_mem P _ hi hj, stepAvg_eq_of_mem P _ hi hj, stepAvg_eq_of_mem P _ hi hj,
    avgV_lin P hU hV]

lemma avgV_stepAvg (U : I → I → ℝ) (i j : Fin P.k) :
    avgV P (stepAvg P U) i j = avgV P U i j := by
  have hc : ∫ p in P.part i ×ˢ P.part j, stepAvg P U p.1 p.2 ∂((volume : Measure I).prod volume) =
      ∫ p in P.part i ×ˢ P.part j, avgV P U i j ∂((volume : Measure I).prod volume) :=
    setIntegral_congr_fun ((P.measurableSet_part i).prod (P.measurableSet_part j))
      fun q hq => stepAvg_eq_of_mem P U hq.1 hq.2
  have hpos := mul_pos (measure_part_pos P i) (measure_part_pos P j)
  conv_lhs => unfold avgV
  rw [hc, setIntegral_const, smul_eq_mul, measureReal_def, Measure.prod_prod,
    ENNReal.toReal_mul, mul_div_cancel_left₀ _ hpos.ne']

lemma stepAvg_stepAvg (U : I → I → ℝ) : stepAvg P (stepAvg P U) = stepAvg P U := by
  funext x y
  obtain ⟨i, hi⟩ := exists_part P x
  obtain ⟨j, hj⟩ := exists_part P y
  rw [stepAvg_eq_of_mem P _ hi hj, stepAvg_eq_of_mem P _ hi hj, avgV_stepAvg]

end StepAvg

/-! ## The cut norm -/

section CutNorm

/-- The set whose supremum is the cut norm. -/
def cutSet (F : I → I → ℝ) : Set ℝ :=
  {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧ r = |∫ p in S ×ˢ T, F p.1 p.2|}

lemma cutNorm_eq (F : I → I → ℝ) : cutNorm F = sSup (cutSet F) := rfl

lemma cutSet_nonempty (F : I → I → ℝ) : (cutSet F).Nonempty :=
  ⟨_, ∅, ∅, MeasurableSet.empty, MeasurableSet.empty, rfl⟩

lemma abs_setIntegral_le {F : I → I → ℝ} {M : ℝ} (hM : ∀ x y, |F x y| ≤ M) (s : Set (I × I)) :
    |∫ p in s, F p.1 p.2 ∂((volume : Measure I).prod volume)| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := ((volume : Measure I).prod volume).restrict s)
    (f := fun p : I × I => F p.1 p.2) (C := M)
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hM _ _)
  rw [Real.norm_eq_abs] at h
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (0 : I) (0 : I))
  refine h.trans ?_
  have : (((volume : Measure I).prod volume).restrict s).real univ ≤ 1 := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    have := prob_le_one (μ := (volume : Measure I).prod volume) (s := s)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  nlinarith

lemma cutSet_bdd {F : I → I → ℝ} {M : ℝ} (hM : ∀ x y, |F x y| ≤ M) : BddAbove (cutSet F) :=
  ⟨M, by rintro r ⟨S, T, -, -, rfl⟩; exact abs_setIntegral_le hM _⟩

lemma le_cutNorm {F : I → I → ℝ} {M : ℝ} (hM : ∀ x y, |F x y| ≤ M) {S T : Set I}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |∫ p in S ×ˢ T, F p.1 p.2| ≤ cutNorm F :=
  le_csSup (cutSet_bdd hM) ⟨S, T, hS, hT, rfl⟩

lemma cutNorm_le {F : I → I → ℝ} {c : ℝ}
    (h : ∀ S T : Set I, MeasurableSet S → MeasurableSet T → |∫ p in S ×ˢ T, F p.1 p.2| ≤ c) :
    cutNorm F ≤ c :=
  csSup_le (cutSet_nonempty F) (by rintro r ⟨S, T, hS, hT, rfl⟩; exact h S T hS hT)

lemma cutNorm_nonneg {F : I → I → ℝ} {M : ℝ} (hM : ∀ x y, |F x y| ≤ M) : 0 ≤ cutNorm F :=
  (abs_nonneg _).trans (le_cutNorm hM MeasurableSet.empty MeasurableSet.empty)


/-- The bilinear test `∫ F(x, y) f(x) g(y)`. -/
noncomputable def bil (F : I → I → ℝ) (f g : I → ℝ) : ℝ :=
  ∫ p : I × I, F p.1 p.2 * f p.1 * g p.2 ∂((volume : Measure I).prod volume)

lemma bil_rect (F : I → I → ℝ) {S T : Set I} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    bil F (S.indicator 1) (T.indicator 1) = ∫ p in S ×ˢ T, F p.1 p.2 := by
  unfold bil
  rw [← integral_indicator (hS.prod hT)]
  congr 1
  funext p
  by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ T <;>
    simp [Set.indicator, Set.mem_prod, h1, h2]

/-- Bounded measurable kernels. -/
def BK (F : I → I → ℝ) : Prop := Measurable (Function.uncurry F) ∧ ∃ M, ∀ x y, |F x y| ≤ M

/-- Test functions bounded by one in absolute value. -/
def T1 (f : I → ℝ) : Prop := Measurable f ∧ ∀ x, |f x| ≤ 1

lemma t1_indicator {S : Set I} (hS : MeasurableSet S) : T1 (S.indicator 1) :=
  ⟨measurable_one.indicator hS, fun x => by
    by_cases h : x ∈ S <;> simp [Set.indicator, h]⟩

lemma cutNorm_lin_le {F G : I → I → ℝ} (hF : BK F) (hG : BK G) (a b : ℝ) :
    cutNorm (fun x y => a * F x y + b * G x y) ≤ |a| * cutNorm F + |b| * cutNorm G := by
  obtain ⟨M, hM⟩ := hF.2
  obtain ⟨N, hN⟩ := hG.2
  refine cutNorm_le fun S T hS hT => ?_
  have hFi : IntegrableOn (fun p : I × I => F p.1 p.2) (S ×ˢ T) (volume : Measure (I × I)) :=
    (integrable_bdd hF.1 M fun p => hM p.1 p.2).integrableOn
  have hGi : IntegrableOn (fun p : I × I => G p.1 p.2) (S ×ˢ T) (volume : Measure (I × I)) :=
    (integrable_bdd hG.1 N fun p => hN p.1 p.2).integrableOn
  rw [integral_add (hFi.const_mul a) (hGi.const_mul b), integral_const_mul, integral_const_mul]
  calc |(a * ∫ p in S ×ˢ T, F p.1 p.2) + b * ∫ p in S ×ˢ T, G p.1 p.2|
      ≤ |a| * |∫ p in S ×ˢ T, F p.1 p.2| + |b| * |∫ p in S ×ˢ T, G p.1 p.2| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ _ := by
        gcongr
        · exact le_cutNorm hM hS hT
        · exact le_cutNorm hN hS hT

lemma integrable_bil {F : I → I → ℝ} (hF : BK F) {f g : I → ℝ} (hf : T1 f) (hg : T1 g) :
    Integrable (fun p : I × I => F p.1 p.2 * f p.1 * g p.2) ((volume : Measure I).prod volume) := by
  obtain ⟨hm, M, hM⟩ := hF
  refine integrable_bdd ((hm.mul (hf.1.comp measurable_fst)).mul (hg.1.comp measurable_snd)) M
    fun p => ?_
  rw [abs_mul, abs_mul]
  have h1 := hf.2 p.1; have h2 := hg.2 p.2; have h3 := hM p.1 p.2
  have := abs_nonneg (F p.1 p.2)
  calc |F p.1 p.2| * |f p.1| * |g p.2| ≤ |F p.1 p.2| * 1 * 1 := by gcongr
    _ ≤ M := by linarith

/-- For `|f| ≤ 1`, `|∫ f h| ≤ |∫_{h > 0} h| + |∫_{h ≤ 0} h|`. -/
lemma abs_int_mul_le {h f : I → ℝ} (hhm : Measurable h) (hh : Integrable h) (hf : T1 f) :
    |∫ x, f x * h x| ≤ |∫ x, {x | 0 < h x}.indicator 1 x * h x| +
      |∫ x, {x | 0 < h x}ᶜ.indicator 1 x * h x| := by
  set S := {x | 0 < h x} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hhm
  have hfi : Integrable (fun x => f x * h x) :=
    hh.bdd_mul hf.1.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hf.2 x)
  have hS : ∀ s : Set I, MeasurableSet s → Integrable (fun x => s.indicator 1 x * h x) :=
    fun s hs => hh.bdd_mul (c := 1) (measurable_one.indicator hs).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact (t1_indicator hs).2 x)
  have habs : ∀ x, |h x| = S.indicator 1 x * h x - Sᶜ.indicator 1 x * h x := fun x => by
    by_cases hx : 0 < h x
    · have : x ∈ S := hx
      simp [Set.indicator, this, abs_of_pos hx]
    · have : x ∉ S := hx
      simp [Set.indicator, this, abs_of_nonpos (not_lt.mp hx)]
  calc |∫ x, f x * h x| ≤ ∫ x, |f x * h x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, |h x| := integral_mono hfi.abs hh.abs fun x => by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hf.2 x)
    _ = (∫ x, S.indicator 1 x * h x) - ∫ x, Sᶜ.indicator 1 x * h x := by
        exact (integral_congr_ae (Eventually.of_forall habs)).trans
          (integral_sub (hS S hSm) (hS Sᶜ hSm.compl))
    _ ≤ _ := by
        have := le_abs_self (∫ x, S.indicator 1 x * h x)
        have := neg_le_abs (∫ x, Sᶜ.indicator 1 x * h x)
        linarith

lemma bil_eq_x {F : I → I → ℝ} (hF : BK F) {f g : I → ℝ} (hf : T1 f) (hg : T1 g) :
    bil F f g = ∫ x, f x * ∫ y, F x y * g y := by
  unfold bil
  rw [integral_prod _ (integrable_bil hF hf hg)]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext y; ring

lemma bil_eq_y {F : I → I → ℝ} (hF : BK F) {f g : I → ℝ} (hf : T1 f) (hg : T1 g) :
    bil F f g = ∫ y, g y * ∫ x, F x y * f x := by
  unfold bil
  rw [integral_prod_symm _ (integrable_bil hF hf hg)]
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext x; ring

lemma integrable_inner_x {F : I → I → ℝ} (hF : BK F) {g : I → ℝ} (hg : T1 g) :
    Measurable (fun x => ∫ y, F x y * g y) ∧ Integrable (fun x => ∫ y, F x y * g y) := by
  obtain ⟨hm, M, hM⟩ := hF
  have hmeas : Measurable (fun x => ∫ y, F x y * g y) := by
    have : Measurable (Function.uncurry fun x y => F x y * g y) :=
      hm.mul (hg.1.comp measurable_snd)
    exact (this.stronglyMeasurable.integral_prod_right (ν := (volume : Measure I))).measurable
  refine ⟨hmeas, integrable_bdd hmeas M fun x => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure I))
    (f := fun y => F x y * g y) (C := M) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hg.2 y)).trans (hM x y))
  simpa using h

lemma integrable_inner_y {F : I → I → ℝ} (hF : BK F) {f : I → ℝ} (hf : T1 f) :
    Measurable (fun y => ∫ x, F x y * f x) ∧ Integrable (fun y => ∫ x, F x y * f x) := by
  have hF' : BK (fun y x => F x y) :=
    ⟨hF.1.comp measurable_swap, hF.2.choose, fun y x => hF.2.choose_spec x y⟩
  exact integrable_inner_x hF' hf

/-- The rank-one test bound `|∫ F(x,y) f(x) g(y)| ≤ 4 ‖F‖_□` for `|f|, |g| ≤ 1`. -/
lemma abs_bil_le {F : I → I → ℝ} (hF : BK F) {f g : I → ℝ} (hf : T1 f) (hg : T1 g) :
    |bil F f g| ≤ 4 * cutNorm F := by
  obtain ⟨M, hM⟩ := hF.2
  -- the `y`-side step, for an indicator in `x`
  have hy : ∀ S : Set I, MeasurableSet S → |bil F (S.indicator 1) g| ≤ 2 * cutNorm F := by
    intro S hS
    have hS1 := t1_indicator hS
    obtain ⟨hkm, hki⟩ := integrable_inner_y hF hS1
    rw [bil_eq_y hF hS1 hg]
    refine (abs_int_mul_le hkm hki hg).trans ?_
    set T := {y | 0 < ∫ x, F x y * S.indicator 1 x} with hT
    have hTm : MeasurableSet T := measurableSet_lt measurable_const hkm
    have e : ∀ T' : Set I, MeasurableSet T' →
        ∫ y, T'.indicator 1 y * ∫ x, F x y * S.indicator 1 x = ∫ p in S ×ˢ T', F p.1 p.2 :=
      fun T' hT' => by rw [← bil_eq_y hF hS1 (t1_indicator hT'), bil_rect F hS hT']
    rw [e T hTm, e Tᶜ hTm.compl]
    have := le_cutNorm hM hS hTm; have := le_cutNorm hM hS hTm.compl
    linarith
  obtain ⟨hhm, hhi⟩ := integrable_inner_x hF hg
  rw [bil_eq_x hF hf hg]
  refine (abs_int_mul_le hhm hhi hf).trans ?_
  set S := {x | 0 < ∫ y, F x y * g y} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hhm
  have e : ∀ S' : Set I, MeasurableSet S' →
      ∫ x, S'.indicator 1 x * ∫ y, F x y * g y = bil F (S'.indicator 1) g :=
    fun S' hS' => (bil_eq_x hF (t1_indicator hS') hg).symm
  rw [e S hSm, e Sᶜ hSm.compl]
  have := hy S hSm; have := hy Sᶜ hSm.compl
  linarith

end CutNorm

/-! ## The counting lemma for decorated bipartite densities -/

section Counting

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Kernels bounded by one in absolute value. -/
def K1 (F : I → I → ℝ) : Prop := Measurable (Function.uncurry F) ∧ ∀ x y, |F x y| ≤ 1

lemma k1_bk {F : I → I → ℝ} (h : K1 F) : BK F := ⟨h.1, 1, h.2⟩

lemma mp_glue {V : Type*} [Fintype V] [DecidableEq V] (c : V) :
    MeasurePreserving (fun w : I × ({v // v ≠ c} → I) => Section1Aux.glue c w.1 w.2)
      ((volume : Measure I).prod (Measure.pi fun _ : {v // v ≠ c} => (volume : Measure I)))
      (Measure.pi fun _ : V => (volume : Measure I)) := by
  have hmp := (measurePreserving_piEquivPiSubtypeProd (α := fun _ : V => (I : Type))
    (fun _ => (volume : Measure I)) (fun v => v = c)).symm
  have hu : MeasurePreserving (MeasurableEquiv.funUnique {v // v = c} I).symm
      (volume : Measure I) (@Measure.pi {v // v = c} (fun _ => I) (Subtype.fintype _) _
        (fun _ => (volume : Measure I))) := by
    convert (measurePreserving_funUnique (volume : Measure I) {v // v = c}).symm
  have := hmp.comp (hu.prod (MeasurePreserving.id
    (Measure.pi fun _ : {v // v ≠ c} => (volume : Measure I))))
  convert this using 1
  funext w
  funext v
  simp only [Section1Aux.glue, Function.comp, Prod.map, id,
    MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  split_ifs with h
  · rfl
  · rfl

/-- The coordinate split at an edge `a = (a₁, a₂)`. -/
def splitA (a : X × Y) (w : (I × I) × (({x // x ≠ a.1} → I) × ({y // y ≠ a.2} → I))) :
    (X → I) × (Y → I) :=
  (Section1Aux.glue a.1 w.1.1 w.2.1, Section1Aux.glue a.2 w.1.2 w.2.2)

lemma mp_splitA (a : X × Y) :
    MeasurePreserving (splitA a)
      (((volume : Measure I).prod volume).prod
        ((Measure.pi fun _ : {x // x ≠ a.1} => (volume : Measure I)).prod
          (Measure.pi fun _ : {y // y ≠ a.2} => (volume : Measure I))))
      (Section2Aux.ρ X Y) := by
  have h1 := Section2Aux.mp_prodProdProdComm (volume : Measure I) (volume : Measure I)
    (Measure.pi fun _ : {x // x ≠ a.1} => (volume : Measure I))
    (Measure.pi fun _ : {y // y ≠ a.2} => (volume : Measure I))
  have h2 := (mp_glue (V := X) a.1).prod (mp_glue (V := Y) a.2)
  exact h2.comp h1

lemma glue_eq_of_ne {V : Type*} [DecidableEq V] (c : V) (s s' : I) (y : {v // v ≠ c} → I)
    {v : V} (hv : v ≠ c) : Section1Aux.glue c s y v = Section1Aux.glue c s' y v := by
  simp [Section1Aux.glue, hv]

/-- **The single-edge bound.** If all decorations but the one of `a` are bounded by one, then
`|t_bi(H; R)| ≤ 4 ‖R_a‖_□`. -/
lemma abs_tBiDec_single (E : Finset (X × Y)) {a : X × Y} (ha : a ∈ E) (R : X × Y → I → I → ℝ)
    (hRa : BK (R a)) (hR : ∀ p, p ≠ a → K1 (R p)) :
    |tBiDec volume E R| ≤ 4 * cutNorm (R a) := by
  set W := ((volume : Measure I).prod (volume : Measure I)).prod
    ((Measure.pi fun _ : {x // x ≠ a.1} => (volume : Measure I)).prod
      (Measure.pi fun _ : {y // y ≠ a.2} => (volume : Measure I))) with hW
  set G : (X → I) × (Y → I) → ℝ := fun z => ∏ p ∈ E, R p (z.1 p.1) (z.2 p.2) with hG
  obtain ⟨M, hM⟩ := hRa.2
  have hM' : ∀ p, ∃ C, ∀ x y, |R p x y| ≤ C := fun p => by
    by_cases hp : p = a
    · subst hp; exact ⟨M, hM⟩
    · exact ⟨1, (hR p hp).2⟩
  have hmeasR : ∀ p, Measurable (Function.uncurry (R p)) := fun p => by
    by_cases hp : p = a
    · subst hp; exact hRa.1
    · exact (hR p hp).1
  have hGi : Integrable G (Section2Aux.ρ X Y) :=
    Section2Aux.integrable_prod E R fun p _ => ⟨hmeasR p, hM' p⟩
  have hmp := mp_splitA (X := X) (Y := Y) a
  rw [Section2Aux.tBiDec_eq, ← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hGi.aestronglyMeasurable)]
  · have hGi' : Integrable (fun w => G (splitA a w)) W := hmp.integrable_comp_of_integrable hGi
    rw [integral_prod_symm _ hGi']
    -- the inner integral is a rank-one test
    have hinner : ∀ uv : ({x // x ≠ a.1} → I) × ({y // y ≠ a.2} → I),
        |∫ st : I × I, G (splitA a (st, uv)) ∂((volume : Measure I).prod volume)| ≤
          4 * cutNorm (R a) := by
      intro uv
      set f : I → ℝ := fun s => ∏ p ∈ (E.erase a).filter (fun p => p.1 = a.1),
        R p s (Section1Aux.glue a.2 0 uv.2 p.2) with hf
      set g : I → ℝ := fun t => ∏ p ∈ (E.erase a).filter (fun p => ¬ p.1 = a.1),
        R p (Section1Aux.glue a.1 0 uv.1 p.1) (Section1Aux.glue a.2 t uv.2 p.2) with hg
      have hfg : ∀ st : I × I, G (splitA a (st, uv)) = R a st.1 st.2 * f st.1 * g st.2 := by
        intro st
        simp only [hG, splitA]
        rw [← Finset.mul_prod_erase E _ ha, Section1Aux.glue_self, Section1Aux.glue_self,
          ← Finset.prod_filter_mul_prod_filter_not (E.erase a) (fun p => p.1 = a.1), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun p hp => ?_
          obtain ⟨hpE, hp1⟩ := Finset.mem_filter.mp hp
          have hpa := Finset.ne_of_mem_erase hpE
          have hp2 : p.2 ≠ a.2 := fun h => hpa (Prod.ext hp1 h)
          rw [hp1, Section1Aux.glue_self, glue_eq_of_ne a.2 st.2 0 uv.2 hp2]
        · refine Finset.prod_congr rfl fun p hp => ?_
          obtain ⟨_, hp1⟩ := Finset.mem_filter.mp hp
          rw [glue_eq_of_ne a.1 st.1 0 uv.1 hp1]
      have hT1f : T1 f := by
        refine ⟨Finset.measurable_prod _ fun p hp => ?_, fun s => ?_⟩
        · have hpa := Finset.ne_of_mem_erase (Finset.mem_filter.mp hp).1
          exact meas_app (hR p hpa).1 measurable_id measurable_const
        · rw [hf]; simp only
          rw [Finset.abs_prod]
          exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p hp =>
            (hR p (Finset.ne_of_mem_erase (Finset.mem_filter.mp hp).1)).2 _ _
      have hT1g : T1 g := by
        have hgl : Measurable (fun t : I => Section1Aux.glue a.2 t uv.2) := by
          refine measurable_pi_iff.mpr fun y => ?_
          by_cases hy : y = a.2
          · simp only [Section1Aux.glue, hy, dite_true]; exact measurable_id
          · simp only [Section1Aux.glue, hy, dite_false]; exact measurable_const
        refine ⟨Finset.measurable_prod _ fun p hp => ?_, fun t => ?_⟩
        · have hpa := Finset.ne_of_mem_erase (Finset.mem_filter.mp hp).1
          exact meas_app (hR p hpa).1 measurable_const ((measurable_pi_apply p.2).comp hgl)
        · rw [hg]; simp only
          rw [Finset.abs_prod]
          exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p hp =>
            (hR p (Finset.ne_of_mem_erase (Finset.mem_filter.mp hp).1)).2 _ _
      have e : ∫ st : I × I, G (splitA a (st, uv)) ∂((volume : Measure I).prod volume) =
          bil (R a) f g := by
        unfold bil; exact integral_congr_ae (Eventually.of_forall hfg)
      rw [e]
      exact abs_bil_le hRa hT1f hT1g
    have h := norm_integral_le_of_norm_le_const
      (μ := (Measure.pi fun _ : {x // x ≠ a.1} => (volume : Measure I)).prod
        (Measure.pi fun _ : {y // y ≠ a.2} => (volume : Measure I)))
      (f := fun uv => ∫ st : I × I, G (splitA a (st, uv)) ∂((volume : Measure I).prod volume))
      (C := 4 * cutNorm (R a)) (Eventually.of_forall fun uv => by
        rw [Real.norm_eq_abs]; exact hinner uv)
    rw [Real.norm_eq_abs] at h
    simpa using h

lemma k1_sub {F G : I → I → ℝ} (hF : K1 F) (hG : K1 G) : BK (fun x y => F x y - G x y) :=
  ⟨hF.1.sub hG.1, 2, fun x y => (abs_sub _ _).trans (by linarith [hF.2 x y, hG.2 x y])⟩

/-- **Counting lemma.** For decorations bounded by one,
`|t_bi(H; U) - t_bi(H; V)| ≤ 4 ∑_e ‖U_e - V_e‖_□`. -/
lemma abs_tBiDec_sub_le (E : Finset (X × Y)) (U V : X × Y → I → I → ℝ) (hU : ∀ p, K1 (U p))
    (hV : ∀ p, K1 (V p)) :
    |tBiDec volume E U - tBiDec volume E V| ≤
      4 * ∑ p ∈ E, cutNorm (fun x y => U p x y - V p x y) := by
  have key : ∀ S : Finset (X × Y), ∀ U V : X × Y → I → I → ℝ, (∀ p, K1 (U p)) →
      (∀ p, K1 (V p)) → (∀ p ∈ E, p ∉ S → U p = V p) →
      |tBiDec volume E U - tBiDec volume E V| ≤
        4 * ∑ p ∈ S, cutNorm (fun x y => U p x y - V p x y) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro U V _ _ h
      rw [Section2Aux.tBiDec_congr E fun p hp => h p hp (Finset.notMem_empty p)]
      simp
    | insert a S haS ih =>
      intro U V hU hV h
      set U' := Function.update U a (V a) with hU'
      have hU'k : ∀ p, K1 (U' p) := fun p => by
        by_cases hp : p = a
        · subst hp; simp only [hU', Function.update_self]; exact hV p
        · simp only [hU', Function.update_of_ne hp]; exact hU p
      have h1 := ih U' V hU'k hV fun p hp hpS => by
        by_cases hpa : p = a
        · subst hpa; simp [hU']
        · simp only [hU', Function.update_of_ne hpa]
          exact h p hp (by simp [hpa, hpS])
      have hsum : ∑ p ∈ S, cutNorm (fun x y => U' p x y - V p x y) =
          ∑ p ∈ S, cutNorm (fun x y => U p x y - V p x y) :=
        Finset.sum_congr rfl fun p hp => by
          have hpa : p ≠ a := fun h => haS (h ▸ hp)
          simp only [hU', Function.update_of_ne hpa]
      rw [hsum] at h1
      have h2 : |tBiDec volume E U - tBiDec volume E U'| ≤
          4 * cutNorm (fun x y => U a x y - V a x y) := by
        by_cases haE : a ∈ E
        · set R := Function.update U a (fun x y => U a x y - V a x y) with hR
          have e : tBiDec volume E U - tBiDec volume E U' = tBiDec volume E R := by
            simp only [Section2Aux.tBiDec_eq]
            rw [← integral_sub (Section2Aux.integrable_prod E U fun p _ => ⟨(hU p).1, 1, (hU p).2⟩)
              (Section2Aux.integrable_prod E U' fun p _ => ⟨(hU'k p).1, 1, (hU'k p).2⟩)]
            congr 1; funext z
            rw [← Finset.mul_prod_erase E _ haE, ← Finset.mul_prod_erase E _ haE,
              ← Finset.mul_prod_erase E (fun p => R p (z.1 p.1) (z.2 p.2)) haE]
            have hrest : ∀ W' : X × Y → I → I → ℝ, (∀ p, p ≠ a → W' p = U p) →
                ∏ p ∈ E.erase a, W' p (z.1 p.1) (z.2 p.2) =
                  ∏ p ∈ E.erase a, U p (z.1 p.1) (z.2 p.2) := fun W' hW' =>
              Finset.prod_congr rfl fun p hp => by rw [hW' p (Finset.ne_of_mem_erase hp)]
            rw [hrest U' (fun p hp => by simp [hU', Function.update_of_ne hp]),
              hrest R (fun p hp => by simp [hR, Function.update_of_ne hp])]
            simp only [hU', hR, Function.update_self]
            ring
          rw [e]
          have hRa : BK (R a) := by
            simp only [hR, Function.update_self]; exact k1_sub (hU a) (hV a)
          have hRp : ∀ p, p ≠ a → K1 (R p) := fun p hp => by
            simp only [hR, Function.update_of_ne hp]; exact hU p
          have := abs_tBiDec_single E haE R hRa hRp
          simpa [hR] using this
        · rw [Section2Aux.tBiDec_congr E (V := U') fun p hp => by
            have : p ≠ a := fun h => haE (h ▸ hp)
            simp [hU', Function.update_of_ne this]]
          simp only [sub_self, abs_zero]
          exact mul_nonneg (by norm_num) (cutNorm_nonneg (k1_sub (hU a) (hV a)).2.choose_spec)
      rw [Finset.sum_insert haS]
      calc |tBiDec volume E U - tBiDec volume E V|
          ≤ |tBiDec volume E U - tBiDec volume E U'| + |tBiDec volume E U' - tBiDec volume E V| :=
            abs_sub_le _ _ _
        _ ≤ _ := by linarith
  exact key E U V hU hV fun p hp hpE => absurd hp hpE

omit [DecidableEq X] [DecidableEq Y] in
/-- Densities are invariant under pulling back all decorations by a measure-preserving map. -/
lemma tBiDec_pullback (E : Finset (X × Y)) (U : X × Y → I → I → ℝ)
    (hU : ∀ p, Measurable (Function.uncurry (U p))) {φ : I → I}
    (hφ : MeasurePreserving φ volume volume) :
    tBiDec volume E (fun p => pullback φ (U p)) = tBiDec volume E U := by
  have hmp : MeasurePreserving (fun z : (X → I) × (Y → I) => (fun x => φ (z.1 x), fun y => φ (z.2 y)))
      (Section2Aux.ρ X Y) (Section2Aux.ρ X Y) :=
    (measurePreserving_pi _ _ fun _ => hφ).prod (measurePreserving_pi _ _ fun _ => hφ)
  have hm : Measurable (fun z : (X → I) × (Y → I) => ∏ p ∈ E, U p (z.1 p.1) (z.2 p.2)) :=
    Finset.measurable_prod _ fun p _ => meas_app (hU p)
      ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_snd)
  rw [Section2Aux.tBiDec_eq, Section2Aux.tBiDec_eq]
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hm.aestronglyMeasurable)]
  rfl

omit [DecidableEq X] [DecidableEq Y] in
lemma tb_pullback (E : Finset (X × Y)) (U : I → I → ℝ) (hU : Measurable (Function.uncurry U))
    {φ : I → I} (hφ : MeasurePreserving φ volume volume) :
    tb E (pullback φ U) = tb E U :=
  tBiDec_pullback E (fun _ => U) (fun _ => hU) hφ

/-- The counting lemma for one kernel. -/
lemma abs_tb_sub_le (E : Finset (X × Y)) {U V : I → I → ℝ} (hU : K1 U) (hV : K1 V) :
    |tb E U - tb E V| ≤ 4 * E.card * cutNorm (fun x y => U x y - V x y) := by
  have := abs_tBiDec_sub_le E (fun _ => U) (fun _ => V) (fun _ => hU) (fun _ => hV)
  rw [Finset.sum_const, nsmul_eq_mul] at this
  simpa [Section2Aux.tb_eq_tBiDec, mul_assoc] using this

end Counting

/-! ## `t(K_{2,2}, F)` controls the cut norm -/

section K22

/-- `k_F(y, y') = ∫ F(x, y) F(x, y') dx`. -/
noncomputable def kk (F : I → I → ℝ) (y y' : I) : ℝ := ∫ x, F x y * F x y'

lemma sq_integral_le {β : Type*} [MeasurableSpace β] {μ : Measure β} [IsProbabilityMeasure μ]
    {g : β → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have hgi : Integrable g μ := integrable_bdd hg C hC
  have hg2 : Integrable (fun x => g x ^ 2) μ :=
    integrable_bdd (hg.pow_const 2) (C ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  set c := ∫ x, g x ∂μ
  have h0 : 0 ≤ ∫ x, (g x - c) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (g x - c) ^ 2 ∂μ = ∫ x, g x ^ 2 ∂μ - c ^ 2 := by
    have e1 : (fun x => (g x - c) ^ 2) = fun x => (g x ^ 2 - 2 * c * g x) + c ^ 2 := by
      funext x; ring
    have i1 : Integrable (fun x => g x ^ 2 - 2 * c * g x) μ := hg2.sub (hgi.const_mul _)
    have a1 := integral_add (μ := μ) (f := fun x => g x ^ 2 - 2 * c * g x) (g := fun _ => c ^ 2)
      i1 (integrable_const _)
    have a2 := integral_sub (μ := μ) (f := fun x => g x ^ 2) (g := fun x => 2 * c * g x)
      hg2 (hgi.const_mul _)
    have a3 := integral_const_mul (μ := μ) (2 * c) g
    rw [e1, a1, a2, a3]
    simp; ring
  linarith

lemma kk_meas {F : I → I → ℝ} (hF : BK F) : Measurable (fun q : I × I => kk F q.1 q.2) := by
  have hm : Measurable (fun r : I × (I × I) => F r.1 r.2.1 * F r.1 r.2.2) :=
    (meas_app hF.1 measurable_fst (measurable_fst.comp measurable_snd)).mul
      (meas_app hF.1 measurable_fst (measurable_snd.comp measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure I))).measurable

lemma kk_bound {F : I → I → ℝ} {M : ℝ} (hM : ∀ x y, |F x y| ≤ M) (y y' : I) :
    |kk F y y'| ≤ M * M := by
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure I))
    (f := fun x => F x y * F x y') (C := M * M) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hM _ _) (hM _ _) (abs_nonneg _) ((abs_nonneg _).trans (hM x y)))
  simpa [kk] using h

lemma tb_K22 {F : I → I → ℝ} (hF : BK F) :
    tb (Finset.univ : Finset (Fin 2 × Fin 2)) F =
      ∫ q : I × I, kk F q.1 q.2 ^ 2 ∂((volume : Measure I).prod volume) := by
  obtain ⟨M, hM⟩ := hF.2
  have hint := Section2Aux.integrable_prod (Finset.univ : Finset (Fin 2 × Fin 2)) (fun _ => F)
    fun _ _ => ⟨hF.1, M, hM⟩
  unfold tb tBi
  rw [integral_prod_symm _ hint]
  have hin : ∀ y : Fin 2 → I, ∫ x : Fin 2 → I, ∏ p ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
      F (x p.1) (y p.2) ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) =
      kk F (y 0) (y 1) ^ 2 := by
    intro y
    have e : ∀ x : Fin 2 → I, ∏ p ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), F (x p.1) (y p.2) =
        ∏ i : Fin 2, (fun (_ : Fin 2) (t : I) => F t (y 0) * F t (y 1)) i (x i) := by
      intro x
      rw [Finset.univ_product_univ.symm, Finset.prod_product]
      simp [Fin.prod_univ_two]
    simp_rw [e]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin 2) (t : I) => F t (y 0) * F t (y 1)),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  simp_rw [hin]
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure I))
  rw [← hmp.integral_comp']
  rfl

/-- `|∫_{S×T} F|^4 ≤ t_bi(K_{2,2}, F)`. -/
lemma rect_pow4_le {F : I → I → ℝ} (hF : BK F) {S T : Set I} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    (∫ p in S ×ˢ T, F p.1 p.2) ^ 4 ≤ tb (Finset.univ : Finset (Fin 2 × Fin 2)) F := by
  obtain ⟨M, hM⟩ := hF.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have hS1 := t1_indicator hS
  have hT1 := t1_indicator hT
  obtain ⟨hhm, hhi⟩ := integrable_inner_x hF hT1
  set h : I → ℝ := fun x => ∫ y, F x y * T.indicator 1 y with hh
  have hhb : ∀ x, |h x| ≤ M := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure I))
      (f := fun y => F x y * T.indicator 1 y) (C := M) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hT1.2 y)).trans (hM x y))
    simpa using this
  -- step 1
  have h1 : (∫ p in S ×ˢ T, F p.1 p.2) ^ 2 ≤ ∫ x, h x ^ 2 := by
    rw [← bil_rect F hS hT, bil_eq_x hF hS1 hT1]
    refine (sq_integral_le (g := fun x => S.indicator 1 x * h x) (hS1.1.mul hhm) (C := M)
      fun x => ?_).trans ?_
    · rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (hS1.2 x)).trans (hhb x)
    · refine integral_mono (integrable_bdd (φ := fun x => (S.indicator 1 x * h x) ^ 2)
        ((hS1.1.mul hhm).pow_const 2) (M ^ 2) fun x => ?_)
        (integrable_bdd (hhm.pow_const 2) (M ^ 2) fun x => ?_) fun x => ?_
      · rw [abs_pow, abs_mul]
        exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          ((mul_le_of_le_one_left (abs_nonneg _) (hS1.2 x)).trans (hhb x)) 2
      · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hhb x) 2
      · simp only
        rw [mul_pow]
        have : S.indicator (1 : I → ℝ) x ^ 2 ≤ 1 := by
          have := hS1.2 x
          rw [← sq_abs]; nlinarith [abs_nonneg (S.indicator (1 : I → ℝ) x)]
        nlinarith [sq_nonneg (h x)]
  -- step 2
  set g : I × I → ℝ := fun q => T.indicator 1 q.1 * T.indicator 1 q.2 * kk F q.1 q.2 with hg
  have hgm : Measurable g :=
    ((hT1.1.comp measurable_fst).mul (hT1.1.comp measurable_snd)).mul (kk_meas hF)
  have hgb : ∀ q, |g q| ≤ M * M := fun q => by
    simp only [hg, abs_mul]
    have := kk_bound hM q.1 q.2
    have h1 := hT1.2 q.1; have h2 := hT1.2 q.2
    calc |T.indicator 1 q.1| * |T.indicator 1 q.2| * |kk F q.1 q.2| ≤ 1 * 1 * (M * M) := by
          gcongr
      _ = M * M := by ring
  have h2 : ∫ x, h x ^ 2 = ∫ q, g q ∂((volume : Measure I).prod volume) := by
    have hint : Integrable (Function.uncurry fun (x : I) (q : I × I) =>
        F x q.1 * T.indicator 1 q.1 * (F x q.2 * T.indicator 1 q.2))
        ((volume : Measure I).prod ((volume : Measure I).prod volume)) := by
      refine integrable_bdd ?_ (M * M) fun r => ?_
      · exact ((meas_app hF.1 measurable_fst (measurable_fst.comp measurable_snd)).mul
          (hT1.1.comp (measurable_fst.comp measurable_snd))).mul
          ((meas_app hF.1 measurable_fst (measurable_snd.comp measurable_snd)).mul
          (hT1.1.comp (measurable_snd.comp measurable_snd)))
      · simp only [Function.uncurry, abs_mul]
        have := hT1.2 r.2.1; have := hT1.2 r.2.2
        have := hM r.1 r.2.1; have := hM r.1 r.2.2
        calc |F r.1 r.2.1| * |T.indicator 1 r.2.1| * (|F r.1 r.2.2| * |T.indicator 1 r.2.2|)
            ≤ M * 1 * (M * 1) := by gcongr
          _ = M * M := by ring
    calc ∫ x, h x ^ 2 = ∫ x : I, ∫ q : I × I, F x q.1 * T.indicator 1 q.1 *
          (F x q.2 * T.indicator 1 q.2) ∂((volume : Measure I).prod volume) := by
          congr 1; funext x
          rw [hh, sq, ← integral_prod_mul (fun y => F x y * T.indicator 1 y)
            (fun y => F x y * T.indicator 1 y)]
      _ = ∫ q : I × I, (∫ x : I, F x q.1 * T.indicator 1 q.1 * (F x q.2 * T.indicator 1 q.2))
          ∂((volume : Measure I).prod volume) := integral_integral_swap hint
      _ = _ := by
          congr 1; funext q
          simp only [hg, kk]
          rw [← integral_const_mul]
          congr 1; funext x; ring
  have h3 : (∫ q, g q ∂((volume : Measure I).prod volume)) ^ 2 ≤
      tb (Finset.univ : Finset (Fin 2 × Fin 2)) F := by
    rw [tb_K22 hF]
    refine (sq_integral_le hgm hgb).trans ?_
    refine integral_mono (integrable_bdd (hgm.pow_const 2) ((M * M) ^ 2) fun q => ?_)
      (integrable_bdd ((kk_meas hF).pow_const 2) ((M * M) ^ 2) fun q => ?_) fun q => ?_
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb q) 2
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (kk_bound hM q.1 q.2) 2
    · simp only [hg]
      have a1 := hT1.2 q.1; have a2 := hT1.2 q.2
      rw [mul_pow, mul_pow]
      have b1 : T.indicator (1 : I → ℝ) q.1 ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (T.indicator (1 : I → ℝ) q.1)]
      have b2 : T.indicator (1 : I → ℝ) q.2 ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (T.indicator (1 : I → ℝ) q.2)]
      have := sq_nonneg (kk F q.1 q.2)
      have := sq_nonneg (T.indicator (1 : I → ℝ) q.1)
      have := sq_nonneg (T.indicator (1 : I → ℝ) q.2)
      calc T.indicator 1 q.1 ^ 2 * T.indicator 1 q.2 ^ 2 * kk F q.1 q.2 ^ 2
          ≤ 1 * 1 * kk F q.1 q.2 ^ 2 := by gcongr
        _ = _ := by ring
  have hpos : 0 ≤ ∫ x, h x ^ 2 := integral_nonneg fun x => sq_nonneg _
  calc (∫ p in S ×ˢ T, F p.1 p.2) ^ 4 = ((∫ p in S ×ˢ T, F p.1 p.2) ^ 2) ^ 2 := by ring
    _ ≤ (∫ x, h x ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ ≤ _ := by rw [h2] at hpos ⊢; exact h3

lemma cutNorm_pow4_le {F : I → I → ℝ} (hF : BK F) :
    cutNorm F ^ 4 ≤ tb (Finset.univ : Finset (Fin 2 × Fin 2)) F := by
  obtain ⟨M, hM⟩ := hF.2
  set t := tb (Finset.univ : Finset (Fin 2 × Fin 2)) F
  have ht : 0 ≤ t := le_trans (by positivity) (rect_pow4_le hF MeasurableSet.empty
    MeasurableSet.empty)
  have hc : cutNorm F ≤ t ^ ((1 : ℝ) / 4) := cutNorm_le fun S T hS hT => by
    have h := rect_pow4_le hF hS hT
    rw [← Even.pow_abs (by decide : Even 4)] at h
    calc |∫ p in S ×ˢ T, F p.1 p.2|
        = (|∫ p in S ×ˢ T, F p.1 p.2| ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
          rw [one_div, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
            Real.pow_rpow_inv_natCast (abs_nonneg _) (by norm_num)]
      _ ≤ t ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h0 := cutNorm_nonneg hM
  calc cutNorm F ^ 4 ≤ (t ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := pow_le_pow_left₀ h0 hc 4
    _ = t := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

end K22

end S1CutDist

end NieWeiOrientedSidorenko
