import NieWeiOrientedSidorenko.Families

/-!
# Auxiliary lemmas for Section 2 (Claim 2.1, Lemma 2.2 and Lemma 2.3)

Helper file for `Section2.lean` (namespace `NieWeiOrientedSidorenko.Section2Aux`): basic facts on
bipartite densities, the tensor-power proof of the weak Hölder inequality, the Jensen lower bound
`t_bi(K_{a,b}, f) ≥ (∫ f)^{ab}`, the norming Hölder inequality, and the two convexity
characterizations; for Claim 2.1, generic facts on directed densities (reversal expansion,
tensor squares, `L¹` continuity, grid approximation, connectivity and self-converse relabelling).
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal

namespace NieWeiOrientedSidorenko

namespace Section2Aux

set_option linter.unusedSectionVars false

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The measure of the bipartite density. -/
noncomputable abbrev ρ (X Y : Type*) [Fintype X] [Fintype Y] :
    Measure ((X → I) × (Y → I)) :=
  (Measure.pi fun _ : X => (volume : Measure I)).prod (Measure.pi fun _ : Y => (volume : Measure I))

lemma tBiDec_eq (E : Finset (X × Y)) (U : X × Y → I → I → ℝ) :
    tBiDec volume E U = ∫ z, ∏ p ∈ E, U p (z.1 p.1) (z.2 p.2) ∂(ρ X Y) := rfl

lemma tb_eq_tBiDec (E : Finset (X × Y)) (U : I → I → ℝ) :
    tb E U = tBiDec volume E (fun _ => U) := rfl

omit [Fintype X] [Fintype Y] in
lemma measurable_coord (p : X × Y) :
    Measurable (fun z : (X → I) × (Y → I) => (z.1 p.1, z.2 p.2)) := by
  fun_prop

lemma integrable_prod (E : Finset (X × Y)) (U : X × Y → I → I → ℝ)
    (hU : ∀ p ∈ E, IsKernel (U p)) :
    Integrable (fun z : (X → I) × (Y → I) => ∏ p ∈ E, U p (z.1 p.1) (z.2 p.2)) (ρ X Y) := by
  choose! M hM using fun p hp => (hU p hp).2
  have hmeas : Measurable (fun z : (X → I) × (Y → I) => ∏ p ∈ E, U p (z.1 p.1) (z.2 p.2)) := by
    refine Finset.measurable_prod _ fun p hp => ?_
    exact (hU p hp).1.comp (measurable_coord p)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (∏ p ∈ E, M p) (Eventually.of_forall ?_)
  intro z
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => hM p hp _ _)

lemma tBiDec_mono (E : Finset (X × Y)) (U V : X × Y → I → I → ℝ)
    (hU : ∀ p ∈ E, IsKernel (U p)) (hV : ∀ p ∈ E, IsKernel (V p))
    (h0 : ∀ p ∈ E, ∀ x y, 0 ≤ U p x y) (h1 : ∀ p ∈ E, ∀ x y, U p x y ≤ V p x y) :
    tBiDec volume E U ≤ tBiDec volume E V := by
  refine integral_mono (integrable_prod E U hU) (integrable_prod E V hV) fun z => ?_
  exact Finset.prod_le_prod₀ (fun p hp => h0 p hp _ _) (fun p hp => h1 p hp _ _)

lemma tBiDec_nonneg (E : Finset (X × Y)) (U : X × Y → I → I → ℝ)
    (h0 : ∀ p ∈ E, ∀ x y, 0 ≤ U p x y) : 0 ≤ tBiDec volume E U :=
  integral_nonneg fun _ => Finset.prod_nonneg fun p hp => h0 p hp _ _

lemma abs_tBiDec_le (E : Finset (X × Y)) (U : X × Y → I → I → ℝ) :
    |tBiDec volume E U| ≤ tBiDec volume E (fun p x y => |U p x y|) := by
  refine (abs_integral_le_integral_abs).trans_eq ?_
  simp only [tBiDec, Finset.abs_prod]

lemma tBiDec_smul (E : Finset (X × Y)) (U : X × Y → I → I → ℝ) (c : X × Y → ℝ) :
    tBiDec volume E (fun p x y => c p * U p x y) = (∏ p ∈ E, c p) * tBiDec volume E U := by
  simp only [tBiDec, Finset.prod_mul_distrib]
  exact integral_const_mul _ _

lemma tb_smul (E : Finset (X × Y)) (U : I → I → ℝ) (c : ℝ) :
    tb E (fun x y => c * U x y) = c ^ E.card * tb E U := by
  have := tBiDec_smul E (fun _ => U) (fun _ => c)
  simp only [Finset.prod_const] at this
  exact this

lemma tb_nonneg (E : Finset (X × Y)) (U : I → I → ℝ) (h0 : ∀ x y, 0 ≤ U x y) : 0 ≤ tb E U :=
  tBiDec_nonneg E _ fun _ _ => h0

lemma isKernel_abs {U : I → I → ℝ} (hU : IsKernel U) : IsKernel (fun x y => |U x y|) := by
  obtain ⟨hm, M, hM⟩ := hU
  exact ⟨hm.abs, M, fun x y => by simpa using hM x y⟩

lemma isKernel_smul {U : I → I → ℝ} (hU : IsKernel U) (c : ℝ) :
    IsKernel (fun x y => c * U x y) := by
  obtain ⟨hm, M, hM⟩ := hU
  refine ⟨hm.const_mul c, |c| * M, fun x y => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM x y) (abs_nonneg c)

lemma isKernel_add {U V : I → I → ℝ} (hU : IsKernel U) (hV : IsKernel V) :
    IsKernel (fun x y => U x y + V x y) := by
  obtain ⟨hm, M, hM⟩ := hU
  obtain ⟨hm', M', hM'⟩ := hV
  exact ⟨hm.add hm', M + M', fun x y => (abs_add_le _ _).trans (add_le_add (hM x y) (hM' x y))⟩

lemma isKernel_sum {ι : Type*} (s : Finset ι) {U : ι → I → I → ℝ} (hU : ∀ i ∈ s, IsKernel (U i)) :
    IsKernel (fun x y => ∑ i ∈ s, U i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨measurable_const, 0, fun x y => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact isKernel_add (hU a (Finset.mem_insert_self a s))
      (ih fun i hi => hU i (Finset.mem_insert_of_mem hi))

/-- For a nonnegative `U`, `tb E U = rNorm E U ^ m`. -/
lemma tb_eq_rNorm_pow (E : Finset (X × Y)) (hE : 0 < E.card) (U : I → I → ℝ)
    (h0 : ∀ x y, 0 ≤ U x y) : tb E U = rNorm E U ^ E.card := by
  have habs : (fun x y => |U x y|) = U := by funext x y; exact abs_of_nonneg (h0 x y)
  unfold rNorm
  rw [habs, ← Real.rpow_natCast, ← Real.rpow_mul (tb_nonneg E U h0)]
  rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hE.ne'), Real.rpow_one]

lemma rNorm_nonneg (E : Finset (X × Y)) (U : I → I → ℝ) : 0 ≤ rNorm E U :=
  Real.rpow_nonneg (tb_nonneg E _ fun _ _ => abs_nonneg _) _


lemma mp_prodProdProdComm {A A' B B' : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] [MeasurableSpace B'] (μ : Measure A) (μ' : Measure A') (ν : Measure B)
    (ν' : Measure B') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] :
    MeasurePreserving (fun w : (A × A') × (B × B') => ((w.1.1, w.2.1), (w.1.2, w.2.2)))
      ((μ.prod μ').prod (ν.prod ν')) ((μ.prod ν).prod (μ'.prod ν')) := by
  have h1 := measurePreserving_prodAssoc μ μ' (ν.prod ν')
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ' ν ν').symm
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := μ') (ν := ν)).prod (MeasurePreserving.id ν'))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν μ' ν')
  have h5 := (measurePreserving_prodAssoc μ ν (μ'.prod ν')).symm
  have := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert this using 1
  funext w
  rfl

/-- A measurable map `I → I × I` pushing Lebesgue measure to the product measure. -/
lemma exists_split : ∃ φ : I → I × I, MeasurePreserving φ volume (volume.prod volume) := by
  obtain ⟨φ, hφ, hmap⟩ := Measure.exists_measurable_map_eq (volume.prod volume : Measure (I × I))
  exact ⟨φ, hφ, hmap⟩

/-- The split of `I^X` induced by `φ`. -/
def splitPi (φ : I → I × I) (X : Type*) (z : X → I) : (X → I) × (X → I) :=
  (fun x => (φ (z x)).1, fun x => (φ (z x)).2)

lemma mp_splitPi {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (X : Type*) [Fintype X] :
    MeasurePreserving (splitPi φ X) (Measure.pi fun _ : X => (volume : Measure I))
      ((Measure.pi fun _ : X => (volume : Measure I)).prod
        (Measure.pi fun _ : X => (volume : Measure I))) := by
  have h1 := measurePreserving_pi (fun _ : X => (volume : Measure I))
    (fun _ : X => (volume : Measure I).prod volume) (f := fun _ => φ) (fun _ => hφ)
  have h2 := measurePreserving_arrowProdEquivProdArrow I I X (fun _ => volume) (fun _ => volume)
  exact h2.comp h1

/-- The tensor square of a kernel, transported to `I` by `φ`. -/
def sqK (φ : I → I × I) (f : I → I → ℝ) : I → I → ℝ :=
  fun x y => f (φ x).1 (φ y).1 * f (φ x).2 (φ y).2

lemma isKernel_sqK {φ : I → I × I} (hφ : Measurable φ) {f : I → I → ℝ} (hf : IsKernel f) :
    IsKernel (sqK φ f) := by
  obtain ⟨hm, M, hM⟩ := hf
  refine ⟨?_, M * M, fun x y => ?_⟩
  · have a : Measurable fun q : I × I => ((φ q.1).1, (φ q.2).1) := by fun_prop
    have b : Measurable fun q : I × I => ((φ q.1).2, (φ q.2).2) := by fun_prop
    exact (hm.comp a).mul (hm.comp b)
  · rw [sqK, abs_mul]
    exact mul_le_mul (hM _ _) (hM _ _) (abs_nonneg _) ((abs_nonneg _).trans (hM 0 0))

lemma tBiDec_sqK {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (E : Finset (X × Y)) (U : X × Y → I → I → ℝ) (hU : ∀ p ∈ E, IsKernel (U p)) :
    tBiDec volume E (fun p => sqK φ (U p)) = tBiDec volume E U ^ 2 := by
  set h : (X → I) × (Y → I) → ℝ := fun z => ∏ p ∈ E, U p (z.1 p.1) (z.2 p.2) with hh
  have hΘ := (mp_splitPi hφ X).prod (mp_splitPi hφ Y)
  have hT := (mp_prodProdProdComm (Measure.pi fun _ : X => (volume : Measure I))
    (Measure.pi fun _ : X => (volume : Measure I)) (Measure.pi fun _ : Y => (volume : Measure I))
    (Measure.pi fun _ : Y => (volume : Measure I))).comp hΘ
  have hmeas : Measurable h := Finset.measurable_prod _ fun p hp =>
    (hU p hp).1.comp (measurable_coord p)
  have key : tBiDec volume E (fun p => sqK φ (U p)) =
      ∫ w, h w.1 * h w.2 ∂((ρ X Y).prod (ρ X Y)) := by
    rw [← hT.map_eq, integral_map (f := fun w => h w.1 * h w.2) hT.measurable.aemeasurable
      ((hmeas.comp measurable_fst).mul (hmeas.comp measurable_snd)).aestronglyMeasurable]
    simp only [tBiDec, sqK, hh, Finset.prod_mul_distrib]
    rfl
  rw [key, integral_prod_mul, sq]
  rfl

lemma rNorm_sqK {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (E : Finset (X × Y)) (f : I → I → ℝ) (hf : IsKernel f) :
    rNorm E (sqK φ f) = rNorm E f ^ 2 := by
  have h1 : (fun x y => |sqK φ f x y|) = sqK φ (fun x y => |f x y|) := by
    funext x y; simp [sqK, abs_mul]
  have h2 : tb E (sqK φ (fun x y => |f x y|)) = tb E (fun x y => |f x y|) ^ 2 :=
    tBiDec_sqK hφ E (fun _ => fun x y => |f x y|) fun _ _ => isKernel_abs hf
  have h0 : 0 ≤ tb E (fun x y => |f x y|) := tb_nonneg E _ fun _ _ => abs_nonneg _
  unfold rNorm
  rw [h1, h2, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_mul h0,
    mul_comm]

lemma rNorm_sum (E : Finset (X × Y)) (hE : IsWeaklyNorming E) {ι : Type*} (s : Finset ι)
    (g : ι → I → I → ℝ) (hg : ∀ i ∈ s, IsKernel (g i)) :
    rNorm E (fun x y => ∑ i ∈ s, g i x y) ≤ ∑ i ∈ s, rNorm E (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hE.1 (fun _ _ => 0) ⟨measurable_const, 0, fun _ _ => by simp⟩ 0
    simp only [mul_zero, abs_zero, zero_mul] at this
    simp [this]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine (hE.2.1 _ _ (hg a (Finset.mem_insert_self a s))
      (isKernel_sum s fun i hi => hg i (Finset.mem_insert_of_mem hi))).trans ?_
    exact add_le_add le_rfl (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma core_bound (E : Finset (X × Y)) (hE : IsWeaklyNorming E) (hne : 0 < E.card)
    (g : X × Y → I → I → ℝ) (hg : ∀ p ∈ E, IsKernel (g p)) (h0 : ∀ p ∈ E, ∀ x y, 0 ≤ g p x y)
    (h1 : ∀ p ∈ E, rNorm E (g p) ≤ 1) :
    tBiDec volume E g ≤ (E.card : ℝ) ^ E.card := by
  set G : I → I → ℝ := fun x y => ∑ q ∈ E, g q x y with hG
  have hGk : IsKernel G := isKernel_sum E hg
  have hG0 : ∀ x y, 0 ≤ G x y := fun x y => Finset.sum_nonneg fun q hq => h0 q hq x y
  have step1 : tBiDec volume E g ≤ tb E G :=
    tBiDec_mono E g (fun _ => G) hg (fun _ _ => hGk) h0
      fun p hp x y => Finset.single_le_sum (f := fun q => g q x y) (fun q hq => h0 q hq x y) hp
  have step2 : rNorm E G ≤ E.card := by
    refine (rNorm_sum E hE E g hg).trans ?_
    calc ∑ q ∈ E, rNorm E (g q) ≤ ∑ q ∈ E, (1 : ℝ) := Finset.sum_le_sum h1
      _ = E.card := by simp
  rw [tb_eq_rNorm_pow E hne G hG0] at step1
  exact step1.trans (pow_le_pow_left₀ (rNorm_nonneg E G) step2 _)

lemma iter_bound (E : Finset (X × Y)) (hE : IsWeaklyNorming E) (hne : 0 < E.card)
    {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume)) (k : ℕ) :
    ∀ g : X × Y → I → I → ℝ, (∀ p ∈ E, IsKernel (g p)) → (∀ p ∈ E, ∀ x y, 0 ≤ g p x y) →
      (∀ p ∈ E, rNorm E (g p) ≤ 1) → tBiDec volume E g ^ (2 ^ k) ≤ (E.card : ℝ) ^ E.card := by
  induction k with
  | zero => intro g hg h0 h1; simpa using core_bound E hE hne g hg h0 h1
  | succ k ih =>
    intro g hg h0 h1
    have := ih (fun p => sqK φ (g p)) (fun p hp => isKernel_sqK hφ.measurable (hg p hp))
      (fun p hp x y => mul_nonneg (h0 p hp _ _) (h0 p hp _ _))
      (fun p hp => by
        rw [rNorm_sqK hφ E _ (hg p hp)]
        exact pow_le_one₀ (rNorm_nonneg E _) (h1 p hp))
    rw [tBiDec_sqK hφ E g hg, ← pow_mul] at this
    rwa [pow_succ, mul_comm]

lemma normalized_le_one (E : Finset (X × Y)) (hE : IsWeaklyNorming E) (hne : 0 < E.card)
    (g : X × Y → I → I → ℝ) (hg : ∀ p ∈ E, IsKernel (g p)) (h0 : ∀ p ∈ E, ∀ x y, 0 ≤ g p x y)
    (h1 : ∀ p ∈ E, rNorm E (g p) ≤ 1) : tBiDec volume E g ≤ 1 := by
  obtain ⟨φ, hφ⟩ := exists_split
  by_contra hv
  replace hv := not_le.mp hv
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((E.card : ℝ) ^ E.card) hv
  have h2 := iter_bound E hE hne hφ k g hg h0 h1
  have h3 : tBiDec volume E g ^ k ≤ tBiDec volume E g ^ (2 ^ k) :=
    pow_le_pow_right₀ hv.le (Nat.lt_two_pow_self).le
  linarith

lemma holder_nonneg (E : Finset (X × Y)) (hE : IsWeaklyNorming E) (hne : 0 < E.card)
    (f : X × Y → I → I → ℝ) (hf : ∀ p ∈ E, IsKernel (f p)) (h0 : ∀ p ∈ E, ∀ x y, 0 ≤ f p x y) :
    tBiDec volume E f ≤ ∏ p ∈ E, rNorm E (f p) := by
  have key : ∀ ε > (0 : ℝ), tBiDec volume E f ≤ ∏ p ∈ E, (rNorm E (f p) + ε) := by
    intro ε hε
    set c : X × Y → ℝ := fun p => rNorm E (f p) + ε with hc
    have cpos : ∀ p, 0 < c p := fun p => add_pos_of_nonneg_of_pos (rNorm_nonneg E _) hε
    have hn := normalized_le_one E hE hne (fun p x y => (c p)⁻¹ * f p x y)
      (fun p hp => isKernel_smul (hf p hp) _)
      (fun p hp x y => mul_nonneg (inv_nonneg.2 (cpos p).le) (h0 p hp x y))
      (fun p hp => by
        rw [hE.1 _ (hf p hp), abs_of_pos (inv_pos.2 (cpos p)), inv_mul_le_one₀ (cpos p)]
        simp [hc, hε.le])
    rw [tBiDec_smul E f (fun p => (c p)⁻¹), Finset.prod_inv_distrib,
      inv_mul_le_one₀ (Finset.prod_pos fun p _ => cpos p)] at hn
    exact hn
  have hcont : Tendsto (fun ε : ℝ => ∏ p ∈ E, (rNorm E (f p) + ε)) (𝓝[>] 0)
      (𝓝 (∏ p ∈ E, rNorm E (f p))) := by
    have : Continuous (fun ε : ℝ => ∏ p ∈ E, (rNorm E (f p) + ε)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

theorem weak_holder {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (hE : IsWeaklyNorming E) (U : X × Y → I → I → ℝ) (hU : ∀ p ∈ E, IsKernel (U p)) :
    |tBiDec volume E U| ≤ ∏ p ∈ E, tb E (fun x y => |U p x y|) ^ ((1 : ℝ) / E.card) := by
  rcases Nat.eq_zero_or_pos E.card with h | hne
  · rw [Finset.card_eq_zero] at h
    subst h
    simp [tBiDec]
  refine (abs_tBiDec_le E U).trans ?_
  refine (holder_nonneg E hE hne _ (fun p hp => isKernel_abs (hU p hp))
    fun p _ x y => abs_nonneg _).trans_eq ?_
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [rNorm]

/-! ### Lemma 2.3 -/

lemma jensen_pow {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1) (n : ℕ) :
    (∫ x, g x ∂μ) ^ n ≤ ∫ x, g x ^ n ∂μ := by
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)
  have hgni : Integrable (fun x => g x ^ n) μ := Integrable.of_bound
    (hg.pow_const n).aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 x) n)]; exact pow_le_one₀ (h0 x) (h1 x))
  exact (convexOn_pow n).map_integral_le (continuous_pow n).continuousOn isClosed_Ici
    (Eventually.of_forall fun x => h0 x) hgi hgni

lemma measurable_pi_prod_f {ι : Type*} [Fintype ι] {f : I → I → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun q : (ι → I) × I => ∏ i, f (q.1 i) q.2) := by
  refine Finset.measurable_prod _ fun i _ => ?_
  have hm : Measurable (fun q : (ι → I) × I => (q.1 i, q.2)) := by fun_prop
  exact hf.comp hm

lemma prod_mem_01 {ι : Type*} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i, 0 ≤ a i)
    (h1 : ∀ i, a i ≤ 1) : 0 ≤ ∏ i ∈ s, a i ∧ ∏ i ∈ s, a i ≤ 1 :=
  ⟨Finset.prod_nonneg fun i _ => h0 i, Finset.prod_le_one₀ (fun i _ => h0 i) fun i _ => h1 i⟩

lemma integrable_of_01 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)

/-- The two Jensen steps: `t_bi(K_{a,b}, f) ≥ (∫ f)^{ab}` for `0 ≤ f ≤ 1`. -/
lemma tb_univ_ge (f : I → I → ℝ) (hf : Measurable (Function.uncurry f))
    (h0 : ∀ x y, 0 ≤ f x y) (h1 : ∀ x y, f x y ≤ 1) :
    (∫ q, f q.1 q.2 ∂((volume : Measure I).prod volume)) ^ (Fintype.card X * Fintype.card Y) ≤
      tb (Finset.univ : Finset (X × Y)) f := by
  set μX := Measure.pi fun _ : X => (volume : Measure I)
  set μY := Measure.pi fun _ : Y => (volume : Measure I)
  set G : (X → I) → ℝ := fun z1 => ∫ t, ∏ i, f (z1 i) t ∂(volume : Measure I) with hG
  set h : I → ℝ := fun t => ∫ s, f s t ∂(volume : Measure I) with hh
  have hFm : Measurable (fun q : (X → I) × I => ∏ i, f (q.1 i) q.2) := measurable_pi_prod_f hf
  have hF01 : ∀ q : (X → I) × I, 0 ≤ ∏ i, f (q.1 i) q.2 ∧ ∏ i, f (q.1 i) q.2 ≤ 1 :=
    fun q => prod_mem_01 _ _ (fun i => h0 _ _) fun i => h1 _ _
  have hFi : Integrable (fun q : (X → I) × I => ∏ i, f (q.1 i) q.2) (μX.prod volume) :=
    integrable_of_01 hFm (fun q => (hF01 q).1) fun q => (hF01 q).2
  have hGm : Measurable G := hFm.stronglyMeasurable.integral_prod_right'.measurable
  have hG0 : ∀ z, 0 ≤ G z := fun z => integral_nonneg fun t => (hF01 (z, t)).1
  have hG1 : ∀ z, G z ≤ 1 := fun z => by
    calc G z ≤ ∫ _t, (1 : ℝ) ∂(volume : Measure I) :=
          integral_mono (integrable_of_01 (hFm.comp (measurable_prodMk_left (x := z)))
            (fun t => (hF01 (z, t)).1) fun t => (hF01 (z, t)).2) (integrable_const 1)
            fun t => (hF01 (z, t)).2
      _ = 1 := by simp
  have hfm' : Measurable (fun q : I × I => f q.1 q.2) := hf
  have hfi : Integrable (fun q : I × I => f q.1 q.2) ((volume : Measure I).prod volume) :=
    integrable_of_01 hfm' (fun q => h0 _ _) fun q => h1 _ _
  have hhm : Measurable h := by
    have := (hfm'.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure I))
    exact this.measurable
  have hh0 : ∀ t, 0 ≤ h t := fun t => integral_nonneg fun s => h0 _ _
  have hh1 : ∀ t, h t ≤ 1 := fun t => by
    calc h t ≤ ∫ _s, (1 : ℝ) ∂(volume : Measure I) :=
          integral_mono (integrable_of_01 (hfm'.comp (measurable_prodMk_right (y := t)))
            (fun s => h0 _ _) fun s => h1 _ _) (integrable_const 1) fun s => h1 _ _
      _ = 1 := by simp
  -- Step A
  have stepA : tb (Finset.univ : Finset (X × Y)) f = ∫ z1, G z1 ^ Fintype.card Y ∂μX := by
    have hint := integrable_prod (Finset.univ : Finset (X × Y)) (fun _ => f)
      fun _ _ => ⟨hf, 1, fun x y => by rw [abs_of_nonneg (h0 x y)]; exact h1 x y⟩
    rw [tb_eq_tBiDec, tBiDec_eq, integral_prod _ hint]
    refine integral_congr_ae (Eventually.of_forall fun z1 => ?_)
    simp only
    have e : ∀ y : Y → I, ∏ x : X × Y, f (z1 x.1) (y x.2) = ∏ j, ∏ i, f (z1 i) (y j) := by
      intro y; rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp_rw [e]
    rw [integral_fintype_prod_eq_prod (fun (_ : Y) (t : I) => ∏ i, f (z1 i) t)]
    simp [hG, Finset.prod_const, Finset.card_univ]
  -- Step C
  have stepC : ∫ z1, G z1 ∂μX = ∫ t, h t ^ Fintype.card X ∂(volume : Measure I) := by
    have := integral_integral_swap (μ := μX) (ν := (volume : Measure I))
      (f := fun z1 t => ∏ i, f (z1 i) t) hFi
    simp only [hG] at this ⊢
    rw [this]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [integral_fintype_prod_eq_prod (fun (_ : X) (s : I) => f s t)]
    simp [hh, Finset.prod_const, Finset.card_univ]
  have stepD : ∫ q, f q.1 q.2 ∂((volume : Measure I).prod volume) = ∫ t, h t ∂volume := by
    rw [integral_prod_symm _ hfi]
  rw [stepA, stepD, pow_mul]
  calc ((∫ t, h t ∂volume) ^ Fintype.card X) ^ Fintype.card Y
      ≤ (∫ z1, G z1 ∂μX) ^ Fintype.card Y := by
        rw [stepC]
        exact pow_le_pow_left₀ (pow_nonneg (integral_nonneg hh0) _)
          (jensen_pow volume h hhm hh0 hh1 _) _
    _ ≤ ∫ z1, G z1 ^ Fintype.card Y ∂μX := jensen_pow μX G hGm hG0 hG1 _

lemma tb_abs_eq (E : Finset (X × Y)) (hne : 0 < E.card) (U : I → I → ℝ) :
    tb E (fun x y => |U x y|) = rNorm E U ^ E.card := by
  rw [tb_eq_rNorm_pow E hne _ fun _ _ => abs_nonneg _]
  simp [rNorm]

lemma rNorm_smul (E : Finset (X × Y)) (hne : 0 < E.card) (U : I → I → ℝ) (c : ℝ) :
    rNorm E (fun x y => c * U x y) = |c| * rNorm E U := by
  have e : (fun x y => |c * U x y|) = fun x y => |c| * |U x y| := by
    funext x y; exact abs_mul _ _
  unfold rNorm
  rw [e, tb_smul, Real.mul_rpow (pow_nonneg (abs_nonneg c) _)
    (tb_nonneg E _ fun _ _ => abs_nonneg _), one_div,
    Real.pow_rpow_inv_natCast (abs_nonneg c) hne.ne']

lemma rNorm_le_of (E : Finset (X × Y)) (hne : 0 < E.card) (U : I → I → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (h : tb E (fun x y => |U x y|) ≤ s ^ E.card) : rNorm E U ≤ s := by
  unfold rNorm
  calc tb E (fun x y => |U x y|) ^ ((1 : ℝ) / E.card) ≤ (s ^ E.card) ^ ((1 : ℝ) / E.card) :=
        Real.rpow_le_rpow (tb_nonneg E _ fun _ _ => abs_nonneg _) h (by positivity)
    _ = s := by rw [one_div, Real.pow_rpow_inv_natCast hs hne.ne']

lemma tb_univ_le (E : Finset (X × Y)) (f : I → I → ℝ) (hf : Measurable (Function.uncurry f))
    (h0 : ∀ x y, 0 ≤ f x y) (h1 : ∀ x y, f x y ≤ 1) :
    tb (Finset.univ : Finset (X × Y)) f ≤ tb E f := by
  classical
  have hk : IsKernel f := ⟨hf, 1, fun x y => by rw [abs_of_nonneg (h0 x y)]; exact h1 x y⟩
  refine integral_mono (integrable_prod _ (fun _ => f) fun _ _ => hk)
    (integrable_prod _ (fun _ => f) fun _ _ => hk) fun z => ?_
  simp only
  rw [← Finset.prod_sdiff (Finset.subset_univ E)]
  have := prod_mem_01 (Finset.univ \ E) (fun p : X × Y => f (z.1 p.1) (z.2 p.2))
    (fun _ => h0 _ _) fun _ => h1 _ _
  have h2 := (prod_mem_01 E (fun p : X × Y => f (z.1 p.1) (z.2 p.2)) (fun _ => h0 _ _)
    fun _ => h1 _ _).1
  exact mul_le_of_le_one_left h2 this.2

lemma rNorm_posdef (E : Finset (X × Y)) (_hne : 0 < E.card) (U : I → I → ℝ) (hU : IsKernel U)
    (h : rNorm E U = 0) : AEEq volume U (fun _ _ => 0) := by
  by_contra hne'
  obtain ⟨hm, M, hM⟩ := hU
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set f : I → I → ℝ := fun x y => M'⁻¹ * |U x y| with hfdef
  have hfm : Measurable (Function.uncurry f) := (hm.abs).const_mul _
  have hf0 : ∀ x y, 0 ≤ f x y := fun x y => mul_nonneg (inv_nonneg.2 hM'pos.le) (abs_nonneg _)
  have hf1 : ∀ x y, f x y ≤ 1 := fun x y => by
    rw [hfdef, inv_mul_le_one₀ hM'pos]; exact (hM x y).trans (le_max_left _ _)
  have hint : Integrable (fun q : I × I => |U q.1 q.2|) ((volume : Measure I).prod volume) :=
    Integrable.of_bound (hm.abs).aestronglyMeasurable M (Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_abs]; exact hM _ _)
  have hpos : 0 < ∫ q, |U q.1 q.2| ∂((volume : Measure I).prod volume) := by
    refine lt_of_le_of_ne (integral_nonneg fun _ => abs_nonneg _) (Ne.symm fun h0 => hne' ?_)
    have := (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hint).1 h0
    filter_upwards [this] with q hq
    simpa using hq
  have hfint : ∫ q, f q.1 q.2 ∂((volume : Measure I).prod volume) =
      M'⁻¹ * ∫ q, |U q.1 q.2| ∂((volume : Measure I).prod volume) := integral_const_mul _ _
  have h3 := (tb_univ_ge (X := X) (Y := Y) f hfm hf0 hf1).trans (tb_univ_le E f hfm hf0 hf1)
  have h4 : 0 < tb E f := lt_of_lt_of_le (pow_pos (by rw [hfint]; positivity) _) h3
  have h5 : tb E (fun x y => |U x y|) = M' ^ E.card * tb E f := by
    rw [← tb_smul]
    congr 1
    funext x y
    simp only [hfdef]
    field_simp
  have h6 : 0 < rNorm E U := Real.rpow_pos_of_pos (by rw [h5]; positivity) _
  exact h6.ne' h

theorem lemma_2_3_1_aux (E : Finset (X × Y)) (hne : 0 < E.card) :
    IsWeaklyNorming E ↔ ConvexOnNonnegKernels E := by
  constructor
  · intro hW U V hU hV hU0 hV0 a ha
    have h1a : 0 ≤ 1 - a := sub_nonneg.2 ha.2
    have hW0 : ∀ x y, 0 ≤ a * U x y + (1 - a) * V x y := fun x y =>
      add_nonneg (mul_nonneg ha.1 (hU0 x y)) (mul_nonneg h1a (hV0 x y))
    rw [tb_eq_rNorm_pow E hne _ hW0, tb_eq_rNorm_pow E hne _ hU0, tb_eq_rNorm_pow E hne _ hV0]
    have htri : rNorm E (fun x y => a * U x y + (1 - a) * V x y) ≤
        a * rNorm E U + (1 - a) * rNorm E V := by
      refine (hW.2.1 _ _ (isKernel_smul hU a) (isKernel_smul hV (1 - a))).trans_eq ?_
      rw [hW.1 U hU, hW.1 V hV, abs_of_nonneg ha.1, abs_of_nonneg h1a]
    calc rNorm E (fun x y => a * U x y + (1 - a) * V x y) ^ E.card
        ≤ (a * rNorm E U + (1 - a) * rNorm E V) ^ E.card :=
          pow_le_pow_left₀ (rNorm_nonneg E _) htri _
      _ ≤ a * rNorm E U ^ E.card + (1 - a) * rNorm E V ^ E.card := by
          have := (convexOn_pow E.card).2 (mem_Ici.2 (rNorm_nonneg E U))
            (mem_Ici.2 (rNorm_nonneg E V)) ha.1 h1a (by ring)
          simpa only [smul_eq_mul] using this
  · intro hC
    refine ⟨fun U _ c => rNorm_smul E hne U c, fun U V hU hV => ?_,
      fun U hU h => rNorm_posdef E hne U hU h⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set p := rNorm E U + ε / 2 with hp
    set q := rNorm E V + ε / 2 with hq
    have hp0 : 0 < p := add_pos_of_nonneg_of_pos (rNorm_nonneg E U) (half_pos hε)
    have hq0 : 0 < q := add_pos_of_nonneg_of_pos (rNorm_nonneg E V) (half_pos hε)
    have hpq : 0 < p + q := add_pos hp0 hq0
    have hA : tb E (fun x y => p⁻¹ * |U x y|) ≤ 1 := by
      rw [tb_smul, tb_abs_eq E hne, ← mul_pow]
      refine pow_le_one₀ (mul_nonneg (inv_nonneg.2 hp0.le) (rNorm_nonneg E U)) ?_
      rw [inv_mul_le_one₀ hp0]; linarith
    have hB : tb E (fun x y => q⁻¹ * |V x y|) ≤ 1 := by
      rw [tb_smul, tb_abs_eq E hne, ← mul_pow]
      refine pow_le_one₀ (mul_nonneg (inv_nonneg.2 hq0.le) (rNorm_nonneg E V)) ?_
      rw [inv_mul_le_one₀ hq0]; linarith
    set a := p / (p + q) with ha
    have ha1 : 1 - a = q / (p + q) := by rw [ha]; field_simp; ring
    have haI : a ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hp0.le hpq.le,
      (div_le_one hpq).2 (by linarith)⟩
    have hconv := hC (fun x y => p⁻¹ * |U x y|) (fun x y => q⁻¹ * |V x y|)
      (isKernel_smul (isKernel_abs hU) _) (isKernel_smul (isKernel_abs hV) _)
      (fun x y => mul_nonneg (inv_nonneg.2 hp0.le) (abs_nonneg _))
      (fun x y => mul_nonneg (inv_nonneg.2 hq0.le) (abs_nonneg _)) a haI
    have hcomb : (fun x y => a * (p⁻¹ * |U x y|) + (1 - a) * (q⁻¹ * |V x y|)) =
        fun x y => (p + q)⁻¹ * (|U x y| + |V x y|) := by
      funext x y; rw [ha1, ha]; field_simp
    rw [hcomb] at hconv
    have hle1 : tb E (fun x y => (p + q)⁻¹ * |U x y + V x y|) ≤ 1 := by
      refine le_trans ?_ (hconv.trans ?_)
      · refine tBiDec_mono E _ _ (fun _ _ => isKernel_smul (isKernel_abs (isKernel_add hU hV)) _)
          (fun _ _ => isKernel_smul (isKernel_add (isKernel_abs hU) (isKernel_abs hV)) _)
          (fun _ _ x y => mul_nonneg (inv_nonneg.2 hpq.le) (abs_nonneg _))
          fun _ _ x y => mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_nonneg.2 hpq.le)
      · calc a * tb E (fun x y => p⁻¹ * |U x y|) + (1 - a) * tb E (fun x y => q⁻¹ * |V x y|)
            ≤ a * 1 + (1 - a) * 1 := add_le_add (mul_le_mul_of_nonneg_left hA haI.1)
              (mul_le_mul_of_nonneg_left hB (sub_nonneg.2 haI.2))
          _ = 1 := by ring
    have : rNorm E (fun x y => U x y + V x y) ≤ p + q := by
      refine rNorm_le_of E hne _ hpq.le ?_
      rw [tb_smul, inv_pow, inv_mul_le_one₀ (pow_pos hpq _)] at hle1
      exact hle1
    linarith

/-! ### Lemma 2.3(2): expansion, a.e. congruence, continuity -/

open scoped Classical in
/-- The decoration putting `U` on `t` and `V` elsewhere. -/
noncomputable def decS (t : Finset (X × Y)) (U V : I → I → ℝ) : X × Y → I → I → ℝ := by
  classical exact fun p => if p ∈ t then U else V

open scoped Classical in
lemma tb_expand (E : Finset (X × Y)) (U V : I → I → ℝ) (hU : IsKernel U) (hV : IsKernel V)
    (a b : ℝ) :
    tb E (fun x y => a * U x y + b * V x y) =
      ∑ t ∈ E.powerset, a ^ t.card * b ^ (E \ t).card * tBiDec volume E (decS t U V) := by
  classical
  have hpt : ∀ z : (X → I) × (Y → I), ∏ p ∈ E, (a * U (z.1 p.1) (z.2 p.2) + b * V (z.1 p.1) (z.2 p.2))
      = ∑ t ∈ E.powerset, a ^ t.card * b ^ (E \ t).card *
          ∏ p ∈ E, decS t U V p (z.1 p.1) (z.2 p.2) := by
    intro z
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htE := Finset.mem_powerset.1 ht
    rw [← Finset.prod_sdiff htE (f := fun p => decS t U V p (z.1 p.1) (z.2 p.2))]
    have h1 : ∏ p ∈ t, decS t U V p (z.1 p.1) (z.2 p.2) = ∏ p ∈ t, U (z.1 p.1) (z.2 p.2) :=
      Finset.prod_congr rfl fun p hp => by simp [decS, hp]
    have h2 : ∏ p ∈ E \ t, decS t U V p (z.1 p.1) (z.2 p.2) =
        ∏ p ∈ E \ t, V (z.1 p.1) (z.2 p.2) :=
      Finset.prod_congr rfl fun p hp => by simp [decS, (Finset.mem_sdiff.1 hp).2]
    rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_const]
    ring
  rw [tb_eq_tBiDec, tBiDec_eq]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_const_mul]
    rfl
  · intro t _
    refine (integrable_prod E (decS t U V) fun p _ => ?_).const_mul _
    unfold decS; split_ifs <;> assumption

lemma tb_congr_ae (E : Finset (X × Y)) {U U' : I → I → ℝ} (h : AEEq volume U U') :
    tb E U = tb E U' := by
  rw [tb_eq_tBiDec, tb_eq_tBiDec, tBiDec_eq, tBiDec_eq]
  refine integral_congr_ae ?_
  have hp : ∀ p ∈ E, ∀ᵐ z ∂(ρ X Y), U (z.1 p.1) (z.2 p.2) = U' (z.1 p.1) (z.2 p.2) := by
    intro p _
    have hmp : MeasurePreserving (fun z : (X → I) × (Y → I) => (z.1 p.1, z.2 p.2)) (ρ X Y)
        ((volume : Measure I).prod volume) :=
      (measurePreserving_eval (fun _ : X => (volume : Measure I)) p.1).prod
        (measurePreserving_eval (fun _ : Y => (volume : Measure I)) p.2)
    exact hmp.quasiMeasurePreserving.ae h
  have := (Filter.eventually_all_finset E).2 hp
  filter_upwards [this] with z hz
  exact Finset.prod_congr rfl hz

open scoped Classical in
lemma continuous_tb_comb (E : Finset (X × Y)) (U V : I → I → ℝ) (hU : IsKernel U)
    (hV : IsKernel V) {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β) :
    Continuous fun s => tb E (fun x y => α s * U x y + β s * V x y) := by
  simp_rw [tb_expand E U V hU hV]
  fun_prop

lemma tb_one (E : Finset (X × Y)) : tb E (fun _ _ => (1 : ℝ)) = 1 := by
  simp [tb, tBi]

lemma tb_const (E : Finset (X × Y)) (c : ℝ) : tb E (fun _ _ => c) = c ^ E.card := by
  have := tb_smul E (fun _ _ => (1 : ℝ)) c
  simp only [mul_one] at this
  rw [this, tb_one, mul_one]

lemma tb_neg (E : Finset (X × Y)) (U : I → I → ℝ) :
    tb E (fun x y => -U x y) = (-1) ^ E.card * tb E U := by
  rw [← tb_smul]; simp

lemma isKernel_neg {U : I → I → ℝ} (hU : IsKernel U) : IsKernel (fun x y => -U x y) := by
  have := isKernel_smul hU (-1)
  simpa using this

lemma isKernel_const (c : ℝ) : IsKernel (fun _ _ : I => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

lemma not_aeEq_const {c d : ℝ} (h : c ≠ d) :
    ¬ AEEq volume (fun _ _ : I => c) (fun _ _ : I => d) := by
  intro hae
  obtain ⟨_, hx⟩ := hae.exists
  exact h hx

lemma hNorm_smul (E : Finset (X × Y)) (hne : 0 < E.card) (U : I → I → ℝ) (c : ℝ) :
    hNorm E (fun x y => c * U x y) = |c| * hNorm E U := by
  unfold hNorm
  rw [tb_smul, abs_mul, abs_pow, Real.mul_rpow (pow_nonneg (abs_nonneg c) _) (abs_nonneg _),
    one_div, Real.pow_rpow_inv_natCast (abs_nonneg c) hne.ne']

lemma hNorm_le_of (E : Finset (X × Y)) (hne : 0 < E.card) (U : I → I → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (h : |tb E U| ≤ s ^ E.card) : hNorm E U ≤ s := by
  unfold hNorm
  calc |tb E U| ^ ((1 : ℝ) / E.card) ≤ (s ^ E.card) ^ ((1 : ℝ) / E.card) :=
        Real.rpow_le_rpow (abs_nonneg _) h (by positivity)
    _ = s := by rw [one_div, Real.pow_rpow_inv_natCast hs hne.ne']

lemma hNorm_nonneg (E : Finset (X × Y)) (U : I → I → ℝ) : 0 ≤ hNorm E U :=
  Real.rpow_nonneg (abs_nonneg _) _

lemma abs_tb_eq_hNorm_pow (E : Finset (X × Y)) (hne : 0 < E.card) (U : I → I → ℝ) :
    |tb E U| = hNorm E U ^ E.card := by
  unfold hNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div,
    inv_mul_cancel₀ (by exact_mod_cast hne.ne'), Real.rpow_one]

/-- The normalisation argument for the triangle inequality of `|t|^{1/m}`, given convexity on
pairs of kernels and nonnegativity of `t`. -/
lemma hNorm_triangle_of (E : Finset (X × Y)) (hne : 0 < E.card)
    (hF0 : ∀ W, IsKernel W → 0 ≤ tb E W)
    (hconv : ∀ A B : I → I → ℝ, IsKernel A → IsKernel B → ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
      tb E (fun x y => a * A x y + (1 - a) * B x y) ≤ a * tb E A + (1 - a) * tb E B)
    (U V : I → I → ℝ) (hU : IsKernel U) (hV : IsKernel V) :
    hNorm E (fun x y => U x y + V x y) ≤ hNorm E U + hNorm E V := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set p := hNorm E U + ε / 2 with hp
  set q := hNorm E V + ε / 2 with hq
  have hp0 : 0 < p := add_pos_of_nonneg_of_pos (hNorm_nonneg E U) (half_pos hε)
  have hq0 : 0 < q := add_pos_of_nonneg_of_pos (hNorm_nonneg E V) (half_pos hε)
  have hpq : 0 < p + q := add_pos hp0 hq0
  have hA : tb E (fun x y => p⁻¹ * U x y) ≤ 1 := by
    rw [tb_smul, ← abs_of_nonneg (hF0 U hU), abs_tb_eq_hNorm_pow E hne, ← mul_pow]
    refine pow_le_one₀ (mul_nonneg (inv_nonneg.2 hp0.le) (hNorm_nonneg E U)) ?_
    rw [inv_mul_le_one₀ hp0]; linarith
  have hB : tb E (fun x y => q⁻¹ * V x y) ≤ 1 := by
    rw [tb_smul, ← abs_of_nonneg (hF0 V hV), abs_tb_eq_hNorm_pow E hne, ← mul_pow]
    refine pow_le_one₀ (mul_nonneg (inv_nonneg.2 hq0.le) (hNorm_nonneg E V)) ?_
    rw [inv_mul_le_one₀ hq0]; linarith
  set a := p / (p + q) with ha
  have ha1 : 1 - a = q / (p + q) := by rw [ha]; field_simp; ring
  have haI : a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hp0 hpq, (div_lt_one hpq).2 (by linarith)⟩
  have hc := hconv (fun x y => p⁻¹ * U x y) (fun x y => q⁻¹ * V x y)
    (isKernel_smul hU _) (isKernel_smul hV _) a haI
  have hcomb : (fun x y => a * (p⁻¹ * U x y) + (1 - a) * (q⁻¹ * V x y)) =
      fun x y => (p + q)⁻¹ * (U x y + V x y) := by
    funext x y; rw [ha1, ha]; field_simp
  rw [hcomb] at hc
  have hle1 : tb E (fun x y => (p + q)⁻¹ * (U x y + V x y)) ≤ 1 := by
    refine hc.trans ?_
    calc a * tb E (fun x y => p⁻¹ * U x y) + (1 - a) * tb E (fun x y => q⁻¹ * V x y)
        ≤ a * 1 + (1 - a) * 1 := add_le_add (mul_le_mul_of_nonneg_left hA haI.1.le)
          (mul_le_mul_of_nonneg_left hB (sub_nonneg.2 haI.2.le))
      _ = 1 := by ring
  have : hNorm E (fun x y => U x y + V x y) ≤ p + q := by
    refine hNorm_le_of E hne _ hpq.le ?_
    rw [tb_smul, inv_pow, inv_mul_le_one₀ (pow_pos hpq _)] at hle1
    rwa [abs_of_nonneg (hF0 _ (isKernel_add hU hV))]
  linarith

lemma strict_to_norming (E : Finset (X × Y)) (hne : 0 < E.card)
    (hS : StrictConvexOnKernels E) : IsNorming E := by
  -- `m` is even
  have heven : Even E.card := by
    have h := hS (fun _ _ => (1 : ℝ)) (fun _ _ => (-1 : ℝ)) (isKernel_const 1) (isKernel_const (-1))
      (not_aeEq_const (by norm_num)) (1 / 2) ⟨by norm_num, by norm_num⟩
    have e : (fun (x y : I) => (1 / 2 : ℝ) * 1 + (1 - 1 / 2) * (-1)) = fun _ _ => (0 : ℝ) := by
      funext x y; norm_num
    rw [e, tb_const, tb_const, tb_const, zero_pow hne.ne'] at h
    rcases Nat.even_or_odd E.card with h' | h'
    · exact h'
    · rw [h'.neg_one_pow] at h; norm_num at h
  -- positivity
  have hpos : ∀ W, IsKernel W → ¬ AEEq volume W (fun _ _ => 0) → 0 < tb E W := by
    intro W hW hW0
    have hnot : ¬ AEEq volume W (fun x y => -W x y) := by
      intro h; apply hW0
      filter_upwards [h] with q hq
      linarith
    have h := hS W (fun x y => -W x y) hW ((isKernel_neg hW)) hnot (1 / 2)
      ⟨by norm_num, by norm_num⟩
    have e : (fun x y => (1 / 2 : ℝ) * W x y + (1 - 1 / 2) * -W x y) = fun _ _ => (0 : ℝ) := by
      funext x y; ring
    rw [e, tb_const, zero_pow hne.ne', tb_neg, heven.neg_one_pow] at h
    linarith
  have hF0 : ∀ W, IsKernel W → 0 ≤ tb E W := by
    intro W hW
    by_cases h : AEEq volume W (fun _ _ => 0)
    · rw [tb_congr_ae E h, tb_const, zero_pow hne.ne']
    · exact (hpos W hW h).le
  have hconv : ∀ A B : I → I → ℝ, IsKernel A → IsKernel B → ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
      tb E (fun x y => a * A x y + (1 - a) * B x y) ≤ a * tb E A + (1 - a) * tb E B := by
    intro A B hA hB a ha
    by_cases h : AEEq volume A B
    · have h1 : AEEq volume (fun x y => a * A x y + (1 - a) * B x y) A := by
        filter_upwards [h] with q hq
        rw [← hq]; ring
      rw [tb_congr_ae E h1, ← tb_congr_ae E h]; ring_nf; exact le_rfl
    · exact (hS A B hA hB h a ha).le
  refine ⟨fun U _ c => hNorm_smul E hne U c,
    fun U V hU hV => hNorm_triangle_of E hne hF0 hconv U V hU hV, fun U hU h => ?_⟩
  by_contra h'
  have := hpos U hU h'
  have h2 : |tb E U| = 0 := by
    rw [abs_tb_eq_hNorm_pow E hne, h, zero_pow hne.ne']
  rw [abs_of_pos this] at h2
  exact this.ne' h2

/-! ### The Hölder inequality for norming graphs -/

section Holder

open scoped Classical

/-- Extension of an `E`-indexed decoration by zero. -/
noncomputable def ext (E : Finset (X × Y)) (χ : E → I → I → ℝ) : X × Y → I → I → ℝ := by
  classical exact fun p => if h : p ∈ E then χ ⟨p, h⟩ else fun _ _ => 0

/-- The decorated density of an `E`-indexed decoration. -/
noncomputable def T (E : Finset (X × Y)) (χ : E → I → I → ℝ) : ℝ := tBiDec volume E (ext E χ)

lemma tBiDec_congr (E : Finset (X × Y)) {U V : X × Y → I → I → ℝ} (h : ∀ p ∈ E, U p = V p) :
    tBiDec volume E U = tBiDec volume E V := by
  unfold tBiDec
  congr 1
  funext z
  exact Finset.prod_congr rfl fun p hp => by rw [h p hp]

omit [Fintype X] [Fintype Y] in
lemma ext_mem (E : Finset (X × Y)) (χ : E → I → I → ℝ) (p : X × Y) (hp : p ∈ E) :
    ext E χ p = χ ⟨p, hp⟩ := by
  simp [ext, hp]

lemma T_eq_prod (E : Finset (X × Y)) (χ : E → I → I → ℝ) :
    T E χ = ∫ z, ∏ e : E, χ e (z.1 e.1.1) (z.2 e.1.2) ∂(ρ X Y) := by
  unfold T
  rw [tBiDec_eq]
  congr 1
  funext z
  rw [← Finset.prod_coe_sort E]
  exact Finset.prod_congr rfl fun e _ => by rw [ext_mem E χ e.1 e.2]

omit [Fintype X] [Fintype Y] in
lemma isKernel_ext (E : Finset (X × Y)) (χ : E → I → I → ℝ) (hχ : ∀ e, IsKernel (χ e)) :
    ∀ p ∈ E, IsKernel (ext E χ p) := fun p hp => by rw [ext_mem E χ p hp]; exact hχ _

lemma T_sqK {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (E : Finset (X × Y)) (χ : E → I → I → ℝ) (hχ : ∀ e, IsKernel (χ e)) :
    T E (fun e => sqK φ (χ e)) = T E χ ^ 2 := by
  unfold T
  rw [← tBiDec_sqK hφ E (ext E χ) (isKernel_ext E χ hχ)]
  refine tBiDec_congr E fun p hp => ?_
  rw [ext_mem _ _ p hp, ext_mem _ _ p hp]

lemma T_iter {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (E : Finset (X × Y)) (χ : E → I → I → ℝ) (hχ : ∀ e, IsKernel (χ e)) (j : ℕ) :
    T E (fun e => (sqK φ)^[j] (χ e)) = T E χ ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hk : ∀ e, IsKernel ((sqK φ)^[j] (χ e)) := fun e => by
      clear ih
      induction j with
      | zero => exact hχ e
      | succ j ih2 =>
        rw [Function.iterate_succ_apply']
        exact isKernel_sqK hφ.measurable ih2
    simp_rw [Function.iterate_succ_apply']
    rw [T_sqK hφ E _ hk, ih, ← pow_mul, pow_succ]

lemma isKernel_iter {φ : I → I × I} (hφ : Measurable φ) {f : I → I → ℝ} (hf : IsKernel f)
    (j : ℕ) : IsKernel ((sqK φ)^[j] f) := by
  induction j with
  | zero => exact hf
  | succ j ih => rw [Function.iterate_succ_apply']; exact isKernel_sqK hφ ih

lemma hNorm_sqK {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (E : Finset (X × Y)) (f : I → I → ℝ) (hf : IsKernel f) :
    hNorm E (sqK φ f) = hNorm E f ^ 2 := by
  have h2 : tb E (sqK φ f) = tb E f ^ 2 := tBiDec_sqK hφ E (fun _ => f) fun _ _ => hf
  unfold hNorm
  rw [h2, abs_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _), mul_comm]

lemma hNorm_iter {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (E : Finset (X × Y)) (f : I → I → ℝ) (hf : IsKernel f) (j : ℕ) :
    hNorm E ((sqK φ)^[j] f) = hNorm E f ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', hNorm_sqK hφ E _ (isKernel_iter hφ.measurable hf j), ih,
      ← pow_mul, pow_succ]

lemma hNorm_sum (E : Finset (X × Y)) (hE : IsNorming E) {ι : Type*} (s : Finset ι)
    (g : ι → I → I → ℝ) (hg : ∀ i ∈ s, IsKernel (g i)) :
    hNorm E (fun x y => ∑ i ∈ s, g i x y) ≤ ∑ i ∈ s, hNorm E (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hE.1 (fun _ _ => 0) ⟨measurable_const, 0, fun _ _ => by simp⟩ 0
    simp only [mul_zero, abs_zero, zero_mul] at this
    simp [this]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine (hE.2.1 _ _ (hg a (Finset.mem_insert_self a s))
      (isKernel_sum s fun i hi => hg i (Finset.mem_insert_of_mem hi))).trans ?_
    exact add_le_add le_rfl (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- Multilinear expansion of `t_bi(H, Σ_e a_e ψ_e)`. -/
lemma tb_sum_expand (E : Finset (X × Y)) (ψ : E → I → I → ℝ) (hψ : ∀ e, IsKernel (ψ e))
    (a : E → ℝ) :
    tb E (fun x y => ∑ e, a e * ψ e x y) =
      ∑ φ : E → E, (∏ e, a (φ e)) * T E (fun e => ψ (φ e)) := by
  classical
  have hpt : ∀ z : (X → I) × (Y → I), ∏ p ∈ E, (∑ e, a e * ψ e (z.1 p.1) (z.2 p.2)) =
      ∑ φ : E → E, (∏ e, a (φ e)) * ∏ e : E, ψ (φ e) (z.1 e.1.1) (z.2 e.1.2) := by
    intro z
    rw [← Finset.prod_coe_sort E, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [tb_eq_tBiDec, tBiDec_eq]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun φ _ => ?_
    rw [integral_const_mul, T_eq_prod]
  · intro φ _
    refine Integrable.const_mul ?_ _
    have := integrable_prod E (ext E fun e => ψ (φ e)) (isKernel_ext E _ fun e => hψ _)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [← Finset.prod_coe_sort E]
    exact Finset.prod_congr rfl fun e _ => by rw [ext_mem E _ e.1 e.2]

/-- The sign of a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> norm_num [sgn]

/-- The polarization coefficient. -/
noncomputable def coef (E : Finset (X × Y)) (φ : E → E) : ℝ :=
  ∑ ε : E → Bool, (∏ e, sgn (ε e)) * ∏ e, sgn (ε (φ e))

omit [Fintype X] [Fintype Y] in
lemma coef_nonneg (E : Finset (X × Y)) (φ : E → E) : 0 ≤ coef E φ := by
  classical
  have h1 : ∀ ε : E → Bool, (∏ e, sgn (ε e)) * ∏ e, sgn (ε (φ e)) =
      ∏ j, sgn (ε j) ^ (Fintype.card {i // φ i = j} + 1) := by
    intro ε
    rw [← Fintype.prod_fiberwise' φ (fun j => sgn (ε j)), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_const, Finset.card_univ, pow_succ, mul_comm]
  unfold coef
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (j : E) (b : Bool) => sgn b ^ (Fintype.card {i // φ i = j} + 1))]
  refine Finset.prod_nonneg fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [sgn, ite_true, one_pow, Bool.false_eq_true, ite_false]
  rcases neg_one_pow_eq_or ℝ (Fintype.card {i // φ i = j} + 1) with h | h <;> rw [h] <;> norm_num

omit [Fintype X] [Fintype Y] in
lemma coef_id (E : Finset (X × Y)) : coef E id = 2 ^ E.card := by
  unfold coef
  simp only [id]
  have : ∀ ε : E → Bool, (∏ e, sgn (ε e)) * ∏ e, sgn (ε e) = 1 := fun ε => by
    rw [← Finset.prod_mul_distrib]; simp [sgn_sq]
  simp_rw [this]
  simp

/-- The polarization identity. -/
lemma polar (E : Finset (X × Y)) (ψ : E → I → I → ℝ) (hψ : ∀ e, IsKernel (ψ e)) :
    ∑ ε : E → Bool, (∏ e, sgn (ε e)) * tb E (fun x y => ∑ e, sgn (ε e) * ψ e x y) =
      ∑ φ : E → E, coef E φ * T E (fun e => ψ (φ e)) := by
  simp_rw [tb_sum_expand E ψ hψ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ _ => ?_
  unfold coef
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ε _ => ?_
  ring

lemma norming_normalized (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card)
    (χ : E → I → I → ℝ) (hχ : ∀ e, IsKernel (χ e)) (h1 : ∀ e, hNorm E (χ e) ≤ 1) :
    |T E χ| ≤ 1 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_split
  have key : ∀ k : ℕ, |T E χ| ^ (2 ^ (k + 1)) ≤ (E.card : ℝ) ^ E.card := by
    intro k
    set ψ : E → I → I → ℝ := fun e => (sqK φ)^[k + 1] (χ e) with hψdef
    have hψ : ∀ e, IsKernel (ψ e) := fun e => isKernel_iter hφ.measurable (hχ e) _
    have hψ1 : ∀ e, hNorm E (ψ e) ≤ 1 := fun e => by
      rw [hψdef, hNorm_iter hφ E _ (hχ e)]
      exact pow_le_one₀ (hNorm_nonneg E _) (h1 e)
    have hTψ : ∀ φ' : E → E, T E (fun e => ψ (φ' e)) = T E (fun e => χ (φ' e)) ^ (2 ^ (k + 1)) :=
      fun φ' => T_iter hφ E (fun e => χ (φ' e)) (fun e => hχ _) (k + 1)
    have hev : ∀ r : ℝ, 0 ≤ r ^ (2 ^ (k + 1)) := fun r => by
      rw [pow_succ, pow_mul]; positivity
    -- lower bound
    have hlow : 2 ^ E.card * |T E χ| ^ (2 ^ (k + 1)) ≤
        ∑ φ' : E → E, coef E φ' * T E (fun e => ψ (φ' e)) := by
      have hid := Finset.single_le_sum (f := fun φ' : E → E => coef E φ' * T E (fun e => ψ (φ' e)))
        (fun φ' _ => mul_nonneg (coef_nonneg E φ') (by rw [hTψ]; exact hev _))
        (Finset.mem_univ id)
      simp only [id] at hid
      rw [coef_id, hTψ] at hid
      have : |T E χ| ^ (2 ^ (k + 1)) = T E χ ^ (2 ^ (k + 1)) := by
        rw [pow_succ, pow_mul, pow_mul, ← abs_pow, sq_abs]
      rw [this]
      exact hid
    -- upper bound
    have hup : ∑ ε : E → Bool, (∏ e, sgn (ε e)) * tb E (fun x y => ∑ e, sgn (ε e) * ψ e x y) ≤
        2 ^ E.card * (E.card : ℝ) ^ E.card := by
      have hb : ∀ ε : E → Bool, (∏ e, sgn (ε e)) * tb E (fun x y => ∑ e, sgn (ε e) * ψ e x y) ≤
          (E.card : ℝ) ^ E.card := by
        intro ε
        refine (le_abs_self _).trans ?_
        rw [abs_mul, Finset.abs_prod]
        simp only [abs_sgn, Finset.prod_const_one, one_mul]
        rw [abs_tb_eq_hNorm_pow E hne]
        refine pow_le_pow_left₀ (hNorm_nonneg E _) ?_ _
        refine (hNorm_sum E hE Finset.univ (fun e x y => sgn (ε e) * ψ e x y)
          fun e _ => isKernel_smul (hψ e) _).trans ?_
        calc ∑ e, hNorm E (fun x y => sgn (ε e) * ψ e x y) ≤ ∑ _e : E, (1 : ℝ) := by
              refine Finset.sum_le_sum fun e _ => ?_
              rw [hNorm_smul E hne, abs_sgn, one_mul]; exact hψ1 e
          _ = E.card := by simp
      calc _ ≤ ∑ _ε : E → Bool, (E.card : ℝ) ^ E.card := Finset.sum_le_sum fun ε _ => hb ε
        _ = 2 ^ E.card * (E.card : ℝ) ^ E.card := by
          simp
    rw [polar E ψ hψ] at hup
    have h2 : (0 : ℝ) < 2 ^ E.card := by positivity
    have := hlow.trans hup
    exact le_of_mul_le_mul_left this h2
  by_contra hv
  replace hv := not_le.mp hv
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((E.card : ℝ) ^ E.card) hv
  have h3 : |T E χ| ^ k ≤ |T E χ| ^ (2 ^ (k + 1)) :=
    pow_le_pow_right₀ hv.le ((Nat.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)))
  linarith [key k]

end Holder

lemma norming_holder (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card)
    (f : X × Y → I → I → ℝ) (hf : ∀ p ∈ E, IsKernel (f p)) :
    |tBiDec volume E f| ≤ ∏ p ∈ E, hNorm E (f p) := by
  have key : ∀ ε > (0 : ℝ), |tBiDec volume E f| ≤ ∏ p ∈ E, (hNorm E (f p) + ε) := by
    intro ε hε
    set c : X × Y → ℝ := fun p => hNorm E (f p) + ε with hc
    have cpos : ∀ p, 0 < c p := fun p => add_pos_of_nonneg_of_pos (hNorm_nonneg E _) hε
    have hn := norming_normalized E hE hne (fun e x y => (c e.1)⁻¹ * f e.1 x y)
      (fun e => isKernel_smul (hf e.1 e.2) _)
      (fun e => by
        rw [hNorm_smul E hne, abs_of_pos (inv_pos.2 (cpos _)), inv_mul_le_one₀ (cpos _)]
        simp [hc, hε.le])
    have hT : T E (fun e x y => (c e.1)⁻¹ * f e.1 x y) =
        (∏ p ∈ E, (c p)⁻¹) * tBiDec volume E f := by
      unfold T
      rw [← tBiDec_smul E f (fun p => (c p)⁻¹)]
      exact tBiDec_congr E fun p hp => by rw [ext_mem _ _ p hp]
    rw [hT, abs_mul, abs_of_pos (Finset.prod_pos fun p _ => inv_pos.2 (cpos p)),
      Finset.prod_inv_distrib, inv_mul_le_one₀ (Finset.prod_pos fun p _ => cpos p)] at hn
    exact hn
  have hcont : Tendsto (fun ε : ℝ => ∏ p ∈ E, (hNorm E (f p) + ε)) (𝓝[>] 0)
      (𝓝 (∏ p ∈ E, hNorm E (f p))) := by
    have : Continuous (fun ε : ℝ => ∏ p ∈ E, (hNorm E (f p) + ε)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

open scoped Classical in
lemma holder_two (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card)
    (U V : I → I → ℝ) (hU : IsKernel U) (hV : IsKernel V) (t : Finset (X × Y)) (ht : t ⊆ E) :
    |tBiDec volume E (decS t U V)| ≤ hNorm E U ^ t.card * hNorm E V ^ (E \ t).card := by
  refine (norming_holder E hE hne _ fun p _ => by unfold decS; split_ifs <;> assumption).trans_eq ?_
  rw [← Finset.prod_sdiff ht, mul_comm]
  congr 1
  · rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun p hp => by simp [decS, hp]
  · rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun p hp => by simp [decS, (Finset.mem_sdiff.1 hp).2]

/-- `F(U+V) + F(U-V) ≤ (u+v)^m + (u-v)^m` (from Hölder; Hatami's inequality in this form). -/
lemma hatami_ineq (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card)
    (U V : I → I → ℝ) (hU : IsKernel U) (hV : IsKernel V) :
    tb E (fun x y => U x y + V x y) + tb E (fun x y => U x y - V x y) ≤
      (hNorm E U + hNorm E V) ^ E.card + (hNorm E U - hNorm E V) ^ E.card := by
  classical
  set u := hNorm E U
  set v := hNorm E V
  have e1 : (fun x y => U x y + V x y) = fun x y => 1 * U x y + 1 * V x y := by
    funext x y; ring
  have e2 : (fun x y => U x y - V x y) = fun x y => 1 * U x y + (-1) * V x y := by
    funext x y; ring
  rw [e1, e2, tb_expand E U V hU hV, tb_expand E U V hU hV, ← Finset.sum_add_distrib]
  have r1 : (u + v) ^ E.card = ∑ t ∈ E.powerset, u ^ t.card * v ^ (E \ t).card := by
    rw [← Finset.prod_const, Finset.prod_add]
    simp [Finset.prod_const]
  have r2 : (u - v) ^ E.card = ∑ t ∈ E.powerset, (-1) ^ (E \ t).card * (u ^ t.card *
      v ^ (E \ t).card) := by
    rw [sub_eq_add_neg, ← Finset.prod_const, Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_const, Finset.prod_const, neg_pow]
    ring
  rw [r1, r2, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t ht => ?_
  have htE := Finset.mem_powerset.1 ht
  have hH := holder_two E hE hne U V hU hV t htE
  simp only [one_pow, one_mul]
  have hc : 0 ≤ 1 + (-1 : ℝ) ^ (E \ t).card := by
    rcases neg_one_pow_eq_or ℝ (E \ t).card with h | h <;> rw [h] <;> norm_num
  calc tBiDec volume E (decS t U V) + (-1) ^ (E \ t).card * tBiDec volume E (decS t U V)
      = (1 + (-1) ^ (E \ t).card) * tBiDec volume E (decS t U V) := by ring
    _ ≤ (1 + (-1) ^ (E \ t).card) * |tBiDec volume E (decS t U V)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hc
    _ ≤ (1 + (-1) ^ (E \ t).card) * (u ^ t.card * v ^ (E \ t).card) :=
        mul_le_mul_of_nonneg_left hH hc
    _ = _ := by ring

/-! ### Nonnegativity of `t_bi` for norming graphs -/

lemma norming_posdef (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card)
    (W : I → I → ℝ) (hW : IsKernel W) (h : tb E W = 0) : AEEq volume W (fun _ _ => 0) := by
  refine hE.2.2 W hW ?_
  unfold hNorm
  rw [h, abs_zero, Real.zero_rpow (by positivity)]

/-- For a norming `E` with `t_bi(E, W) < 0 < t_bi(E, W')`, some point `(1 - s) W + s W'`, `s ∈ [0, 1]`,
of the segment from `W` to `W'` is the zero kernel almost everywhere. True only vacuously: a norming edge set has nonnegative density (`norming_nonneg`);
this is the intermediate-value step of the argument at tex l.615-617, used inside proofs by
contradiction. -/
lemma seg_zero (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card)
    (W W' : I → I → ℝ) (hW : IsKernel W) (hW' : IsKernel W') (h1 : tb E W < 0)
    (h2 : 0 < tb E W') :
    ∃ s ∈ Icc (0 : ℝ) 1, AEEq volume (fun x y => (1 - s) * W x y + s * W' x y) (fun _ _ => 0) := by
  set g : ℝ → ℝ := fun s => tb E (fun x y => (1 - s) * W x y + s * W' x y) with hg
  have hc : Continuous g := continuous_tb_comb E W W' hW hW' (by fun_prop) (by fun_prop)
  have g0 : g 0 = tb E W := by simp [hg]
  have g1 : g 1 = tb E W' := by simp [hg]
  have := intermediate_value_Icc (zero_le_one' ℝ) hc.continuousOn
  obtain ⟨s, hs, hgs⟩ := this (show (0 : ℝ) ∈ Icc (g 0) (g 1) from
    ⟨by rw [g0]; exact h1.le, by rw [g1]; exact h2.le⟩)
  refine ⟨s, hs, norming_posdef E hE hne _ ?_ hgs⟩
  exact isKernel_add (isKernel_smul hW _) (isKernel_smul hW' _)

lemma aeEq_const_of_comb {A : I → I → ℝ} {α β : ℝ} (hα : α ≠ 0)
    (h : AEEq volume (fun x y => α * A x y + β) (fun _ _ => 0)) :
    AEEq volume A (fun _ _ => -β / α) := by
  filter_upwards [h] with q hq
  field_simp
  linarith

/-- The kernel `(x, y) ↦ x`. -/
def coordK : I → I → ℝ := fun x _ => (x : ℝ)

lemma isKernel_coordK : IsKernel coordK :=
  ⟨(continuous_subtype_val.measurable).comp measurable_fst, 1, fun x _ => by
    simp only [coordK]; rw [abs_of_nonneg x.2.1]; exact x.2.2⟩

lemma coordK_not_const (c : ℝ) : ¬ AEEq volume coordK (fun _ _ => c) := by
  intro h
  have h2 := Measure.ae_ae_of_ae_prod h
  have h3 : ∀ᵐ x : I ∂volume, (x : ℝ) = c := by
    filter_upwards [h2] with x hx
    exact hx.exists.choose_spec
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

lemma norming_even (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card) :
    Even E.card := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hm1 : tb E (fun _ _ => (-1 : ℝ)) < 0 := by rw [tb_const, hodd.neg_one_pow]; norm_num
  have hp1 : 0 < tb E (fun _ _ => (1 : ℝ)) := by rw [tb_one]; norm_num
  have hK0 : tb E coordK ≠ 0 := fun h => coordK_not_const 0 (norming_posdef E hE hne _
    isKernel_coordK h)
  rcases lt_or_gt_of_ne hK0 with hK | hK
  · obtain ⟨s, hs, h⟩ := seg_zero E hE hne coordK _ isKernel_coordK (isKernel_const 1) hK hp1
    by_cases hs1 : s = 1
    · subst hs1
      apply not_aeEq_const (one_ne_zero (α := ℝ))
      filter_upwards [h] with q hq; simp at hq
    · have : AEEq volume (fun x y => (1 - s) * coordK x y + s) (fun _ _ => 0) := by
        filter_upwards [h] with q hq; simpa using hq
      exact coordK_not_const _ (aeEq_const_of_comb (sub_ne_zero.2 (Ne.symm hs1)) this)
  · obtain ⟨s, hs, h⟩ := seg_zero E hE hne _ coordK (isKernel_const (-1)) isKernel_coordK hm1 hK
    by_cases hs0 : s = 0
    · subst hs0
      apply not_aeEq_const (show (-1 : ℝ) ≠ 0 by norm_num)
      filter_upwards [h] with q hq; simp at hq
    · have : AEEq volume (fun x y => s * coordK x y + (-(1 - s))) (fun _ _ => 0) := by
        filter_upwards [h] with q hq; linarith
      exact coordK_not_const _ (aeEq_const_of_comb hs0 this)

lemma norming_nonneg (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card)
    (W : I → I → ℝ) (hW : IsKernel W) : 0 ≤ tb E W := by
  have heven := norming_even E hE hne
  by_contra hneg
  replace hneg := not_le.mp hneg
  by_cases hc : ∃ c, AEEq volume W (fun _ _ => c)
  · obtain ⟨c, hc⟩ := hc
    rw [tb_congr_ae E hc, tb_const] at hneg
    exact absurd hneg (not_lt.2 (heven.pow_nonneg c))
  · push Not at hc
    have hp1 : 0 < tb E (fun _ _ => (1 : ℝ)) := by rw [tb_one]; norm_num
    obtain ⟨s, hs, h⟩ := seg_zero E hE hne W _ hW (isKernel_const 1) hneg hp1
    by_cases hs1 : s = 1
    · subst hs1
      apply not_aeEq_const (one_ne_zero (α := ℝ))
      filter_upwards [h] with q hq; simp at hq
    · have : AEEq volume (fun x y => (1 - s) * W x y + s) (fun _ _ => 0) := by
        filter_upwards [h] with q hq; simpa using hq
      exact hc _ (aeEq_const_of_comb (sub_ne_zero.2 (Ne.symm hs1)) this)

lemma norming_to_strict (E : Finset (X × Y)) (hE : IsNorming E) (hne : 0 < E.card) :
    StrictConvexOnKernels E := by
  set m := E.card with hm
  have heven := norming_even E hE hne
  have hm2 : 2 ≤ m := by
    obtain ⟨r, hr⟩ := heven; omega
  have hF : ∀ W, IsKernel W → tb E W = hNorm E W ^ m := fun W hW => by
    rw [← abs_tb_eq_hNorm_pow E hne, abs_of_nonneg (norming_nonneg E hE hne W hW)]
  have conv : ∀ A B : I → I → ℝ, IsKernel A → IsKernel B → ∀ b ∈ Icc (0 : ℝ) 1,
      tb E (fun x y => b * A x y + (1 - b) * B x y) ≤ b * tb E A + (1 - b) * tb E B := by
    intro A B hA hB b hb
    have h1b : 0 ≤ 1 - b := sub_nonneg.2 hb.2
    rw [hF _ (isKernel_add (isKernel_smul hA _) (isKernel_smul hB _)), hF A hA, hF B hB]
    have htri : hNorm E (fun x y => b * A x y + (1 - b) * B x y) ≤
        b * hNorm E A + (1 - b) * hNorm E B := by
      refine (hE.2.1 _ _ (isKernel_smul hA b) (isKernel_smul hB (1 - b))).trans_eq ?_
      rw [hNorm_smul E hne, hNorm_smul E hne, abs_of_nonneg hb.1, abs_of_nonneg h1b]
    calc hNorm E (fun x y => b * A x y + (1 - b) * B x y) ^ m
        ≤ (b * hNorm E A + (1 - b) * hNorm E B) ^ m :=
          pow_le_pow_left₀ (hNorm_nonneg E _) htri _
      _ ≤ b * hNorm E A ^ m + (1 - b) * hNorm E B ^ m := by
          have := (convexOn_pow m).2 (mem_Ici.2 (hNorm_nonneg E A))
            (mem_Ici.2 (hNorm_nonneg E B)) hb.1 h1b (by ring)
          simpa only [smul_eq_mul] using this
  have mid : ∀ A B : I → I → ℝ, IsKernel A → IsKernel B → ¬ AEEq volume A B →
      tb E (fun x y => (1 / 2 : ℝ) * A x y + (1 - 1 / 2) * B x y) <
        (1 / 2) * tb E A + (1 - 1 / 2) * tb E B := by
    intro A B hA hB hAB
    rw [hF A hA, hF B hB]
    set u := hNorm E A with hu
    set v := hNorm E B with hv
    have hcomb := isKernel_add (isKernel_smul hA (1 / 2 : ℝ)) (isKernel_smul hB (1 - 1 / 2 : ℝ))
    by_cases huv : u = v
    · -- the Hatami inequality case
      have hH := hatami_ineq E hE hne A B hA hB
      rw [← hu, ← hv, huv, sub_self, zero_pow hne.ne'] at hH
      have hsub : ¬ AEEq volume (fun x y => A x y - B x y) (fun _ _ => 0) := by
        intro h; apply hAB
        filter_upwards [h] with q hq
        linarith
      have hpos : 0 < tb E (fun x y => A x y - B x y) := by
        refine lt_of_le_of_ne (norming_nonneg E hE hne _ (isKernel_add hA (isKernel_neg hB)))
          (Ne.symm fun h => hsub (norming_posdef E hE hne _
            (isKernel_add hA (isKernel_neg hB)) h))
      have e : (fun x y => (1 / 2 : ℝ) * A x y + (1 - 1 / 2) * B x y) =
          fun x y => (1 / 2 : ℝ) * (A x y + B x y) := by funext x y; ring
      rw [e, tb_smul]
      have h2 : (v + v) ^ m = 2 ^ m * v ^ m := by rw [← two_mul, mul_pow]
      rw [h2] at hH
      have : tb E (fun x y => A x y + B x y) < 2 ^ m * v ^ m := by linarith
      calc (1 / 2 : ℝ) ^ m * tb E (fun x y => A x y + B x y) < (1 / 2) ^ m * (2 ^ m * v ^ m) :=
            mul_lt_mul_of_pos_left this (by positivity)
        _ = 1 / 2 * u ^ m + (1 - 1 / 2) * v ^ m := by
            rw [huv, ← mul_assoc, ← mul_pow]; norm_num; ring
    · rw [hF _ hcomb]
      have htri : hNorm E (fun x y => (1 / 2 : ℝ) * A x y + (1 - 1 / 2) * B x y) ≤
          1 / 2 * u + (1 - 1 / 2) * v := by
        refine (hE.2.1 _ _ (isKernel_smul hA _) (isKernel_smul hB _)).trans_eq ?_
        rw [hNorm_smul E hne, hNorm_smul E hne, ← hu, ← hv]; norm_num
      calc hNorm E (fun x y => (1 / 2 : ℝ) * A x y + (1 - 1 / 2) * B x y) ^ m
          ≤ (1 / 2 * u + (1 - 1 / 2) * v) ^ m := pow_le_pow_left₀ (hNorm_nonneg E _) htri _
        _ < 1 / 2 * u ^ m + (1 - 1 / 2) * v ^ m := by
            have := (strictConvexOn_pow hm2).2 (mem_Ici.2 (hNorm_nonneg E A))
              (mem_Ici.2 (hNorm_nonneg E B)) huv (by norm_num : (0 : ℝ) < 1 / 2)
              (by norm_num : (0 : ℝ) < 1 - 1 / 2) (by ring)
            simpa only [smul_eq_mul] using this
  intro U V hU hV hUV a ha
  rcases le_or_gt a (1 / 2) with hle | hgt
  · set W2 : I → I → ℝ := fun x y => (2 * a) * U x y + (1 - 2 * a) * V x y with hW2
    have hW2k : IsKernel W2 := isKernel_add (isKernel_smul hU _) (isKernel_smul hV _)
    have hnot : ¬ AEEq volume V W2 := by
      intro h; apply hUV
      filter_upwards [h] with q hq
      simp only [hW2] at hq
      have : 2 * a * (U q.1 q.2 - V q.1 q.2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith [ha.1]
      · linarith
    have h1 := mid V W2 hV hW2k hnot
    have e : (fun x y => (1 / 2 : ℝ) * V x y + (1 - 1 / 2) * W2 x y) =
        fun x y => a * U x y + (1 - a) * V x y := by funext x y; simp only [hW2]; ring
    rw [e] at h1
    have h2 := conv U V hU hV (2 * a) ⟨by linarith [ha.1], by linarith⟩
    linarith
  · set W2 : I → I → ℝ := fun x y => (2 * a - 1) * U x y + (1 - (2 * a - 1)) * V x y with hW2
    have hW2k : IsKernel W2 := isKernel_add (isKernel_smul hU _) (isKernel_smul hV _)
    have hnot : ¬ AEEq volume U W2 := by
      intro h; apply hUV
      filter_upwards [h] with q hq
      simp only [hW2] at hq
      have : (2 - 2 * a) * (U q.1 q.2 - V q.1 q.2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith [ha.2]
      · linarith
    have h1 := mid U W2 hU hW2k hnot
    have e : (fun x y => (1 / 2 : ℝ) * U x y + (1 - 1 / 2) * W2 x y) =
        fun x y => a * U x y + (1 - a) * V x y := by funext x y; simp only [hW2]; ring
    rw [e] at h1
    have h2 := conv U V hU hV (2 * a - 1) ⟨by linarith, by linarith [ha.2]⟩
    linarith

theorem lemma_2_3_2_aux (E : Finset (X × Y)) (hne : 0 < E.card) :
    IsNorming E ↔ StrictConvexOnKernels E :=
  ⟨fun h => norming_to_strict E h hne, fun h => strict_to_norming E hne h⟩

/-! ### Claim 2.1: generic directed-density facts -/

section Directed

variable {V : Type*} [Fintype V]

/-- The vertex measure. -/
noncomputable abbrev πV (V : Type*) [Fintype V] : Measure (V → I) :=
  Measure.pi fun _ : V => (volume : Measure I)

open scoped Classical in
/-- The density with the arcs of `F` reversed. -/
noncomputable def revDens (A F : Finset (V × V)) (U : I → I → ℝ) : ℝ :=
  ∫ x, ∏ p ∈ A, (if p ∈ F then U (x p.2) (x p.1) else U (x p.1) (x p.2)) ∂(πV V)

lemma integrable_prod_arcs (A : Finset (V × V)) (G : V × V → (V → I) → ℝ)
    (hG : ∀ p ∈ A, Measurable (G p)) (hb : ∀ p ∈ A, ∀ x, |G p x| ≤ 1) :
    Integrable (fun x => ∏ p ∈ A, G p x) (πV V) := by
  refine Integrable.of_bound (Finset.measurable_prod _ hG).aestronglyMeasurable 1
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p hp => hb p hp x

omit [Fintype V] in
lemma measurable_pair (p : V × V) : Measurable fun x : V → I => (x p.1, x p.2) := by fun_prop

lemma t_eq_revDens (D : OrientedGraph V) (U : I → I → ℝ) : t D U = revDens D.arcs ∅ U := by
  simp [revDens, t, tDir]

open scoped Classical in
lemma t_symmetrize (A : Finset (V × V)) (U : I → I → ℝ) (hU : IsDigraphon U) :
    ∫ x, ∏ p ∈ A, symmetrize U (x p.1) (x p.2) ∂(πV V) =
      (1 / 2) ^ A.card * ∑ F ∈ A.powerset, revDens A F U := by
  have hpt : ∀ x : V → I, ∏ p ∈ A, symmetrize U (x p.1) (x p.2) =
      ∑ F ∈ A.powerset, (1 / 2) ^ A.card *
        ∏ p ∈ A, (if p ∈ F then U (x p.2) (x p.1) else U (x p.1) (x p.2)) := by
    intro x
    have e : ∀ p ∈ A, symmetrize U (x p.1) (x p.2) =
        1 / 2 * U (x p.2) (x p.1) + 1 / 2 * U (x p.1) (x p.2) := fun p _ => by
      simp only [symmetrize]; ring
    rw [Finset.prod_congr rfl e, Finset.prod_add]
    refine Finset.sum_congr rfl fun F hF => ?_
    have hFA := Finset.mem_powerset.1 hF
    rw [← Finset.prod_sdiff hFA (f := fun p => if p ∈ F then U (x p.2) (x p.1)
      else U (x p.1) (x p.2))]
    have h1 : ∏ p ∈ F, (if p ∈ F then U (x p.2) (x p.1) else U (x p.1) (x p.2)) =
        ∏ p ∈ F, U (x p.2) (x p.1) := Finset.prod_congr rfl fun p hp => by simp [hp]
    have h2 : ∏ p ∈ A \ F, (if p ∈ F then U (x p.2) (x p.1) else U (x p.1) (x p.2)) =
        ∏ p ∈ A \ F, U (x p.1) (x p.2) :=
      Finset.prod_congr rfl fun p hp => by simp [(Finset.mem_sdiff.1 hp).2]
    rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_const, ← Finset.card_sdiff_add_card_eq_card hFA, pow_add]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun F _ => ?_
    rw [integral_const_mul]
    rfl
  · intro F _
    refine Integrable.const_mul ?_ _
    refine integrable_prod_arcs A _ (fun p _ => ?_) fun p _ x => ?_
    · split_ifs
      · exact hU.1.comp (f := fun x : V → I => (x p.2, x p.1)) (by fun_prop)
      · exact hU.1.comp (measurable_pair p)
    · split_ifs <;> (rw [abs_of_nonneg (hU.2 _ _).1]; exact (hU.2 _ _).2)

open scoped Classical in
lemma revDens_sqK {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (A F : Finset (V × V)) (U : I → I → ℝ) (hU : IsKernel U) :
    revDens A F (sqK φ U) = revDens A F U ^ 2 := by
  set h : (V → I) → ℝ := fun y => ∏ p ∈ A, (if p ∈ F then U (y p.2) (y p.1)
    else U (y p.1) (y p.2)) with hh
  have hmeas : Measurable h := by
    refine Finset.measurable_prod _ fun p _ => ?_
    split_ifs
    · exact hU.1.comp (f := fun x : V → I => (x p.2, x p.1)) (by fun_prop)
    · exact hU.1.comp (measurable_pair p)
  have hmp := mp_splitPi hφ V
  have key : revDens A F (sqK φ U) = ∫ w, h w.1 * h w.2 ∂((πV V).prod (πV V)) := by
    rw [← hmp.map_eq, integral_map (f := fun w => h w.1 * h w.2) hmp.measurable.aemeasurable
      ((hmeas.comp measurable_fst).mul (hmeas.comp measurable_snd)).aestronglyMeasurable]
    unfold revDens
    congr 1
    funext x
    simp only [hh, splitPi, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    split_ifs <;> rfl
  rw [key, integral_prod_mul, sq]
  rfl

/-- `|∏ a - ∏ b| ≤ Σ |a - b|` for families in `[0, 1]`. -/
lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1)
    (hb : ∀ i, b i ∈ Icc (0 : ℝ) 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq, Finset.sum_insert hq]
    have e : a q * ∏ i ∈ s, a i - b q * ∏ i ∈ s, b i =
        a q * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a q - b q) * ∏ i ∈ s, b i := by ring
    rw [e]
    have hpb := prod_mem_01 s b (fun i => (hb i).1) fun i => (hb i).2
    calc |a q * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a q - b q) * ∏ i ∈ s, b i|
        ≤ |a q| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a q - b q| * |∏ i ∈ s, b i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, |a i - b i| + |a q - b q| * 1 := by
          refine add_le_add (mul_le_mul ?_ ih (abs_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
          · rw [abs_of_nonneg (ha q).1]; exact (ha q).2
          · rw [abs_of_nonneg hpb.1]; exact hpb.2
      _ = |a q - b q| + ∑ i ∈ s, |a i - b i| := by ring

/-- The pair evaluation `x ↦ (x u, x v)`, `u ≠ v`, is measure preserving. -/
lemma mp_pair {u v : V} (huv : u ≠ v) :
    MeasurePreserving (fun x : V → I => (x u, x v)) (πV V) ((volume : Measure I).prod volume) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [Measure.map_apply (by fun_prop) (hs.prod ht)]
  have : (fun x : V → I => (x u, x v)) ⁻¹' (s ×ˢ t) =
      Set.pi univ (fun w => if w = u then s else if w = v then t else univ) := by
    ext x
    simp only [mem_preimage, mem_prod, Set.mem_univ_pi]
    constructor
    · rintro ⟨h1, h2⟩ w
      by_cases h3 : w = u
      · subst h3; simpa using h1
      · by_cases h4 : w = v
        · subst h4; simpa [h3] using h2
        · simp [h3, h4]
    · intro h
      refine ⟨by simpa using h u, ?_⟩
      simpa [Ne.symm huv] using h v
  rw [this, Measure.pi_pi]
  rw [Finset.prod_eq_mul_of_mem u v (Finset.mem_univ u) (Finset.mem_univ v) huv]
  · simp [Ne.symm huv]
  · intro c _ hc
    simp [hc.1, hc.2]

lemma mem_arcs (D : OrientedGraph V) (p : V × V) : p ∈ D.arcs ↔ D.Adj p.1 p.2 := by
  classical
  unfold OrientedGraph.arcs
  simp

/-- `L¹` continuity of `t(D, ·)` on digraphons. -/
lemma abs_t_sub_le (D : OrientedGraph V) (A B : I → I → ℝ) (hA : IsDigraphon A)
    (hB : IsDigraphon B) :
    |t D A - t D B| ≤ D.numArcs * ∫ q, |A q.1 q.2 - B q.1 q.2| ∂((volume : Measure I).prod volume) := by
  have hAi := integrable_prod_arcs D.arcs (fun p x => A (x p.1) (x p.2))
    (fun p _ => hA.1.comp (measurable_pair p))
    fun p _ x => by rw [abs_of_nonneg (hA.2 _ _).1]; exact (hA.2 _ _).2
  have hBi := integrable_prod_arcs D.arcs (fun p x => B (x p.1) (x p.2))
    (fun p _ => hB.1.comp (measurable_pair p))
    fun p _ x => by rw [abs_of_nonneg (hB.2 _ _).1]; exact (hB.2 _ _).2
  have hdi : ∀ p ∈ D.arcs, Integrable (fun x : V → I => |A (x p.1) (x p.2) - B (x p.1) (x p.2)|)
      (πV V) := fun p _ => by
    refine Integrable.of_bound (((hA.1.comp (measurable_pair p)).sub
      (hB.1.comp (measurable_pair p))).abs.aestronglyMeasurable) 1
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    have ha1 := hA.2 (x p.1) (x p.2); have ha2 := hB.2 (x p.1) (x p.2)
    constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]
  have hAB : Integrable (fun q : I × I => |A q.1 q.2 - B q.1 q.2|) ((volume : Measure I).prod volume) := by
    refine Integrable.of_bound ((hA.1.sub hB.1).abs.aestronglyMeasurable) 1
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    have ha1 := hA.2 q.1 q.2; have ha2 := hB.2 q.1 q.2
    constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]
  unfold t tDir
  rw [← integral_sub hAi hBi]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |∏ p ∈ D.arcs, A (x p.1) (x p.2) - ∏ p ∈ D.arcs, B (x p.1) (x p.2)| ∂(πV V)
      ≤ ∫ x, ∑ p ∈ D.arcs, |A (x p.1) (x p.2) - B (x p.1) (x p.2)| ∂(πV V) := by
        refine integral_mono (hAi.sub hBi).abs (integrable_finsetSum _ hdi) fun x => ?_
        exact abs_prod_sub_prod_le D.arcs (fun p => A (x p.1) (x p.2)) (fun p => B (x p.1) (x p.2))
          (fun p => hA.2 _ _) fun p => hB.2 _ _
    _ = ∑ p ∈ D.arcs, ∫ q, |A q.1 q.2 - B q.1 q.2| ∂((volume : Measure I).prod volume) := by
        rw [integral_finsetSum _ hdi]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hne : p.1 ≠ p.2 := fun h => D.irrefl p.1 (by
          have := (mem_arcs D p).1 hp; rwa [← h] at this)
        have hmp := mp_pair (V := V) hne
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hAB.aestronglyMeasurable)]
    _ = D.numArcs * ∫ q, |A q.1 q.2 - B q.1 q.2| ∂((volume : Measure I).prod volume) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl

lemma isDigraphon_symmetrize {A : I → I → ℝ} (hA : IsDigraphon A) : IsDigraphon (symmetrize A) := by
  refine ⟨?_, fun x y => ?_⟩
  · have h2 : Measurable fun q : I × I => A q.2 q.1 := hA.1.comp measurable_swap
    exact (hA.1.add h2).div_const 2
  · have ha1 := hA.2 x y; have ha2 := hA.2 y x
    simp only [symmetrize]
    constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]

lemma integral_symm_sub_le (A B : I → I → ℝ) (hA : IsDigraphon A) (hB : IsDigraphon B) :
    ∫ q, |symmetrize A q.1 q.2 - symmetrize B q.1 q.2| ∂((volume : Measure I).prod volume) ≤
      ∫ q, |A q.1 q.2 - B q.1 q.2| ∂((volume : Measure I).prod volume) := by
  have hAB : Integrable (fun q : I × I => |A q.1 q.2 - B q.1 q.2|) ((volume : Measure I).prod volume) := by
    refine Integrable.of_bound ((hA.1.sub hB.1).abs.aestronglyMeasurable) 1
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    have ha1 := hA.2 q.1 q.2; have ha2 := hB.2 q.1 q.2
    constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]
  have hsw : ∫ q, |A q.2 q.1 - B q.2 q.1| ∂((volume : Measure I).prod volume) =
      ∫ q, |A q.1 q.2 - B q.1 q.2| ∂((volume : Measure I).prod volume) := by
    have := integral_prod_swap (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (fun q : I × I => |A q.1 q.2 - B q.1 q.2|)
    simpa using this
  have hAB' : Integrable (fun q : I × I => |A q.2 q.1 - B q.2 q.1|) ((volume : Measure I).prod volume) :=
    (Measure.measurePreserving_swap.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).2 hAB
  calc ∫ q, |symmetrize A q.1 q.2 - symmetrize B q.1 q.2| ∂((volume : Measure I).prod volume)
      ≤ ∫ q, (|A q.1 q.2 - B q.1 q.2| + |A q.2 q.1 - B q.2 q.1|) / 2
          ∂((volume : Measure I).prod volume) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hAB.add hAB').div_const 2) (Eventually.of_forall fun q => ?_)
        simp only [symmetrize]
        rw [show (A q.1 q.2 + A q.2 q.1) / 2 - (B q.1 q.2 + B q.2 q.1) / 2 =
          ((A q.1 q.2 - B q.1 q.2) + (A q.2 q.1 - B q.2 q.1)) / 2 by ring, abs_div,
          abs_of_pos (two_pos : (0:ℝ) < 2)]
        exact div_le_div_of_nonneg_right (abs_add_le _ _) zero_le_two
    _ = ∫ q, |A q.1 q.2 - B q.1 q.2| ∂((volume : Measure I).prod volume) := by
        rw [integral_div, integral_add hAB hAB', hsw]; ring

/-! ### Grid approximation of digraphons -/

/-- The index of the grid cell of `x` for the partition of `[0,1]` into `n + 1` intervals. -/
noncomputable def gridIdx (n : ℕ) (x : I) : Fin (n + 1) :=
  ⟨min ⌊(x : ℝ) * (n + 1)⌋₊ n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The left end point of the `i`-th grid cell. -/
noncomputable def gridPt (n : ℕ) (i : Fin (n + 1)) : I :=
  ⟨(i : ℝ) / (n + 1), div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity)).2 (by have := i.2; norm_cast; omega)⟩

lemma measurable_gridIdx (n : ℕ) : Measurable (gridIdx n) := by
  have h1 : Measurable fun x : I => ⌊(x : ℝ) * (n + 1)⌋₊ :=
    Nat.measurable_floor.comp (measurable_subtype_coe.mul_const _)
  have h2 : Measurable fun x : I => min ⌊(x : ℝ) * (n + 1)⌋₊ n :=
    (measurable_from_nat (f := fun k => min k n)).comp h1
  exact measurable_to_countable' fun i => by
    have : gridIdx n ⁻¹' {i} = (fun x : I => min ⌊(x : ℝ) * (n + 1)⌋₊ n) ⁻¹' {(i : ℕ)} := by
      ext x; simp [gridIdx, Fin.ext_iff]
    rw [this]; exact h2 (measurableSet_singleton _)

lemma dist_gridPt_le (n : ℕ) (x : I) : dist x (gridPt n (gridIdx n x)) ≤ 1 / (n + 1) := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [gridPt, gridIdx]
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hx0 : 0 ≤ (x : ℝ) := x.2.1
  have hx1 : (x : ℝ) ≤ 1 := x.2.2
  set k : ℕ := min ⌊(x : ℝ) * (n + 1)⌋₊ n with hk
  have key : |(x : ℝ) * (n + 1) - k| ≤ 1 := by
    rw [abs_le]
    rcases le_total ⌊(x : ℝ) * (n + 1)⌋₊ n with h | h
    · rw [hk, min_eq_left h]
      have hf1 := Nat.floor_le (mul_nonneg hx0 hn.le)
      have hf2 := Nat.lt_floor_add_one ((x : ℝ) * (n + 1))
      constructor <;> linarith
    · rw [hk, min_eq_right h]
      have hf : (n : ℝ) ≤ (x : ℝ) * (n + 1) := by
        have := (Nat.le_floor_iff (mul_nonneg hx0 hn.le)).1 h; exact_mod_cast this
      constructor <;> nlinarith
  calc |(x : ℝ) - (k : ℝ) / (n + 1)| = |(x : ℝ) * (n + 1) - k| / (n + 1) := by
        rw [show (x : ℝ) - (k : ℝ) / (n + 1) = ((x : ℝ) * (n + 1) - k) / (n + 1) by
          field_simp, abs_div, abs_of_pos hn]
    _ ≤ 1 / (n + 1) := div_le_div_of_nonneg_right key hn.le

lemma volume_gridIdx_pos (n : ℕ) (i : Fin (n + 1)) :
    0 < (volume : Measure I) (gridIdx n ⁻¹' {i}) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hi : (i : ℝ) + 1 ≤ n + 1 := by have := i.2; exact_mod_cast this
  set a : I := ⟨(i : ℝ) / (n + 1), div_nonneg (Nat.cast_nonneg _) hn.le,
    (div_le_one hn).2 (by linarith)⟩
  set b : I := ⟨((i : ℝ) + 1) / (n + 1), div_nonneg (by positivity) hn.le,
    (div_le_one hn).2 hi⟩
  have hsub : Set.Ioo a b ⊆ gridIdx n ⁻¹' {i} := by
    intro x hx
    simp only [mem_Ioo, a, b, ← Subtype.coe_lt_coe] at hx
    rw [div_lt_iff₀ hn] at hx
    rw [lt_div_iff₀ hn] at hx
    have hfl : ⌊(x : ℝ) * (n + 1)⌋₊ = i := by
      rw [Nat.floor_eq_iff (by nlinarith [x.2.1])]
      constructor <;> linarith [hx.1, hx.2]
    simp only [mem_preimage, mem_singleton_iff, gridIdx, Fin.ext_iff, hfl]
    exact min_eq_left (Nat.lt_succ_iff.1 i.2)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [unitInterval.volume_Ioo]
  simp only [a, b, ENNReal.ofReal_pos]
  have : (i : ℝ) / (n + 1) < ((i : ℝ) + 1) / (n + 1) := div_lt_div_of_pos_right (by linarith) hn
  linarith

lemma clamp_dist (a b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) : |max 0 (min 1 a) - b| ≤ |a - b| := by
  obtain ⟨hb0, hb1⟩ := hb
  rcases le_total a 0 with h0 | h0
  · rw [min_eq_right (h0.trans zero_le_one), max_eq_left h0, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total a 1 with h1 | h1
    · rw [min_eq_right h1, max_eq_right h0]
    · rw [min_eq_left h1, max_eq_right zero_le_one, abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith

/-- Every digraphon is `L¹`-approximated by `[0,1]`-valued grid step functions. -/
lemma exists_grid_approx (U : I → I → ℝ) (hU : IsDigraphon U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (h : Fin (n + 1) → Fin (n + 1) → ℝ), (∀ i j, h i j ∈ Icc (0 : ℝ) 1) ∧
      ∫ q, |h (gridIdx n q.1) (gridIdx n q.2) - U q.1 q.2| ∂((volume : Measure I).prod volume)
        ≤ ε := by
  have hUi : Integrable (fun q : I × I => U q.1 q.2) ((volume : Measure I).prod volume) := by
    refine Integrable.of_bound hU.1.aestronglyMeasurable 1 (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hU.2 _ _).1]; exact (hU.2 _ _).2
  obtain ⟨g, hg, hgi⟩ := hUi.exists_boundedContinuous_integral_sub_le (half_pos hε)
  set c : I × I → ℝ := fun q => max 0 (min 1 (g q)) with hc
  have hcc : Continuous c := continuous_const.max (continuous_const.min g.continuous)
  have hc01 : ∀ q, c q ∈ Icc (0 : ℝ) 1 := fun q =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hcc) (ε / 2) (half_pos hε)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, fun i j => c (gridPt n i, gridPt n j), fun i j => hc01 _, ?_⟩
  have hpt : ∀ q : I × I, |c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) - c q| ≤ ε / 2 := by
    intro q
    have hd : dist (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) q < δ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_comm]; exact (dist_gridPt_le n q.1).trans_lt hn
      · rw [dist_comm]; exact (dist_gridPt_le n q.2).trans_lt hn
    exact (hδc hd).le
  have hgm : Measurable fun q : I × I => c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) := by
    have : (fun q : I × I => c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2))) =
        (fun ij : Fin (n + 1) × Fin (n + 1) => c (gridPt n ij.1, gridPt n ij.2)) ∘
          (fun q : I × I => (gridIdx n q.1, gridIdx n q.2)) := rfl
    rw [this]
    exact (measurable_of_finite _).comp ((measurable_gridIdx n).comp measurable_fst |>.prodMk
      ((measurable_gridIdx n).comp measurable_snd))
  have hb : ∀ {f : I × I → ℝ}, Measurable f → (∀ q, |f q| ≤ 2) →
      Integrable f ((volume : Measure I).prod volume) := fun hf hfb =>
    Integrable.of_bound hf.aestronglyMeasurable 2 (Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]; exact hfb q)
  have hcm : Measurable c := hcc.measurable
  have i1 : Integrable (fun q : I × I =>
      |c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) - c q|)
      ((volume : Measure I).prod volume) := hb ((hgm.sub hcm).abs) fun q => by
    show |(|c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) - c q|)| ≤ 2
    rw [abs_abs, abs_le]; constructor <;> linarith [(hc01 q).1, (hc01 q).2,
      (hc01 (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2))).1,
      (hc01 (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2))).2]
  have i2 : Integrable (fun q : I × I => |c q - U q.1 q.2|)
      ((volume : Measure I).prod volume) := hb ((hcm.sub hU.1).abs) fun q => by
    show |(|c q - U q.1 q.2|)| ≤ 2
    rw [abs_abs, abs_le]; constructor <;> linarith [(hc01 q).1, (hc01 q).2, (hU.2 q.1 q.2).1,
      (hU.2 q.1 q.2).2]
  have i3 : Integrable (fun q : I × I => ‖U q.1 q.2 - g q‖) ((volume : Measure I).prod volume) :=
    (hUi.sub hgi).norm
  calc ∫ q, |c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) - U q.1 q.2|
        ∂((volume : Measure I).prod volume)
      ≤ ∫ q, (|c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) - c q| + |c q - U q.1 q.2|)
          ∂((volume : Measure I).prod volume) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (i1.add i2)
          (Eventually.of_forall fun q => ?_)
        have := abs_sub_le (c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2))) (c q)
          (U q.1 q.2)
        exact this
    _ = ∫ q, |c (gridPt n (gridIdx n q.1), gridPt n (gridIdx n q.2)) - c q|
          ∂((volume : Measure I).prod volume) +
        ∫ q, |c q - U q.1 q.2| ∂((volume : Measure I).prod volume) := integral_add i1 i2
    _ ≤ ∫ _q, ε / 2 ∂((volume : Measure I).prod volume) +
        ∫ q, ‖U q.1 q.2 - g q‖ ∂((volume : Measure I).prod volume) := by
        refine add_le_add (integral_mono i1 (integrable_const _) hpt)
          (integral_mono i2 i3 fun q => ?_)
        rw [Real.norm_eq_abs, abs_sub_comm (U q.1 q.2)]
        exact clamp_dist _ _ (hU.2 _ _)
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add (by simp) hg
    _ = ε := by ring

/-! ### Connectivity and self-converse relabelling -/

lemma const_of_connected (D : OrientedGraph V) (hconn : D.IsConnected) {β : Type*} (c : V → β)
    (hc : ∀ p ∈ D.arcs, c p.1 = c p.2) (u v : V) : c u = c v := by
  obtain ⟨w⟩ := hconn.preconnected u v
  induction w with
  | nil => rfl
  | cons h w ih =>
    rename_i a b _
    rw [← ih]
    have h' := h
    simp only [OrientedGraph.underlying, SimpleGraph.fromRel_adj] at h'
    rcases h'.2 with h2 | h2
    · exact hc (a, b) ((mem_arcs D _).2 h2)
    · exact (hc (b, a) ((mem_arcs D _).2 h2)).symm

lemma t_transpose_eq (D : OrientedGraph V) (hsc : D.IsSelfConverse) (U : I → I → ℝ) :
    ∫ x, ∏ p ∈ D.arcs, U (x p.2) (x p.1) ∂(πV V) = t D U := by
  obtain ⟨iso⟩ := hsc
  set e : V ≃ V := iso.toEquiv
  have hadj : ∀ u v, D.Adj (e v) (e u) ↔ D.Adj u v := fun u v => iso.map_adj_iff u v
  set ψ := MeasurableEquiv.piCongrLeft (fun _ : V => I) e
  have hψ : ∀ (y : V → I) v, ψ y v = y (e.symm v) := by
    intro y v
    conv_lhs => rw [← e.apply_symm_apply v]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : V => I) e y (e.symm v)
  have hmp : MeasurePreserving ψ (πV V) (πV V) :=
    measurePreserving_piCongrLeft (fun _ : V => (volume : Measure I)) e
  rw [← hmp.integral_comp' (g := fun x => ∏ p ∈ D.arcs, U (x p.2) (x p.1))]
  unfold t tDir
  congr 1
  funext y
  simp only [hψ]
  refine Finset.prod_nbij' (fun p => (e.symm p.2, e.symm p.1)) (fun q => (e q.2, e q.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_arcs] at hp ⊢
    have := (hadj (e.symm p.2) (e.symm p.1)).1
    simp only [Equiv.apply_symm_apply] at this
    exact this hp
  · intro q hq
    rw [mem_arcs] at hq ⊢
    exact (hadj q.1 q.2).2 hq
  · intro p _; simp
  · intro q _; simp
  · intro p _; rfl

end Directed

end Section2Aux

end NieWeiOrientedSidorenko
