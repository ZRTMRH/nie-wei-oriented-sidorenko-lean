import NieWeiOrientedSidorenko.Section2
import NieWeiOrientedSidorenko.Literature

/-!
# Section 4, auxiliary lemmas (part 1)

Auxiliary lemmas for `Section4.lean`: the splitting map `[0,1] → [0,1] × {false, true}`, kernel
facts, and the whole proof of Lemma 4.6 (`lemma_4_6_core`), split off to keep each file under
about 2000 lines. `Section4.lean` imports this file.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace Section4Aux

lemma isKernel_const_mul {U : I → I → ℝ} (hU : IsKernel U) (c : ℝ) :
    IsKernel (fun x y => c * U x y) := by
  refine ⟨?_, ?_⟩
  · exact measurable_const.mul hU.1
  · obtain ⟨M, hM⟩ := hU.2
    refine ⟨|c| * M, fun x y => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x y) (abs_nonneg c)

lemma tb_nonneg {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y)) (U : I → I → ℝ)
    (hU : ∀ x y, 0 ≤ U x y) : 0 ≤ tb E U :=
  integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => hU _ _

lemma tb_empty {X Y : Type*} [Fintype X] [Fintype Y] (U : I → I → ℝ) :
    tb (∅ : Finset (X × Y)) U = 1 := by
  simp [tb, tBi]

/-- Monotonicity of `t_bi` read off the weak norm, for nonnegative kernels. -/
lemma tb_le_of_rNorm_le {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (U U' : I → I → ℝ) (hU : ∀ x y, 0 ≤ U x y) (hU' : ∀ x y, 0 ≤ U' x y)
    (h : rNorm E U ≤ rNorm E U') : tb E U ≤ tb E U' := by
  rcases Nat.eq_zero_or_pos E.card with h0 | h0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    rw [tb_empty, tb_empty]
  · have e1 : (fun x y => |U x y|) = U := by funext x y; exact abs_of_nonneg (hU x y)
    have e2 : (fun x y => |U' x y|) = U' := by funext x y; exact abs_of_nonneg (hU' x y)
    unfold rNorm at h
    rw [e1, e2] at h
    have hm : (0 : ℝ) < 1 / E.card := by
      have : (0 : ℝ) < E.card := by exact_mod_cast h0
      positivity
    exact (Real.rpow_le_rpow_iff (tb_nonneg E U hU) (tb_nonneg E U' hU') hm).1 h

/-- The rescaling of each half of `[0,1]` onto `[0,1]`. -/
noncomputable def halfRescale (x : I) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (if (x : ℝ) ≤ 1 / 2 then 2 * x else 2 * x - 1)

/-- The splitting map `[0,1] → [0,1] × {false, true}`. -/
noncomputable def halfSplit (x : I) : I × Bool :=
  (halfRescale x, decide ((1 : ℝ) / 2 < x))

lemma measurable_halfRescale : Measurable halfRescale := by
  unfold halfRescale
  refine (continuous_projIcc).measurable.comp ?_
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact measurableSet_le measurable_subtype_coe measurable_const

lemma measurable_halfSplit : Measurable halfSplit := by
  refine measurable_halfRescale.prodMk ?_
  refine measurable_to_countable' fun b => ?_
  have : (fun x : I => decide ((1 : ℝ) / 2 < x)) ⁻¹' {b} =
      {x : I | b = true ↔ (1 : ℝ) / 2 < x} := by
    ext x; cases b <;> simp
  rw [this]
  cases b
  · simp only [Bool.false_eq_true, false_iff, not_lt]
    exact measurableSet_le measurable_subtype_coe measurable_const
  · simp only [true_iff]
    exact measurableSet_lt measurable_const measurable_subtype_coe

lemma volume_left_half (A : Set I) :
    volume ({x : I | (x : ℝ) ≤ 1 / 2} ∩ halfRescale ⁻¹' A) = 2⁻¹ * volume A := by
  rw [unitInterval.volume_apply, unitInterval.volume_apply]
  have : Subtype.val '' ({x : I | (x : ℝ) ≤ 1 / 2} ∩ halfRescale ⁻¹' A) =
      (fun y : ℝ => 2 * y) ⁻¹' (Subtype.val '' A) := by
    ext y
    simp only [mem_image, mem_inter_iff, mem_setOf_eq, mem_preimage, halfRescale]
    constructor
    · rintro ⟨x, ⟨hx, hA⟩, rfl⟩
      rw [if_pos hx] at hA
      refine ⟨_, hA, ?_⟩
      rw [Set.projIcc_of_mem _ ⟨by linarith [x.2.1], by linarith⟩]
    · rintro ⟨z, hz, hzy⟩
      have h0 : 0 ≤ y := by linarith [z.2.1]
      have h1 : y ≤ 1 / 2 := by linarith [z.2.2]
      refine ⟨⟨y, h0, by linarith⟩, ⟨h1, ?_⟩, rfl⟩
      simp only
      rw [if_pos h1]
      convert hz
      apply Subtype.ext
      rw [Set.projIcc_of_mem _ ⟨by linarith, by linarith⟩]
      exact hzy.symm
  rw [this, Real.volume_preimage_mul_left (by norm_num)]
  congr 1
  rw [abs_of_pos (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma volume_right_half (A : Set I) :
    volume ({x : I | (1 : ℝ) / 2 < x} ∩ halfRescale ⁻¹' A) = 2⁻¹ * volume A := by
  rw [unitInterval.volume_apply, unitInterval.volume_apply]
  have : Subtype.val '' ({x : I | (1 : ℝ) / 2 < x} ∩ halfRescale ⁻¹' A) =
      (fun y : ℝ => 2 * y) ⁻¹' ((fun y : ℝ => y + (-1)) ⁻¹' (Subtype.val '' A \ {0})) := by
    ext y
    simp only [mem_image, mem_inter_iff, mem_setOf_eq, mem_preimage, halfRescale, mem_diff,
      mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hx, hA⟩, rfl⟩
      rw [if_neg (by linarith)] at hA
      refine ⟨⟨_, hA, ?_⟩, by linarith⟩
      rw [Set.projIcc_of_mem _ ⟨by linarith, by linarith [x.2.2]⟩]
      ring
    · rintro ⟨⟨z, hz, hzy⟩, hne⟩
      have hz0 := z.2.1
      have hz1 := z.2.2
      have hzpos : (0 : ℝ) < z := lt_of_le_of_ne hz0 (fun h => hne (by rw [← hzy, ← h]))
      have h0 : 1 / 2 < y := by linarith
      have h1 : y ≤ 1 := by linarith
      refine ⟨⟨y, by linarith, h1⟩, ⟨h0, ?_⟩, rfl⟩
      simp only
      rw [if_neg (by linarith)]
      convert hz
      apply Subtype.ext
      rw [Set.projIcc_of_mem _ ⟨by linarith, by linarith⟩]
      simp only
      linarith
  rw [this, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add_right,
    measure_sdiff_null (measure_singleton 0)]
  congr 1
  rw [abs_of_pos (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma measurePreserving_halfSplit : MeasurePreserving halfSplit volume twoCopies := by
  classical
  refine ⟨measurable_halfSplit, ?_⟩
  unfold twoCopies
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply measurable_halfSplit (hA.prod hB)]
  have hpre : halfSplit ⁻¹' (A ×ˢ B) =
      (if false ∈ B then {x : I | (x : ℝ) ≤ 1 / 2} ∩ halfRescale ⁻¹' A else ∅) ∪
      (if true ∈ B then {x : I | (1 : ℝ) / 2 < x} ∩ halfRescale ⁻¹' A else ∅) := by
    ext x
    simp only [halfSplit, mem_preimage, mem_prod, mem_union]
    by_cases hx : (1 : ℝ) / 2 < x
    · have h' : ¬ (x : ℝ) ≤ 1 / 2 := not_le.2 hx
      rw [show decide ((1 : ℝ) / 2 < x) = true from decide_eq_true hx]
      split_ifs <;> simp_all [one_div]
    · have h' : (x : ℝ) ≤ 1 / 2 := not_lt.1 hx
      rw [show decide ((1 : ℝ) / 2 < x) = false from decide_eq_false hx]
      split_ifs <;> simp_all [one_div]
  have hdisj : Disjoint (if false ∈ B then {x : I | (x : ℝ) ≤ 1 / 2} ∩ halfRescale ⁻¹' A else ∅)
      (if true ∈ B then {x : I | (1 : ℝ) / 2 < x} ∩ halfRescale ⁻¹' A else ∅) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    split_ifs at h1 h2 <;> simp_all only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false]
    linarith [h1.1, h2.1]
  have hmeas : MeasurableSet
      (if true ∈ B then {x : I | (1 : ℝ) / 2 < x} ∩ halfRescale ⁻¹' A else ∅) := by
    split_ifs
    · exact (measurableSet_lt measurable_const measurable_subtype_coe).inter
        (measurable_halfRescale hA)
    · exact MeasurableSet.empty
  rw [hpre, measure_union hdisj hmeas]
  have hsing : ∀ b : Bool, halfCount {b} = 2⁻¹ := by
    intro b
    simp [halfCount, Measure.count_singleton]
  have hB : halfCount B = (if false ∈ B then 2⁻¹ else 0) + (if true ∈ B then 2⁻¹ else 0) := by
    by_cases hf : false ∈ B <;> by_cases ht : true ∈ B
    · have : B = univ := by ext b; cases b <;> simp [hf, ht]
      rw [if_pos hf, if_pos ht, this, measure_univ, ENNReal.inv_two_add_inv_two]
    · have : B = {false} := by ext b; cases b <;> simp [hf, ht]
      rw [if_pos hf, if_neg ht, this, hsing, add_zero]
    · have : B = {true} := by ext b; cases b <;> simp [hf, ht]
      rw [if_neg hf, if_pos ht, this, hsing, zero_add]
    · have : B = ∅ := by ext b; cases b <;> simp [hf, ht]
      rw [if_neg hf, if_neg ht, this, measure_empty, add_zero]
  rw [hB]
  split_ifs <;> simp only [Set.union_empty, Set.empty_union, measure_empty, volume_left_half,
    volume_right_half] <;> ring

section Bip

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] [Fintype Y] in
lemma measurable_integrandBi {Ω : Type*} [MeasurableSpace Ω] (E : Finset (X × Y))
    {K : Ω → Ω → ℝ} (hK : Measurable (Function.uncurry K)) :
    Measurable fun z : (X → Ω) × (Y → Ω) => ∏ p ∈ E, K (z.1 p.1) (z.2 p.2) := by
  refine Finset.measurable_prod _ fun p _ => ?_
  exact hK.comp (by fun_prop : Measurable fun z : (X → Ω) × (Y → Ω) => (z.1 p.1, z.2 p.2))

/-- Bipartite densities are invariant under coordinatewise measure-preserving maps. -/
lemma tBi_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
    {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Finset (X × Y)) (K : Ω' → Ω' → ℝ) (hK : Measurable (Function.uncurry K))
    {φ ψ : Ω → Ω'} (hφ : MeasurePreserving φ μ ν) (hψ : MeasurePreserving ψ μ ν) :
    tBi μ E (fun x y => K (φ x) (ψ y)) = tBi ν E K := by
  have hX := measurePreserving_pi (fun _ : X => μ) (fun _ => ν) (fun _ => hφ)
  have hY := measurePreserving_pi (fun _ : Y => μ) (fun _ => ν) (fun _ => hψ)
  have hmp := hX.prod hY
  unfold tBi
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (measurable_integrandBi E hK).aestronglyMeasurable]
  rfl

omit [Fintype X] [Fintype Y] in
lemma abs_integrandBi_le {Ω : Type*} (E : Finset (X × Y)) {K : Ω → Ω → ℝ} {M : ℝ}
    (hK : ∀ p q, |K p q| ≤ M) (z : (X → Ω) × (Y → Ω)) :
    ‖∏ p ∈ E, K (z.1 p.1) (z.2 p.2)‖ ≤ M ^ E.card := by
  rw [Real.norm_eq_abs, Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => hK _ _)

lemma tBi_eq_pi {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (E : Finset (X × Y)) (K : Ω → Ω → ℝ) :
    tBi μ E K = ∫ w : X ⊕ Y → Ω, ∏ p ∈ E, K (w (.inl p.1)) (w (.inr p.2))
      ∂(Measure.pi fun _ => μ) := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm (fun _ : X ⊕ Y => μ)
  have h := hmp.integral_comp' (g := fun w : X ⊕ Y → Ω => ∏ p ∈ E, K (w (.inl p.1)) (w (.inr p.2)))
  unfold tBi
  rw [← h]
  rfl

lemma tBiDec_eq_pi {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (E : Finset (X × Y)) (U : X × Y → Ω → Ω → ℝ) :
    tBiDec μ E U = ∫ w : X ⊕ Y → Ω, ∏ p ∈ E, U p (w (.inl p.1)) (w (.inr p.2))
      ∂(Measure.pi fun _ => μ) := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm (fun _ : X ⊕ Y => μ)
  have h := hmp.integral_comp'
    (g := fun w : X ⊕ Y → Ω => ∏ p ∈ E, U p (w (.inl p.1)) (w (.inr p.2)))
  unfold tBiDec
  rw [← h]
  rfl

end Bip

/-- Integrals over `(Z → [0,1] × Bool)` as averages over the copy labels. -/
lemma integral_pi_twoCopies {Z : Type*} [Fintype Z] [DecidableEq Z]
    (G : (Z → I × Bool) → ℝ) (hG : Measurable G) (M : ℝ) (hGb : ∀ w, |G w| ≤ M) :
    ∫ w, G w ∂(Measure.pi fun _ : Z => twoCopies) = ∑ τ : Z → Bool,
      (2⁻¹ : ℝ) ^ Fintype.card Z * ∫ x : Z → I, G (fun z => (x z, τ z))
        ∂(Measure.pi fun _ => (volume : Measure I)) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow I Bool Z (fun _ => volume)
    (fun _ => halfCount)
  unfold twoCopies
  have h1 := hmp.symm.integral_comp' (g := G)
  rw [← h1]
  have hint : Integrable (fun z : (Z → I) × (Z → Bool) => G (fun v => (z.1 v, z.2 v)))
      ((Measure.pi fun _ => (volume : Measure I)).prod (Measure.pi fun _ => halfCount)) := by
    refine Integrable.of_bound ?_ M (ae_of_all _ fun z => ?_)
    · have : Measurable fun z : (Z → I) × (Z → Bool) => fun v => (z.1 v, z.2 v) := by fun_prop
      exact (hG.comp this).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hGb _
  refine (integral_prod_symm _ hint).trans ?_
  rw [integral_fintype]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_eq_mul]
    congr 1
    have : ({τ} : Set (Z → Bool)) = Set.pi univ fun v => {τ v} := by
      ext τ'; simp [funext_iff]
    rw [measureReal_def, this, Measure.pi_pi]
    simp [halfCount, Measure.count_singleton, ENNReal.toReal_prod]
  · exact Integrable.of_finite

/-- `±1` from a Boolean. -/
noncomputable def sgnB (b : Bool) : ℝ := if b then 1 else -1

lemma abs_sgnB (b : Bool) : |sgnB b| = 1 := by cases b <;> simp [sgnB]

lemma sgnB_mul_self (b : Bool) : sgnB b * sgnB b = 1 := by cases b <;> simp [sgnB]

/-- The Boolean product (`xnor`), matching `sgnB`. -/
def bmul (b c : Bool) : Bool := !(xor b c)

lemma sgnB_bmul (b c : Bool) : sgnB (bmul b c) = sgnB b * sgnB c := by
  cases b <;> cases c <;> simp [sgnB, bmul]

/-- The sign-lifted kernel `K_B((x,ε),(y,δ)) = S(x,y) + εδ B(x,y)`. -/
noncomputable def lift (S B : I → I → ℝ) : I × Bool → I × Bool → ℝ := fun p q =>
  S p.1 q.1 + sgnB p.2 * sgnB q.2 * B p.1 q.1

lemma measurable_sgnB_comp {α : Type*} [MeasurableSpace α] {f : α → Bool} (hf : Measurable f) :
    Measurable fun a => sgnB (f a) :=
  (measurable_of_countable sgnB).comp hf

lemma measurable_lift {S B : I → I → ℝ} (hS : Measurable (Function.uncurry S))
    (hB : Measurable (Function.uncurry B)) : Measurable (Function.uncurry (lift S B)) := by
  have h1 : Measurable fun z : (I × Bool) × (I × Bool) => S z.1.1 z.2.1 :=
    hS.comp (by fun_prop : Measurable fun z : (I × Bool) × (I × Bool) => (z.1.1, z.2.1))
  have h2 : Measurable fun z : (I × Bool) × (I × Bool) => B z.1.1 z.2.1 :=
    hB.comp (by fun_prop : Measurable fun z : (I × Bool) × (I × Bool) => (z.1.1, z.2.1))
  have h3 : Measurable fun z : (I × Bool) × (I × Bool) => sgnB z.1.2 :=
    measurable_sgnB_comp (by fun_prop)
  have h4 : Measurable fun z : (I × Bool) × (I × Bool) => sgnB z.2.2 :=
    measurable_sgnB_comp (by fun_prop)
  exact h1.add ((h3.mul h4).mul h2)

lemma abs_lift_le {S B : I → I → ℝ} {MS MB : ℝ} (hS : ∀ x y, |S x y| ≤ MS)
    (hB : ∀ x y, |B x y| ≤ MB) (p q : I × Bool) : |lift S B p q| ≤ MS + MB := by
  unfold lift
  refine (abs_add_le _ _).trans (add_le_add (hS _ _) ?_)
  rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, one_mul, one_mul]
  exact hB _ _

/-! ### Rectangular step functions -/

/-- `f` is a rectangular step function: `f(x, y) = c(π₁ x, π₂ y)` for measurable finite-valued
`π₁, π₂`. -/
def GridRep (f : I → I → ℝ) : Prop :=
  ∃ (α β : Type) (_ : Fintype α) (_ : Fintype β) (π1 : I → α) (π2 : I → β),
    (∀ a, MeasurableSet (π1 ⁻¹' {a})) ∧ (∀ b, MeasurableSet (π2 ⁻¹' {b})) ∧
      ∃ c : α → β → ℝ, ∀ x y, f x y = c (π1 x) (π2 y)

lemma gridRep_op {f g : I → I → ℝ} (hf : GridRep f) (hg : GridRep g) (op : ℝ → ℝ → ℝ) :
    GridRep (fun x y => op (f x y) (g x y)) := by
  obtain ⟨α, β, _, _, π1, π2, h1, h2, c, hc⟩ := hf
  obtain ⟨α', β', _, _, π1', π2', h1', h2', c', hc'⟩ := hg
  refine ⟨α × α', β × β', inferInstance, inferInstance, fun x => (π1 x, π1' x),
    fun y => (π2 y, π2' y), fun a => ?_, fun b => ?_,
    fun a b => op (c a.1 b.1) (c' a.2 b.2), fun x y => ?_⟩
  rotate_left 2
  · show op (f x y) (g x y) = op (c (π1 x) (π2 y)) (c' (π1' x) (π2' y))
    rw [hc, hc']
  · have : (fun x => (π1 x, π1' x)) ⁻¹' {a} = π1 ⁻¹' {a.1} ∩ π1' ⁻¹' {a.2} := by
      ext x; simp [Prod.ext_iff]
    rw [this]; exact (h1 _).inter (h1' _)
  · have : (fun y => (π2 y, π2' y)) ⁻¹' {b} = π2 ⁻¹' {b.1} ∩ π2' ⁻¹' {b.2} := by
      ext y; simp [Prod.ext_iff]
    rw [this]; exact (h2 _).inter (h2' _)

lemma gridRep_rect {P Q : Set I} (hP : MeasurableSet P) (hQ : MeasurableSet Q) :
    GridRep (fun x y => (P ×ˢ Q).indicator (fun _ => (1 : ℝ)) (x, y)) := by
  classical
  refine ⟨Bool, Bool, inferInstance, inferInstance, fun x => decide (x ∈ P),
    fun y => decide (y ∈ Q), fun a => ?_, fun b => ?_,
    fun a b => if a = true ∧ b = true then 1 else 0, fun x y => ?_⟩
  · cases a
    · have : (fun x => decide (x ∈ P)) ⁻¹' {false} = Pᶜ := by ext; simp
      rw [this]; exact hP.compl
    · have : (fun x => decide (x ∈ P)) ⁻¹' {true} = P := by ext; simp
      rw [this]; exact hP
  · cases b
    · have : (fun y => decide (y ∈ Q)) ⁻¹' {false} = Qᶜ := by ext; simp
      rw [this]; exact hQ.compl
    · have : (fun y => decide (y ∈ Q)) ⁻¹' {true} = Q := by ext; simp
      rw [this]; exact hQ
  · by_cases hx : x ∈ P <;> by_cases hy : y ∈ Q <;> simp [Set.indicator, hx, hy]

/-- A rectangular step function is a finite combination of products of sign functions. -/
lemma gridRep_comb {f : I → I → ℝ} (hf : GridRep f) :
    ∃ (Q : Type) (_ : Fintype Q) (a : Q → ℝ) (r s : Q → I → Bool),
      (∀ q, Measurable (r q)) ∧ (∀ q, Measurable (s q)) ∧
        ∀ x y, f x y = ∑ q, a q * sgnB (r q x) * sgnB (s q y) := by
  classical
  obtain ⟨α, β, _, _, π1, π2, h1, h2, c, hc⟩ := hf
  refine ⟨(α × β) × (Bool × Bool), inferInstance, fun q => c q.1.1 q.1.2 / 4,
    fun q x => if q.2.1 then decide (π1 x = q.1.1) else true,
    fun q y => if q.2.2 then decide (π2 y = q.1.2) else true, fun q => ?_, fun q => ?_,
    fun x y => ?_⟩
  · refine measurable_to_countable' fun b => ?_
    by_cases hq : q.2.1 = true
    · simp only [hq, if_true]
      cases b
      · have : (fun x => decide (π1 x = q.1.1)) ⁻¹' {false} = (π1 ⁻¹' {q.1.1})ᶜ := by
          ext x; simp
        rw [this]; exact (h1 _).compl
      · have : (fun x => decide (π1 x = q.1.1)) ⁻¹' {true} = π1 ⁻¹' {q.1.1} := by
          ext x; simp
        rw [this]; exact h1 _
    · simp only [Bool.not_eq_true] at hq
      simp only [hq]
      exact measurableSet_preimage measurable_const (measurableSet_singleton _)
  · refine measurable_to_countable' fun b => ?_
    by_cases hq : q.2.2 = true
    · simp only [hq, if_true]
      cases b
      · have : (fun y => decide (π2 y = q.1.2)) ⁻¹' {false} = (π2 ⁻¹' {q.1.2})ᶜ := by
          ext y; simp
        rw [this]; exact (h2 _).compl
      · have : (fun y => decide (π2 y = q.1.2)) ⁻¹' {true} = π2 ⁻¹' {q.1.2} := by
          ext y; simp
        rw [this]; exact h2 _
    · simp only [Bool.not_eq_true] at hq
      simp only [hq]
      exact measurableSet_preimage measurable_const (measurableSet_singleton _)
  · rw [hc, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    have key : ∀ (a : α) (b : β), c a b / 4 * sgnB (decide (π1 x = a)) * sgnB (decide (π2 y = b)) +
        c a b / 4 * sgnB (decide (π1 x = a)) * sgnB true +
        (c a b / 4 * sgnB true * sgnB (decide (π2 y = b)) + c a b / 4 * sgnB true * sgnB true) =
        if π1 x = a ∧ π2 y = b then c a b else 0 := by
      intro a b
      by_cases ha : π1 x = a <;> by_cases hb : π2 y = b <;> simp [ha, hb, sgnB] <;> ring
    simp_rw [key]
    rw [Finset.sum_eq_single (π1 x), Finset.sum_eq_single (π2 y)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm ha]
    · simp

lemma isSetSemiring_rect :
    IsSetSemiring (Set.image2 (· ×ˢ ·) {s : Set I | MeasurableSet s}
      {t : Set I | MeasurableSet t}) := by
  classical
  have hm : ∀ {s : Set I}, MeasurableSet s → s ∈ {s : Set I | MeasurableSet s} := fun h => h
  refine ⟨Set.mem_image2.2 ⟨∅, hm MeasurableSet.empty, ∅, hm MeasurableSet.empty,
    Set.prod_empty⟩, ?_, ?_⟩
  · rintro _ ⟨P, hP, Q, hQ, rfl⟩ _ ⟨P', hP', Q', hQ', rfl⟩
    exact Set.mem_image2.2 ⟨P ∩ P', hm (MeasurableSet.inter hP hP'), Q ∩ Q',
      hm (MeasurableSet.inter hQ hQ'), (Set.prod_inter_prod).symm⟩
  · rintro _ ⟨P, hP, Q, hQ, rfl⟩ _ ⟨P', hP', Q', hQ', rfl⟩
    refine ⟨{(P \ P') ×ˢ Q, (P ∩ P') ×ˢ (Q \ Q')}, ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact Set.mem_image2.2 ⟨P \ P', hm (MeasurableSet.diff hP hP'), Q, hQ, rfl⟩
      · exact Set.mem_image2.2 ⟨P ∩ P', hm (MeasurableSet.inter hP hP'), Q \ Q',
          hm (MeasurableSet.diff hQ hQ'), rfl⟩
    · intro t ht t' ht' hne
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ht ht'
      simp only [Function.onFun, id]
      rw [Set.disjoint_left]
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
      · exact absurd rfl hne
      · rintro ⟨x, y⟩ h1 h2
        exact h1.1.2 h2.1.2
      · rintro ⟨x, y⟩ h1 h2
        exact h2.1.2 h1.1.2
      · exact absurd rfl hne
    · ext ⟨x, y⟩
      simp only [Set.mem_diff, Set.mem_prod, Finset.coe_insert, Finset.coe_singleton,
        Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_inter_iff]
      tauto

/-- Every measurable subset of `[0,1]²` is approximated in measure by sets whose indicators are
rectangular step functions. -/
lemma exists_gridRep_approx {T : Set (I × I)} (hT : MeasurableSet T) {ε : ENNReal}
    (hε : 0 < ε) : ∃ t : Set (I × I), MeasurableSet t ∧
      GridRep (fun x y => t.indicator (fun _ => (1 : ℝ)) (x, y)) ∧
        ((volume : Measure I).prod volume) (symmDiff t T) < ε := by
  have hgen : (inferInstance : MeasurableSpace (I × I)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) {s : Set I | MeasurableSet s}
        {t : Set I | MeasurableSet t}) := generateFrom_prod.symm
  obtain ⟨t, ht, hlt⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    (μ := (volume : Measure I).prod volume) isSetSemiring_rect
    ⟨{Set.univ}, Set.countable_singleton _, by
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact Set.mem_image2.2 ⟨Set.univ, (MeasurableSet.univ : MeasurableSet (Set.univ : Set I)),
        Set.univ, (MeasurableSet.univ : MeasurableSet (Set.univ : Set I)), Set.univ_prod_univ⟩,
      by simp⟩ hgen hT hε
  let Good : Set (Set (I × I)) := {u | MeasurableSet u ∧
    GridRep (fun x y => u.indicator (fun _ => (1 : ℝ)) (x, y))}
  have hsub : Set.image2 (· ×ˢ ·) {s : Set I | MeasurableSet s}
      {t : Set I | MeasurableSet t} ⊆ Good := by
    rintro _ ⟨P, hP, Q, hQ, rfl⟩
    exact ⟨hP.prod hQ, gridRep_rect hP hQ⟩
  have hclosed : SupClosed Good := by
    rintro u ⟨hu, hgu⟩ v ⟨hv, hgv⟩
    refine ⟨hu.union hv, ?_⟩
    have heq : (fun x y => (u ∪ v).indicator (fun _ => (1 : ℝ)) (x, y)) =
        fun x y => max (u.indicator (fun _ => (1 : ℝ)) (x, y))
          (v.indicator (fun _ => (1 : ℝ)) (x, y)) := by
      funext x y
      by_cases h1 : (x, y) ∈ u <;> by_cases h2 : (x, y) ∈ v <;> simp [Set.indicator, h1, h2]
    show GridRep fun x y => (u ∪ v).indicator (fun _ => (1 : ℝ)) (x, y)
    rw [heq]
    exact gridRep_op hgu hgv max
  obtain ⟨htm, htg⟩ := supClosure_min hsub hclosed ht
  exact ⟨t, htm, htg, hlt⟩

section Lift

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The sign-average formula for lifted kernels. -/
lemma tBi_lift_eq_avg [DecidableEq X] [DecidableEq Y] (E : Finset (X × Y)) (S B : I → I → ℝ)
    (hS : Measurable (Function.uncurry S)) (hB : Measurable (Function.uncurry B)) {MS MB : ℝ}
    (hMS : ∀ x y, |S x y| ≤ MS) (hMB : ∀ x y, |B x y| ≤ MB) :
    tBi twoCopies E (lift S B) = ∑ τ : X ⊕ Y → Bool, (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) *
      tBiDec volume E (fun p x y => S x y + sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) * B x y) := by
  rw [tBi_eq_pi]
  refine Eq.trans (integral_pi_twoCopies (fun w : X ⊕ Y → I × Bool => ∏ p ∈ E,
    lift S B (w (.inl p.1)) (w (.inr p.2))) ?_ ((MS + MB) ^ E.card) ?_) ?_
  rotate_left 2
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [tBiDec_eq_pi]
    rfl
  · refine Finset.measurable_prod _ fun p _ => ?_
    exact (measurable_lift hS hB).comp
      (by fun_prop : Measurable fun w : X ⊕ Y → I × Bool => (w (.inl p.1), w (.inr p.2)))
  · intro w
    rw [Finset.abs_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_lift_le hMS hMB _ _)

lemma tb_sign_eq (E : Finset (X × Y)) (S A : I → I → ℝ)
    (hplus : tb E (fun x y => S x y + A x y) = tb E S)
    (hminus : tb E (fun x y => S x y - A x y) = tb E S) (a b : Bool) :
    tb E (fun x y => S x y + sgnB a * sgnB b * A x y) = tb E S := by
  have hp : (fun x y => S x y + (1 : ℝ) * 1 * A x y) = fun x y => S x y + A x y := by
    funext x y; ring
  have hp' : (fun x y => S x y + (-1 : ℝ) * -1 * A x y) = fun x y => S x y + A x y := by
    funext x y; ring
  have hm : (fun x y => S x y + (1 : ℝ) * -1 * A x y) = fun x y => S x y - A x y := by
    funext x y; ring
  have hm' : (fun x y => S x y + (-1 : ℝ) * 1 * A x y) = fun x y => S x y - A x y := by
    funext x y; ring
  cases a <;> cases b <;> simp only [sgnB, if_true, if_false, Bool.false_eq_true]
  · rw [hp', hplus]
  · rw [hm', hminus]
  · rw [hm, hminus]
  · rw [hp, hplus]

/-- Upper bound through the weak Hölder inequality (Lemma 2.2, used as a black box). -/
lemma tBi_lift_le (E : Finset (X × Y)) (hm : 0 < E.card) (hE : IsWeaklyNorming E)
    (S A : I → I → ℝ) (hS : IsKernel S) (hA : IsKernel A) (hSA : ∀ x y, |A x y| ≤ S x y)
    (hplus : tb E (fun x y => S x y + A x y) = tb E S)
    (hminus : tb E (fun x y => S x y - A x y) = tb E S) :
    tBi twoCopies E (lift S A) ≤ tb E S := by
  classical
  obtain ⟨MS, hMS⟩ := hS.2
  obtain ⟨MA, hMA⟩ := hA.2
  have hc0 : 0 ≤ tb E S := tb_nonneg E S (fun x y => (abs_nonneg _).trans (hSA x y))
  rw [tBi_lift_eq_avg E S A hS.1 hA.1 hMS hMA]
  have hterm : ∀ τ : X ⊕ Y → Bool, tBiDec volume E (fun p x y =>
      S x y + sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) * A x y) ≤ tb E S := by
    intro τ
    refine (le_abs_self _).trans ((lemma_2_2 E hE _ fun p _ => ?_).trans (le_of_eq ?_))
    · refine ⟨hS.1.add ((measurable_const.mul measurable_const).mul hA.1), MS + MA, ?_⟩
      intro x y
      refine (abs_add_le _ _).trans (add_le_add (hMS x y) ?_)
      rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, one_mul, one_mul]
      exact hMA x y
    · have habs : ∀ p : X × Y, (fun x y => |S x y + sgnB (τ (.inl p.1)) *
          sgnB (τ (.inr p.2)) * A x y|) =
          fun x y => S x y + sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) * A x y := by
        intro p; funext x y
        apply abs_of_nonneg
        have h1 := hSA x y
        have h2 : |sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) * A x y| = |A x y| := by
          rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, one_mul, one_mul]
        have h3 := neg_abs_le (sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) * A x y)
        linarith
      simp_rw [habs, tb_sign_eq E S A hplus hminus]
      rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hc0, one_div,
        inv_mul_cancel₀ (by exact_mod_cast hm.ne'), Real.rpow_one]
  calc ∑ τ : X ⊕ Y → Bool, (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) * tBiDec volume E _
      ≤ ∑ τ : X ⊕ Y → Bool, (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) * tb E S :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hterm τ) (by positivity)
    _ = tb E S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul,
          ← mul_assoc]
        push_cast
        rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]

lemma map_bmul_halfCount (c : Bool) : Measure.map (fun b => bmul b c) halfCount = halfCount := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have : (fun b' => bmul b' c) ⁻¹' {b} = {bmul b c} := by
    ext b'; cases b <;> cases b' <;> cases c <;> simp [bmul]
  rw [this]
  simp [halfCount, Measure.count_singleton]

/-- Multiplying the copy label by a measurable sign function is measure preserving. -/
lemma measurePreserving_flipBy {r : I → Bool} (hr : Measurable r) :
    MeasurePreserving (fun p : I × Bool => (p.1, bmul p.2 (r p.1))) twoCopies twoCopies := by
  unfold twoCopies
  refine MeasurePreserving.skew_product (f := id) (g := fun x b => bmul b (r x))
    (MeasurePreserving.id _) ?_ (ae_of_all _ fun x => map_bmul_halfCount (r x))
  exact (measurable_of_countable (fun q : Bool × Bool => bmul q.1 q.2)).comp
    (measurable_snd.prodMk (hr.comp measurable_fst))

/-- Sign switching: `Φ(K_{A r s}) = Φ(K_A)` for measurable sign functions `r, s`. -/
lemma tBi_lift_signSwitch (E : Finset (X × Y)) (S B : I → I → ℝ)
    (hS : Measurable (Function.uncurry S)) (hB : Measurable (Function.uncurry B))
    {r s : I → Bool} (hr : Measurable r) (hs : Measurable s) :
    tBi twoCopies E (lift S (fun x y => B x y * sgnB (r x) * sgnB (s y))) =
      tBi twoCopies E (lift S B) := by
  rw [← tBi_comp E (lift S B) (measurable_lift hS hB) (measurePreserving_flipBy hr)
    (measurePreserving_flipBy hs)]
  congr 1
  funext p q
  simp only [lift, sgnB_bmul]
  ring

lemma measurePreserving_fst_twoCopies :
    MeasurePreserving (Prod.fst : I × Bool → I) twoCopies volume := by
  unfold twoCopies
  exact measurePreserving_fst

lemma tBi_lift_zero (E : Finset (X × Y)) (S : I → I → ℝ) (hS : Measurable (Function.uncurry S)) :
    tBi twoCopies E (lift S (fun _ _ => 0)) = tb E S := by
  rw [show tb E S = tBi volume E S from rfl,
    ← tBi_comp E S hS measurePreserving_fst_twoCopies measurePreserving_fst_twoCopies]
  congr 1
  funext p q
  simp [lift]

lemma tBi_lift_neg (E : Finset (X × Y)) (S B : I → I → ℝ)
    (hS : Measurable (Function.uncurry S)) (hB : Measurable (Function.uncurry B)) :
    tBi twoCopies E (lift S (fun x y => - B x y)) = tBi twoCopies E (lift S B) := by
  have h := tBi_lift_signSwitch E S B hS hB (r := fun _ => false) (s := fun _ => true)
    measurable_const measurable_const
  rw [← h]
  congr 1
  funext p q
  simp [lift, sgnB]

/-- The pull-back of a kernel on the two copies to `[0,1]`. -/
noncomputable def pb (K : I × Bool → I × Bool → ℝ) : I → I → ℝ :=
  fun x y => K (halfSplit x) (halfSplit y)

lemma tBi_eq_tb_pb (E : Finset (X × Y)) (K : I × Bool → I × Bool → ℝ)
    (hK : Measurable (Function.uncurry K)) : tBi twoCopies E K = tb E (pb K) :=
  (tBi_comp E K hK measurePreserving_halfSplit measurePreserving_halfSplit).symm

lemma isKernel_pb {K : I × Bool → I × Bool → ℝ} (hK : Measurable (Function.uncurry K)) {M : ℝ}
    (hM : ∀ p q, |K p q| ≤ M) : IsKernel (pb K) :=
  ⟨hK.comp (measurable_halfSplit.prodMap measurable_halfSplit), M, fun _ _ => hM _ _⟩

lemma lift_nonneg {S B : I → I → ℝ} (hSB : ∀ x y, |B x y| ≤ S x y) (p q : I × Bool) :
    0 ≤ lift S B p q := by
  unfold lift
  have h1 := hSB p.1 q.1
  have h2 : |sgnB p.2 * sgnB q.2 * B p.1 q.1| = |B p.1 q.1| := by
    rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, one_mul, one_mul]
  have h3 := neg_abs_le (sgnB p.2 * sgnB q.2 * B p.1 q.1)
  linarith

lemma rNorm_pb_eq (E : Finset (X × Y)) {K : I × Bool → I × Bool → ℝ}
    (hK : Measurable (Function.uncurry K)) (hK0 : ∀ p q, 0 ≤ K p q) :
    rNorm E (pb K) = tBi twoCopies E K ^ ((1 : ℝ) / E.card) := by
  unfold rNorm
  rw [tBi_eq_tb_pb E K hK]
  congr 2
  funext x y
  exact abs_of_nonneg (hK0 _ _)

/-- The lower bound `Φ(K_B) ≥ Φ(S)` for `|B| ≤ S`. -/
lemma tb_le_tBi_lift (E : Finset (X × Y)) (hE : IsWeaklyNorming E) (S B : I → I → ℝ)
    (hS : IsKernel S) (hB : IsKernel B) (hSB : ∀ x y, |B x y| ≤ S x y) :
    tb E S ≤ tBi twoCopies E (lift S B) := by
  obtain ⟨MS, hMS⟩ := hS.2
  obtain ⟨MB, hMB⟩ := hB.2
  have hBm : Measurable (Function.uncurry fun x y => - B x y) := hB.1.neg
  have hSBn : ∀ x y, |(fun x y => - B x y) x y| ≤ S x y := fun x y => by
    simp only [abs_neg]; exact hSB x y
  have hMBn : ∀ x y, |(fun x y => - B x y) x y| ≤ MB := fun x y => by
    simp only [abs_neg]; exact hMB x y
  have hk1 := isKernel_pb (measurable_lift hS.1 hB.1) (abs_lift_le hMS hMB)
  have hk2 := isKernel_pb (measurable_lift hS.1 hBm) (abs_lift_le hMS hMBn)
  have hsum := hE.2.1 _ _ (isKernel_const_mul hk1 (1 / 2)) (isKernel_const_mul hk2 (1 / 2))
  rw [hE.1 _ hk1, hE.1 _ hk2, rNorm_pb_eq E (measurable_lift hS.1 hB.1) (lift_nonneg hSB),
    rNorm_pb_eq E (measurable_lift hS.1 hBm) (lift_nonneg hSBn),
    tBi_lift_neg E S B hS.1 hB.1] at hsum
  have hmid : (fun x y => (1 / 2 : ℝ) * pb (lift S B) x y + (1 / 2 : ℝ) *
      pb (lift S fun x y => - B x y) x y) = pb (lift S (fun _ _ => 0)) := by
    funext x y; simp only [pb, lift]; ring
  rw [hmid] at hsum
  have h0m : Measurable (Function.uncurry (lift S (fun _ _ => (0 : ℝ)))) :=
    measurable_lift hS.1 measurable_const
  have h00 : ∀ x y, |(fun _ _ : I => (0 : ℝ)) x y| ≤ S x y := fun x y => by
    simp only [abs_zero]; exact (abs_nonneg _).trans (hSB x y)
  rw [rNorm_pb_eq E h0m (lift_nonneg h00)] at hsum
  have key : rNorm E (pb (lift S fun _ _ => 0)) ≤ rNorm E (pb (lift S B)) := by
    rw [rNorm_pb_eq E h0m (lift_nonneg h00), rNorm_pb_eq E (measurable_lift hS.1 hB.1)
      (lift_nonneg hSB)]
    refine hsum.trans (le_of_eq ?_)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have := tb_le_of_rNorm_le E _ _ (fun x y => lift_nonneg h00 _ _)
    (fun x y => lift_nonneg hSB _ _) key
  rw [tBi_eq_tb_pb E _ (measurable_lift hS.1 hB.1), ← tBi_lift_zero E S hS.1,
    tBi_eq_tb_pb E _ h0m]
  exact this

lemma isKernel_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (K : ι → I → I → ℝ)
    (hK : ∀ i ∈ s, IsKernel (K i)) : IsKernel (fun x y => ∑ i ∈ s, c i * K i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨measurable_const, 0, fun _ _ => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 := isKernel_const_mul (hK a (Finset.mem_insert_self a s)) (c a)
    have h2 := ih fun i hi => hK i (Finset.mem_insert_of_mem hi)
    refine ⟨h1.1.add h2.1, ?_⟩
    obtain ⟨M1, hM1⟩ := h1.2
    obtain ⟨M2, hM2⟩ := h2.2
    exact ⟨M1 + M2, fun x y => (abs_add_le _ _).trans (add_le_add (hM1 x y) (hM2 x y))⟩

/-- The weak norm is subadditive over finite sums. -/
lemma rNorm_sum_le (E : Finset (X × Y)) (hE : IsWeaklyNorming E) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (K : ι → I → I → ℝ) (hK : ∀ i ∈ s, IsKernel (K i)) :
    rNorm E (fun x y => ∑ i ∈ s, c i * K i x y) ≤ ∑ i ∈ s, |c i| * rNorm E (K i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : IsKernel (fun _ _ : I => (0 : ℝ)) := ⟨measurable_const, 0, fun _ _ => by simp⟩
    have := hE.1 _ h0 0
    simp only [zero_mul, abs_zero] at this
    rw [this]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 := isKernel_const_mul (hK a (Finset.mem_insert_self a s)) (c a)
    have h2 := isKernel_sum s c K fun i hi => hK i (Finset.mem_insert_of_mem hi)
    refine (hE.2.1 _ _ h1 h2).trans ?_
    rw [hE.1 _ (hK a (Finset.mem_insert_self a s))]
    exact add_le_add_right (ih fun i hi => hK i (Finset.mem_insert_of_mem hi)) _

/-- `t ↦ Φ(K_{tB})` is a polynomial. -/
lemma tBi_lift_poly (E : Finset (X × Y)) (S B : I → I → ℝ) (hS : IsKernel S) (hB : IsKernel B) :
    ∃ C : Finset (X × Y) → ℝ, ∀ t : ℝ,
      tBi twoCopies E (lift S (fun x y => t * B x y)) = ∑ F ∈ E.powerset, C F * t ^ F.card := by
  classical
  obtain ⟨MS, hMS⟩ := hS.2
  obtain ⟨MB, hMB⟩ := hB.2
  let G : X × Y → (X → I × Bool) × (Y → I × Bool) → ℝ := fun p z =>
    sgnB (z.1 p.1).2 * sgnB (z.2 p.2).2 * B (z.1 p.1).1 (z.2 p.2).1
  let H : X × Y → (X → I × Bool) × (Y → I × Bool) → ℝ := fun p z => S (z.1 p.1).1 (z.2 p.2).1
  refine ⟨fun F => ∫ z, (∏ p ∈ F, G p z) * ∏ p ∈ E \ F, H p z
    ∂((Measure.pi fun _ => twoCopies).prod (Measure.pi fun _ => twoCopies)), fun t => ?_⟩
  unfold tBi
  have hexp : ∀ z : (X → I × Bool) × (Y → I × Bool),
      ∏ p ∈ E, lift S (fun x y => t * B x y) (z.1 p.1) (z.2 p.2) =
        ∑ F ∈ E.powerset, ((∏ p ∈ F, G p z) * ∏ p ∈ E \ F, H p z) * t ^ F.card := by
    intro z
    have : ∀ p, lift S (fun x y => t * B x y) (z.1 p.1) (z.2 p.2) = t * G p z + H p z := by
      intro p; simp only [lift, G, H]; ring
    simp_rw [this]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    ring
  simp_rw [hexp]
  have hGm : ∀ p, Measurable (G p) := by
    intro p
    have h1 : Measurable fun z : (X → I × Bool) × (Y → I × Bool) => sgnB (z.1 p.1).2 :=
      measurable_sgnB_comp (by fun_prop)
    have h2 : Measurable fun z : (X → I × Bool) × (Y → I × Bool) => sgnB (z.2 p.2).2 :=
      measurable_sgnB_comp (by fun_prop)
    have h3 : Measurable fun z : (X → I × Bool) × (Y → I × Bool) =>
        B (z.1 p.1).1 (z.2 p.2).1 :=
      hB.1.comp (by fun_prop : Measurable fun z : (X → I × Bool) × (Y → I × Bool) =>
        ((z.1 p.1).1, (z.2 p.2).1))
    exact (h1.mul h2).mul h3
  have hHm : ∀ p, Measurable (H p) := fun p =>
    hS.1.comp (by fun_prop : Measurable fun z : (X → I × Bool) × (Y → I × Bool) =>
      ((z.1 p.1).1, (z.2 p.2).1))
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun F _ => ?_
    rw [integral_mul_const]
  · intro F _
    refine Integrable.mul_const ?_ _
    refine Integrable.of_bound ?_ (MB ^ F.card * MS ^ (E \ F).card) (ae_of_all _ fun z => ?_)
    · exact ((Finset.measurable_prod _ fun p _ => hGm p).mul
        (Finset.measurable_prod _ fun p _ => hHm p)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const,
        ← Finset.prod_const]
      refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p _ => ?_)
        (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p _ => hMS _ _)
        (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        (Finset.prod_nonneg fun _ _ => (abs_nonneg _).trans (hMB (Classical.arbitrary I)
          (Classical.arbitrary I)))
      simp only [G]
      rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, one_mul, one_mul]
      exact hMB _ _

/-- The finite-combination step of eq. (11) (eq:sign-multiplier, tex l.909-934) in the proof of
Lemma 4.6: `Φ(K_{Ah}) = Φ(S)` for every finite combination `h` of products of
sign functions. -/
lemma tBi_lift_comb (E : Finset (X × Y)) (hm : 0 < E.card) (hE : IsWeaklyNorming E)
    (S A : I → I → ℝ) (hS : IsKernel S) (hA : IsKernel A) (hSA : ∀ x y, |A x y| ≤ S x y)
    (hplus : tb E (fun x y => S x y + A x y) = tb E S)
    (hminus : tb E (fun x y => S x y - A x y) = tb E S)
    {Q : Type*} [Fintype Q] (a : Q → ℝ) (r s : Q → I → Bool) (hr : ∀ q, Measurable (r q))
    (hs : ∀ q, Measurable (s q)) :
    tBi twoCopies E (lift S (fun x y => A x y * ∑ q, a q * sgnB (r q x) * sgnB (s q y))) =
      tb E S := by
  classical
  set c := tb E S with hc
  have hc0 : 0 ≤ c := tb_nonneg E S (fun x y => (abs_nonneg _).trans (hSA x y))
  have hcA : tBi twoCopies E (lift S A) = c :=
    le_antisymm (tBi_lift_le E hm hE S A hS hA hSA hplus hminus) (tb_le_tBi_lift E hE S A hS hA hSA)
  set h : I → I → ℝ := fun x y => ∑ q, a q * sgnB (r q x) * sgnB (s q y) with hh
  set L : ℝ := ∑ q, |a q| with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hhL : ∀ x y, |h x y| ≤ L := by
    intro x y
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, mul_one, mul_one]
  have hhm : Measurable (Function.uncurry h) := by
    refine Finset.measurable_sum _ fun q _ => ?_
    exact (measurable_const.mul (measurable_sgnB_comp ((hr q).comp measurable_fst))).mul
      (measurable_sgnB_comp ((hs q).comp measurable_snd))
  obtain ⟨MA, hMA⟩ := hA.2
  have hAh : IsKernel (fun x y => A x y * h x y) := by
    refine ⟨hA.1.mul hhm, MA * L, fun x y => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hMA x y) (hhL x y) (abs_nonneg _) ((abs_nonneg _).trans (hMA x y))
  rcases eq_or_lt_of_le hL0 with hL | hL
  · -- `L = 0`: `h = 0`
    have ha : ∀ q, a q = 0 := by
      intro q
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => abs_nonneg (a q))).1 hL.symm q
        (Finset.mem_univ q)
      exact abs_eq_zero.1 this
    have : (fun x y => A x y * h x y) = fun _ _ => 0 := by
      funext x y; simp [hh, ha]
    rw [this, tBi_lift_zero E S hS.1]
  -- the interval identity
  have hint : ∀ t ∈ Icc (0 : ℝ) (1 / L),
      tBi twoCopies E (lift S (fun x y => t * (A x y * h x y))) = c := by
    intro t ht
    have htL : t * L ≤ 1 := by
      have := ht.2; rw [le_div_iff₀ hL] at this; linarith
    have ht0 := ht.1
    have hB : IsKernel (fun x y => t * (A x y * h x y)) := isKernel_const_mul hAh t
    have hSB : ∀ x y, |t * (A x y * h x y)| ≤ S x y := by
      intro x y
      rw [abs_mul, abs_mul, abs_of_nonneg ht0]
      calc t * (|A x y| * |h x y|) ≤ t * (|A x y| * L) := by
            gcongr; exact hhL x y
        _ = (t * L) * |A x y| := by ring
        _ ≤ 1 * |A x y| := by gcongr
        _ ≤ S x y := by rw [one_mul]; exact hSA x y
    refine le_antisymm ?_ (tb_le_tBi_lift E hE S _ hS hB hSB)
    -- the upper bound through the triangle inequality
    let r' : Q → I → Bool := fun q x => if 0 ≤ a q then r q x else !(r q x)
    have hr' : ∀ q, Measurable (r' q) := by
      intro q
      by_cases hq : 0 ≤ a q
      · simp only [r', hq, if_true]; exact hr q
      · simp only [r', hq, if_false]
        exact (measurable_of_countable (fun b : Bool => !b)).comp (hr q)
    have hr'a : ∀ q x, |a q| * sgnB (r' q x) = a q * sgnB (r q x) := by
      intro q x
      by_cases hq : 0 ≤ a q
      · simp only [r', hq, if_true, abs_of_nonneg hq]
      · simp only [r', hq, if_false, abs_of_neg (not_le.1 hq)]
        cases r q x <;> simp [sgnB]
    let Bq : Q → I → I → ℝ := fun q x y => A x y * sgnB (r' q x) * sgnB (s q y)
    have hBq : ∀ q, tBi twoCopies E (lift S (Bq q)) = c := by
      intro q
      rw [tBi_lift_signSwitch E S A hS.1 hA.1 (hr' q) (hs q), hcA]
    have hBqm : ∀ q, Measurable (Function.uncurry (lift S (Bq q))) := by
      intro q
      refine measurable_lift hS.1 ?_
      exact (hA.1.mul (measurable_sgnB_comp ((hr' q).comp measurable_fst))).mul
        (measurable_sgnB_comp ((hs q).comp measurable_snd))
    have hSBq : ∀ q x y, |Bq q x y| ≤ S x y := by
      intro q x y
      simp only [Bq]
      rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, mul_one, mul_one]
      exact hSA x y
    obtain ⟨MS, hMS⟩ := hS.2
    have hMBq : ∀ q x y, |Bq q x y| ≤ MA := by
      intro q x y
      simp only [Bq]
      rw [abs_mul, abs_mul, abs_sgnB, abs_sgnB, mul_one, mul_one]
      exact hMA x y
    -- coefficients and kernels indexed by `Option Q`
    let coef : Option Q → ℝ := fun o => match o with
      | none => 1 - t * L
      | some q => t * |a q|
    let ker : Option Q → I → I → ℝ := fun o => match o with
      | none => pb (lift S (fun _ _ => 0))
      | some q => pb (lift S (Bq q))
    have h00 : ∀ x y, |(fun _ _ : I => (0 : ℝ)) x y| ≤ S x y := fun x y => by
      simp only [abs_zero]; exact (abs_nonneg _).trans (hSA x y)
    have h0m : Measurable (Function.uncurry (lift S (fun _ _ => (0 : ℝ)))) :=
      measurable_lift hS.1 measurable_const
    have hker : ∀ o ∈ (Finset.univ : Finset (Option Q)), IsKernel (ker o) := by
      intro o _
      rcases o with _ | q
      · exact isKernel_pb h0m (abs_lift_le hMS (MB := 0) (fun _ _ => by simp))
      · exact isKernel_pb (hBqm q) (abs_lift_le hMS (hMBq q))
    have alg : ∀ (S0 A0 e : ℝ) (σr σr' σs : Q → ℝ), (∀ q, |a q| * σr' q = a q * σr q) →
        S0 + e * (t * (A0 * ∑ q, a q * σr q * σs q)) =
          (1 - t * L) * (S0 + e * 0) + ∑ q, t * |a q| * (S0 + e * (A0 * σr' q * σs q)) := by
      intro S0 A0 e σr σr' σs hσ
      have h1 : ∑ q, t * |a q| * (S0 + e * (A0 * σr' q * σs q)) =
          ∑ q, (t * S0 * |a q| + e * t * A0 * (a q * σr q * σs q)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have := hσ q
        calc t * |a q| * (S0 + e * (A0 * σr' q * σs q))
            = t * S0 * |a q| + e * t * A0 * ((|a q| * σr' q) * σs q) := by ring
          _ = t * S0 * |a q| + e * t * A0 * (a q * σr q * σs q) := by rw [this]
      rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hLdef]
      ring
    have hdecomp : pb (lift S (fun x y => t * (A x y * h x y))) =
        fun x y => ∑ o, coef o * ker o x y := by
      funext x y
      rw [Fintype.sum_option]
      simp only [coef, ker, pb, lift, Bq, hh]
      exact alg _ _ _ (fun q => sgnB (r q (halfSplit x).1)) (fun q => sgnB (r' q (halfSplit x).1))
        (fun q => sgnB (s q (halfSplit y).1)) (fun q => hr'a q _)
    have hnn : ∀ p q, 0 ≤ lift S (fun x y => t * (A x y * h x y)) p q := lift_nonneg hSB
    have hlm : Measurable (Function.uncurry (lift S (fun x y => t * (A x y * h x y)))) :=
      measurable_lift hS.1 hB.1
    have hN := rNorm_sum_le E hE Finset.univ coef ker hker
    rw [← hdecomp, rNorm_pb_eq E hlm hnn, Fintype.sum_option] at hN
    simp only [coef, ker] at hN
    rw [rNorm_pb_eq E h0m (lift_nonneg h00), tBi_lift_zero E S hS.1] at hN
    simp_rw [rNorm_pb_eq E (hBqm _) (lift_nonneg (hSBq _)), hBq] at hN
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t * L)] at hN
    simp_rw [abs_mul, abs_of_nonneg ht0, abs_abs] at hN
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← hLdef] at hN
    have hN' : tBi twoCopies E (lift S fun x y => t * (A x y * h x y)) ^ ((1 : ℝ) / E.card) ≤
        c ^ ((1 : ℝ) / E.card) := by
      refine hN.trans (le_of_eq ?_); ring
    have hpos : (0 : ℝ) < 1 / E.card := by
      have : (0 : ℝ) < E.card := by exact_mod_cast hm
      positivity
    exact (Real.rpow_le_rpow_iff (tBi_eq_tb_pb E _ hlm ▸ tb_nonneg E _ (fun x y => hnn _ _))
      hc0 hpos).1 hN'
  -- the polynomial identity
  obtain ⟨C, hC⟩ := tBi_lift_poly E S (fun x y => A x y * h x y) hS hAh
  let P : Polynomial ℝ := ∑ F ∈ E.powerset, Polynomial.C (C F) * Polynomial.X ^ F.card
  have hP : ∀ t, P.eval t = tBi twoCopies E (lift S (fun x y => t * (A x y * h x y))) := by
    intro t
    rw [hC t]
    simp [P, Polynomial.eval_finsetSum]
  have hPc : P = Polynomial.C c := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (fun t ht => ?_) (Set.Icc_infinite (by positivity : (0 : ℝ) < 1 / L))
    simp only [Set.mem_setOf_eq, Polynomial.eval_C]
    rw [hP t, hint t ht]
  have := hP 1
  rw [hPc, Polynomial.eval_C] at this
  rw [this]
  congr 2
  funext x y
  rw [one_mul]

lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hf : ∀ i ∈ s, |f i| ≤ M) (hg : ∀ i ∈ s, |g i| ≤ M) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ M ^ s.card * ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hfs : ∀ i ∈ s, |f i| ≤ M := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, |g i| ≤ M := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have ih' := ih hfs hgs
    have hF : |∏ i ∈ s, f i| ≤ M ^ s.card := by
      rw [Finset.abs_prod, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hfs
    have hga := hg a (Finset.mem_insert_self a s)
    have hM0 : 0 ≤ M := by linarith
    have hpow : 1 ≤ M ^ s.card := one_le_pow₀ hM
    have hsum0 : 0 ≤ ∑ i ∈ s, |f i - g i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i|
        = |(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)| := by ring_nf
      _ ≤ |f a - g a| * M ^ s.card + M * (M ^ s.card * ∑ i ∈ s, |f i - g i|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hF (abs_nonneg _)
          · rw [abs_mul]; exact mul_le_mul hga ih' (abs_nonneg _) hM0
      _ ≤ M ^ (s.card + 1) * (|f a - g a| + ∑ i ∈ s, |f i - g i|) := by
          rw [pow_succ]
          nlinarith [abs_nonneg (f a - g a), mul_le_mul_of_nonneg_left hpow (abs_nonneg (f a - g a))]

/-- The marginal of an edge. -/
lemma integral_edge_marginal (g : I → I → ℝ) (hg : Measurable (Function.uncurry g)) (u : X)
    (v : Y) :
    ∫ z : (X → I × Bool) × (Y → I × Bool), g (z.1 u).1 (z.2 v).1
      ∂((Measure.pi fun _ => twoCopies).prod (Measure.pi fun _ => twoCopies)) =
      ∫ w : I × I, g w.1 w.2 ∂((volume : Measure I).prod volume) := by
  have h1 := measurePreserving_fst_twoCopies.comp
    (measurePreserving_eval (fun _ : X => twoCopies) u)
  have h2 := measurePreserving_fst_twoCopies.comp
    (measurePreserving_eval (fun _ : Y => twoCopies) v)
  have hmp := h1.prod h2
  rw [← hmp.map_eq]
  exact (integral_map (f := fun w : I × I => g w.1 w.2) hmp.measurable.aemeasurable
    hg.aestronglyMeasurable).symm

/-- Lipschitz dependence of `Φ(K_{Ah})` on `h` in `L¹`. -/
lemma tBi_lift_lipschitz (E : Finset (X × Y)) (S A : I → I → ℝ) (hS : IsKernel S)
    (hA : IsKernel A) {Mh : ℝ} (hMh : 0 ≤ Mh) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ h h' : I → I → ℝ, Measurable (Function.uncurry h) →
      Measurable (Function.uncurry h') → (∀ x y, |h x y| ≤ Mh) → (∀ x y, |h' x y| ≤ Mh) →
      |tBi twoCopies E (lift S (fun x y => A x y * h x y)) -
      tBi twoCopies E (lift S (fun x y => A x y * h' x y))| ≤
        Λ * ∫ w : I × I, |h w.1 w.2 - h' w.1 w.2| ∂((volume : Measure I).prod volume) := by
  obtain ⟨MS, hMS⟩ := hS.2
  obtain ⟨MA, hMA⟩ := hA.2
  have hMA0 : 0 ≤ MA := (abs_nonneg _).trans (hMA (Classical.arbitrary I) (Classical.arbitrary I))
  have hMS0 : 0 ≤ MS := (abs_nonneg _).trans (hMS (Classical.arbitrary I) (Classical.arbitrary I))
  set M : ℝ := MS + MA * Mh + 1 with hM
  have hM1 : 1 ≤ M := by have := mul_nonneg hMA0 hMh; linarith
  refine ⟨M ^ E.card * (MA * E.card), by positivity, fun h h' hhm hh'm hh hh' => ?_⟩
  have hAhm : ∀ k : I → I → ℝ, Measurable (Function.uncurry k) →
      Measurable (Function.uncurry fun x y => A x y * k x y) := fun k hk => hA.1.mul hk
  have hbd : ∀ k : I → I → ℝ, (∀ x y, |k x y| ≤ Mh) → ∀ p q,
      |lift S (fun x y => A x y * k x y) p q| ≤ M := by
    intro k hk p q
    refine (abs_lift_le hMS (MB := MA * Mh) (fun x y => ?_) p q).trans (by linarith)
    rw [abs_mul]; exact mul_le_mul (hMA x y) (hk x y) (abs_nonneg _) hMA0
  have hint : ∀ k : I → I → ℝ, Measurable (Function.uncurry k) → (∀ x y, |k x y| ≤ Mh) →
      Integrable (fun z : (X → I × Bool) × (Y → I × Bool) =>
        ∏ p ∈ E, lift S (fun x y => A x y * k x y) (z.1 p.1) (z.2 p.2))
        ((Measure.pi fun _ => twoCopies).prod (Measure.pi fun _ => twoCopies)) := by
    intro k hk hkb
    refine Integrable.of_bound (measurable_integrandBi E
      (measurable_lift hS.1 (hAhm k hk))).aestronglyMeasurable (M ^ E.card)
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun _ _ => hbd k hkb _ _
  have hdm : Measurable (Function.uncurry fun x y => |h x y - h' x y|) :=
    (hhm.sub hh'm).abs
  have hedge : ∀ p : X × Y, Integrable (fun z : (X → I × Bool) × (Y → I × Bool) =>
      |h (z.1 p.1).1 (z.2 p.2).1 - h' (z.1 p.1).1 (z.2 p.2).1|)
      ((Measure.pi fun _ => twoCopies).prod (Measure.pi fun _ => twoCopies)) := by
    intro p
    refine Integrable.of_bound ?_ (Mh + Mh) (ae_of_all _ fun z => ?_)
    · exact (hdm.comp (by fun_prop : Measurable fun z : (X → I × Bool) × (Y → I × Bool) =>
        ((z.1 p.1).1, (z.2 p.2).1))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_abs]
      exact (abs_sub _ _).trans (add_le_add (hh _ _) (hh' _ _))
  unfold tBi
  rw [← integral_sub (hint h hhm hh) (hint h' hh'm hh')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ z, |∏ p ∈ E, lift S (fun x y => A x y * h x y) (z.1 p.1) (z.2 p.2) -
        ∏ p ∈ E, lift S (fun x y => A x y * h' x y) (z.1 p.1) (z.2 p.2)|
        ∂((Measure.pi fun _ => twoCopies).prod (Measure.pi fun _ => twoCopies))
      ≤ ∫ z, M ^ E.card * ∑ p ∈ E, MA * |h (z.1 p.1).1 (z.2 p.2).1 - h' (z.1 p.1).1 (z.2 p.2).1|
        ∂((Measure.pi fun _ => twoCopies).prod (Measure.pi fun _ => twoCopies)) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) ?_
          (ae_of_all _ fun z => ?_)
        · exact (integrable_finsetSum _ fun p _ => (hedge p).const_mul MA).const_mul _
        · refine (abs_prod_sub_prod_le E _ _ hM1 (fun p _ => hbd h hh _ _)
            (fun p _ => hbd h' hh' _ _)).trans ?_
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) (by positivity)
          simp only [lift]
          rw [show S (z.1 p.1).1 (z.2 p.2).1 + sgnB (z.1 p.1).2 * sgnB (z.2 p.2).2 *
              (A (z.1 p.1).1 (z.2 p.2).1 * h (z.1 p.1).1 (z.2 p.2).1) -
              (S (z.1 p.1).1 (z.2 p.2).1 + sgnB (z.1 p.1).2 * sgnB (z.2 p.2).2 *
              (A (z.1 p.1).1 (z.2 p.2).1 * h' (z.1 p.1).1 (z.2 p.2).1)) =
              sgnB (z.1 p.1).2 * sgnB (z.2 p.2).2 * A (z.1 p.1).1 (z.2 p.2).1 *
              (h (z.1 p.1).1 (z.2 p.2).1 - h' (z.1 p.1).1 (z.2 p.2).1) by ring]
          rw [abs_mul, abs_mul, abs_mul, abs_sgnB, abs_sgnB, one_mul, one_mul]
          exact mul_le_mul_of_nonneg_right (hMA _ _) (abs_nonneg _)
    _ = M ^ E.card * (MA * E.card) *
        ∫ w : I × I, |h w.1 w.2 - h' w.1 w.2| ∂((volume : Measure I).prod volume) := by
        rw [integral_const_mul, integral_finsetSum _ fun p _ => (hedge p).const_mul MA]
        simp_rw [integral_const_mul]
        simp_rw [integral_edge_marginal (fun x y => |h x y - h' x y|) hdm]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The degree of a vertex of `X ⊕ Y` in an edge set `G ⊆ X × Y`. -/
def bdeg [DecidableEq X] [DecidableEq Y] (G : Finset (X × Y)) : X ⊕ Y → ℕ
  | .inl x => (G.filter (fun p => p.1 = x)).card
  | .inr y => (G.filter (fun p => p.2 = y)).card

lemma prod_sgn_eq [DecidableEq X] [DecidableEq Y] (G : Finset (X × Y)) (τ : X ⊕ Y → Bool) :
    ∏ p ∈ G, sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) =
      ∏ z, sgnB (τ z) ^ bdeg G z := by
  rw [Finset.prod_mul_distrib, Fintype.prod_sum_type]
  congr 1
  · rw [← Finset.prod_fiberwise G (fun p => p.1)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.prod_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.prod_const]
    rfl
  · rw [← Finset.prod_fiberwise G (fun p => p.2)]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [Finset.prod_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.prod_const]
    rfl

/-- The character sum `𝔼_τ ∏_{(u,v) ∈ G} τ_u τ_v`. -/
lemma charSum_eq [DecidableEq X] [DecidableEq Y] (G : Finset (X × Y)) :
    ∑ τ : X ⊕ Y → Bool, (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) *
      ∏ p ∈ G, sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) =
    (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) * ∏ z, (1 + (-1 : ℝ) ^ bdeg G z) := by
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [prod_sgn_eq]
  have h := Fintype.prod_sum (fun (z : X ⊕ Y) (b : Bool) => sgnB b ^ bdeg G z)
  refine (Eq.trans ?_ h.symm).trans ?_
  · rfl
  · refine Finset.prod_congr rfl fun z _ => ?_
    rw [Fintype.sum_bool]
    simp [sgnB, add_comm]

lemma charSum_nonneg [DecidableEq X] [DecidableEq Y] (G : Finset (X × Y)) :
    0 ≤ ∑ τ : X ⊕ Y → Bool, (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) *
      ∏ p ∈ G, sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) := by
  rw [charSum_eq]
  refine mul_nonneg (by positivity) (Finset.prod_nonneg fun z _ => ?_)
  rcases neg_one_pow_eq_or ℝ (bdeg G z) with h | h <;> rw [h] <;> norm_num

lemma charSum_even [DecidableEq X] [DecidableEq Y] (G : Finset (X × Y))
    (hG : ∀ z, Even (bdeg G z)) :
    ∑ τ : X ⊕ Y → Bool, (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) *
      ∏ p ∈ G, sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) = 1 := by
  rw [charSum_eq]
  rw [Finset.prod_congr rfl (fun z _ => by rw [(hG z).neg_one_pow]), Finset.prod_const, Finset.card_univ, ← mul_pow]
  norm_num

/-- The even-subgraph lower bound: `Φ(K_C) ≥ Φ(S) + Φ(C)` when `0 ≤ C ≤ S` and `E` has a nonempty
edge set all of whose degrees are even. -/
lemma tBi_lift_even_lower [DecidableEq X] [DecidableEq Y] (E : Finset (X × Y))
    (S Cc : I → I → ℝ) (hS : IsKernel S) (hC : IsKernel Cc) (hC0 : ∀ x y, 0 ≤ Cc x y)
    (hCS : ∀ x y, Cc x y ≤ S x y) (F : Finset (X × Y)) (hF : F ⊆ E) (hFne : F.Nonempty)
    (heven : ∀ z, Even (bdeg F z)) :
    tb E S + tb E Cc ≤ tBi twoCopies E (lift S Cc) := by
  obtain ⟨MS, hMS⟩ := hS.2
  obtain ⟨MC, hMC⟩ := hC.2
  rw [tBi_lift_eq_avg E S Cc hS.1 hC.1 hMS hMC]
  let a : Finset (X × Y) → ℝ := fun G => ∫ w : X ⊕ Y → I,
    (∏ p ∈ G, Cc (w (.inl p.1)) (w (.inr p.2))) * ∏ p ∈ E \ G, S (w (.inl p.1)) (w (.inr p.2))
      ∂(Measure.pi fun _ => (volume : Measure I))
  have hpm : ∀ p : X × Y, Measurable fun w : X ⊕ Y → I => (w (Sum.inl p.1), w (Sum.inr p.2)) :=
    fun p => (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hSm : ∀ p : X × Y, Measurable fun w : X ⊕ Y → I => S (w (.inl p.1)) (w (.inr p.2)) :=
    fun p => hS.1.comp (hpm p)
  have hCm : ∀ p : X × Y, Measurable fun w : X ⊕ Y → I => Cc (w (.inl p.1)) (w (.inr p.2)) :=
    fun p => hC.1.comp (hpm p)
  have hint : ∀ G : Finset (X × Y), Integrable (fun w : X ⊕ Y → I =>
      (∏ p ∈ G, Cc (w (.inl p.1)) (w (.inr p.2))) * ∏ p ∈ E \ G, S (w (.inl p.1)) (w (.inr p.2)))
      (Measure.pi fun _ => (volume : Measure I)) := by
    intro G
    refine Integrable.of_bound ((Finset.measurable_prod _ fun p _ => hCm p).mul
      (Finset.measurable_prod _ fun p _ => hSm p)).aestronglyMeasurable
      (MC ^ G.card * MS ^ (E \ G).card) (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const,
      ← Finset.prod_const]
    exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p _ => hMC _ _)
      (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p _ => hMS _ _)
      (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      (Finset.prod_nonneg fun _ _ => (abs_nonneg _).trans (hMC (Classical.arbitrary I)
        (Classical.arbitrary I)))
  have hexp : ∀ τ : X ⊕ Y → Bool, tBiDec volume E (fun p x y =>
      S x y + sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2)) * Cc x y) =
      ∑ G ∈ E.powerset, (∏ p ∈ G, sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2))) * a G := by
    intro τ
    rw [tBiDec_eq_pi]
    have : ∀ w : X ⊕ Y → I, ∏ p ∈ E, (S (w (.inl p.1)) (w (.inr p.2)) + sgnB (τ (.inl p.1)) *
        sgnB (τ (.inr p.2)) * Cc (w (.inl p.1)) (w (.inr p.2))) =
        ∑ G ∈ E.powerset, (∏ p ∈ G, sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2))) *
          ((∏ p ∈ G, Cc (w (.inl p.1)) (w (.inr p.2))) *
            ∏ p ∈ E \ G, S (w (.inl p.1)) (w (.inr p.2))) := by
      intro w
      simp_rw [add_comm (S _ _)]
      rw [Finset.prod_add]
      refine Finset.sum_congr rfl fun G _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    simp_rw [this]
    rw [integral_finsetSum _ fun G _ => (hint G).const_mul _]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [integral_const_mul]
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have ha0 : ∀ G, 0 ≤ a G := fun G => integral_nonneg fun w =>
    mul_nonneg (Finset.prod_nonneg fun p _ => hC0 _ _)
      (Finset.prod_nonneg fun p _ => (hC0 _ _).trans (hCS _ _))
  have hterm : ∀ G ∈ E.powerset, 0 ≤ (∑ τ : X ⊕ Y → Bool, (2⁻¹ : ℝ) ^ Fintype.card (X ⊕ Y) *
      ∏ p ∈ G, sgnB (τ (.inl p.1)) * sgnB (τ (.inr p.2))) * a G :=
    fun G _ => mul_nonneg (charSum_nonneg G) (ha0 G)
  have hsub : ({∅, F} : Finset (Finset (X × Y))) ⊆ E.powerset := by
    intro G hG
    simp only [Finset.mem_insert, Finset.mem_singleton] at hG
    rcases hG with rfl | rfl
    · exact Finset.empty_mem_powerset _
    · exact Finset.mem_powerset.2 hF
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun G hG _ => hterm G hG)
  rw [Finset.sum_pair (Ne.symm hFne.ne_empty)]
  have h0 : ∀ z, Even (bdeg (∅ : Finset (X × Y)) z) := by
    intro z; cases z <;> simp [bdeg]
  rw [charSum_even _ h0, charSum_even F heven, one_mul, one_mul]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [a, Finset.prod_empty, one_mul, Finset.sdiff_empty]
    rw [show tb E S = tBi volume E S from rfl, tBi_eq_pi]
  · rw [show tb E Cc = tBi volume E Cc from rfl, tBi_eq_pi]
    refine integral_mono_of_nonneg (ae_of_all _ fun w => Finset.prod_nonneg fun p _ => hC0 _ _)
      (hint F) (ae_of_all _ fun w => ?_)
    simp only
    rw [← Finset.prod_sdiff hF, mul_comm]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun p _ => hC0 _ _)
      (fun p _ => hCS _ _)) (Finset.prod_nonneg fun p _ => hC0 _ _)

omit [Fintype X] [Fintype Y] in
lemma bipGraph_adj_iff (E : Finset (X × Y)) (a b : X ⊕ Y) :
    (bipGraph E).Adj a b ↔ ∃ x y, (x, y) ∈ E ∧ ((a = .inl x ∧ b = .inr y) ∨
      (a = .inr y ∧ b = .inl x)) := by
  simp only [bipGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨x, y, rfl, rfl, h⟩ | ⟨x, y, rfl, rfl, h⟩⟩
    · exact ⟨x, y, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨x, y, h, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨x, y, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨by simp, Or.inl ⟨x, y, rfl, rfl, h⟩⟩
    · exact ⟨by simp, Or.inr ⟨x, y, rfl, rfl, h⟩⟩

/-- A cycle of `H` gives a nonempty edge set all of whose degrees are even. -/
lemma exists_even_of_not_acyclic [DecidableEq X] [DecidableEq Y] (E : Finset (X × Y))
    (hcyc : ¬ (bipGraph E).IsAcyclic) :
    ∃ F ⊆ E, F.Nonempty ∧ ∀ z, Even (bdeg F z) := by
  classical
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hcyc
  obtain ⟨v, c, hc⟩ := hcyc
  let F := E.filter fun p => s(Sum.inl p.1, Sum.inr p.2) ∈ c.edges
  refine ⟨F, Finset.filter_subset _ _, ?_, ?_⟩
  · have hlen := hc.three_le_length
    obtain ⟨e, he⟩ : ∃ e, e ∈ c.edges := by
      rcases hl : c.edges with _ | ⟨e, l⟩
      · have := SimpleGraph.Walk.length_edges c
        rw [hl] at this; simp at this; omega
      · exact ⟨e, by simp⟩
    induction e using Sym2.ind with
    | h a b =>
      have hab := c.adj_of_mem_edges he
      obtain ⟨x, y, hxy, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (bipGraph_adj_iff E a b).1 hab
      · exact ⟨(x, y), Finset.mem_filter.2 ⟨hxy, he⟩⟩
      · exact ⟨(x, y), Finset.mem_filter.2 ⟨hxy, by rw [Sym2.eq_swap]; exact he⟩⟩
  · have ht := hc.isTrail
    have hcount : ∀ w : X ⊕ Y, Even (c.edges.countP fun e => w ∈ e) := fun w =>
      (ht.even_countP_edges_iff w).2 fun h => absurd rfl h
    have hcard : ∀ w : X ⊕ Y, (ht.edgesFinset.filter fun e => w ∈ e).card =
        c.edges.countP fun e => w ∈ e := by
      intro w
      simp [Finset.card, Finset.filter, List.countP_eq_length_filter]
    intro z
    rcases z with x | y
    · show Even (F.filter fun p => p.1 = x).card
      rw [← Finset.card_image_of_injOn (f := fun p : X × Y => s(Sum.inl p.1, Sum.inr p.2))]
      · convert hcount (.inl x) using 1
        rw [← hcard]
        congr 1
        ext e
        simp only [Finset.mem_image, Finset.mem_filter, F, Finset.mem_mk, Multiset.mem_coe]
        constructor
        · rintro ⟨p, ⟨⟨_, hp⟩, rfl⟩, rfl⟩
          exact ⟨hp, Sym2.mem_mk_left _ _⟩
        · rintro ⟨he, hx⟩
          obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hx
          have hadj := c.adj_of_mem_edges he
          obtain ⟨x', y', hxy, ⟨h1, rfl⟩ | ⟨h1, -⟩⟩ := (bipGraph_adj_iff E _ _).1 hadj
          · cases h1
            exact ⟨(_, y'), ⟨⟨hxy, he⟩, rfl⟩, rfl⟩
          · cases h1
      · rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 h
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at h1 h2
        simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
          or_false] at h
        rw [Prod.mk.injEq]
        exact ⟨h.1, h.2⟩
    · show Even (F.filter fun p => p.2 = y).card
      rw [← Finset.card_image_of_injOn (f := fun p : X × Y => s(Sum.inl p.1, Sum.inr p.2))]
      · convert hcount (.inr y) using 1
        rw [← hcard]
        congr 1
        ext e
        simp only [Finset.mem_image, Finset.mem_filter, F, Finset.mem_mk, Multiset.mem_coe]
        constructor
        · rintro ⟨p, ⟨⟨_, hp⟩, rfl⟩, rfl⟩
          exact ⟨hp, Sym2.mem_mk_right _ _⟩
        · rintro ⟨he, hy⟩
          obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hy
          have hadj := c.adj_of_mem_edges he
          obtain ⟨x', y', hxy, ⟨h1, -⟩ | ⟨h1, rfl⟩⟩ := (bipGraph_adj_iff E _ _).1 hadj
          · cases h1
          · cases h1
            exact ⟨(x', _), ⟨⟨hxy, by rw [Sym2.eq_swap]; exact he⟩, rfl⟩, Sym2.eq_swap⟩
      · rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 h
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at h1 h2
        simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
          or_false] at h
        rw [Prod.mk.injEq]
        exact ⟨h.1, h.2⟩

lemma integral_abs_indicator_sub (U V : Set (I × I)) (hU : MeasurableSet U)
    (hV : MeasurableSet V) :
    ∫ w : I × I, |U.indicator (fun _ => (1 : ℝ)) (w.1, w.2) -
      V.indicator (fun _ => (1 : ℝ)) (w.1, w.2)| ∂((volume : Measure I).prod volume) =
      ((volume : Measure I).prod volume).real (symmDiff U V) := by
  have : (fun w : I × I => |U.indicator (fun _ => (1 : ℝ)) (w.1, w.2) -
      V.indicator (fun _ => (1 : ℝ)) (w.1, w.2)|) = (symmDiff U V).indicator 1 := by
    funext w
    by_cases h1 : w ∈ U <;> by_cases h2 : w ∈ V <;>
      simp [Set.indicator, h1, h2, Set.mem_symmDiff]
  rw [this, integral_indicator_one (hU.symmDiff hV)]

lemma eq_zero_of_abs_le_mul {r K : ℝ} (hK : 0 ≤ K) (h : ∀ δ > 0, |r| ≤ K * δ) : r = 0 := by
  by_contra hr
  have hpos : 0 < |r| := abs_pos.2 hr
  have := h (|r| / (2 * (K + 1))) (by positivity)
  have h2 : K * (|r| / (2 * (K + 1))) < |r| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

theorem lemma_4_6_core (E : Finset (X × Y))
    (hE : IsWeaklyNorming E) (hcyc : ¬ (bipGraph E).IsAcyclic) (S A : I → I → ℝ)
    (hS : IsKernel S) (hA : IsKernel A) (hSA : ∀ x y, |A x y| ≤ S x y)
    (hplus : tb E (fun x y => S x y + A x y) = tb E S)
    (hminus : tb E (fun x y => S x y - A x y) = tb E S) :
    AEEq volume A (fun _ _ => 0) := by
  classical
  obtain ⟨F, hFE, hFne, hFeven⟩ := exists_even_of_not_acyclic E hcyc
  have hm : 0 < E.card := Finset.card_pos.2 (hFne.mono hFE)
  set c := tb E S with hc
  -- the sign of `A` as a difference of indicators
  let Tp : Set (I × I) := {w | 0 < A w.1 w.2}
  let Tn : Set (I × I) := {w | A w.1 w.2 < 0}
  have hTp : MeasurableSet Tp := measurableSet_lt measurable_const hA.1
  have hTn : MeasurableSet Tn := measurableSet_lt hA.1 measurable_const
  let ind : Set (I × I) → I → I → ℝ := fun U x y => U.indicator (fun _ => (1 : ℝ)) (x, y)
  have hindm : ∀ U, MeasurableSet U → Measurable (Function.uncurry (ind U)) := by
    intro U hU
    exact (measurable_const.indicator hU : Measurable (U.indicator fun _ => (1 : ℝ)))
  let sgnA : I → I → ℝ := fun x y => ind Tp x y - ind Tn x y
  have hsgn : (fun x y => A x y * sgnA x y) = fun x y => |A x y| := by
    funext x y
    simp only [sgnA, ind, Set.indicator, Tp, Tn, Set.mem_setOf_eq]
    rcases lt_trichotomy (A x y) 0 with h | h | h
    · rw [if_neg (not_lt.2 h.le), if_pos h, abs_of_neg h]; ring
    · rw [h]; simp
    · rw [if_pos h, if_neg (not_lt.2 h.le), abs_of_pos h]; ring
  have hbd : ∀ U V : Set (I × I), ∀ x y, |ind U x y - ind V x y| ≤ 1 := by
    intro U V x y
    simp only [ind, Set.indicator]
    split_ifs <;> norm_num
  obtain ⟨Λ, hΛ, hlip⟩ := tBi_lift_lipschitz E S A hS hA (Mh := 1) zero_le_one
  have hkey : ∀ δ > 0, |tBi twoCopies E (lift S (fun x y => A x y * sgnA x y)) - c| ≤
      (2 * Λ) * δ := by
    intro δ hδ
    obtain ⟨tp, htpm, htpg, htp⟩ := exists_gridRep_approx hTp (ENNReal.ofReal_pos.2 hδ)
    obtain ⟨tn, htnm, htng, htn⟩ := exists_gridRep_approx hTn (ENNReal.ofReal_pos.2 hδ)
    let hε : I → I → ℝ := fun x y => ind tp x y - ind tn x y
    have hg : GridRep hε := gridRep_op htpg htng (fun a b => a - b)
    obtain ⟨Q, _, a, r, s, hr, hs, hcomb⟩ := gridRep_comb hg
    have hΨ : tBi twoCopies E (lift S (fun x y => A x y * hε x y)) = c := by
      refine Eq.trans ?_ (tBi_lift_comb E hm hE S A hS hA hSA hplus hminus a r s hr hs)
      congr 2
      funext x y
      rw [hcomb]
    have hl := hlip sgnA hε ((hindm Tp hTp).sub (hindm Tn hTn))
      ((hindm tp htpm).sub (hindm tn htnm)) (hbd Tp Tn) (hbd tp tn)
    rw [hΨ] at hl
    refine hl.trans ?_
    have hint : ∫ w : I × I, |sgnA w.1 w.2 - hε w.1 w.2| ∂((volume : Measure I).prod volume) ≤
        2 * δ := by
      have hle : ∀ w : I × I, |sgnA w.1 w.2 - hε w.1 w.2| ≤
          |ind Tp w.1 w.2 - ind tp w.1 w.2| + |ind Tn w.1 w.2 - ind tn w.1 w.2| := by
        intro w
        simp only [sgnA, hε]
        rw [show ind Tp w.1 w.2 - ind Tn w.1 w.2 - (ind tp w.1 w.2 - ind tn w.1 w.2) =
          (ind Tp w.1 w.2 - ind tp w.1 w.2) - (ind Tn w.1 w.2 - ind tn w.1 w.2) by ring]
        exact abs_sub _ _
      have hi1 : Integrable (fun w : I × I => |ind Tp w.1 w.2 - ind tp w.1 w.2|)
          ((volume : Measure I).prod volume) :=
        Integrable.of_bound (((hindm Tp hTp).sub (hindm tp htpm)).abs.aestronglyMeasurable) 1
          (ae_of_all _ fun w => by rw [Real.norm_eq_abs, abs_abs]; exact hbd _ _ _ _)
      have hi2 : Integrable (fun w : I × I => |ind Tn w.1 w.2 - ind tn w.1 w.2|)
          ((volume : Measure I).prod volume) :=
        Integrable.of_bound (((hindm Tn hTn).sub (hindm tn htnm)).abs.aestronglyMeasurable) 1
          (ae_of_all _ fun w => by rw [Real.norm_eq_abs, abs_abs]; exact hbd _ _ _ _)
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hi1.add hi2)
        (ae_of_all _ hle)).trans ?_
      simp only [Pi.add_apply]
      rw [integral_add hi1 hi2]
      simp only [ind]
      rw [integral_abs_indicator_sub _ _ hTp htpm, integral_abs_indicator_sub _ _ hTn htnm,
        symmDiff_comm Tp, symmDiff_comm Tn]
      have e1 : ((volume : Measure I).prod volume).real (symmDiff tp Tp) ≤ δ := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal hδ.le htp.le
      have e2 : ((volume : Measure I).prod volume).real (symmDiff tn Tn) ≤ δ := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal hδ.le htn.le
      linarith
    calc Λ * ∫ w : I × I, |sgnA w.1 w.2 - hε w.1 w.2| ∂((volume : Measure I).prod volume)
        ≤ Λ * (2 * δ) := mul_le_mul_of_nonneg_left hint hΛ
      _ = 2 * Λ * δ := by ring
  have hΨA : tBi twoCopies E (lift S (fun x y => |A x y|)) = c := by
    rw [← hsgn]
    exact sub_eq_zero.1 (eq_zero_of_abs_le_mul (by positivity) hkey)
  have hlow := tBi_lift_even_lower E S (fun x y => |A x y|) hS
    ⟨hA.1.abs, by obtain ⟨M, hM⟩ := hA.2; exact ⟨M, fun x y => by rw [abs_abs]; exact hM x y⟩⟩
    (fun x y => abs_nonneg _) hSA F hFE hFne hFeven
  rw [hΨA] at hlow
  have h0 : tb E (fun x y => |A x y|) = 0 :=
    le_antisymm (by linarith) (tb_nonneg E _ fun x y => abs_nonneg _)
  refine hE.2.2 A hA ?_
  unfold rNorm
  rw [h0, Real.zero_rpow]
  have : (0 : ℝ) < E.card := by exact_mod_cast hm
  positivity

end Lift

end Section4Aux

end NieWeiOrientedSidorenko
