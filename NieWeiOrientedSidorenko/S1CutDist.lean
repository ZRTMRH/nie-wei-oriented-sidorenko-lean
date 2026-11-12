import NieWeiOrientedSidorenko.Section1Aux
import NieWeiOrientedSidorenko.S1CutDistB

/-!
# Theorem 1.4 and B4(i)

Proofs of `thm_1_4` and `k23_weaklyNorming_stepForcing_not_norming` of
`NieWeiOrientedSidorenko/Section1.lean`, as `thm_1_4_proof` and
`k23_weaklyNorming_stepForcing_not_norming_proof`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace S1CutDist

/-! ## Step forcing -/

section StepForcing

variable {V : Type u} [Fintype V]

lemma tU_eq_tb (H : SimpleGraph V) (s : V → Prop) [DecidablePred s] (hbip : IsBipartition H s)
    {K : I → I → ℝ} (hK : ∀ x y, K x y = K y x) : tU H K = tb (sideEdges H s) K := by
  have hD := Section1Aux.sideOG_underlying H s hbip
  have h1 := Section1Aux.tU_eq_t H (Section1Aux.sideOG H s) hD hK
  have h2 := Section1Aux.t_eq_tb_side (Section1Aux.sideOG H s) s (fun u v h => h.2) K
  rw [hD] at h2
  rw [h1, h2]

lemma not_acyclic_bip (H : SimpleGraph V) (s : V → Prop) [DecidablePred s]
    (hbip : IsBipartition H s) (hcyc : ¬ H.IsAcyclic) :
    ¬ (bipGraph (sideEdges H s)).IsAcyclic := by
  obtain ⟨f, hf⟩ := Section1Aux.bipGraph_hom_inj H s hbip
  exact fun h => hcyc (h.comap f hf)

lemma aeEq_trans {U V W : I → I → ℝ} (h1 : AEEq volume U V) (h2 : AEEq volume V W) :
    AEEq volume U W := by
  unfold AEEq at *
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1, hp2]

lemma aeEq_symm {U V : I → I → ℝ} (h : AEEq volume U V) : AEEq volume V U := by
  unfold AEEq at *
  filter_upwards [h] with p hp
  rw [hp]

/-- Step forcing from weak norming with a cycle (hence strict convexity, Theorem 1.6) and step
Sidorenko: with `Q = W^𝒫` and
`M = (W + Q)/2`, `M^𝒫 = Q`, so `t(Q) ≤ t(M) < (t(W) + t(Q))/2`. -/
lemma stepForcing_of_wn (H : SimpleGraph V) (s : V → Prop) [DecidablePred s]
    (hbip : IsBipartition H s) (hWN : IsWeaklyNorming (sideEdges H s)) (hcyc : ¬ H.IsAcyclic)
    (hSS : IsStepSidorenko H) : IsStepForcing H := by
  intro U hU P hne
  obtain ⟨hS, hae⟩ := Section1Aux.symmVersion_spec hU
  set S := Section1Aux.symmVersion U with hSdef
  rw [Section1Aux.stepAvg_congr_ae P hae, Section1Aux.tU_congr_ae H hae]
  have hne' : ¬ AEEq volume S (stepAvg P S) := by
    intro h
    apply hne
    rw [Section1Aux.stepAvg_congr_ae P hae]
    exact aeEq_trans hae h
  set Q := stepAvg P S with hQdef
  have hQd : IsDigraphon Q := isDigraphon_stepAvg P hS.1
  have hQs : ∀ x y, Q x y = Q y x := stepAvg_symm P hS.2
  have hSk := Section1Aux.isKernel_of_isDigraphon hS.1
  have hQk := Section1Aux.isKernel_of_isDigraphon hQd
  set M : I → I → ℝ := fun x y => (1 / 2 : ℝ) * S x y + (1 - 1 / 2) * Q x y with hMdef
  have hMQ : stepAvg P M = Q := by
    rw [hMdef, stepAvg_lin P hSk hQk, hQdef, stepAvg_stepAvg]
    funext x y; ring
  have hMs : ∀ x y, M x y = M y x := fun x y => by
    simp only [hMdef]; rw [hS.2, hQs]
  have hMg : IsGraphon volume M := by
    refine ⟨⟨(Section1Aux.isKernel_lin hSk hQk _ _).1, fun x y => ?_⟩,
      Eventually.of_forall fun p => hMs p.1 p.2⟩
    have := hS.1.2 x y; have := hQd.2 x y
    simp only [hMdef, mem_Icc] at *
    constructor <;> nlinarith
  have h1 := hSS M hMg P
  rw [hMQ] at h1
  have hcycE := not_acyclic_bip H s hbip hcyc
  have hE : 0 < (sideEdges H s).card :=
    lt_of_lt_of_le (by norm_num) (Section1Aux.card_ge_three_of_cycle _ hcycE)
  have h2 := Section1Aux.thm16_forward _ hE hWN hcycE S Q hSk hQk (fun x y => (hS.1.2 x y).1)
    (fun x y => (hQd.2 x y).1) hne' (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [tU_eq_tb H s hbip hQs, tU_eq_tb H s hbip hMs] at h1
  rw [tU_eq_tb H s hbip hQs, tU_eq_tb H s hbip hS.2]
  have : tb (sideEdges H s) M = tb (sideEdges H s)
      (fun x y => 1 / 2 * S x y + (1 - 1 / 2) * Q x y) := rfl
  linarith

/-- The step forcing half of Theorem 1.4. -/
lemma isStepForcing_of_wnGraph (hA2 : DGHRRCor324Hyp.{u}) (H : SimpleGraph V)
    (hH : IsWeaklyNormingGraph H) (hcyc : ¬ H.IsAcyclic) : IsStepForcing H := by
  have hSS : IsStepSidorenko H :=
    Section1Aux.stepSid_of_symm (hA2 V H (Section1Aux.seminorm_of_wnGraph hH))
  obtain ⟨s, hbip, hwn⟩ := hH
  let _ := Classical.decPred s
  exact stepForcing_of_wn H s hbip hwn hcyc hSS

end StepForcing

/-! ## `K_{2,3}` is weakly norming -/

section K23

/-- Nonnegative bounded measurable kernels. -/
def NK (f : I → I → ℝ) : Prop := IsKernel f ∧ ∀ x y, 0 ≤ f x y

/-- The measure of `t_bi(K_{2,3}, ·)`. -/
noncomputable abbrev ρ23 : Measure ((Fin 2 → I) × (Fin 3 → I)) :=
  (Measure.pi fun _ : Fin 2 => (volume : Measure I)).prod
    (Measure.pi fun _ : Fin 3 => (volume : Measure I))

/-- `G(f, g)(a, b) = ∫ f(a, y) g(b, y) dy`. -/
noncomputable def Gk (f g : I → I → ℝ) (a b : I) : ℝ := ∫ y, f a y * g b y

/-- `F_f(y₀, y₁, y₂) = ∫ f(a, y₀) f(a, y₁) f(a, y₂) da`. -/
noncomputable def Fm (f : I → I → ℝ) (y : Fin 3 → I) : ℝ := ∫ a, ∏ j, f a (y j)

/-- The density of `K_{2,3}` with the first left vertex decorated by `f`, the second by `g`. -/
noncomputable def Gen (f g : I → I → ℝ) : ℝ :=
  ∫ z, ∏ j : Fin 3, (f (z.1 0) (z.2 j) * g (z.1 1) (z.2 j)) ∂ρ23

lemma nk_bound {f : I → I → ℝ} (hf : NK f) : ∃ M, 0 ≤ M ∧ ∀ x y, f x y ≤ M := by
  obtain ⟨⟨_, M, hM⟩, h0⟩ := hf
  refine ⟨max M 0, le_max_right _ _, fun x y => ?_⟩
  have := hM x y; rw [abs_of_nonneg (h0 x y)] at this
  exact this.trans (le_max_left _ _)

lemma tb_univ_eq_Gen (f : I → I → ℝ) :
    tb (Finset.univ : Finset (Fin 2 × Fin 3)) f = Gen f f := by
  unfold tb tBi Gen
  congr 1
  funext z
  rw [Fintype.prod_prod_type, Fin.prod_univ_two, ← Finset.prod_mul_distrib]

lemma measurable_Gen_integrand {f g : I → I → ℝ} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : (Fin 2 → I) × (Fin 3 → I) =>
      ∏ j : Fin 3, (f (z.1 0) (z.2 j) * g (z.1 1) (z.2 j))) := by
  refine Finset.measurable_prod _ fun j _ => Measurable.mul ?_ ?_
  · exact meas_app hf ((measurable_pi_apply 0).comp measurable_fst)
      ((measurable_pi_apply j).comp measurable_snd)
  · exact meas_app hg ((measurable_pi_apply 1).comp measurable_fst)
      ((measurable_pi_apply j).comp measurable_snd)

lemma integrable_Gen_integrand {f g : I → I → ℝ} (hf : NK f) (hg : NK g) :
    Integrable (fun z : (Fin 2 → I) × (Fin 3 → I) =>
      ∏ j : Fin 3, (f (z.1 0) (z.2 j) * g (z.1 1) (z.2 j))) ρ23 := by
  obtain ⟨M, hM0, hM⟩ := nk_bound hf
  obtain ⟨N, hN0, hN⟩ := nk_bound hg
  refine integrable_bdd (measurable_Gen_integrand hf.1.1 hg.1.1) ((M * N) ^ 3) fun z => ?_
  rw [Finset.abs_prod, ← Fin.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => by
    rw [abs_mul, abs_of_nonneg (hf.2 _ _), abs_of_nonneg (hg.2 _ _)]
    exact mul_le_mul (hM _ _) (hN _ _) (hg.2 _ _) hM0

lemma Gen_eq_Gk (f g : I → I → ℝ) (hf : NK f) (hg : NK g) :
    Gen f g = ∫ q : I × I, Gk f g q.1 q.2 ^ 3 ∂((volume : Measure I).prod volume) := by
  unfold Gen
  rw [integral_prod _ (integrable_Gen_integrand hf hg)]
  have hin : ∀ x : Fin 2 → I, ∫ y : Fin 3 → I, ∏ j : Fin 3, (f (x 0) (y j) * g (x 1) (y j))
      ∂(Measure.pi fun _ : Fin 3 => (volume : Measure I)) = Gk f g (x 0) (x 1) ^ 3 := by
    intro x
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin 3) (t : I) => f (x 0) t * g (x 1) t)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  simp_rw [hin]
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure I))
  rw [← hmp.integral_comp']
  rfl

lemma Gen_eq_Fm (f g : I → I → ℝ) (hf : NK f) (hg : NK g) :
    Gen f g = ∫ y : Fin 3 → I, Fm f y * Fm g y
      ∂(Measure.pi fun _ : Fin 3 => (volume : Measure I)) := by
  unfold Gen
  rw [integral_prod_symm _ (integrable_Gen_integrand hf hg)]
  congr 1
  funext y
  simp only
  simp_rw [Finset.prod_mul_distrib]
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure I))
  have : ∫ x : Fin 2 → I, (∏ j : Fin 3, f (x 0) (y j)) * ∏ j : Fin 3, g (x 1) (y j)
      ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) =
      ∫ q : I × I, (∏ j : Fin 3, f q.1 (y j)) * ∏ j : Fin 3, g q.2 (y j)
        ∂((volume : Measure I).prod volume) := by
    rw [← hmp.integral_comp']; rfl
  rw [this, integral_prod_mul (fun a => ∏ j : Fin 3, f a (y j)) (fun b => ∏ j : Fin 3, g b (y j))]
  rfl

end K23

/-- Minkowski's inequality in `L³` on a probability space, for nonnegative bounded measurable
functions. -/
lemma mink3 {β : Type*} [MeasurableSpace β] {μ : Measure β} [IsProbabilityMeasure μ]
    {φ ψ : β → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hψ0 : ∀ x, 0 ≤ ψ x) {C D : ℝ} (hφC : ∀ x, φ x ≤ C) (hψD : ∀ x, ψ x ≤ D) :
    (∫ x, (φ x + ψ x) ^ 3 ∂μ) ^ ((1 : ℝ) / 3) ≤
      (∫ x, φ x ^ 3 ∂μ) ^ ((1 : ℝ) / 3) + (∫ x, ψ x ^ 3 ∂μ) ^ ((1 : ℝ) / 3) := by
  have key : ∀ h : β → ℝ, Measurable h → (∀ x, 0 ≤ h x) → ∀ C : ℝ, (∀ x, h x ≤ C) →
      eLpNorm h 3 μ = ENNReal.ofReal ((∫ x, h x ^ 3 ∂μ) ^ ((1 : ℝ) / 3)) := by
    intro h hm h0 C hC
    have hmem : MemLp h 3 μ := MemLp.of_bound hm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (h0 x)]; exact hC x)
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    congr 2
    · congr 1
      funext x
      rw [Real.norm_of_nonneg (h0 x)]
      norm_num
    · norm_num
  have hnn : ∀ h : β → ℝ, (∀ x, 0 ≤ h x) → 0 ≤ (∫ x, h x ^ 3 ∂μ) ^ ((1 : ℝ) / 3) :=
    fun h h0 => Real.rpow_nonneg (integral_nonneg fun x => pow_nonneg (h0 x) 3) _
  have h1 := eLpNorm_add_le (f := φ) (g := ψ) (μ := μ) (p := 3) (by norm_num)
  rw [key _ (hφ.add hψ) (fun x => add_nonneg (hφ0 x) (hψ0 x)) (C + D)
      (fun x => add_le_add (hφC x) (hψD x)), key φ hφ hφ0 C hφC, key ψ hψ hψ0 D hψD,
    ← ENNReal.ofReal_add (hnn φ hφ0) (hnn ψ hψ0)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hnn φ hφ0) (hnn ψ hψ0))).mp h1

section K23b

lemma integrable_row {f g : I → I → ℝ} (hf : NK f) (hg : NK g) (a b : I) :
    Integrable (fun y => f a y * g b y) := by
  obtain ⟨M, hM0, hM⟩ := nk_bound hf
  obtain ⟨N, hN0, hN⟩ := nk_bound hg
  refine integrable_bdd ((meas_app hf.1.1 measurable_const measurable_id).mul
    (meas_app hg.1.1 measurable_const measurable_id)) (M * N) fun y => ?_
  rw [abs_mul, abs_of_nonneg (hf.2 _ _), abs_of_nonneg (hg.2 _ _)]
  exact mul_le_mul (hM _ _) (hN _ _) (hg.2 _ _) hM0

lemma measurable_Gk {f g : I → I → ℝ} (hf : NK f) (hg : NK g) :
    Measurable (fun q : I × I => Gk f g q.1 q.2) := by
  have hm : Measurable (fun r : (I × I) × I => f r.1.1 r.2 * g r.1.2 r.2) :=
    (meas_app hf.1.1 (measurable_fst.comp measurable_fst) measurable_snd).mul
      (meas_app hg.1.1 (measurable_snd.comp measurable_fst) measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure I))).measurable

lemma Gk_nonneg {f g : I → I → ℝ} (hf : NK f) (hg : NK g) (a b : I) : 0 ≤ Gk f g a b :=
  integral_nonneg fun y => mul_nonneg (hf.2 _ _) (hg.2 _ _)

lemma Gk_le {f g : I → I → ℝ} (hf : NK f) (hg : NK g) {M N : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x y, f x y ≤ M) (hN : ∀ x y, g x y ≤ N) (a b : I) : Gk f g a b ≤ M * N := by
  unfold Gk
  calc ∫ y, f a y * g b y ≤ ∫ _y : I, M * N :=
        integral_mono (integrable_row hf hg a b) (integrable_const _)
          fun y => mul_le_mul (hM _ _) (hN _ _) (hg.2 _ _) hM0
    _ = M * N := by simp

lemma Gk_add {f g : I → I → ℝ} (hf : NK f) (hg : NK g) (a b : I) :
    Gk (fun x y => f x y + g x y) (fun x y => f x y + g x y) a b =
      ((Gk f f a b + Gk f g a b) + Gk g f a b) + Gk g g a b := by
  unfold Gk
  have e : (fun y => (f a y + g a y) * (f b y + g b y)) =
      fun y => ((f a y * f b y + f a y * g b y) + g a y * f b y) + g a y * g b y := by
    funext y; ring
  rw [e, integral_add, integral_add, integral_add]
  all_goals first
    | exact integrable_row hf hf a b | exact integrable_row hf hg a b
    | exact integrable_row hg hf a b | exact integrable_row hg hg a b
    | exact (integrable_row hf hf a b).add (integrable_row hf hg a b)
    | exact ((integrable_row hf hf a b).add (integrable_row hf hg a b)).add
        (integrable_row hg hf a b)

lemma measurable_Fm {f : I → I → ℝ} (hf : NK f) :
    Measurable (Fm f) := by
  have hm : Measurable (fun r : I × (Fin 3 → I) => ∏ j, f r.1 (r.2 j)) :=
    Finset.measurable_prod _ fun j _ =>
      meas_app hf.1.1 measurable_fst ((measurable_pi_apply j).comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure I))).measurable

lemma Fm_nonneg {f : I → I → ℝ} (hf : NK f) (y : Fin 3 → I) : 0 ≤ Fm f y :=
  integral_nonneg fun a => Finset.prod_nonneg fun j _ => hf.2 _ _

lemma Fm_le {f : I → I → ℝ} (hf : NK f) {M : ℝ} (hM : ∀ x y, f x y ≤ M)
    (y : Fin 3 → I) : Fm f y ≤ M ^ 3 := by
  unfold Fm
  have hint : Integrable (fun a => ∏ j, f a (y j)) := by
    refine integrable_bdd (Finset.measurable_prod _ fun j _ =>
      meas_app hf.1.1 measurable_id measurable_const) (M ^ 3) fun a => ?_
    rw [Finset.abs_prod, ← Fin.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => by
      rw [abs_of_nonneg (hf.2 _ _)]; exact hM _ _
  calc ∫ a, ∏ j, f a (y j) ≤ ∫ _a : I, M ^ 3 :=
        integral_mono hint (integrable_const _) fun a => by
          rw [← Fin.prod_const]
          exact Finset.prod_le_prod₀ (fun _ _ => hf.2 _ _) fun j _ => hM _ _
    _ = M ^ 3 := by simp

/-- The Cauchy–Schwarz step: `Gen(f, g) ≤ √Gen(f, f) √Gen(g, g)`. -/
lemma Gen_cs {f g : I → I → ℝ} (hf : NK f) (hg : NK g) :
    Gen f g ≤ Gen f f ^ ((1 : ℝ) / 2) * Gen g g ^ ((1 : ℝ) / 2) := by
  obtain ⟨M, hM0, hM⟩ := nk_bound hf
  obtain ⟨N, hN0, hN⟩ := nk_bound hg
  have hmem : ∀ {h : I → I → ℝ} (hh : NK h) {M : ℝ}, 0 ≤ M → (∀ x y, h x y ≤ M) →
      MemLp (Fm h) (ENNReal.ofReal 2) (Measure.pi fun _ : Fin 3 => (volume : Measure I)) :=
    fun hh M hM0 hM => MemLp.of_bound (measurable_Fm hh).aestronglyMeasurable (M ^ 3)
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Fm_nonneg hh y)]; exact Fm_le hh hM y)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun y => Fm_nonneg hf y) (Eventually.of_forall fun y => Fm_nonneg hg y)
    (hmem hf hM0 hM) (hmem hg hN0 hN)
  have e : ∀ h : I → I → ℝ, NK h → ∫ y, Fm h y ^ (2 : ℝ)
      ∂(Measure.pi fun _ : Fin 3 => (volume : Measure I)) = Gen h h := fun h hh => by
    rw [Gen_eq_Fm h h hh hh]
    congr 1; funext y; rw [Real.rpow_two, sq]
  rw [e f hf, e g hg, ← Gen_eq_Fm f g hf hg] at h
  exact h

lemma Gen_nonneg {f g : I → I → ℝ} (hf : NK f) (hg : NK g) : 0 ≤ Gen f g :=
  integral_nonneg fun z => Finset.prod_nonneg fun j _ => mul_nonneg (hf.2 _ _) (hg.2 _ _)

lemma Gen_comm {f g : I → I → ℝ} (hf : NK f) (hg : NK g) : Gen f g = Gen g f := by
  rw [Gen_eq_Fm f g hf hg, Gen_eq_Fm g f hg hf]
  congr 1; funext y; ring

lemma nk_add {f g : I → I → ℝ} (hf : NK f) (hg : NK g) : NK (fun x y => f x y + g x y) :=
  ⟨Section2Aux.isKernel_add hf.1 hg.1, fun x y => add_nonneg (hf.2 x y) (hg.2 x y)⟩

/-- The triangle inequality for `t(K_{2,3}, ·)^{1/6}` on nonnegative kernels. -/
lemma Gen_triangle {f g : I → I → ℝ} (hf : NK f) (hg : NK g) :
    Gen (fun x y => f x y + g x y) (fun x y => f x y + g x y) ^ ((1 : ℝ) / 6) ≤
      Gen f f ^ ((1 : ℝ) / 6) + Gen g g ^ ((1 : ℝ) / 6) := by
  obtain ⟨M, hM0, hM⟩ := nk_bound hf
  obtain ⟨N, hN0, hN⟩ := nk_bound hg
  have hfg := nk_add hf hg
  set n3 : (I × I → ℝ) → ℝ := fun φ =>
    (∫ q, φ q ^ 3 ∂((volume : Measure I).prod volume)) ^ ((1 : ℝ) / 3) with hn3
  have hG : ∀ {u v : I → I → ℝ} (hu : NK u) (hv : NK v),
      Gen u v ^ ((1 : ℝ) / 3) = n3 (fun q => Gk u v q.1 q.2) := fun hu hv => by
    rw [Gen_eq_Gk _ _ hu hv]
  -- Minkowski, three times
  have hmk : ∀ {φ ψ : I × I → ℝ}, Measurable φ → Measurable ψ → (∀ q, 0 ≤ φ q) →
      (∀ q, 0 ≤ ψ q) → ∀ C D : ℝ, (∀ q, φ q ≤ C) → (∀ q, ψ q ≤ D) →
      n3 (fun q => φ q + ψ q) ≤ n3 φ + n3 ψ :=
    fun hφ hψ hφ0 hψ0 C D hC hD => mink3 hφ hψ hφ0 hψ0 hC hD
  have mff := measurable_Gk hf hf; have mfg := measurable_Gk hf hg
  have mgf := measurable_Gk hg hf; have mgg := measurable_Gk hg hg
  have nff := fun q : I × I => Gk_nonneg hf hf q.1 q.2
  have nfg := fun q : I × I => Gk_nonneg hf hg q.1 q.2
  have ngf := fun q : I × I => Gk_nonneg hg hf q.1 q.2
  have ngg := fun q : I × I => Gk_nonneg hg hg q.1 q.2
  have bff := fun q : I × I => Gk_le hf hf hM0 hM hM q.1 q.2
  have bfg := fun q : I × I => Gk_le hf hg hM0 hM hN q.1 q.2
  have bgf := fun q : I × I => Gk_le hg hf hN0 hN hM q.1 q.2
  have bgg := fun q : I × I => Gk_le hg hg hN0 hN hN q.1 q.2
  have hsum : n3 (fun q => Gk (fun x y => f x y + g x y) (fun x y => f x y + g x y) q.1 q.2) ≤
      ((n3 (fun q => Gk f f q.1 q.2) + n3 (fun q => Gk f g q.1 q.2)) +
        n3 (fun q => Gk g f q.1 q.2)) + n3 (fun q => Gk g g q.1 q.2) := by
    have e : (fun q : I × I => Gk (fun x y => f x y + g x y) (fun x y => f x y + g x y) q.1 q.2) =
        fun q => ((Gk f f q.1 q.2 + Gk f g q.1 q.2) + Gk g f q.1 q.2) + Gk g g q.1 q.2 := by
      funext q; exact Gk_add hf hg q.1 q.2
    rw [e]
    refine (hmk (φ := fun q => (Gk f f q.1 q.2 + Gk f g q.1 q.2) + Gk g f q.1 q.2)
      ((mff.add mfg).add mgf) mgg
      (fun q => add_nonneg (add_nonneg (nff q) (nfg q)) (ngf q)) ngg (M * M + M * N + N * M)
      (N * N) (fun q => add_le_add (add_le_add (bff q) (bfg q)) (bgf q)) bgg).trans ?_
    gcongr
    refine (hmk (φ := fun q => Gk f f q.1 q.2 + Gk f g q.1 q.2) (mff.add mfg) mgf
      (fun q => add_nonneg (nff q) (nfg q)) ngf
      (M * M + M * N) (N * M) (fun q => add_le_add (bff q) (bfg q)) bgf).trans ?_
    gcongr
    exact hmk mff mfg nff nfg (M * M) (M * N) bff bfg
  rw [← hG hfg hfg, ← hG hf hf, ← hG hf hg, ← hG hg hf, ← hG hg hg] at hsum
  -- the Cauchy–Schwarz bounds
  set a := Gen f f with ha
  set b := Gen g g with hb
  have ha0 : 0 ≤ a := Gen_nonneg hf hf
  have hb0 : 0 ≤ b := Gen_nonneg hg hg
  set α := a ^ ((1 : ℝ) / 6) with hα
  set β := b ^ ((1 : ℝ) / 6) with hβ
  have hα0 : 0 ≤ α := Real.rpow_nonneg ha0 _
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hb0 _
  have hpow : ∀ x : ℝ, 0 ≤ x → ∀ r : ℝ, x ^ r = (x ^ ((1 : ℝ) / 6)) ^ (6 * r) := by
    intro x hx r
    rw [← Real.rpow_mul hx]; congr 1; ring
  have ha3 : a ^ ((1 : ℝ) / 3) = α ^ 2 := by
    rw [hpow a ha0, ← hα, show (6 : ℝ) * (1 / 3) = (2 : ℕ) by norm_num, Real.rpow_natCast]
  have hb3 : b ^ ((1 : ℝ) / 3) = β ^ 2 := by
    rw [hpow b hb0, ← hβ, show (6 : ℝ) * (1 / 3) = (2 : ℕ) by norm_num, Real.rpow_natCast]
  have ha2 : a ^ ((1 : ℝ) / 2) = α ^ 3 := by
    rw [hpow a ha0, ← hα, show (6 : ℝ) * (1 / 2) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hb2 : b ^ ((1 : ℝ) / 2) = β ^ 3 := by
    rw [hpow b hb0, ← hβ, show (6 : ℝ) * (1 / 2) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hcs : ∀ c : ℝ, 0 ≤ c → c ≤ α ^ 3 * β ^ 3 → c ^ ((1 : ℝ) / 3) ≤ α * β := by
    intro c hc hle
    calc c ^ ((1 : ℝ) / 3) ≤ ((α * β) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := by
          rw [mul_pow]; exact Real.rpow_le_rpow hc hle (by norm_num)
      _ = α * β := by
          rw [one_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
            Real.pow_rpow_inv_natCast (mul_nonneg hα0 hβ0) (by norm_num)]
  have c1 := hcs (Gen f g) (Gen_nonneg hf hg) (by rw [← ha2, ← hb2]; exact Gen_cs hf hg)
  have c2 := hcs (Gen g f) (Gen_nonneg hg hf) (by
    rw [← ha2, ← hb2, mul_comm]; exact Gen_cs hg hf)
  rw [ha3, hb3] at hsum
  have hT : Gen (fun x y => f x y + g x y) (fun x y => f x y + g x y) ^ ((1 : ℝ) / 3) ≤
      (α + β) ^ 2 := by nlinarith
  set T := Gen (fun x y => f x y + g x y) (fun x y => f x y + g x y)
  have hT0 : 0 ≤ T := Gen_nonneg hfg hfg
  calc T ^ ((1 : ℝ) / 6) = (T ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul hT0]; norm_num
    _ ≤ ((α + β) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hT0 _) hT (by norm_num)
    _ = α + β := by
        rw [one_div, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.pow_rpow_inv_natCast (add_nonneg hα0 hβ0) (by norm_num)]

lemma card_univ23 : (Finset.univ : Finset (Fin 2 × Fin 3)).card = 6 := by
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **`K_{2,3}` is weakly norming** (bipartition into the parts of sizes 2 and 3). -/
lemma isWeaklyNorming_K23 : IsWeaklyNorming (Finset.univ : Finset (Fin 2 × Fin 3)) := by
  set E := (Finset.univ : Finset (Fin 2 × Fin 3)) with hE
  have hne : 0 < E.card := by rw [card_univ23]; norm_num
  refine ⟨fun U _ c => Section2Aux.rNorm_smul E hne U c, fun U V hU hV => ?_,
    fun U hU h => Section2Aux.rNorm_posdef E hne U hU h⟩
  have hU' : NK (fun x y => |U x y|) := ⟨Section2Aux.isKernel_abs hU, fun _ _ => abs_nonneg _⟩
  have hV' : NK (fun x y => |V x y|) := ⟨Section2Aux.isKernel_abs hV, fun _ _ => abs_nonneg _⟩
  have hmono : tb E (fun x y => |U x y + V x y|) ≤ tb E (fun x y => |U x y| + |V x y|) :=
    Section2Aux.tBiDec_mono E _ _
      (fun _ _ => Section2Aux.isKernel_abs (Section2Aux.isKernel_add hU hV))
      (fun _ _ => (nk_add hU' hV').1) (fun _ _ _ _ => abs_nonneg _)
      fun _ _ x y => abs_add_le _ _
  unfold rNorm
  rw [card_univ23]
  push_cast
  calc tb E (fun x y => |U x y + V x y|) ^ ((1 : ℝ) / 6)
      ≤ tb E (fun x y => |U x y| + |V x y|) ^ ((1 : ℝ) / 6) :=
        Real.rpow_le_rpow (Section2Aux.tb_nonneg E _ fun _ _ => abs_nonneg _) hmono
          (by norm_num)
    _ ≤ _ := by
        rw [hE, tb_univ_eq_Gen, tb_univ_eq_Gen, tb_univ_eq_Gen]
        exact Gen_triangle hU' hV'

end K23b

/-! ## B4(i) -/

section B4

/-- The bipartition of `K_{2,3}` into its two sides. -/
def leftSide : Fin 2 ⊕ Fin 3 → Prop := fun v => v.isLeft = true

lemma isBipartition_leftSide :
    IsBipartition (completeBipartiteGraph (Fin 2) (Fin 3)) leftSide := by
  intro u v h
  simp only [completeBipartiteGraph_adj] at h
  simp only [leftSide]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, Sum.isLeft_eq_false.mpr h2]
  · rw [Sum.isLeft_eq_false.mpr h1]; simp [h2]

/-- `Fin 2` is the left side. -/
def eL : Fin 2 ≃ {v : Fin 2 ⊕ Fin 3 // leftSide v} where
  toFun i := ⟨Sum.inl i, rfl⟩
  invFun v := v.1.getLeft v.2
  left_inv i := rfl
  right_inv := by
    rintro ⟨v, h⟩
    cases v with
    | inl i => rfl
    | inr j => simp [leftSide] at h

/-- `Fin 3` is the right side. -/
def eR : Fin 3 ≃ {v : Fin 2 ⊕ Fin 3 // ¬ leftSide v} where
  toFun j := ⟨Sum.inr j, by simp [leftSide]⟩
  invFun v := v.1.getRight (by have := v.2; simp only [leftSide] at this; simpa using this)
  left_inv j := rfl
  right_inv := by
    rintro ⟨v, h⟩
    cases v with
    | inl i => simp [leftSide] at h
    | inr j => rfl

lemma isWeaklyNormingGraph_K23 :
    IsWeaklyNormingGraph (completeBipartiteGraph (Fin 2) (Fin 3)) := by
  refine ⟨leftSide, isBipartition_leftSide, ?_⟩
  let _ := Classical.decPred leftSide
  have hE : sideEdges (completeBipartiteGraph (Fin 2) (Fin 3)) leftSide =
      (Finset.univ : Finset (Fin 2 × Fin 3)).map (eL.prodCongr eR).toEmbedding := by
    ext p
    rw [Section1Aux.mem_sideEdges]
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Equiv.coe_toEmbedding,
      Equiv.prodCongr_apply]
    constructor
    · intro _
      exact ⟨(eL.symm p.1, eR.symm p.2), by simp⟩
    · intro _
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
      simp only [leftSide] at ha hb
      simp only [completeBipartiteGraph_adj]
      left
      exact ⟨ha, by simpa using hb⟩
  rw [hE, Section1Aux.isWeaklyNorming_map_equiv]
  exact isWeaklyNorming_K23

lemma not_acyclic_K23 : ¬ (completeBipartiteGraph (Fin 2) (Fin 3)).IsAcyclic := by
  intro h
  have h1 : (completeBipartiteGraph (Fin 2) (Fin 3)).Adj (Sum.inl 0) (Sum.inr 0) := by simp
  have h2 : (completeBipartiteGraph (Fin 2) (Fin 3)).Adj (Sum.inr 0) (Sum.inl 1) := by simp
  have h3 : (completeBipartiteGraph (Fin 2) (Fin 3)).Adj (Sum.inl 1) (Sum.inr 1) := by simp
  have h4 : (completeBipartiteGraph (Fin 2) (Fin 3)).Adj (Sum.inr 1) (Sum.inl 0) := by simp
  refine h (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3
    (SimpleGraph.Walk.cons h4 SimpleGraph.Walk.nil)))) ?_
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  simp

lemma card_edgeFinset_K23 :
    (letI := Classical.decRel (completeBipartiteGraph (Fin 2) (Fin 3)).Adj
    (completeBipartiteGraph (Fin 2) (Fin 3)).edgeFinset.card) = 6 := by
  rw [Section1Aux.edgeFinset_K23, Finset.card_image_of_injective _ (fun p q h => by
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
    · exact absurd h1 Sum.inl_ne_inr), card_univ23]

lemma not_isNormingGraph_K23 :
    ¬ IsNormingGraph (completeBipartiteGraph (Fin 2) (Fin 3)) := by
  classical
  rintro ⟨s, hbip, hN⟩
  set H := completeBipartiteGraph (Fin 2) (Fin 3) with hH
  set E := (letI := Classical.decPred s; sideEdges H s) with hEdef
  have hcard : E.card = 6 := by
    have hD := Section1Aux.sideOG_underlying H s hbip
    have h1 := Section1Aux.card_sideEdges (Section1Aux.sideOG H s) s (fun u v h => h.2)
    rw [hD] at h1
    let _ := Classical.decRel H.Adj
    have h2 := Section1Aux.card_edgeFinset_eq H (Section1Aux.sideOG H s) hD
    rw [hEdef, h1, ← h2]
    exact card_edgeFinset_K23
  have key : ∀ U : I → I → ℝ, (∀ x y, U x y = U y x) →
      hNorm E U = |tU H U| ^ ((1 : ℝ) / 6) := by
    intro U hU
    unfold hNorm
    rw [hcard, hEdef, tU_eq_tb H s hbip hU]
    norm_num
  apply Section1Aux.k23_not_norming_symm'
  refine ⟨⟨fun U hU c => ?_, fun U V hU hV => ?_⟩, fun U hU h0 => ?_⟩
  · have := hN.1 U hU.1 c
    rw [key _ (Section1Aux.isSymmKernel_smul hU c).2, key _ hU.2] at this
    exact this
  · have := hN.2.1 U V hU.1 hV.1
    rw [key _ (Section1Aux.isSymmKernel_add hU hV).2, key _ hU.2, key _ hV.2] at this
    exact this
  · exact hN.2.2 U hU.1 (by rw [key _ hU.2]; exact h0)

/-- **B4(i).** `K_{2,3}` is weakly norming (for its bipartition into the parts of sizes 2 and 3)
and step forcing, but not norming (for any bipartition). -/
theorem k23_weaklyNorming_stepForcing_not_norming_proof (hA2 : DGHRRCor324Hyp.{0}) :
    IsWeaklyNorming (Finset.univ : Finset (Fin 2 × Fin 3)) ∧
    IsStepForcing (completeBipartiteGraph (Fin 2) (Fin 3)) ∧
    ¬ IsNormingGraph (completeBipartiteGraph (Fin 2) (Fin 3)) :=
  ⟨isWeaklyNorming_K23,
    isStepForcing_of_wnGraph hA2 _ isWeaklyNormingGraph_K23 not_acyclic_K23,
    not_isNormingGraph_K23⟩

end B4

/-! ## Four-colour encoding and the uniform convexity gap -/

section Gap

/-- The four-colour encoding of a pair of graphons. -/
noncomputable def enc (A B : I → I → ℝ) : Fin 4 → I → I → ℝ :=
  ![fun x y => A x y * B x y, fun x y => A x y * (1 - B x y),
    fun x y => (1 - A x y) * B x y, fun x y => (1 - A x y) * (1 - B x y)]

lemma isKGraphon_enc {A B : I → I → ℝ} (hA : IsSymmGraphon A) (hB : IsSymmGraphon B) :
    IsKGraphon 4 (enc A B) := by
  have mA := hA.1.1; have mB := hB.1.1
  refine ⟨fun i => ?_, fun i x y => ?_, fun x y => ?_, fun i x y => ?_⟩
  · fin_cases i <;> simp only [enc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    · exact mA.mul mB
    · exact mA.mul (measurable_const.sub mB)
    · exact (measurable_const.sub mA).mul mB
    · exact (measurable_const.sub mA).mul (measurable_const.sub mB)
  · have a := hA.1.2 x y; have b := hB.1.2 x y
    fin_cases i <;> simp only [enc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] <;>
      apply mul_nonneg <;> linarith [a.1, a.2, b.1, b.2]
  · simp only [enc, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons]
    ring
  · fin_cases i <;> simp only [enc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] <;>
      rw [hA.2 x y, hB.2 x y]

/-- The first decoded graphon `U = P₁₁ + P₁₀`. -/
def decA (P : Fin 4 → I → I → ℝ) : I → I → ℝ := fun x y => P 0 x y + P 1 x y

/-- The second decoded graphon `V = P₁₁ + P₀₁`. -/
def decB (P : Fin 4 → I → I → ℝ) : I → I → ℝ := fun x y => P 0 x y + P 2 x y

lemma decA_enc (A B : I → I → ℝ) : decA (enc A B) = A := by
  funext x y; simp only [decA, enc, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

lemma decB_enc (A B : I → I → ℝ) : decB (enc A B) = B := by
  funext x y
  simp only [decB, enc, Matrix.cons_val_zero, Matrix.cons_val, Matrix.head_cons]; ring

lemma kg_le_one {P : Fin 4 → I → I → ℝ} (hP : IsKGraphon 4 P) (i : Fin 4) (x y : I) :
    P i x y ≤ 1 := by
  have h := hP.2.2.1 x y
  rw [← h]
  exact Finset.single_le_sum (fun j _ => hP.2.1 j x y) (Finset.mem_univ i)

lemma kg_mem {P : Fin 4 → I → I → ℝ} (hP : IsKGraphon 4 P) (i : Fin 4) (x y : I) :
    P i x y ∈ Icc (0 : ℝ) 1 := ⟨hP.2.1 i x y, kg_le_one hP i x y⟩

lemma kg_sum_le {P : Fin 4 → I → I → ℝ} (hP : IsKGraphon 4 P) (x y : I) :
    P 0 x y + P 1 x y ≤ 1 ∧ P 0 x y + P 2 x y ≤ 1 := by
  have h := hP.2.2.1 x y
  rw [Fin.sum_univ_four] at h
  have := hP.2.1 2 x y; have := hP.2.1 3 x y; have := hP.2.1 1 x y
  constructor <;> linarith

lemma isSymmGraphon_decA {P : Fin 4 → I → I → ℝ} (hP : IsKGraphon 4 P) :
    IsSymmGraphon (decA P) :=
  ⟨⟨(hP.1 0).add (hP.1 1), fun x y => ⟨add_nonneg (hP.2.1 0 x y) (hP.2.1 1 x y),
    (kg_sum_le hP x y).1⟩⟩, fun x y => by simp only [decA]; rw [hP.2.2.2 0, hP.2.2.2 1]⟩

lemma isSymmGraphon_decB {P : Fin 4 → I → I → ℝ} (hP : IsKGraphon 4 P) :
    IsSymmGraphon (decB P) :=
  ⟨⟨(hP.1 0).add (hP.1 2), fun x y => ⟨add_nonneg (hP.2.1 0 x y) (hP.2.1 2 x y),
    (kg_sum_le hP x y).2⟩⟩, fun x y => by simp only [decB]; rw [hP.2.2.2 0, hP.2.2.2 2]⟩

/-- Pulling back a `[4]`-graphon by a measure-preserving map. -/
noncomputable def pullK {φ : I → I} (hφ : MeasurePreserving φ volume volume) (P : KGraphon 4) :
    KGraphon 4 where
  toFun i := pullback φ (P.toFun i)
  isKGraphon := ⟨fun i => (P.isKGraphon.1 i).comp (hφ.measurable.prodMap hφ.measurable),
    fun i x y => P.isKGraphon.2.1 i _ _, fun x y => P.isKGraphon.2.2.1 _ _,
    fun i x y => P.isKGraphon.2.2.2 i _ _⟩

lemma k1_of_mem {F : I → I → ℝ} (hm : Measurable (Function.uncurry F))
    (h : ∀ x y, F x y ∈ Icc (0 : ℝ) 1) : K1 F :=
  ⟨hm, fun x y => by rw [abs_le]; constructor <;> linarith [(h x y).1, (h x y).2]⟩

lemma k1_sym {F : I → I → ℝ} (h : IsSymmGraphon F) : K1 F := k1_of_mem h.1.1 h.1.2

/-- Coordinates are controlled by `d_{□,4}`. -/
lemma cutNorm_coord_le (P Q : KGraphon 4) (W : Fin 4 → I → I → ℝ) (hW : W = Q.toFun) (i : Fin 4) :
    cutNorm (fun x y => P.toFun i x y - W i x y) ≤ kCutNormDist 4 P.toFun W := by
  subst hW
  have hb : ∀ j (x y : I), |P.toFun j x y - Q.toFun j x y| ≤ 1 := fun j x y => by
    have h1 := kg_mem P.isKGraphon j x y; have h2 := kg_mem Q.isKGraphon j x y
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hbdd : BddAbove {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧
      r = ∑ j, |∫ p in S ×ˢ T, (P.toFun j p.1 p.2 - Q.toFun j p.1 p.2)|} := by
    refine ⟨∑ _j : Fin 4, (1 : ℝ), ?_⟩
    rintro r ⟨S, T, -, -, rfl⟩
    exact Finset.sum_le_sum fun j _ => abs_setIntegral_le (hb j) _
  refine cutNorm_le fun S T hS hT => ?_
  refine le_trans ?_ (le_csSup hbdd ⟨S, T, hS, hT, rfl⟩)
  exact Finset.single_le_sum (f := fun j => |∫ p in S ×ˢ T, (P.toFun j p.1 p.2 - Q.toFun j p.1 p.2)|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma kCutNormDist_nonneg (U W : Fin 4 → I → I → ℝ) : 0 ≤ kCutNormDist 4 U W :=
  Real.sSup_nonneg fun r ⟨_, _, _, _, hr⟩ => hr ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma kCutDist_set_nonempty (P Q : KGraphon 4) :
    {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = kCutNormDist 4 P.toFun (fun i => pullback φ (Q.toFun i))}.Nonempty :=
  ⟨_, id, MeasurePreserving.id _, rfl⟩

lemma kCutDist_self_le (P : KGraphon 4) : kCutDist 4 P.toFun P.toFun ≤ 0 := by
  have hbdd : BddBelow {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = kCutNormDist 4 P.toFun (fun i => pullback φ (P.toFun i))} :=
    ⟨0, fun r ⟨_, _, hr⟩ => hr ▸ kCutNormDist_nonneg _ _⟩
  refine (csInf_le hbdd ⟨id, MeasurePreserving.id _, rfl⟩).trans ?_
  refine csSup_le ⟨_, ∅, ∅, MeasurableSet.empty, MeasurableSet.empty, rfl⟩ ?_
  rintro r ⟨S, T, -, -, rfl⟩
  simp [pullback]

/-- A functional invariant under pullbacks and Lipschitz in `d_{□,4}` is controlled on
`δ_{□,4}`-balls. -/
lemma ball_bound {F : KGraphon 4 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hinv : ∀ (φ : I → I) (hφ : MeasurePreserving φ volume volume) Q, F (pullK hφ Q) = F Q)
    (hlip : ∀ P Q, |F P - F Q| ≤ C * kCutNormDist 4 P.toFun Q.toFun) {P Q : KGraphon 4} {r : ℝ}
    (h : kCutDist 4 P.toFun Q.toFun < r) : |F P - F Q| ≤ C * r := by
  obtain ⟨b, ⟨φ, hφ, rfl⟩, hb⟩ := exists_lt_of_csInf_lt (kCutDist_set_nonempty P Q) h
  rw [← hinv φ hφ Q]
  exact (hlip P (pullK hφ Q)).trans (mul_le_mul_of_nonneg_left hb.le hC)

lemma cont_of_ball {F : KGraphon 4 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ P Q r, kCutDist 4 P.toFun Q.toFun < r → |F P - F Q| ≤ C * r) :
    @Continuous _ _ (kCutTopology 4) _ F := by
  letI := kCutTopology 4
  rw [continuous_iff_continuousAt]
  intro P
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set r := ε / (2 * (C + 1)) with hr
  have hr0 : 0 < r := div_pos hε (by positivity)
  have hB : {W : KGraphon 4 | kCutDist 4 P.toFun W.toFun < r} ∈ nhds P :=
    IsOpen.mem_nhds (TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, r, rfl⟩)
      (show kCutDist 4 P.toFun P.toFun < r from lt_of_le_of_lt (kCutDist_self_le P) hr0)
  filter_upwards [hB] with W hW
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt (hball P W r hW) ?_
  rw [hr]
  have : C * (ε / (2 * (C + 1))) = ε * (C / (2 * (C + 1))) := by ring
  rw [this]
  have : C / (2 * (C + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
  nlinarith

lemma resp_of_ball {F : KGraphon 4 → ℝ} {C : ℝ}
    (hball : ∀ P Q r, kCutDist 4 P.toFun Q.toFun < r → |F P - F Q| ≤ C * r) (P Q : KGraphon 4)
    (h : kCutDist 4 P.toFun Q.toFun = 0) : F P = F Q := by
  have : |F P - F Q| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hball P Q (ε / (|C| + 1)) (by rw [h]; positivity)
    have h2 : C * (ε / (|C| + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [le_abs_self C]
    linarith
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

section Functionals

variable {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))

/-- The midpoint convexity gap `(t(A) + t(B))/2 - t((A + B)/2)`. -/
noncomputable def gapE (A B : I → I → ℝ) : ℝ :=
  (tb E A + tb E B) / 2 - tb E (fun x y => 1 / 2 * A x y + (1 - 1 / 2) * B x y)

noncomputable def PhiK (P : KGraphon 4) : ℝ := gapE E (decA P.toFun) (decB P.toFun)

noncomputable def MK (P : KGraphon 4) : ℝ :=
  tb (Finset.univ : Finset (Fin 2 × Fin 2)) (fun x y => decA P.toFun x y - decB P.toFun x y)

lemma coord_k1 (P : KGraphon 4) (i : Fin 4) : K1 (P.toFun i) :=
  k1_of_mem (P.isKGraphon.1 i) (kg_mem P.isKGraphon i)

lemma coord_sub_bk (P Q : KGraphon 4) (i : Fin 4) :
    BK (fun x y => P.toFun i x y - Q.toFun i x y) := k1_sub (coord_k1 P i) (coord_k1 Q i)

lemma cut_two_le (P Q : KGraphon 4) (i j : Fin 4) (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    cutNorm (fun x y => a * (P.toFun i x y - Q.toFun i x y) + b * (P.toFun j x y - Q.toFun j x y))
      ≤ 2 * kCutNormDist 4 P.toFun Q.toFun := by
  refine (cutNorm_lin_le (coord_sub_bk P Q i) (coord_sub_bk P Q j) a b).trans ?_
  have h1 := cutNorm_coord_le P Q Q.toFun rfl i
  have h2 := cutNorm_coord_le P Q Q.toFun rfl j
  have n1 := cutNorm_nonneg (coord_sub_bk P Q i).2.choose_spec
  have n2 := cutNorm_nonneg (coord_sub_bk P Q j).2.choose_spec
  nlinarith [abs_nonneg a, abs_nonneg b]

lemma k1_decA (P : KGraphon 4) : K1 (decA P.toFun) := k1_sym (isSymmGraphon_decA P.isKGraphon)
lemma k1_decB (P : KGraphon 4) : K1 (decB P.toFun) := k1_sym (isSymmGraphon_decB P.isKGraphon)

lemma k1_mid (P : KGraphon 4) :
    K1 (fun x y => 1 / 2 * decA P.toFun x y + (1 - 1 / 2) * decB P.toFun x y) := by
  have hA := isSymmGraphon_decA P.isKGraphon
  have hB := isSymmGraphon_decB P.isKGraphon
  refine k1_of_mem ((hA.1.1.const_mul _).add (hB.1.1.const_mul _)) fun x y => ?_
  have := hA.1.2 x y; have := hB.1.2 x y
  simp only [mem_Icc] at *
  constructor <;> linarith

lemma k1_diff (P : KGraphon 4) : K1 (fun x y => decA P.toFun x y - decB P.toFun x y) := by
  have hA := isSymmGraphon_decA P.isKGraphon
  have hB := isSymmGraphon_decB P.isKGraphon
  refine ⟨hA.1.1.sub hB.1.1, fun x y => ?_⟩
  have := hA.1.2 x y; have := hB.1.2 x y
  simp only [mem_Icc] at *
  rw [abs_le]; constructor <;> linarith

lemma PhiK_lip (P Q : KGraphon 4) :
    |PhiK E P - PhiK E Q| ≤ (16 * E.card) * kCutNormDist 4 P.toFun Q.toFun := by
  classical
  set d := kCutNormDist 4 P.toFun Q.toFun
  have hA := abs_tb_sub_le E (k1_decA P) (k1_decA Q)
  have hB := abs_tb_sub_le E (k1_decB P) (k1_decB Q)
  have hM := abs_tb_sub_le E (k1_mid P) (k1_mid Q)
  have cA : cutNorm (fun x y => decA P.toFun x y - decA Q.toFun x y) ≤ 2 * d := by
    have := cut_two_le P Q 0 1 1 1 (by norm_num) (by norm_num)
    convert this using 2; funext x y; simp only [decA]; ring
  have cB : cutNorm (fun x y => decB P.toFun x y - decB Q.toFun x y) ≤ 2 * d := by
    have := cut_two_le P Q 0 2 1 1 (by norm_num) (by norm_num)
    convert this using 2; funext x y; simp only [decB]; ring
  have cM : cutNorm (fun x y => (1 / 2 * decA P.toFun x y + (1 - 1 / 2) * decB P.toFun x y) -
      (1 / 2 * decA Q.toFun x y + (1 - 1 / 2) * decB Q.toFun x y)) ≤ 2 * d := by
    have h1 := cutNorm_lin_le (k1_sub (k1_decA P) (k1_decA Q)) (k1_sub (k1_decB P) (k1_decB Q))
      (1 / 2) (1 - 1 / 2)
    have e : (fun x y => (1 / 2 * decA P.toFun x y + (1 - 1 / 2) * decB P.toFun x y) -
        (1 / 2 * decA Q.toFun x y + (1 - 1 / 2) * decB Q.toFun x y)) =
        fun x y => 1 / 2 * (decA P.toFun x y - decA Q.toFun x y) +
          (1 - 1 / 2) * (decB P.toFun x y - decB Q.toFun x y) := by funext x y; ring
    rw [e]; refine h1.trans ?_
    norm_num; linarith
  have hd := kCutNormDist_nonneg P.toFun Q.toFun
  unfold PhiK gapE
  have hc : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
  calc |(tb E (decA P.toFun) + tb E (decB P.toFun)) / 2 -
        tb E (fun x y => 1 / 2 * decA P.toFun x y + (1 - 1 / 2) * decB P.toFun x y) -
        ((tb E (decA Q.toFun) + tb E (decB Q.toFun)) / 2 -
        tb E (fun x y => 1 / 2 * decA Q.toFun x y + (1 - 1 / 2) * decB Q.toFun x y))|
      ≤ |tb E (decA P.toFun) - tb E (decA Q.toFun)| / 2 +
        |tb E (decB P.toFun) - tb E (decB Q.toFun)| / 2 +
        |tb E (fun x y => 1 / 2 * decA P.toFun x y + (1 - 1 / 2) * decB P.toFun x y) -
          tb E (fun x y => 1 / 2 * decA Q.toFun x y + (1 - 1 / 2) * decB Q.toFun x y)| := by
        rw [abs_le]; constructor <;>
          linarith [le_abs_self (tb E (decA P.toFun) - tb E (decA Q.toFun)),
            neg_abs_le (tb E (decA P.toFun) - tb E (decA Q.toFun)),
            le_abs_self (tb E (decB P.toFun) - tb E (decB Q.toFun)),
            neg_abs_le (tb E (decB P.toFun) - tb E (decB Q.toFun)),
            le_abs_self (tb E (fun x y => 1 / 2 * decA P.toFun x y + (1 - 1 / 2) * decB P.toFun x y) -
              tb E (fun x y => 1 / 2 * decA Q.toFun x y + (1 - 1 / 2) * decB Q.toFun x y)),
            neg_abs_le (tb E (fun x y => 1 / 2 * decA P.toFun x y + (1 - 1 / 2) * decB P.toFun x y) -
              tb E (fun x y => 1 / 2 * decA Q.toFun x y + (1 - 1 / 2) * decB Q.toFun x y))]
    _ ≤ (4 * E.card * (2 * d)) / 2 + (4 * E.card * (2 * d)) / 2 + 4 * E.card * (2 * d) := by
        gcongr
        · exact hA.trans (by gcongr)
        · exact hB.trans (by gcongr)
        · exact hM.trans (by gcongr)
    _ = (16 * E.card) * d := by ring

lemma MK_lip (P Q : KGraphon 4) :
    |MK P - MK Q| ≤ 32 * kCutNormDist 4 P.toFun Q.toFun := by
  have h := abs_tb_sub_le (Finset.univ : Finset (Fin 2 × Fin 2)) (k1_diff P) (k1_diff Q)
  have c : cutNorm (fun x y => (decA P.toFun x y - decB P.toFun x y) -
      (decA Q.toFun x y - decB Q.toFun x y)) ≤ 2 * kCutNormDist 4 P.toFun Q.toFun := by
    have := cut_two_le P Q 1 2 1 (-1) (by norm_num) (by norm_num)
    convert this using 2; funext x y; simp only [decA, decB]; ring
  have hcard : ((Finset.univ : Finset (Fin 2 × Fin 2)).card : ℝ) = 4 := by simp
  unfold MK
  rw [hcard] at h
  linarith

lemma PhiK_inv (φ : I → I) (hφ : MeasurePreserving φ volume volume) (Q : KGraphon 4) :
    PhiK E (pullK hφ Q) = PhiK E Q := by
  classical
  unfold PhiK gapE
  have hA := isSymmGraphon_decA Q.isKGraphon
  have hB := isSymmGraphon_decB Q.isKGraphon
  have e1 : decA (pullK hφ Q).toFun = pullback φ (decA Q.toFun) := rfl
  have e2 : decB (pullK hφ Q).toFun = pullback φ (decB Q.toFun) := rfl
  have e3 : (fun x y => 1 / 2 * decA (pullK hφ Q).toFun x y + (1 - 1 / 2) *
      decB (pullK hφ Q).toFun x y) = pullback φ (fun x y => 1 / 2 * decA Q.toFun x y +
        (1 - 1 / 2) * decB Q.toFun x y) := rfl
  rw [e3, e1, e2, tb_pullback E _ hA.1.1 hφ, tb_pullback E _ hB.1.1 hφ,
    tb_pullback E (fun x y => 1 / 2 * decA Q.toFun x y + (1 - 1 / 2) * decB Q.toFun x y)
      (k1_mid Q).1 hφ]

lemma MK_inv (φ : I → I) (hφ : MeasurePreserving φ volume volume) (Q : KGraphon 4) :
    MK (pullK hφ Q) = MK Q := by
  unfold MK
  have hA := isSymmGraphon_decA Q.isKGraphon
  have hB := isSymmGraphon_decB Q.isKGraphon
  have e : (fun x y => decA (pullK hφ Q).toFun x y - decB (pullK hφ Q).toFun x y) =
      pullback φ (fun x y => decA Q.toFun x y - decB Q.toFun x y) := rfl
  rw [e, tb_pullback _ (fun x y => decA Q.toFun x y - decB Q.toFun x y) (hA.1.1.sub hB.1.1) hφ]

end Functionals

/-- **The uniform convexity gap** (tex l.1073-1095, via the FRHSU four-colour compactness). For a
bipartite edge set `E` with at least one edge that is weakly norming (`IsWeaklyNorming E`) and whose
graph contains a cycle, and assuming `FRHSUThm43Hyp`: with `t = t_bi(E, ·)`, for every `ε > 0` there is `η > 0` with `t((A+B)/2) ≤ (t(A) + t(B))/2 - η`
for all everywhere-symmetric graphons `A`, `B` (`IsSymmGraphon`) with `‖A - B‖_□ ≥ ε`. -/
lemma gap_lemma {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y)) (hE0 : 0 < E.card)
    (hWN : IsWeaklyNorming E) (hcyc : ¬ (bipGraph E).IsAcyclic) (hFR : FRHSUThm43Hyp)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ A B : I → I → ℝ, IsSymmGraphon A → IsSymmGraphon B →
      ε ≤ cutNorm (fun x y => A x y - B x y) → η ≤ gapE E A B := by
  classical
  letI := kCutTopology 4
  haveI : CompactSpace (Quot fun U W : KGraphon 4 => kCutDist 4 U.toFun W.toFun = 0) :=
    hFR 4 (by norm_num)
  have hC1 : (0 : ℝ) ≤ 16 * E.card := by positivity
  have bΦ : ∀ P Q r, kCutDist 4 P.toFun Q.toFun < r → |PhiK E P - PhiK E Q| ≤ (16 * E.card) * r :=
    fun P Q r h => ball_bound hC1 (PhiK_inv E) (PhiK_lip E) h
  have bM : ∀ P Q r, kCutDist 4 P.toFun Q.toFun < r → |MK P - MK Q| ≤ 32 * r :=
    fun P Q r h => ball_bound (by norm_num) MK_inv MK_lip h
  set Φq := Quot.lift (PhiK E) (resp_of_ball bΦ) with hΦq
  set Mq := Quot.lift MK (resp_of_ball bM) with hMq
  have cΦ : Continuous Φq := continuous_quot_lift _ (cont_of_ball hC1 bΦ)
  have cM : Continuous Mq := continuous_quot_lift _ (cont_of_ball (by norm_num) bM)
  set K := Mq ⁻¹' Ici (ε ^ 4) with hK
  have hKc : IsCompact K := (isClosed_Ici.preimage cM).isCompact
  have hε4 : 0 < ε ^ 4 := by positivity
  have key : ∀ P : KGraphon 4, ε ^ 4 ≤ MK P → 0 < PhiK E P := by
    intro P hP
    have hA := isSymmGraphon_decA P.isKGraphon
    have hB := isSymmGraphon_decB P.isKGraphon
    by_cases hae : AEEq volume (decA P.toFun) (decB P.toFun)
    · exfalso
      have h0 : AEEq volume (fun x y => decA P.toFun x y - decB P.toFun x y) (fun _ _ => 0) := by
        unfold AEEq at *
        filter_upwards [hae] with q hq
        rw [hq, sub_self]
      have : MK P = 0 := by
        unfold MK
        rw [Section1Aux.tb_congr_ae _ h0, Section2Aux.tb_const]
        simp
      linarith
    · have h := Section1Aux.thm16_forward E hE0 hWN hcyc _ _ (Section1Aux.isKernel_of_isDigraphon hA.1)
        (Section1Aux.isKernel_of_isDigraphon hB.1) (fun x y => (hA.1.2 x y).1)
        (fun x y => (hB.1.2 x y).1) hae (1 / 2) ⟨by norm_num, by norm_num⟩
      unfold PhiK gapE
      linarith
  have hMenc : ∀ A B : I → I → ℝ, ∀ (hA : IsSymmGraphon A) (hB : IsSymmGraphon B),
      ε ≤ cutNorm (fun x y => A x y - B x y) →
      ε ^ 4 ≤ MK ⟨enc A B, isKGraphon_enc hA hB⟩ := by
    intro A B hA hB hcut
    unfold MK
    simp only [decA_enc, decB_enc]
    have hbk : BK (fun x y => A x y - B x y) := k1_sub (k1_sym hA) (k1_sym hB)
    exact (pow_le_pow_left₀ hε.le hcut 4).trans (cutNorm_pow4_le hbk)
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := hKc.exists_isMinOn hne cΦ.continuousOn
    obtain ⟨P0, rfl⟩ := Quot.exists_rep x0
    refine ⟨PhiK E P0, key P0 hx0, fun A B hA hB hcut => ?_⟩
    have hmem : Quot.mk _ (⟨enc A B, isKGraphon_enc hA hB⟩ : KGraphon 4) ∈ K :=
      hMenc A B hA hB hcut
    have := hmin hmem
    simp only [hΦq] at this
    have e : PhiK E ⟨enc A B, isKGraphon_enc hA hB⟩ = gapE E A B := by
      unfold PhiK; simp only [decA_enc, decB_enc]
    rw [← e]
    exact this
  · refine ⟨1, one_pos, fun A B hA hB hcut => ?_⟩
    exact absurd ⟨Quot.mk _ (⟨enc A B, isKGraphon_enc hA hB⟩ : KGraphon 4),
      hMenc A B hA hB hcut⟩ hne

end Gap

/-! ## Weak* lower semicontinuity of `t(H, ·)` -/

section LSC

variable (P : PosPartition (volume : Measure I))

lemma ind_sum_one (x : I) : ∑ i, (P.part i).indicator (1 : I → ℝ) x = 1 := by
  obtain ⟨i, hi⟩ := exists_part P x
  have := Section2Aux.indicator_sum P.part P.disjoint hi (fun _ => (1 : ℝ))
  simp only [mul_one] at this
  convert this using 2

lemma integral_stepAvg {G : I → I → ℝ} (hG : BK G) :
    ∫ q, stepAvg P G q.1 q.2 ∂((volume : Measure I).prod volume) =
      ∫ q, G q.1 q.2 ∂((volume : Measure I).prod volume) := by
  have hone : BK (fun _ _ : I => (1 : ℝ)) := ⟨measurable_const, 1, fun _ _ => by simp⟩
  have hcell : ∀ i j, ∫ q : I × I, (P.part i).indicator (fun _ => (1 : ℝ)) q.1 *
      (P.part j).indicator (fun _ => (1 : ℝ)) q.2 * avgV P G i j
        ∂((volume : Measure I).prod volume) =
      ∫ q in P.part i ×ˢ P.part j, G q.1 q.2 := by
    intro i j
    rw [integral_mul_const]
    have h1 := bil_rect (fun _ _ => (1 : ℝ)) (P.measurableSet_part i) (P.measurableSet_part j)
    unfold bil at h1
    simp only [one_mul] at h1
    have e : (fun q : I × I => (P.part i).indicator (fun _ => (1 : ℝ)) q.1 *
        (P.part j).indicator (fun _ => (1 : ℝ)) q.2) =
        fun q => (P.part i).indicator 1 q.1 * (P.part j).indicator 1 q.2 := rfl
    rw [e, h1, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Measure.volume_eq_prod,
      Measure.prod_prod, ENNReal.toReal_mul]
    unfold avgV
    have hpos := mul_pos (measure_part_pos P i) (measure_part_pos P j)
    rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hpos.ne'
  have hint : ∀ i j, Integrable (fun q : I × I => (P.part i).indicator (fun _ => (1 : ℝ)) q.1 *
      (P.part j).indicator (fun _ => (1 : ℝ)) q.2 * avgV P G i j)
      ((volume : Measure I).prod volume) := fun i j =>
    ((integrable_bil hone (t1_indicator (P.measurableSet_part i))
      (t1_indicator (P.measurableSet_part j))).mul_const (avgV P G i j)).congr
      (Eventually.of_forall fun q => by simp only [one_mul]; rfl)
  unfold stepAvg
  change ∫ q : I × I, ∑ i, ∑ j, (P.part i).indicator (fun _ => (1 : ℝ)) q.1 *
      (P.part j).indicator (fun _ => (1 : ℝ)) q.2 * avgV P G i j
        ∂((volume : Measure I).prod volume) = _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, hcell]
  -- reassemble
  have e2 : ∀ i j, ∫ q in P.part i ×ˢ P.part j, G q.1 q.2 =
      ∫ q : I × I, G q.1 q.2 * (P.part i).indicator 1 q.1 * (P.part j).indicator 1 q.2
        ∂((volume : Measure I).prod volume) := fun i j =>
    (bil_rect G (P.measurableSet_part i) (P.measurableSet_part j)).symm
  simp_rw [e2]
  have hint2 : ∀ i j, Integrable (fun q : I × I => G q.1 q.2 * (P.part i).indicator 1 q.1 *
      (P.part j).indicator 1 q.2) ((volume : Measure I).prod volume) := fun i j =>
    integrable_bil hG (t1_indicator (P.measurableSet_part i)) (t1_indicator (P.measurableSet_part j))
  symm
  calc ∫ q : I × I, G q.1 q.2 ∂((volume : Measure I).prod volume)
      = ∫ q : I × I, ∑ i, ∑ j, G q.1 q.2 * (P.part i).indicator 1 q.1 *
          (P.part j).indicator 1 q.2 ∂((volume : Measure I).prod volume) := by
        congr 1; funext q
        simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ind_sum_one, one_mul, mul_one]
    _ = _ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint2 i j]
        simp_rw [integral_finsetSum _ fun j _ => hint2 _ j]

lemma abs_avgV_le (F : I → I → ℝ) (i j : Fin P.k) :
    |avgV P F i j| ≤ avgV P (fun x y => |F x y|) i j := by
  unfold avgV
  have hpos := mul_pos (measure_part_pos P i) (measure_part_pos P j)
  rw [abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right (abs_integral_le_integral_abs) hpos.le

lemma bk_stepAvg {F : I → I → ℝ} (hF : BK F) : BK (stepAvg P F) := by
  obtain ⟨M, hM⟩ := hF.2
  refine ⟨measurable_stepAvg P F, M, fun x y => ?_⟩
  obtain ⟨i, hi⟩ := exists_part P x
  obtain ⟨j, hj⟩ := exists_part P y
  rw [stepAvg_eq_of_mem P F hi hj]
  refine (abs_avgV_le P F i j).trans ?_
  unfold avgV
  have hpos := mul_pos (measure_part_pos P i) (measure_part_pos P j)
  rw [div_le_iff₀ hpos]
  calc ∫ p in P.part i ×ˢ P.part j, |F p.1 p.2| ∂((volume : Measure I).prod volume)
      ≤ ∫ p in P.part i ×ˢ P.part j, M ∂((volume : Measure I).prod volume) :=
        setIntegral_mono ((integrable_bdd hF.1.abs M fun p => by
          rw [abs_abs]; exact hM _ _).integrableOn) (integrableOn_const (measure_ne_top _ _))
          fun p => hM _ _
    _ = M * _ := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Measure.prod_prod,
          ENNReal.toReal_mul, mul_comm]

lemma bk_abs {F : I → I → ℝ} (hF : BK F) : BK (fun x y => |F x y|) :=
  ⟨hF.1.abs, hF.2.choose, fun x y => by rw [abs_abs]; exact hF.2.choose_spec x y⟩

lemma integrable_bk {F : I → I → ℝ} (hF : BK F) :
    Integrable (fun q : I × I => F q.1 q.2) ((volume : Measure I).prod volume) :=
  integrable_bdd hF.1 hF.2.choose fun q => hF.2.choose_spec q.1 q.2

/-- Step averaging is an `L¹` contraction. -/
lemma integral_abs_stepAvg_le {F : I → I → ℝ} (hF : BK F) :
    ∫ q, |stepAvg P F q.1 q.2| ∂((volume : Measure I).prod volume) ≤
      ∫ q, |F q.1 q.2| ∂((volume : Measure I).prod volume) := by
  rw [← integral_stepAvg P (bk_abs hF)]
  refine integral_mono (integrable_bk (bk_abs (bk_stepAvg P hF)))
    (integrable_bk (bk_stepAvg P (bk_abs hF))) fun q => ?_
  obtain ⟨i, hi⟩ := exists_part P q.1
  obtain ⟨j, hj⟩ := exists_part P q.2
  simp only
  rw [stepAvg_eq_of_mem P _ hi hj, stepAvg_eq_of_mem P _ hi hj]
  exact abs_avgV_le P F i j

end LSC

/-- The partition of `[0,1]` into `n + 1` equal intervals. -/
noncomputable def gridPart (n : ℕ) : PosPartition (volume : Measure I) where
  k := n + 1
  part i := Section2Aux.gridIdx n ⁻¹' {i}
  measurableSet_part i := Section2Aux.measurable_gridIdx n (measurableSet_singleton _)
  pos i := Section2Aux.volume_gridIdx_pos n i
  disjoint i j hij := by
    refine Set.disjoint_left.mpr fun x hi hj => hij ?_
    simp only [mem_preimage, mem_singleton_iff] at hi hj
    rw [← hi, ← hj]
  cover := by
    ext x; simp only [mem_iUnion, mem_preimage, mem_singleton_iff, mem_univ, iff_true]
    exact ⟨_, rfl⟩

lemma stepAvg_grid (n : ℕ) (h : Fin (n + 1) → Fin (n + 1) → ℝ) :
    stepAvg (gridPart n) (fun x y => h (Section2Aux.gridIdx n x) (Section2Aux.gridIdx n y)) =
      fun x y => h (Section2Aux.gridIdx n x) (Section2Aux.gridIdx n y) := by
  funext x y
  have hx : x ∈ (gridPart n).part (Section2Aux.gridIdx n x) := rfl
  have hy : y ∈ (gridPart n).part (Section2Aux.gridIdx n y) := rfl
  rw [stepAvg_eq_of_mem _ _ hx hy]
  set i := Section2Aux.gridIdx n x
  set j := Section2Aux.gridIdx n y
  have hc : ∫ p in (gridPart n).part i ×ˢ (gridPart n).part j,
      h (Section2Aux.gridIdx n p.1) (Section2Aux.gridIdx n p.2) ∂((volume : Measure I).prod volume) =
      ∫ p in (gridPart n).part i ×ˢ (gridPart n).part j, h i j
        ∂((volume : Measure I).prod volume) :=
    setIntegral_congr_fun (((gridPart n).measurableSet_part i).prod
      ((gridPart n).measurableSet_part j)) fun q hq => by
      have h1 : Section2Aux.gridIdx n q.1 = i := hq.1
      have h2 : Section2Aux.gridIdx n q.2 = j := hq.2
      simp only [h1, h2]
  have hpos := mul_pos (measure_part_pos (gridPart n) i) (measure_part_pos (gridPart n) j)
  unfold avgV
  rw [hc, setIntegral_const, smul_eq_mul, measureReal_def, Measure.prod_prod,
    ENNReal.toReal_mul, mul_div_cancel_left₀ _ hpos.ne']

/-- For every `δ > 0` some step average of a digraphon is `δ`-close to it in `L¹` (a grid partition
works). -/
lemma exists_stepAvg_close {Z : I → I → ℝ} (hZ : IsDigraphon Z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : PosPartition (volume : Measure I),
      ∫ q, |stepAvg P Z q.1 q.2 - Z q.1 q.2| ∂((volume : Measure I).prod volume) ≤ δ := by
  obtain ⟨n, h, hmem, hclose⟩ := Section2Aux.exists_grid_approx Z hZ (half_pos hδ)
  set G : I → I → ℝ := fun x y => h (Section2Aux.gridIdx n x) (Section2Aux.gridIdx n y) with hG
  have hGd : IsDigraphon G := ⟨by
    have hm : Measurable (fun q : I × I => (Section2Aux.gridIdx n q.1, Section2Aux.gridIdx n q.2)) :=
      ((Section2Aux.measurable_gridIdx n).comp measurable_fst).prodMk
        ((Section2Aux.measurable_gridIdx n).comp measurable_snd)
    exact (measurable_of_countable (Function.uncurry h)).comp hm, fun x y => hmem _ _⟩
  have hZk := k1_bk (k1_of_mem hZ.1 hZ.2)
  have hGk := k1_bk (k1_of_mem hGd.1 hGd.2)
  have hD : BK (fun x y => Z x y - G x y) := k1_sub (k1_of_mem hZ.1 hZ.2) (k1_of_mem hGd.1 hGd.2)
  refine ⟨gridPart n, ?_⟩
  have hlin := stepAvg_lin (gridPart n) ⟨hZ.1, hZk.2⟩ ⟨hGd.1, hGk.2⟩ 1 (-1)
  rw [stepAvg_grid] at hlin
  have e : ∀ q : I × I, stepAvg (gridPart n) Z q.1 q.2 - Z q.1 q.2 =
      stepAvg (gridPart n) (fun x y => Z x y - G x y) q.1 q.2 + (G q.1 q.2 - Z q.1 q.2) := by
    intro q
    have := congrFun (congrFun hlin q.1) q.2
    have e2 : (fun x y => (1 : ℝ) * Z x y + -1 * G x y) = fun x y => Z x y - G x y := by
      funext x y; ring
    rw [e2] at this
    rw [this]; ring
  have hc1 := integral_abs_stepAvg_le (gridPart n) hD
  have hi1 := integrable_bk (bk_abs (bk_stepAvg (gridPart n) hD))
  have hi2 := integrable_bk (bk_abs (k1_sub (k1_of_mem hGd.1 hGd.2) (k1_of_mem hZ.1 hZ.2)))
  calc ∫ q, |stepAvg (gridPart n) Z q.1 q.2 - Z q.1 q.2| ∂((volume : Measure I).prod volume)
      ≤ ∫ q, (|stepAvg (gridPart n) (fun x y => Z x y - G x y) q.1 q.2| +
          |G q.1 q.2 - Z q.1 q.2|) ∂((volume : Measure I).prod volume) := by
        refine integral_mono (integrable_bk (bk_abs (k1_sub ⟨measurable_stepAvg _ _, fun x y => by
            have := (isDigraphon_stepAvg (gridPart n) hZ).2 x y
            rw [abs_le]; constructor <;> linarith [this.1, this.2]⟩
          (k1_of_mem hZ.1 hZ.2)))) (hi1.add hi2) fun q => ?_
        simp only; rw [e q]; exact abs_add_le _ _
    _ = ∫ q, |stepAvg (gridPart n) (fun x y => Z x y - G x y) q.1 q.2|
          ∂((volume : Measure I).prod volume) +
        ∫ q, |G q.1 q.2 - Z q.1 q.2| ∂((volume : Measure I).prod volume) := integral_add hi1 hi2
    _ ≤ δ / 2 + δ / 2 := by
        gcongr
        · refine hc1.trans (le_of_eq_of_le ?_ hclose)
          congr 1; funext q; rw [abs_sub_comm]
    _ = δ := by ring


section LSC2

variable {V : Type u} [Fintype V]

lemma abs_tU_sub_le (H : SimpleGraph V) {K K' : I → I → ℝ} (hK : IsDigraphon K)
    (hK' : IsDigraphon K') (sK : ∀ x y, K x y = K y x) (sK' : ∀ x y, K' x y = K' y x) :
    |tU H K - tU H K'| ≤ ((Section1Aux.orientOut H).numArcs : ℝ) *
      ∫ q, |K q.1 q.2 - K' q.1 q.2| ∂((volume : Measure I).prod volume) := by
  classical
  rw [Section1Aux.tU_eq_t H _ (Section1Aux.orientOut_underlying H) sK,
    Section1Aux.tU_eq_t H _ (Section1Aux.orientOut_underlying H) sK']
  exact Section2Aux.abs_t_sub_le _ K K' hK hK'

lemma tendsto_avgV {Zn : ℕ → I → I → ℝ} {Z : I → I → ℝ} (hw : WeakStarTendsto Zn Z)
    (P : PosPartition (volume : Measure I)) (i j : Fin P.k) :
    Tendsto (fun n => avgV P (Zn n) i j) atTop (𝓝 (avgV P Z i j)) := by
  unfold avgV
  exact (hw _ _ (P.measurableSet_part i) (P.measurableSet_part j)).div_const _

/-- **Weak\* lower semicontinuity** (tex l.1098-1110): for a step Sidorenko `H` and
everywhere-symmetric graphons `Z_n`, `Z` (`IsSymmGraphon`), if `Z_n → Z` weak\* and
`t(H, Z_n) ≤ c` for all `n`, then `t(H, Z) ≤ c`. -/
lemma tU_le_of_weakStar (H : SimpleGraph V) (hSS : IsStepSidorenko H)
    {Zn : ℕ → I → I → ℝ} {Z : I → I → ℝ} (hZn : ∀ n, IsSymmGraphon (Zn n))
    (hZ : IsSymmGraphon Z) (hw : WeakStarTendsto Zn Z) {c : ℝ}
    (hc : ∀ n, tU H (Zn n) ≤ c) : tU H Z ≤ c := by
  set N : ℝ := ((Section1Aux.orientOut H).numArcs : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hstep : ∀ P : PosPartition (volume : Measure I), tU H (stepAvg P Z) ≤ c := by
    intro P
    have hle : ∀ n, tU H (stepAvg P (Zn n)) ≤ c := fun n =>
      (hSS (Zn n) ⟨(hZn n).1, Eventually.of_forall fun q => (hZn n).2 q.1 q.2⟩ P).trans (hc n)
    refine le_of_tendsto' (f := fun n => tU H (stepAvg P (Zn n))) (x := atTop) ?_ hle
    set d : ℕ → ℝ := fun n => ∑ i, ∑ j, |avgV P (Zn n) i j - avgV P Z i j| with hd
    have hd0 : Tendsto d atTop (𝓝 0) := by
      have : Tendsto d atTop (𝓝 (∑ i : Fin P.k, ∑ j : Fin P.k, |avgV P Z i j - avgV P Z i j|)) :=
        tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
          ((tendsto_avgV hw P i j).sub tendsto_const_nhds).abs
      simpa using this
    have hbd : ∀ n, |tU H (stepAvg P (Zn n)) - tU H (stepAvg P Z)| ≤ N * d n := by
      intro n
      refine (abs_tU_sub_le H (isDigraphon_stepAvg P (hZn n).1) (isDigraphon_stepAvg P hZ.1)
        (stepAvg_symm P (hZn n).2) (stepAvg_symm P hZ.2)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hN0
      have hpt : ∀ q : I × I, |stepAvg P (Zn n) q.1 q.2 - stepAvg P Z q.1 q.2| ≤ d n := by
        intro q
        obtain ⟨i, hi⟩ := exists_part P q.1
        obtain ⟨j, hj⟩ := exists_part P q.2
        rw [stepAvg_eq_of_mem P _ hi hj, stepAvg_eq_of_mem P _ hi hj, hd]
        refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg
          fun j _ => abs_nonneg _) (Finset.mem_univ i))
        exact Finset.single_le_sum (f := fun j => |avgV P (Zn n) i j - avgV P Z i j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      have := norm_integral_le_of_norm_le_const (μ := (volume : Measure I).prod volume)
        (f := fun q : I × I => |stepAvg P (Zn n) q.1 q.2 - stepAvg P Z q.1 q.2|) (C := d n)
        (Eventually.of_forall fun q => by rw [Real.norm_eq_abs, abs_abs]; exact hpt q)
      simp only [Real.norm_eq_abs, probReal_univ, mul_one] at this
      exact (le_abs_self _).trans this
    have h0 : Tendsto (fun n => N * d n) atTop (𝓝 0) := by simpa using hd0.const_mul N
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hbd n) h0
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨P, hP⟩ := exists_stepAvg_close hZ.1 (δ := δ / (N + 1)) (by positivity)
  have h1 := abs_tU_sub_le H (isDigraphon_stepAvg P hZ.1) hZ.1 (stepAvg_symm P hZ.2) hZ.2
  have h2 : N * ∫ q, |stepAvg P Z q.1 q.2 - Z q.1 q.2| ∂((volume : Measure I).prod volume) ≤ δ := by
    calc N * _ ≤ N * (δ / (N + 1)) := mul_le_mul_of_nonneg_left hP hN0
      _ ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have := hstep P
  rw [abs_le] at h1
  linarith [h1.1]

end LSC2

/-! ## Envelopes and the cut distance under a.e. modification -/

section Envelope

lemma pullback_aeEq {U U' : I → I → ℝ} (h : AEEq volume U U') {φ : I → I}
    (hφ : MeasurePreserving φ volume volume) : AEEq volume (pullback φ U) (pullback φ U') :=
  (hφ.prod hφ).quasiMeasurePreserving.ae h

lemma envelope_congr {U U' : I → I → ℝ} (h : AEEq volume U U') : envelope U = envelope U' := by
  have key : ∀ {U U' : I → I → ℝ}, AEEq volume U U' → envelope U ⊆ envelope U' := by
    intro U U' h V ⟨hV, φ, hφ⟩
    refine ⟨hV, φ, fun A B hA hB => ?_⟩
    have e : ∀ n, ∫ p in A ×ˢ B, pullback (φ n).1 U' p.1 p.2 = ∫ p in A ×ˢ B, pullback (φ n).1 U p.1 p.2 :=
      fun n => integral_congr_ae (ae_restrict_of_ae (by
        have := pullback_aeEq h (φ n).2
        unfold AEEq at this
        filter_upwards [this] with p hp
        exact hp.symm))
    simp_rw [e]
    exact hφ A B hA hB
  exact Set.Subset.antisymm (key h) (key (aeEq_symm h))

/-- The identity as a measure-preserving bijection. -/
def idBij : MPBij := ⟨MeasurableEquiv.refl I, MeasurePreserving.id volume⟩

lemma mem_envelope_self {U : I → I → ℝ} (hU : IsGraphon volume U) : U ∈ envelope U :=
  ⟨hU, fun _ => idBij, fun _ _ _ _ => tendsto_const_nhds⟩

lemma cutNorm_congr_ae {F F' : I → I → ℝ} (h : AEEq volume F F') : cutNorm F = cutNorm F' := by
  unfold cutNorm
  congr 1
  ext r
  constructor <;> rintro ⟨S, T, hS, hT, rfl⟩ <;> refine ⟨S, T, hS, hT, ?_⟩ <;>
    congr 1 <;> refine integral_congr_ae (ae_restrict_of_ae ?_)
  · unfold AEEq at h; filter_upwards [h] with p hp; exact hp
  · unfold AEEq at h; filter_upwards [h] with p hp; exact hp.symm

lemma cutDist_congr {U U' W W' : I → I → ℝ} (hU : AEEq volume U U') (hW : AEEq volume W W') :
    cutDist U W = cutDist U' W' := by
  unfold cutDist
  congr 1
  ext r
  have key : ∀ φ : MPBij, cutNorm (fun x y => U x y - pullback φ.1 W x y) =
      cutNorm (fun x y => U' x y - pullback φ.1 W' x y) := fun φ => by
    apply cutNorm_congr_ae
    have h2 := pullback_aeEq hW φ.2
    unfold AEEq at *
    filter_upwards [hU, h2] with p h1 h2
    show U p.1 p.2 - pullback φ.1 W p.1 p.2 = U' p.1 p.2 - pullback φ.1 W' p.1 p.2
    rw [h1, h2]
  constructor <;> rintro ⟨φ, rfl⟩ <;> exact ⟨φ, by rw [key]⟩

lemma cutNorm_nonneg' (F : I → I → ℝ) : 0 ≤ cutNorm F :=
  Real.sSup_nonneg fun r ⟨_, _, _, _, hr⟩ => hr ▸ abs_nonneg _

lemma cutDist_nonneg (U W : I → I → ℝ) : 0 ≤ cutDist U W :=
  Real.sInf_nonneg fun r ⟨_, hr⟩ => hr ▸ cutNorm_nonneg' _

lemma cutDist_le (U W : I → I → ℝ) (φ : MPBij) :
    cutDist U W ≤ cutNorm (fun x y => U x y - pullback φ.1 W x y) :=
  csInf_le ⟨0, fun r ⟨_, hr⟩ => hr ▸ cutNorm_nonneg' _⟩ ⟨φ, rfl⟩

end Envelope

/-! ## Theorem 1.4 -/

section Main

variable {V : Type u} [Fintype V]

lemma isSymmGraphon_pullback {W : I → I → ℝ} (hW : IsSymmGraphon W) {φ : I → I}
    (hφ : Measurable φ) : IsSymmGraphon (pullback φ W) :=
  ⟨⟨hW.1.1.comp (hφ.prodMap hφ), fun x y => hW.1.2 _ _⟩, fun x y => hW.2 _ _⟩

lemma isSymmGraphon_mid {A B : I → I → ℝ} (hA : IsSymmGraphon A) (hB : IsSymmGraphon B) :
    IsSymmGraphon (fun x y => 1 / 2 * A x y + (1 - 1 / 2) * B x y) := by
  refine ⟨⟨(hA.1.1.const_mul _).add (hB.1.1.const_mul _), fun x y => ?_⟩, fun x y => ?_⟩
  · have := hA.1.2 x y; have := hB.1.2 x y
    simp only [mem_Icc] at *
    constructor <;> linarith
  · simp only; rw [hA.2, hB.2]

/-- The cut distance identifying half of Theorem 1.4. -/
lemma cutDistIdentifying_of_wnGraph (hA2 : DGHRRCor324Hyp.{u}) (hF218 : DGHRRFact218Hyp)
    (hFR : FRHSUThm43Hyp) (H : SimpleGraph V) (hH : IsWeaklyNormingGraph H)
    (hcyc : ¬ H.IsAcyclic) : CutDistIdentifying (tU H) := by
  classical
  intro U W hU hW hlt
  have hSS : IsStepSidorenko H :=
    Section1Aux.stepSid_of_symm (hA2 V H (Section1Aux.seminorm_of_wnGraph hH))
  obtain ⟨s, hbip, hwn⟩ := hH
  let _ := Classical.decPred s
  set E := sideEdges H s with hE
  have hcycE := not_acyclic_bip H s hbip hcyc
  have hE0 : 0 < E.card :=
    lt_of_lt_of_le (by norm_num) (Section1Aux.card_ge_three_of_cycle _ hcycE)
  obtain ⟨hU', haeU⟩ := Section1Aux.symmVersion_spec hU
  obtain ⟨hW', haeW⟩ := Section1Aux.symmVersion_spec hW
  set U' := Section1Aux.symmVersion U with hU'def
  set W' := Section1Aux.symmVersion W with hW'def
  have hlt' : envelope U' ⊂ envelope W' := by
    have h := hlt
    unfold StructLT at h
    rwa [envelope_congr haeU, envelope_congr haeW] at h
  have hgU' : IsGraphon volume U' := ⟨hU'.1, Eventually.of_forall fun p => hU'.2 p.1 p.2⟩
  obtain ⟨-, φ, hφ⟩ := hlt'.subset (mem_envelope_self hgU')
  have h218 := hF218 U' W' hU' hW' hlt'.subset
  have hε : 0 < cutDist U' W' :=
    lt_of_le_of_ne (cutDist_nonneg _ _) fun h => hlt'.not_subset (h218.mpr h.symm)
  obtain ⟨η, hη, hgap⟩ := gap_lemma E hE0 hwn hcycE hFR hε
  set Bn : ℕ → I → I → ℝ := fun n => pullback (φ n).1 W' with hBn
  have hBs : ∀ n, IsSymmGraphon (Bn n) := fun n => isSymmGraphon_pullback hW' (φ n).1.measurable
  set Zn : ℕ → I → I → ℝ := fun n x y => 1 / 2 * U' x y + (1 - 1 / 2) * Bn n x y with hZn
  have hZs : ∀ n, IsSymmGraphon (Zn n) := fun n => isSymmGraphon_mid hU' (hBs n)
  have hbound : ∀ n, tU H (Zn n) ≤ (tb E U' + tb E W') / 2 - η := by
    intro n
    have h1 := hgap U' (Bn n) hU' (hBs n) (cutDist_le U' W' (φ n))
    have h2 : tb E (Bn n) = tb E W' := tb_pullback E W' hW'.1.1 (φ n).2
    rw [tU_eq_tb H s hbip (hZs n).2]
    change tb E (fun x y => 1 / 2 * U' x y + (1 - 1 / 2) * Bn n x y) ≤ _
    unfold gapE at h1
    rw [h2] at h1
    linarith
  have hw : WeakStarTendsto Zn U' := by
    intro A B hA hB
    have hiU : IntegrableOn (fun p : I × I => U' p.1 p.2) (A ×ˢ B) :=
      (integrable_bk (k1_bk (k1_sym hU'))).integrableOn
    have hiB : ∀ n, IntegrableOn (fun p : I × I => Bn n p.1 p.2) (A ×ˢ B) := fun n =>
      (integrable_bk (k1_bk (k1_sym (hBs n)))).integrableOn
    have e : ∀ n, ∫ p in A ×ˢ B, Zn n p.1 p.2 =
        1 / 2 * (∫ p in A ×ˢ B, U' p.1 p.2) + (1 - 1 / 2) * ∫ p in A ×ˢ B, Bn n p.1 p.2 := by
      intro n
      simp only [hZn]
      rw [integral_add (hiU.const_mul _) ((hiB n).const_mul _), integral_const_mul,
        integral_const_mul]
    simp_rw [e]
    have := ((tendsto_const_nhds (x := 1 / 2 * (∫ p in A ×ˢ B, U' p.1 p.2))).add
      ((hφ A B hA hB).const_mul (1 - 1 / 2)))
    convert this using 2
    ring
  have hlsc := tU_le_of_weakStar H hSS hZs hU' hw hbound
  rw [tU_eq_tb H s hbip hU'.2] at hlsc
  rw [Section1Aux.tU_congr_ae H haeU, Section1Aux.tU_congr_ae H haeW, tU_eq_tb H s hbip hU'.2,
    tU_eq_tb H s hbip hW'.2]
  linarith

/-- **Theorem 1.4.** -/
theorem thm_1_4_proof (hA2 : DGHRRCor324Hyp.{u}) (hF218 : DGHRRFact218Hyp)
    (hFR : FRHSUThm43Hyp)
    (H : SimpleGraph V) (hH : IsWeaklyNormingGraph H) (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H :=
  ⟨cutDistIdentifying_of_wnGraph hA2 hF218 hFR H hH hcyc,
    isStepForcing_of_wnGraph hA2 H hH hcyc⟩

end Main

end S1CutDist

end NieWeiOrientedSidorenko
