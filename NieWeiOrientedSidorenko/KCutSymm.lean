import NieWeiOrientedSidorenko.Mixing

/-!
# Symmetry of the map-based cut distances (Checkpoint B, condition Q3)

Auxiliary file (no new result of the paper). It proves that the two map-based cut distances used
by `FRHSUThm43Hyp` and `FHMZCompactHyp` are symmetric:

* `cutDistMap_comm`: `δ_□^{map}(U, W) = δ_□^{map}(W, U)` for digraphons;
* `kCutDist_comm`: `δ_{□_k}(U, W) = δ_{□_k}(W, U)` for `[k]`-graphons (one map for all colours).

No literature hypothesis is used. The argument (Lovász, Large Networks, §8.2, made explicit):

1. `kc_le_add_L1`, `l1_sub_pullback`: the cut functional moves by at most the `L¹` distance, and
   `L¹` distances are invariant under measure-preserving maps.
2. `exists_grid_approx_ge`: every digraphon is `L¹`-close to a step function on every fine enough
   grid of `n + 1` equal intervals (so all colours of `U` and `W` share one grid).
3. `kc_comp_le`: for step kernels `g_i(c x, c x')` the cut functional only sees the fibre masses of
   the cell map `c`; if `d` has the same fibre masses, `kc (g ∘ d) ≤ kc (g ∘ c)`. The proof
   replaces sets by `[0,1]`-valued cell-constant tests (`sum_abs_bil_le`), so no non-atomicity
   argument is needed.
4. `exists_transport`: for every nonnegative matrix with all row and column sums `1/(n+1)` there
   is a measure-preserving piecewise translation `ψ : I → I` realising it as the overlap matrix of
   the grid with its `ψ`-preimage.
5. `kCutDist_le_swap`: given `φ`, approximate, take the overlap matrix `a` of `φ`, transport its
   transpose by `ψ`, and compare: `δ(W, U) ≤ δ(U, W) + (4k + 1)η` for every `η > 0`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko
namespace KCutSymm

/-! ## The `k`-colour cut functional -/

/-- `kc F = sup_{S,T} ∑_i |∫_{S×T} F_i|`. -/
noncomputable def kc {k : ℕ} (F : Fin k → I → I → ℝ) : ℝ :=
  sSup {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧
    r = ∑ i, |∫ p in S ×ˢ T, F i p.1 p.2|}

/-- Every colour bounded measurable. -/
def BKF {k : ℕ} (F : Fin k → I → I → ℝ) : Prop := ∀ i, S1CutDist.BK (F i)

/-- `d_{□_k}(U, W) = kc (U - W)`. -/
lemma kCutNormDist_eq (k : ℕ) (U W : Fin k → I → I → ℝ) :
    kCutNormDist k U W = kc (fun i x y => U i x y - W i x y) := rfl

/-- For bounded measurable colours the set defining `kc` is bounded above. -/
lemma kc_bdd {k : ℕ} {F : Fin k → I → I → ℝ} (hF : BKF F) :
    BddAbove {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧
      r = ∑ i, |∫ p in S ×ˢ T, F i p.1 p.2|} := by
  choose M hM using fun i => (hF i).2
  refine ⟨∑ i, M i, ?_⟩
  rintro r ⟨S, T, -, -, rfl⟩
  exact Finset.sum_le_sum fun i _ => S1CutDist.abs_setIntegral_le (hM i) _

/-- Every pair of measurable sets is a lower bound for `kc`. -/
lemma le_kc {k : ℕ} {F : Fin k → I → I → ℝ} (hF : BKF F) {S T : Set I}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∑ i, |∫ p in S ×ˢ T, F i p.1 p.2| ≤ kc F :=
  le_csSup (kc_bdd hF) ⟨S, T, hS, hT, rfl⟩

/-- `kc F ≤ c` once every pair of measurable sets gives at most `c`. -/
lemma kc_le {k : ℕ} {F : Fin k → I → I → ℝ} {c : ℝ}
    (h : ∀ S T : Set I, MeasurableSet S → MeasurableSet T →
      ∑ i, |∫ p in S ×ˢ T, F i p.1 p.2| ≤ c) : kc F ≤ c :=
  csSup_le ⟨_, ∅, ∅, MeasurableSet.empty, MeasurableSet.empty, rfl⟩
    (by rintro r ⟨S, T, hS, hT, rfl⟩; exact h S T hS hT)

/-- `kc F ≥ 0` (bounded measurable colours). -/
lemma kc_nonneg {k : ℕ} {F : Fin k → I → I → ℝ} (hF : BKF F) : 0 ≤ kc F :=
  (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans
    (le_kc hF MeasurableSet.empty MeasurableSet.empty)

/-! ## Fractional tests: `[0,1]`-valued test functions do no better than sets -/

/-- A measurable `[0,1]`-valued function is a test function bounded by one. -/
lemma t1_of_mem {f : I → ℝ} (hf : Measurable f) (h01 : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    S1CutDist.T1 f :=
  ⟨hf, fun x => by rw [abs_le]; constructor <;> linarith [(h01 x).1, (h01 x).2]⟩

/-- `sign(r) · r = |r|`. -/
lemma sgn_mul_eq (r : ℝ) : (if 0 ≤ r then (1 : ℝ) else -1) * r = |r| := by
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (not_le.mp h)]

/-- The `x`-side step: a `[0,1]`-valued test in `x` can be replaced by an indicator. -/
lemma exists_set_x {k : ℕ} {F : Fin k → I → I → ℝ} (hF : BKF F) {f g : I → ℝ}
    (hf : Measurable f) (hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hg : S1CutDist.T1 g) :
    ∃ S, MeasurableSet S ∧ ∑ i, |S1CutDist.bil (F i) f g| ≤
      ∑ i, |S1CutDist.bil (F i) (S.indicator 1) g| := by
  set sg : Fin k → ℝ := fun i => if 0 ≤ S1CutDist.bil (F i) f g then 1 else -1 with hsg
  set Φ : I → ℝ := fun x => ∑ i, sg i * ∫ y, F i x y * g y with hΦ
  have hΦm : Measurable Φ :=
    Finset.measurable_sum _ fun i _ => (S1CutDist.integrable_inner_x (hF i) hg).1.const_mul _
  have hΦi : ∀ i, Integrable (fun x => ∫ y, F i x y * g y) :=
    fun i => (S1CutDist.integrable_inner_x (hF i) hg).2
  have key : ∀ h : I → ℝ, S1CutDist.T1 h →
      ∑ i, sg i * S1CutDist.bil (F i) h g = ∫ x, h x * Φ x := by
    intro h hh
    have hint : ∀ i, Integrable (fun x => sg i * (h x * ∫ y, F i x y * g y)) := fun i =>
      ((hΦi i).bdd_mul (c := 1) hh.1.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hh.2 x)).const_mul _
    simp_rw [S1CutDist.bil_eq_x (hF _) hh hg]
    rw [show (∑ i, sg i * ∫ x, h x * ∫ y, F i x y * g y) =
        ∑ i, ∫ x, sg i * (h x * ∫ y, F i x y * g y) from
      Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm]
    rw [← integral_finsetSum _ fun i _ => hint i]
    congr 1; funext x
    simp only [hΦ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨{x | 0 < Φ x}, measurableSet_lt measurable_const hΦm, ?_⟩
  set S := {x | 0 < Φ x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hΦm
  have hfT := t1_of_mem hf hf01
  have hST := S1CutDist.t1_indicator hS
  have hΦint : Integrable Φ := integrable_finsetSum _ fun i _ => (hΦi i).const_mul _
  calc ∑ i, |S1CutDist.bil (F i) f g| = ∑ i, sg i * S1CutDist.bil (F i) f g :=
        Finset.sum_congr rfl fun i _ => (sgn_mul_eq _).symm
    _ = ∫ x, f x * Φ x := key f hfT
    _ ≤ ∫ x, S.indicator 1 x * Φ x := by
        refine integral_mono (hΦint.bdd_mul (c := 1) hf.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfT.2 x))
          (hΦint.bdd_mul (c := 1) hST.1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hST.2 x)) fun x => ?_
        by_cases hx : 0 < Φ x
        · have : x ∈ S := hx
          simp only [Set.indicator, this, ite_true, Pi.one_apply, one_mul]
          nlinarith [(hf01 x).2]
        · have : x ∉ S := hx
          simp only [Set.indicator, this, ite_false, zero_mul]
          nlinarith [(hf01 x).1, not_lt.mp hx]
    _ = ∑ i, sg i * S1CutDist.bil (F i) (S.indicator 1) g := (key _ hST).symm
    _ ≤ ∑ i, |S1CutDist.bil (F i) (S.indicator 1) g| :=
        Finset.sum_le_sum fun i _ => by
          simp only [hsg]
          split_ifs with h
          · rw [one_mul]; exact le_abs_self _
          · rw [neg_one_mul]; exact neg_le_abs _

/-- `∫ F(x,y) f(x) g(y) = ∫ Fᵀ(y,x) g(y) f(x)`. -/
lemma bil_swap (F : I → I → ℝ) (f g : I → ℝ) :
    S1CutDist.bil F f g = S1CutDist.bil (fun y x => F x y) g f := by
  unfold S1CutDist.bil
  rw [← integral_prod_swap]
  congr 1; funext p; simp only [Prod.fst_swap, Prod.snd_swap]; ring

/-- Transposing every colour keeps it bounded measurable. -/
lemma bkf_swap {k : ℕ} {F : Fin k → I → I → ℝ} (hF : BKF F) : BKF (fun i y x => F i x y) :=
  fun i => ⟨(hF i).1.comp measurable_swap, (hF i).2.choose, fun y x => (hF i).2.choose_spec x y⟩

/-- `[0,1]`-valued tests: `∑_i |∫ F_i(x,y) f(x) g(y)| ≤ kc F`. -/
lemma sum_abs_bil_le {k : ℕ} {F : Fin k → I → I → ℝ} (hF : BKF F) {f g : I → ℝ}
    (hf : Measurable f) (hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    ∑ i, |S1CutDist.bil (F i) f g| ≤ kc F := by
  obtain ⟨S, hS, h1⟩ := exists_set_x hF hf hf01 (t1_of_mem hg hg01)
  obtain ⟨T, hT, h2⟩ := exists_set_x (bkf_swap hF) hg hg01
    (S1CutDist.t1_indicator hS)
  calc ∑ i, |S1CutDist.bil (F i) f g| ≤ ∑ i, |S1CutDist.bil (F i) (S.indicator 1) g| := h1
    _ = ∑ i, |S1CutDist.bil (fun y x => F i x y) g (S.indicator 1)| := by
        simp_rw [bil_swap (F _) _ g]
    _ ≤ ∑ i, |S1CutDist.bil (fun y x => F i x y) (T.indicator 1) (S.indicator 1)| := h2
    _ = ∑ i, |∫ p in S ×ˢ T, F i p.1 p.2| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← bil_swap, S1CutDist.bil_rect _ hS hT]
    _ ≤ kc F := le_kc hF hS hT

/-! ## Step kernels -/

section Step

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The integral of `v(e x, e y) a(x) b(y)` for a finite-valued `e`. -/
lemma integral_step {e : I → ι} (he : Measurable e) (v : ι → ι → ℝ) {a b : I → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ha1 : ∀ x, |a x| ≤ 1) (hb1 : ∀ x, |b x| ≤ 1) :
    ∫ q : I × I, v (e q.1) (e q.2) * a q.1 * b q.2 ∂((volume : Measure I).prod volume) =
      ∑ α, ∑ β, v α β * (∫ x in e ⁻¹' {α}, a x) * (∫ y in e ⁻¹' {β}, b y) := by
  classical
  have hfib : ∀ α, MeasurableSet (e ⁻¹' {α}) := fun α => he (measurableSet_singleton α)
  have hpt : ∀ q : I × I, v (e q.1) (e q.2) * a q.1 * b q.2 =
      ∑ α, ∑ β, v α β * ((e ⁻¹' {α}).indicator a q.1 * (e ⁻¹' {β}).indicator b q.2) := by
    intro q
    simp only [Set.indicator, mem_preimage, mem_singleton_iff]
    simp only [mul_ite, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_eq_single (e q.1) (fun α _ hα => by
      refine Finset.sum_eq_zero fun β _ => ?_
      split_ifs with h1 h2 <;> first | rfl | exact absurd h2.symm hα)
      (by simp)]
    rw [Finset.sum_eq_single (e q.2) (fun β _ hβ => by
      split_ifs with h1 h2 <;> first | rfl | exact absurd h1.symm hβ)
      (by simp)]
    simp only [ite_true]; ring
  have hind : ∀ (s : Set I), MeasurableSet s → ∀ {c : I → ℝ}, Measurable c → (∀ x, |c x| ≤ 1) →
      Measurable (s.indicator c) ∧ ∀ x, |s.indicator c x| ≤ 1 := by
    intro s hs c hc hc1
    refine ⟨hc.indicator hs, fun x => ?_⟩
    by_cases hx : x ∈ s
    · simp [Set.indicator, hx, hc1 x]
    · simp [Set.indicator, hx]
  have hterm : ∀ α β, Integrable (fun q : I × I =>
      v α β * ((e ⁻¹' {α}).indicator a q.1 * (e ⁻¹' {β}).indicator b q.2))
      ((volume : Measure I).prod volume) := by
    intro α β
    obtain ⟨hA, hA1⟩ := hind _ (hfib α) ha ha1
    obtain ⟨hB, hB1⟩ := hind _ (hfib β) hb hb1
    refine (S1CutDist.integrable_bdd ((hA.comp measurable_fst).mul (hB.comp measurable_snd)) 1
      fun q => ?_).const_mul _
    show |(e ⁻¹' {α}).indicator a q.1 * (e ⁻¹' {β}).indicator b q.2| ≤ 1
    rw [abs_mul]
    nlinarith [hA1 q.1, hB1 q.2, abs_nonneg ((e ⁻¹' {α}).indicator a q.1),
      abs_nonneg ((e ⁻¹' {β}).indicator b q.2)]
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hterm α β]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finsetSum _ fun β _ => hterm α β]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_const_mul, integral_prod_mul, integral_indicator (hfib α),
    integral_indicator (hfib β)]
  ring

/-- A step kernel `v(e x, e y)` with finite-valued measurable `e` is bounded measurable. -/
lemma bk_step {e : I → ι} (he : Measurable e) (v : ι → ι → ℝ) :
    S1CutDist.BK (fun x y => v (e x) (e y)) := by
  refine ⟨?_, ∑ α, ∑ β, |v α β|, fun x y => ?_⟩
  · exact (measurable_of_finite (Function.uncurry v)).comp
      ((he.comp measurable_fst).prodMk (he.comp measurable_snd))
  · calc |v (e x) (e y)| ≤ ∑ β, |v (e x) β| :=
          Finset.single_le_sum (f := fun β => |v (e x) β|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ _)
      _ ≤ ∑ α, ∑ β, |v α β| :=
          Finset.single_le_sum (f := fun α => ∑ β, |v α β|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

/-- `∫_A 1_S = λ(S ∩ A)`. -/
lemma integral_ind_mem {A S : Set I} (_hA : MeasurableSet A) (hS : MeasurableSet S) :
    ∫ x in A, S.indicator (1 : I → ℝ) x = (volume : Measure I).real (S ∩ A) := by
  rw [integral_indicator_one hS, measureReal_restrict_apply hS]

/-- **Transfer of step kernels.** If `c, d : I → ι` have the same fibre masses, the cut functional
of `(g_i(d y, d y'))_i` is at most that of `(g_i(c x, c x'))_i`. -/
lemma kc_comp_le {c d : I → ι} (hc : Measurable c) (hd : Measurable d)
    (hcd : ∀ α, (volume : Measure I) (c ⁻¹' {α}) = volume (d ⁻¹' {α})) {k : ℕ}
    (g : Fin k → ι → ι → ℝ) :
    kc (fun i y y' => g i (d y) (d y')) ≤ kc (fun i x x' => g i (c x) (c x')) := by
  have hcf : ∀ α, MeasurableSet (c ⁻¹' {α}) := fun α => hc (measurableSet_singleton α)
  have hdf : ∀ α, MeasurableSet (d ⁻¹' {α}) := fun α => hd (measurableSet_singleton α)
  have hreal : ∀ α, (volume : Measure I).real (c ⁻¹' {α}) = volume.real (d ⁻¹' {α}) := by
    intro α; simp only [measureReal_def, hcd α]
  refine kc_le fun S T hS hT => ?_
  -- the fractional tests
  let s : Set I → ι → ℝ := fun A α =>
    (∫ x in d ⁻¹' {α}, A.indicator 1 x) / (volume : Measure I).real (c ⁻¹' {α})
  have hs01 : ∀ A, MeasurableSet A → ∀ α, s A α ∈ Icc (0 : ℝ) 1 := by
    intro A hA α
    simp only [s]
    rw [integral_ind_mem (hdf α) hA]
    refine ⟨div_nonneg measureReal_nonneg measureReal_nonneg, ?_⟩
    rcases eq_or_lt_of_le (measureReal_nonneg (μ := (volume : Measure I)) (s := c ⁻¹' {α}))
      with h0 | hpos
    · rw [← h0, div_zero]; exact zero_le_one
    · rw [div_le_one hpos, hreal α]; exact measureReal_mono inter_subset_right
  have hsint : ∀ A, MeasurableSet A → ∀ α,
      ∫ x in c ⁻¹' {α}, s A (c x) = ∫ x in d ⁻¹' {α}, A.indicator 1 x := by
    intro A hA α
    rw [setIntegral_congr_fun (hcf α) (fun x hx => by
      rw [show c x = α from hx])]
    rw [setIntegral_const, smul_eq_mul]
    simp only [s]
    rcases eq_or_lt_of_le (measureReal_nonneg (μ := (volume : Measure I)) (s := c ⁻¹' {α}))
      with h0 | hpos
    · rw [← h0, zero_mul, integral_ind_mem (hdf α) hA]
      rw [hreal α] at h0
      exact (measureReal_mono_null inter_subset_right h0.symm).symm
    · field_simp
  have hfm : ∀ A, Measurable (fun x => s A (c x)) := fun A =>
    (measurable_of_finite (s A)).comp hc
  have hbk : BKF (fun i x x' => g i (c x) (c x')) := fun i => bk_step hc (g i)
  have hab : ∀ A, MeasurableSet A → ∀ x, |s A (c x)| ≤ 1 := fun A hA x => by
    rw [abs_le]; constructor <;> linarith [(hs01 A hA (c x)).1, (hs01 A hA (c x)).2]
  have hind1 : ∀ A, MeasurableSet A → ∀ x, |A.indicator (1 : I → ℝ) x| ≤ 1 := fun A hA x =>
    (S1CutDist.t1_indicator hA).2 x
  calc ∑ i, |∫ p in S ×ˢ T, g i (d p.1) (d p.2)|
      = ∑ i, |S1CutDist.bil (fun x x' => g i (c x) (c x')) (fun x => s S (c x))
          (fun x => s T (c x))| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← S1CutDist.bil_rect (fun y y' => g i (d y) (d y')) hS hT]
        unfold S1CutDist.bil
        rw [integral_step hd (g i) (measurable_one.indicator hS) (measurable_one.indicator hT)
          (hind1 S hS) (hind1 T hT),
          integral_step hc (g i) (hfm S) (hfm T) (hab S hS) (hab T hT)]
        simp_rw [hsint S hS, hsint T hT]
    _ ≤ _ := sum_abs_bil_le hbk (hfm S) (fun x => hs01 S hS _) (hfm T) (fun x => hs01 T hT _)

end Step

/-! ## `L¹` control -/

/-- `kc F ≥ 0` (no hypotheses: `sSup` of a set of nonnegative reals). -/
lemma kc_nonneg' {k : ℕ} (F : Fin k → I → I → ℝ) : 0 ≤ kc F :=
  Real.sSup_nonneg (by rintro _ ⟨S, T, -, -, rfl⟩; exact Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- `kc (-F) = kc F`. -/
lemma kc_neg {k : ℕ} (F : Fin k → I → I → ℝ) : kc (fun i x y => -F i x y) = kc F := by
  unfold kc
  congr 1
  ext r
  simp only [integral_neg, abs_neg]

/-- A bounded measurable kernel is integrable on `I × I`. -/
lemma integrable_bk {F : I → I → ℝ} (hF : S1CutDist.BK F) :
    Integrable (fun q : I × I => F q.1 q.2) ((volume : Measure I).prod volume) :=
  S1CutDist.integrable_bdd hF.1 hF.2.choose fun q => hF.2.choose_spec q.1 q.2

/-- The difference of two bounded measurable kernels is bounded measurable. -/
lemma bk_sub {F G : I → I → ℝ} (hF : S1CutDist.BK F) (hG : S1CutDist.BK G) :
    S1CutDist.BK (fun x y => F x y - G x y) := by
  obtain ⟨M, hM⟩ := hF.2
  obtain ⟨N, hN⟩ := hG.2
  exact ⟨hF.1.sub hG.1, M + N, fun x y => (abs_sub _ _).trans (add_le_add (hM x y) (hN x y))⟩

/-- `kc C ≤ kc A + ∑_i ‖C_i - A_i‖₁`. -/
lemma kc_le_add_L1 {k : ℕ} {A C : Fin k → I → I → ℝ} (hA : BKF A) (hC : BKF C) :
    kc C ≤ kc A + ∑ i, ∫ q, |C i q.1 q.2 - A i q.1 q.2| ∂((volume : Measure I).prod volume) := by
  refine kc_le fun S T hS hT => ?_
  have h1 : ∀ i, |∫ p in S ×ˢ T, C i p.1 p.2| ≤ |∫ p in S ×ˢ T, A i p.1 p.2| +
      ∫ q, |C i q.1 q.2 - A i q.1 q.2| ∂((volume : Measure I).prod volume) := by
    intro i
    have hCi : Integrable (fun q : I × I => C i q.1 q.2) volume := integrable_bk (hC i)
    have hAi : Integrable (fun q : I × I => A i q.1 q.2) volume := integrable_bk (hA i)
    have hD : Integrable (fun q : I × I => C i q.1 q.2 - A i q.1 q.2) volume :=
      integrable_bk (bk_sub (hC i) (hA i))
    have e : ∫ p in S ×ˢ T, C i p.1 p.2 = (∫ p in S ×ˢ T, A i p.1 p.2) +
        ∫ p in S ×ˢ T, (C i p.1 p.2 - A i p.1 p.2) := by
      rw [integral_sub hCi.integrableOn hAi.integrableOn]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (abs_integral_le_integral_abs).trans ?_
    exact setIntegral_le_integral hD.abs (Eventually.of_forall fun _ => abs_nonneg _)
  calc ∑ i, |∫ p in S ×ˢ T, C i p.1 p.2| ≤ ∑ i, (|∫ p in S ×ˢ T, A i p.1 p.2| +
        ∫ q, |C i q.1 q.2 - A i q.1 q.2| ∂((volume : Measure I).prod volume)) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = _ := by rw [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (le_kc hA hS hT) le_rfl

/-- Change of variables under `(x, y) ↦ (ψ x, ψ y)` for measure-preserving `ψ`. -/
lemma integral_pullback {ψ : I → I} (hψ : MeasurePreserving ψ volume volume) {F : I × I → ℝ}
    (hF : Measurable F) :
    ∫ q, F (ψ q.1, ψ q.2) ∂((volume : Measure I).prod volume) =
      ∫ q, F q ∂((volume : Measure I).prod volume) := by
  have h2 := hψ.prod hψ
  have := integral_map (μ := (volume : Measure I).prod volume) h2.measurable.aemeasurable
    (f := F) hF.aestronglyMeasurable
  rw [h2.map_eq] at this
  rw [this]; rfl

/-- `‖(A' - B'^φ) - (A - B^φ)‖₁ ≤ ‖A' - A‖₁ + ‖B' - B‖₁`. -/
lemma l1_sub_pullback {φ : I → I} (hφ : MeasurePreserving φ volume volume) {A A' B B' : I → I → ℝ}
    (hA : S1CutDist.BK A) (hA' : S1CutDist.BK A') (hB : S1CutDist.BK B) (hB' : S1CutDist.BK B') :
    ∫ q, |(A' q.1 q.2 - B' (φ q.1) (φ q.2)) - (A q.1 q.2 - B (φ q.1) (φ q.2))|
        ∂((volume : Measure I).prod volume) ≤
      ∫ q, |A' q.1 q.2 - A q.1 q.2| ∂((volume : Measure I).prod volume) +
      ∫ q, |B' q.1 q.2 - B q.1 q.2| ∂((volume : Measure I).prod volume) := by
  have hBB := bk_sub hB' hB
  have hm : Measurable fun q : I × I => |B' q.1 q.2 - B q.1 q.2| := hBB.1.abs
  rw [← integral_pullback hφ hm]
  have i1 := (integrable_bk (bk_sub hA' hA)).abs
  have hBφ : S1CutDist.BK (fun x y => B' (φ x) (φ y) - B (φ x) (φ y)) :=
    ⟨hBB.1.comp (hφ.measurable.prodMap hφ.measurable), hBB.2.choose,
      fun x y => hBB.2.choose_spec _ _⟩
  have i2 := (integrable_bk hBφ).abs
  rw [← integral_add i1 i2]
  have hAll : S1CutDist.BK (fun x y => (A' x y - B' (φ x) (φ y)) - (A x y - B (φ x) (φ y))) := by
    have := bk_sub (bk_sub hA' hA) hBφ
    refine ⟨?_, this.2.choose, fun x y => ?_⟩
    · have e : (Function.uncurry fun x y => (A' x y - B' (φ x) (φ y)) - (A x y - B (φ x) (φ y)))
          = Function.uncurry fun x y => (A' x y - A x y) - (B' (φ x) (φ y) - B (φ x) (φ y)) := by
        funext q; simp only [Function.uncurry]; ring
      rw [e]; exact this.1
    · have := this.2.choose_spec x y
      calc _ = |(A' x y - A x y) - (B' (φ x) (φ y) - B (φ x) (φ y))| := by ring_nf
        _ ≤ _ := this
  refine integral_mono (integrable_bk hAll).abs (i1.add i2) fun q => ?_
  dsimp only
  calc |(A' q.1 q.2 - B' (φ q.1) (φ q.2)) - (A q.1 q.2 - B (φ q.1) (φ q.2))|
      = |(A' q.1 q.2 - A q.1 q.2) - (B' (φ q.1) (φ q.2) - B (φ q.1) (φ q.2))| := by ring_nf
    _ ≤ _ := abs_sub _ _

/-! ## Grid intervals -/

/-- The half-open interval `[a, b)` of `I`. -/
def ico (a b : ℝ) : Set I := {y | a ≤ (y : ℝ) ∧ (y : ℝ) < b}

/-- `[a, b) ∩ I` is measurable. -/
lemma measurableSet_ico (a b : ℝ) : MeasurableSet (ico a b) :=
  (measurableSet_le measurable_const measurable_subtype_coe).inter
    (measurableSet_lt measurable_subtype_coe measurable_const)

/-- The real image of `[a, b) ∩ I` is `[a, b)` when `0 ≤ a` and `b ≤ 1`. -/
lemma image_ico {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) : Subtype.val '' ico a b = Ico a b := by
  ext t; constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨t, ha.trans h1, h2.le.trans hb⟩, ⟨h1, h2⟩, rfl⟩

/-- `λ([a, b) ∩ I) = b - a` when `0 ≤ a` and `b ≤ 1`. -/
lemma volume_ico {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (volume : Measure I) (ico a b) = ENNReal.ofReal (b - a) := by
  rw [unitInterval.volume_apply, image_ico ha hb, Real.volume_Ico]

/-- Consecutive half-open intervals are disjoint. -/
lemma disjoint_ico {a b a' b' : ℝ} (h : b ≤ a') : Disjoint (ico a b) (ico a' b') :=
  Set.disjoint_left.2 fun _ h1 h2 => by linarith [h1.2, h2.1]

/-- Points of `[p/(n+1), (p+1)/(n+1))` lie in grid cell `p`. -/
lemma gridIdx_eq {n : ℕ} {p : Fin (n + 1)} {y : I}
    (hy : y ∈ ico ((p : ℝ) / (n + 1)) (((p : ℝ) + 1) / (n + 1))) :
    Section2Aux.gridIdx n y = p := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  obtain ⟨h1, h2⟩ := hy
  rw [div_le_iff₀ hn] at h1
  rw [lt_div_iff₀ hn] at h2
  have hfl : ⌊(y : ℝ) * (n + 1)⌋₊ = p := by
    rw [Nat.floor_eq_iff (by nlinarith [y.2.1])]
    constructor <;> linarith
  simp only [Section2Aux.gridIdx, Fin.ext_iff, hfl]
  exact min_eq_left (Nat.lt_succ_iff.1 p.2)

/-- The left end of a grid cell is nonnegative. -/
lemma cell_lo_nonneg {n : ℕ} (p : Fin (n + 1)) : 0 ≤ (p : ℝ) / (n + 1) := by positivity

/-- The right end of a grid cell is at most one. -/
lemma cell_hi_le {n : ℕ} (p : Fin (n + 1)) : ((p : ℝ) + 1) / (n + 1) ≤ 1 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_one hn]
  have : (p : ℝ) + 1 ≤ n + 1 := by have := p.2; exact_mod_cast this
  linarith

/-- If `f ≤ g` termwise and `∑ g ≤ ∑ f < ∞`, then `f = g`. -/
lemma eq_of_le_of_sum {κ : Type*} [Fintype κ] {f g : κ → ENNReal} (hle : ∀ i, f i ≤ g i)
    (hsum : ∑ i, g i ≤ ∑ i, f i) (hfin : ∑ i, f i ≠ ⊤) (i : κ) : f i = g i := by
  have hg : ∀ j, g j ≠ ⊤ := fun j => ne_top_of_le_ne_top (ne_top_of_le_ne_top hfin hsum)
    (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j))
  have hf : ∀ j, f j ≠ ⊤ := fun j => ne_top_of_le_ne_top (hg j) (hle j)
  have hs : ∑ j, (f j).toReal = ∑ j, (g j).toReal := by
    rw [← ENNReal.toReal_sum (fun j _ => hf j), ← ENNReal.toReal_sum (fun j _ => hg j)]
    congr 1; exact le_antisymm (Finset.sum_le_sum fun j _ => hle j) hsum
  have := (Finset.sum_eq_sum_iff_of_le (fun j _ =>
    (ENNReal.toReal_le_toReal (hf j) (hg j)).2 (hle j))).1 hs i (Finset.mem_univ i)
  exact (ENNReal.toReal_eq_toReal_iff' (hf i) (hg i)).1 this

/-- `∑_{p ≤ n} 1/(n+1) = 1`. -/
lemma sum_ofReal_const (n : ℕ) :
    ∑ _p : Fin (n + 1), ENNReal.ofReal (1 / ((n : ℝ) + 1)) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_one_div_cancel (by positivity), ENNReal.ofReal_one]

/-- The fibres of a finite-valued measurable map have total mass one. -/
lemma sum_preimage {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : I → κ} (he : Measurable e) : ∑ i, (volume : Measure I) (e ⁻¹' {i}) = 1 := by
  rw [sum_measure_preimage_singleton Finset.univ (fun i _ => he (measurableSet_singleton i)),
    Finset.coe_univ, preimage_univ, measure_univ]

/-- Every grid cell has measure `1/(n+1)`. -/
lemma volume_gridIdx (n : ℕ) (p : Fin (n + 1)) :
    (volume : Measure I) (Section2Aux.gridIdx n ⁻¹' {p}) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  have hle : ∀ p : Fin (n + 1), ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤
      (volume : Measure I) (Section2Aux.gridIdx n ⁻¹' {p}) := by
    intro p
    have h := volume_ico (cell_lo_nonneg p) (cell_hi_le p)
    rw [show ((p : ℝ) + 1) / (n + 1) - p / (n + 1) = 1 / (n + 1) by ring] at h
    rw [← h]
    exact measure_mono fun y hy => gridIdx_eq hy
  refine (eq_of_le_of_sum hle ?_ ?_ p).symm
  · rw [sum_preimage (Section2Aux.measurable_gridIdx n), sum_ofReal_const]
  · rw [sum_ofReal_const]; exact ENNReal.one_ne_top

/-! ## Measure-preserving maps glued from pieces -/

/-- A measurable map that sends each piece `R i` of a partition of `I` (up to a null set) measure-preservingly onto the piece `E i` of another such partition is measure-preserving. -/
lemma mp_of_pieces {κ : Type*} [Fintype κ] {ψ : I → I} (hψ : Measurable ψ) {R E : κ → Set I}
    (hR : ∀ i, MeasurableSet (R i)) (hE : ∀ i, MeasurableSet (E i))
    (hRd : Pairwise (Function.onFun Disjoint R)) (hEd : Pairwise (Function.onFun Disjoint E))
    (hRs : ∑ i, (volume : Measure I) (R i) = 1) (hEs : ∑ i, (volume : Measure I) (E i) = 1)
    (h : ∀ i S, MeasurableSet S → (volume : Measure I) (R i ∩ ψ ⁻¹' S) = volume (E i ∩ S)) :
    MeasurePreserving ψ volume volume := by
  refine ⟨hψ, Measure.ext fun S hS => ?_⟩
  rw [Measure.map_apply hψ hS]
  have hnull : ∀ {F : κ → Set I}, (∀ i, MeasurableSet (F i)) → Pairwise (Function.onFun Disjoint F) →
      ∑ i, (volume : Measure I) (F i) = 1 → (volume : Measure I) (⋃ i, F i)ᶜ = 0 := by
    intro F hF hFd hFs
    rw [measure_compl (MeasurableSet.iUnion hF) (measure_ne_top _ _), measure_iUnion hFd hF,
      tsum_fintype, hFs, measure_univ, tsub_self]
  have hsplit : ∀ {F : κ → Set I}, (∀ i, MeasurableSet (F i)) → Pairwise (Function.onFun Disjoint F) →
      ∑ i, (volume : Measure I) (F i) = 1 → ∀ A : Set I, MeasurableSet A →
      (volume : Measure I) A = ∑ i, volume (F i ∩ A) := by
    intro F hF hFd hFs A hA
    rw [← measure_inter_conull (s := A) (hnull hF hFd hFs), inter_iUnion,
      measure_iUnion (fun i j hij => ((hFd hij).mono inter_subset_right inter_subset_right))
        (fun i => hA.inter (hF i)), tsum_fintype]
    exact Finset.sum_congr rfl fun i _ => by rw [inter_comm]
  rw [hsplit hR hRd hRs _ (hψ hS), hsplit hE hEd hEs _ hS]
  exact Finset.sum_congr rfl fun i _ => h i S hS

/-! ## The transport map -/

section Transport

variable {n : ℕ}

/-- `lo b p q = p/(n+1) + ∑_{q' < q} b p q'`. -/
noncomputable def lo (b : Fin (n + 1) → Fin (n + 1) → ℝ) (p q : Fin (n + 1)) : ℝ :=
  (p : ℝ) / (n + 1) + ∑ q' ∈ Finset.univ.filter (fun x => x < q), b p q'

/-- The piece `[lo b p q, lo b p q + b p q)` of the `p`-th grid cell. -/
noncomputable def piece (b : Fin (n + 1) → Fin (n + 1) → ℝ) (p q : Fin (n + 1)) : Set I :=
  ico (lo b p q) (lo b p q + b p q)

/-- The pieces are measurable. -/
lemma measurableSet_piece (b : Fin (n + 1) → Fin (n + 1) → ℝ) (p q : Fin (n + 1)) :
    MeasurableSet (piece b p q) := measurableSet_ico _ _

/-- `∑_{q' < q} b q' + b q ≤ ∑_{s} b` for nonnegative `b` and `{q' ≤ q} ⊆ s`. -/
lemma sum_lt_add_le {b : Fin (n + 1) → ℝ} (hb : ∀ q, 0 ≤ b q) {q : Fin (n + 1)}
    {s : Finset (Fin (n + 1))} (hq : q ∈ s) (hs : Finset.univ.filter (fun x => x < q) ⊆ s) :
    ∑ q' ∈ Finset.univ.filter (fun x => x < q), b q' + b q ≤ ∑ q' ∈ s, b q' := by
  have hnot : q ∉ Finset.univ.filter (fun x => x < q) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.insert_subset hq hs) (fun _ _ _ => hb _)

variable {b : Fin (n + 1) → Fin (n + 1) → ℝ}

/-- A piece of cell `p` starts at or after `p/(n+1)`. -/
lemma lo_ge (hb0 : ∀ p q, 0 ≤ b p q) (p q : Fin (n + 1)) : (p : ℝ) / (n + 1) ≤ lo b p q :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => hb0 _ _)

/-- A piece of cell `p` ends at or before `(p+1)/(n+1)`. -/
lemma hi_le (hb0 : ∀ p q, 0 ≤ b p q) (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1)) (p q : Fin (n + 1)) :
    lo b p q + b p q ≤ ((p : ℝ) + 1) / (n + 1) := by
  have := sum_lt_add_le (hb0 p) (Finset.mem_univ q) (Finset.subset_univ _)
  rw [hrow p] at this
  unfold lo
  rw [add_div]
  linarith

/-- A piece starts at a nonnegative point. -/
lemma lo_nonneg (hb0 : ∀ p q, 0 ≤ b p q) (p q : Fin (n + 1)) : 0 ≤ lo b p q :=
  (cell_lo_nonneg p).trans (lo_ge hb0 p q)

/-- A piece ends at or before one. -/
lemma hi_le_one (hb0 : ∀ p q, 0 ≤ b p q) (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1))
    (p q : Fin (n + 1)) : lo b p q + b p q ≤ 1 :=
  (hi_le hb0 hrow p q).trans (cell_hi_le p)

/-- The piece `(p, q)` has measure `b p q`. -/
lemma volume_piece (hb0 : ∀ p q, 0 ≤ b p q) (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1))
    (p q : Fin (n + 1)) : (volume : Measure I) (piece b p q) = ENNReal.ofReal (b p q) := by
  rw [piece, volume_ico (lo_nonneg hb0 p q) (hi_le_one hb0 hrow p q), add_sub_cancel_left]

/-- The piece `(p, q)` lies in grid cell `p`. -/
lemma piece_sub (hb0 : ∀ p q, 0 ≤ b p q) (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1))
    (p q : Fin (n + 1)) : piece b p q ⊆ Section2Aux.gridIdx n ⁻¹' {p} := fun _ hy =>
  gridIdx_eq ⟨(lo_ge hb0 p q).trans hy.1, hy.2.trans_le (hi_le hb0 hrow p q)⟩

/-- Pieces in lexicographic order are disjoint. -/
lemma piece_disj_lt (hb0 : ∀ p q, 0 ≤ b p q) (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1))
    {p p' q q' : Fin (n + 1)} (h : p < p' ∨ (p = p' ∧ q < q')) :
    Disjoint (piece b p q) (piece b p' q') := by
  refine disjoint_ico ?_
  rcases h with h | ⟨rfl, h⟩
  · refine (hi_le hb0 hrow p q).trans ((?_ : ((p : ℝ) + 1) / (n + 1) ≤ p' / (n + 1)).trans
      (lo_ge hb0 p' q'))
    have : (p : ℝ) + 1 ≤ p' := by
      have : (p : ℕ) + 1 ≤ p' := h
      exact_mod_cast this
    exact div_le_div_of_nonneg_right this (by positivity)
  · have := sum_lt_add_le (hb0 p) (s := Finset.univ.filter (fun x => x < q'))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩) (fun x hx => by simp at hx ⊢; exact hx.trans h)
    unfold lo
    linarith

/-- Distinct pieces are disjoint. -/
lemma piece_disj (hb0 : ∀ p q, 0 ≤ b p q) (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1))
    {p p' q q' : Fin (n + 1)} (h : (p, q) ≠ (p', q')) :
    Disjoint (piece b p q) (piece b p' q') := by
  rcases lt_trichotomy p p' with hp | rfl | hp
  · exact piece_disj_lt hb0 hrow (Or.inl hp)
  · rcases lt_trichotomy q q' with hq | rfl | hq
    · exact piece_disj_lt hb0 hrow (Or.inr ⟨rfl, hq⟩)
    · exact absurd rfl h
    · exact (piece_disj_lt hb0 hrow (Or.inr ⟨rfl, hq⟩)).symm
  · exact (piece_disj_lt hb0 hrow (Or.inl hp)).symm

/-- The transpose. -/
def bt (b : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin (n + 1) → Fin (n + 1) → ℝ := fun q p => b p q

/-- The translation of the piece `(p, q)`. -/
noncomputable def tau (b : Fin (n + 1) → Fin (n + 1) → ℝ) (p q : Fin (n + 1)) : ℝ :=
  lo (bt b) q p - lo b p q

/-- The transport map, as a real function. -/
noncomputable def psi0 (b : Fin (n + 1) → Fin (n + 1) → ℝ) (y : I) : ℝ :=
  (y : ℝ) + ∑ κ : Fin (n + 1) × Fin (n + 1), (piece b κ.1 κ.2).indicator (fun _ => tau b κ.1 κ.2) y

/-- The transport map `ψ : I → I`: on the piece `(p, q)` of cell `p` it translates onto the piece
`(q, p)` of cell `q` of the transposed matrix. -/
noncomputable def psi (b : Fin (n + 1) → Fin (n + 1) → ℝ) (y : I) : I :=
  projIcc 0 1 zero_le_one (psi0 b y)

/-- The transport map is measurable. -/
lemma measurable_psi (b : Fin (n + 1) → Fin (n + 1) → ℝ) : Measurable (psi b) := by
  refine continuous_projIcc.measurable.comp ?_
  exact measurable_subtype_coe.add (Finset.measurable_sum _ fun κ _ =>
    measurable_const.indicator (measurableSet_ico _ _))

variable (hb0 : ∀ p q, 0 ≤ b p q) (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1))
  (hcol : ∀ q, ∑ p, b p q = 1 / (n + 1))
include hb0 hrow

/-- On the piece `(p, q)` the real transport map is translation by `tau b p q`. -/
lemma psi0_eq {p q : Fin (n + 1)} {y : I} (hy : y ∈ piece b p q) : psi0 b y = y + tau b p q := by
  unfold psi0
  congr 1
  rw [Finset.sum_eq_single (p, q) (fun κ _ hκ => ?_) (by simp)]
  · simp [Set.indicator, hy]
  · have hne : (κ.1, κ.2) ≠ (p, q) := by simpa using hκ
    exact Set.indicator_of_notMem (Set.disjoint_left.1 (piece_disj hb0 hrow hne).symm hy) _

include hcol

/-- On the piece `(p, q)` the transport map is translation by `tau b p q`, onto the piece `(q, p)` of the transposed matrix. -/
lemma psi_spec {p q : Fin (n + 1)} {y : I} (hy : y ∈ piece b p q) :
    ((psi b y : I) : ℝ) = y + tau b p q ∧ psi b y ∈ piece (bt b) q p := by
  have hb0' : ∀ q p, 0 ≤ bt b q p := fun q p => hb0 p q
  have hrow' : ∀ q, ∑ p, bt b q p = 1 / (n + 1) := hcol
  have h1 : lo (bt b) q p ≤ (y : ℝ) + tau b p q := by unfold tau; linarith [hy.1]
  have h2 : (y : ℝ) + tau b p q < lo (bt b) q p + bt b q p := by
    unfold tau; simp only [bt]; linarith [hy.2]
  have hmem : (y : ℝ) + tau b p q ∈ Icc (0 : ℝ) 1 :=
    ⟨(lo_nonneg hb0' q p).trans h1, h2.le.trans (hi_le_one hb0' hrow' q p)⟩
  have hv : ((psi b y : I) : ℝ) = y + tau b p q := by
    unfold psi; rw [psi0_eq hb0 hrow hy, projIcc_of_mem _ hmem]
  exact ⟨hv, by show lo (bt b) q p ≤ _ ∧ _; rw [hv]; exact ⟨h1, h2⟩⟩

/-- The transport map sends the piece `(p, q)` measure-preservingly onto the piece `(q, p)` of the transposed matrix. -/
lemma piece_preimage (p q : Fin (n + 1)) {S : Set I} :
    (volume : Measure I) (piece b p q ∩ psi b ⁻¹' S) = volume (piece (bt b) q p ∩ S) := by
  have hb0' : ∀ q p, 0 ≤ bt b q p := fun q p => hb0 p q
  have hrow' : ∀ q, ∑ p, bt b q p = 1 / (n + 1) := hcol
  rw [unitInterval.volume_apply, unitInterval.volume_apply]
  have e2 : Subtype.val '' (piece (bt b) q p ∩ S) =
      Ico (lo (bt b) q p) (lo (bt b) q p + b p q) ∩ Subtype.val '' S := by
    rw [image_inter Subtype.val_injective, piece,
      image_ico (lo_nonneg hb0' q p) (hi_le_one hb0' hrow' q p)]
    rfl
  have e1 : Subtype.val '' (piece b p q ∩ psi b ⁻¹' S) = (fun t => t + tau b p q) ⁻¹'
      (Ico (lo (bt b) q p) (lo (bt b) q p + b p q) ∩ Subtype.val '' S) := by
    ext t; constructor
    · rintro ⟨y, ⟨hy, hyS⟩, rfl⟩
      obtain ⟨hv, hmem⟩ := psi_spec hb0 hrow hcol hy
      refine ⟨?_, ⟨psi b y, hyS, hv⟩⟩
      show (y : ℝ) + tau b p q ∈ _
      rw [← hv]; exact hmem
    · rintro ⟨⟨h1, h2⟩, ⟨z, hz, hzt⟩⟩
      have h1' : lo b p q ≤ t := by unfold tau at h1; linarith
      have h2' : t < lo b p q + b p q := by unfold tau at h2; linarith
      have ht : t ∈ Icc (0 : ℝ) 1 :=
        ⟨(lo_nonneg hb0 p q).trans h1', h2'.le.trans (hi_le_one hb0 hrow p q)⟩
      have hy : (⟨t, ht⟩ : I) ∈ piece b p q := ⟨h1', h2'⟩
      have hpz : psi b ⟨t, ht⟩ = z := by
        apply Subtype.ext
        rw [(psi_spec hb0 hrow hcol hy).1, hzt]
      exact ⟨⟨t, ht⟩, ⟨hy, show psi b ⟨t, ht⟩ ∈ S from hpz ▸ hz⟩, rfl⟩
  rw [e1, e2, measure_preimage_add_right]

omit hcol in
/-- The pieces have total mass one. -/
lemma sum_volume_piece :
    ∑ κ : Fin (n + 1) × Fin (n + 1), (volume : Measure I) (piece b κ.1 κ.2) = 1 := by
  simp_rw [volume_piece hb0 hrow]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hb0 _ _), Fintype.sum_prod_type]
  simp_rw [hrow]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_one_div_cancel (by positivity), ENNReal.ofReal_one]

end Transport

/-- **The transport map.** For a nonnegative matrix `b` on the grid of `n + 1` equal intervals with
all row and column sums `1/(n+1)` there is a measure-preserving `ψ : I → I` with
`λ{y : y ∈ cell p, ψ y ∈ cell q} = b p q`. -/
theorem exists_transport {n : ℕ} (b : Fin (n + 1) → Fin (n + 1) → ℝ) (hb0 : ∀ p q, 0 ≤ b p q)
    (hrow : ∀ p, ∑ q, b p q = 1 / (n + 1)) (hcol : ∀ q, ∑ p, b p q = 1 / (n + 1)) :
    ∃ ψ : I → I, MeasurePreserving ψ volume volume ∧ ∀ p q,
      (volume : Measure I) {y | Section2Aux.gridIdx n y = p ∧ Section2Aux.gridIdx n (ψ y) = q} =
        ENNReal.ofReal (b p q) := by
  have hb0' : ∀ q p, 0 ≤ bt b q p := fun q p => hb0 p q
  have hrow' : ∀ q, ∑ p, bt b q p = 1 / (n + 1) := hcol
  have hmp : MeasurePreserving (psi b) volume volume := by
    have hs1 : ∑ κ : Fin (n + 1) × Fin (n + 1), (volume : Measure I) (piece b κ.1 κ.2) = 1 :=
      sum_volume_piece hb0 hrow
    have hpre : ∀ (κ : Fin (n + 1) × Fin (n + 1)) (S : Set I), MeasurableSet S →
        (volume : Measure I) (piece b κ.1 κ.2 ∩ psi b ⁻¹' S) =
          volume (piece (bt b) κ.2 κ.1 ∩ S) :=
      fun κ S _ => piece_preimage hb0 hrow hcol κ.1 κ.2
    refine mp_of_pieces (κ := Fin (n + 1) × Fin (n + 1)) (measurable_psi b) (R := fun κ => piece b κ.1 κ.2)
      (E := fun κ => piece (bt b) κ.2 κ.1) (fun κ => measurableSet_piece b κ.1 κ.2)
      (fun κ => measurableSet_piece (bt b) κ.2 κ.1) ?_ ?_ hs1 ?_ hpre
    · intro κ κ' h
      exact piece_disj hb0 hrow (by simpa using h)
    · intro κ κ' h
      refine piece_disj hb0' hrow' ?_
      intro h'
      apply h
      simp only [Prod.mk.injEq] at h'
      exact Prod.ext h'.2 h'.1
    · have : ∀ κ : Fin (n + 1) × Fin (n + 1), (volume : Measure I) (piece (bt b) κ.2 κ.1) =
          volume (piece b κ.1 κ.2) := fun κ => by
        rw [volume_piece hb0' hrow', volume_piece hb0 hrow]; rfl
      simp only [this]; exact hs1
  refine ⟨psi b, hmp, fun p q => ?_⟩
  set e : I → Fin (n + 1) × Fin (n + 1) := fun y =>
    (Section2Aux.gridIdx n y, Section2Aux.gridIdx n (psi b y)) with he
  have hem : Measurable e :=
    (Section2Aux.measurable_gridIdx n).prodMk ((Section2Aux.measurable_gridIdx n).comp hmp.1)
  have hset : ∀ κ : Fin (n + 1) × Fin (n + 1), e ⁻¹' {κ} =
      {y | Section2Aux.gridIdx n y = κ.1 ∧ Section2Aux.gridIdx n (psi b y) = κ.2} := by
    intro κ; ext y; simp [he, Prod.ext_iff]
  have hle : ∀ κ : Fin (n + 1) × Fin (n + 1),
      (volume : Measure I) (piece b κ.1 κ.2) ≤ volume (e ⁻¹' {κ}) := by
    intro κ
    refine measure_mono fun y hy => ?_
    rw [hset]
    refine ⟨piece_sub hb0 hrow _ _ hy, ?_⟩
    exact piece_sub hb0' hrow' _ _ (psi_spec hb0 hrow hcol hy).2
  have := eq_of_le_of_sum hle (by rw [sum_preimage hem, sum_volume_piece hb0 hrow])
    (by rw [sum_volume_piece hb0 hrow]; exact ENNReal.one_ne_top) (p, q)
  rw [← volume_piece hb0 hrow, this, hset]

/-! ## Grid approximation -/

/-- Every digraphon is `L¹`-approximated by grid step functions on every fine enough grid (the
proof of `Section2Aux.exists_grid_approx`, with the grid size left free above a threshold). -/
lemma exists_grid_approx_ge (U : I → I → ℝ) (hU : IsDigraphon U) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ h : Fin (n + 1) → Fin (n + 1) → ℝ,
      ∫ q, |h (Section2Aux.gridIdx n q.1) (Section2Aux.gridIdx n q.2) - U q.1 q.2| ∂((volume : Measure I).prod volume)
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
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hNn => ⟨fun i j => c (Section2Aux.gridPt n i, Section2Aux.gridPt n j), ?_⟩⟩
  have hn : 1 / ((n : ℝ) + 1) < δ := lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity)
    (by have : (N : ℝ) ≤ n := by exact_mod_cast hNn
        linarith)) hN
  have hpt : ∀ q : I × I, |c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) - c q| ≤ ε / 2 := by
    intro q
    have hd : dist (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) q < δ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_comm]; exact (Section2Aux.dist_gridPt_le n q.1).trans_lt hn
      · rw [dist_comm]; exact (Section2Aux.dist_gridPt_le n q.2).trans_lt hn
    exact (hδc hd).le
  have hgm : Measurable fun q : I × I => c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) := by
    have : (fun q : I × I => c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2))) =
        (fun ij : Fin (n + 1) × Fin (n + 1) => c (Section2Aux.gridPt n ij.1, Section2Aux.gridPt n ij.2)) ∘
          (fun q : I × I => (Section2Aux.gridIdx n q.1, Section2Aux.gridIdx n q.2)) := rfl
    rw [this]
    exact (measurable_of_finite _).comp ((Section2Aux.measurable_gridIdx n).comp measurable_fst |>.prodMk
      ((Section2Aux.measurable_gridIdx n).comp measurable_snd))
  have hb : ∀ {f : I × I → ℝ}, Measurable f → (∀ q, |f q| ≤ 2) →
      Integrable f ((volume : Measure I).prod volume) := fun hf hfb =>
    Integrable.of_bound hf.aestronglyMeasurable 2 (Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]; exact hfb q)
  have hcm : Measurable c := hcc.measurable
  have i1 : Integrable (fun q : I × I =>
      |c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) - c q|)
      ((volume : Measure I).prod volume) := hb ((hgm.sub hcm).abs) fun q => by
    show |(|c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) - c q|)| ≤ 2
    rw [abs_abs, abs_le]; constructor <;> linarith [(hc01 q).1, (hc01 q).2,
      (hc01 (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2))).1,
      (hc01 (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2))).2]
  have i2 : Integrable (fun q : I × I => |c q - U q.1 q.2|)
      ((volume : Measure I).prod volume) := hb ((hcm.sub hU.1).abs) fun q => by
    show |(|c q - U q.1 q.2|)| ≤ 2
    rw [abs_abs, abs_le]; constructor <;> linarith [(hc01 q).1, (hc01 q).2, (hU.2 q.1 q.2).1,
      (hU.2 q.1 q.2).2]
  have i3 : Integrable (fun q : I × I => ‖U q.1 q.2 - g q‖) ((volume : Measure I).prod volume) :=
    (hUi.sub hgi).norm
  calc ∫ q, |c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) - U q.1 q.2|
        ∂((volume : Measure I).prod volume)
      ≤ ∫ q, (|c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) - c q| + |c q - U q.1 q.2|)
          ∂((volume : Measure I).prod volume) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (i1.add i2)
          (Eventually.of_forall fun q => ?_)
        have := abs_sub_le (c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2))) (c q)
          (U q.1 q.2)
        exact this
    _ = ∫ q, |c (Section2Aux.gridPt n (Section2Aux.gridIdx n q.1), Section2Aux.gridPt n (Section2Aux.gridIdx n q.2)) - c q|
          ∂((volume : Measure I).prod volume) +
        ∫ q, |c q - U q.1 q.2| ∂((volume : Measure I).prod volume) := integral_add i1 i2
    _ ≤ ∫ _q, ε / 2 ∂((volume : Measure I).prod volume) +
        ∫ q, ‖U q.1 q.2 - g q‖ ∂((volume : Measure I).prod volume) := by
        refine add_le_add (integral_mono i1 (integrable_const _) hpt)
          (integral_mono i2 i3 fun q => ?_)
        rw [Real.norm_eq_abs, abs_sub_comm (U q.1 q.2)]
        exact Section2Aux.clamp_dist _ _ (hU.2 _ _)
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add (by simp) hg
    _ = ε := by ring


/-! ## Assembly -/

/-- A digraphon is a bounded measurable kernel. -/
lemma bk_of_digraphon {F : I → I → ℝ} (hF : IsDigraphon F) : S1CutDist.BK F :=
  ⟨hF.1, 1, fun x y => abs_le.2 ⟨by linarith [(hF.2 x y).1], (hF.2 x y).2⟩⟩

/-- Pullbacks of bounded measurable kernels along measurable maps are bounded measurable. -/
lemma bk_pullback {F : I → I → ℝ} (hF : S1CutDist.BK F) {φ : I → I} (hφ : Measurable φ) :
    S1CutDist.BK (fun x y => F (φ x) (φ y)) :=
  ⟨hF.1.comp (hφ.prodMap hφ), hF.2.choose, fun _ _ => hF.2.choose_spec _ _⟩

/-- `∑_q λ{e₁ = p, e₂ = q} = λ{e₁ = p}`. -/
lemma sum_fiber {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e₁ e₂ : I → κ} (_he₁ : Measurable e₁) (he₂ : Measurable e₂) (p : κ) :
    ∑ q, (volume : Measure I) {x | e₁ x = p ∧ e₂ x = q} = volume (e₁ ⁻¹' {p}) := by
  have h := sum_measure_preimage_singleton (μ := (volume : Measure I).restrict (e₁ ⁻¹' {p}))
    Finset.univ (fun q _ => he₂ (measurableSet_singleton q))
  rw [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Measure.restrict_apply (he₂ (measurableSet_singleton q))]
  congr 1; ext x; simp [and_comm]

/-- Every colour of a `[k]`-graphon is a digraphon. -/
lemma isDigraphon_coord {k : ℕ} {U : Fin k → I → I → ℝ} (hU : IsKGraphon k U) (i : Fin k) :
    IsDigraphon (U i) := by
  refine ⟨hU.1 i, fun x y => ⟨hU.2.1 i x y, ?_⟩⟩
  have := Finset.single_le_sum (f := fun j => U j x y) (fun j _ => hU.2.1 j x y)
    (Finset.mem_univ i)
  rw [hU.2.2.1 x y] at this
  exact this

/-- **One direction of symmetry.** For families of digraphons, `δ_{□_k}(W, U) ≤ δ_{□_k}(U, W)`. -/
theorem kCutDist_le_swap {k : ℕ} {U W : Fin k → I → I → ℝ} (hU : ∀ i, IsDigraphon (U i))
    (hW : ∀ i, IsDigraphon (W i)) : kCutDist k W U ≤ kCutDist k U W := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η : ℝ := ε / (4 * k + 1) with hη
  have hη0 : 0 < η := by positivity
  have hηε : (4 * k + 1) * η = ε := by rw [hη]; field_simp
  -- a near-optimal map `φ` for `δ(U, W)`
  obtain ⟨φ, hφ, hlt⟩ : ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      kCutNormDist k U (fun i => pullback φ (W i)) < kCutDist k U W + η := by
    have hne : Set.Nonempty {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
        r = kCutNormDist k U (fun i => pullback φ (W i))} := ⟨_, id, MeasurePreserving.id _, rfl⟩
    obtain ⟨_, ⟨φ, hφ, rfl⟩, h⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ hη0)
    exact ⟨φ, hφ, h⟩
  -- a common grid on which every colour of `U` and `W` is `η`-approximated in `L¹`
  choose NU hNU using fun i => exists_grid_approx_ge (U i) (hU i) hη0
  choose NW hNW using fun i => exists_grid_approx_ge (W i) (hW i) hη0
  set n : ℕ := ∑ i, (NU i + NW i) with hn
  have hNUn : ∀ i, NU i ≤ n := fun i => (Nat.le_add_right _ _).trans
    (Finset.single_le_sum (f := fun i => NU i + NW i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hNWn : ∀ i, NW i ≤ n := fun i => (Nat.le_add_left _ _).trans
    (Finset.single_le_sum (f := fun i => NU i + NW i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  choose u hu using fun i => hNU i n (hNUn i)
  choose w hw using fun i => hNW i n (hNWn i)
  set g : I → Fin (n + 1) := Section2Aux.gridIdx n with hgdef
  have hg : Measurable g := Section2Aux.measurable_gridIdx n
  -- the overlap matrix of `φ` and its transport map
  set a : Fin (n + 1) → Fin (n + 1) → ℝ := fun p q =>
    ((volume : Measure I) {x | g x = p ∧ g (φ x) = q}).toReal with ha
  have hrowa : ∀ p, ∑ q, a p q = 1 / (n + 1) := by
    intro p
    rw [ha]; dsimp only
    rw [← ENNReal.toReal_sum (fun q _ => measure_ne_top _ _), sum_fiber (e₂ := fun x => g (φ x)) hg (hg.comp hφ.1),
      volume_gridIdx, ENNReal.toReal_ofReal (by positivity)]
  have hcola : ∀ q, ∑ p, a p q = 1 / (n + 1) := by
    intro q
    rw [ha]; dsimp only
    rw [← ENNReal.toReal_sum (fun q _ => measure_ne_top _ _)]
    have e : ∀ p, (volume : Measure I) {x | g x = p ∧ g (φ x) = q} =
        volume {x | g (φ x) = q ∧ g x = p} := fun p => by simp only [and_comm]
    simp_rw [e]
    rw [sum_fiber (e₁ := fun x => g (φ x)) (hg.comp hφ.1) hg,
      show (fun x => g (φ x)) ⁻¹' {q} = φ ⁻¹' (g ⁻¹' {q}) from rfl, hφ.measure_preimage
      (hg (measurableSet_singleton q)).nullMeasurableSet, volume_gridIdx,
      ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨ψ, hψ, hψlaw⟩ := exists_transport (fun q p => a p q)
    (fun _ _ => ENNReal.toReal_nonneg) hcola hrowa
  -- the cell maps
  set c : I → Fin (n + 1) × Fin (n + 1) := fun x => (g x, g (φ x)) with hc
  set d : I → Fin (n + 1) × Fin (n + 1) := fun y => (g (ψ y), g y) with hd
  have hcm : Measurable c := hg.prodMk (hg.comp hφ.1)
  have hdm : Measurable d := (hg.comp hψ.1).prodMk hg
  have hcd : ∀ α, (volume : Measure I) (c ⁻¹' {α}) = volume (d ⁻¹' {α}) := by
    rintro ⟨p, q⟩
    have e1 : c ⁻¹' {(p, q)} = {x | g x = p ∧ g (φ x) = q} := by
      ext x; simp [hc, Prod.ext_iff]
    have e2 : d ⁻¹' {(p, q)} = {y | g y = q ∧ g (ψ y) = p} := by
      ext y; simp [hd, Prod.ext_iff, and_comm]
    rw [e1, e2, hψlaw q p, ha, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- the step kernel
  set v : Fin k → (Fin (n + 1) × Fin (n + 1)) → (Fin (n + 1) × Fin (n + 1)) → ℝ :=
    fun i α β => u i α.1 β.1 - w i α.2 β.2 with hv
  have hUb : ∀ i, S1CutDist.BK (U i) := fun i => bk_of_digraphon (hU i)
  have hWb : ∀ i, S1CutDist.BK (W i) := fun i => bk_of_digraphon (hW i)
  have hub : ∀ i, S1CutDist.BK (fun x y => u i (g x) (g y)) := fun i => bk_step hg (u i)
  have hwb : ∀ i, S1CutDist.BK (fun x y => w i (g x) (g y)) := fun i => bk_step hg (w i)
  -- step A: `kc(v ∘ c) ≤ δ(U, W) + η + 2kη`
  have hA : kc (fun i x x' => v i (c x) (c x')) ≤
      kCutNormDist k U (fun i => pullback φ (W i)) + k * (2 * η) := by
    rw [kCutNormDist_eq]
    refine (kc_le_add_L1 (fun i => bk_sub (hUb i) (bk_pullback (hWb i) hφ.1))
      (fun i => bk_step hcm (v i))).trans (add_le_add le_rfl ?_)
    calc _ ≤ ∑ _i : Fin k, (2 * η) := Finset.sum_le_sum fun i _ => by
          have := l1_sub_pullback hφ (hUb i) (hub i) (hWb i) (hwb i)
          refine le_trans (le_of_eq ?_) (this.trans (by linarith [hu i, hw i]))
          rfl
      _ = k * (2 * η) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- step B: transfer to the transposed cells
  have hB : kc (fun i y y' => -v i (d y) (d y')) ≤ kc (fun i x x' => v i (c x) (c x')) := by
    have := kc_comp_le hcm hdm hcd (fun i α β => -v i α β)
    rwa [kc_neg (fun i x x' => v i (c x) (c x'))] at this
  -- step C: back to `W - U^ψ`
  have hC : kCutNormDist k W (fun i => pullback ψ (U i)) ≤
      kc (fun i y y' => -v i (d y) (d y')) + k * (2 * η) := by
    rw [kCutNormDist_eq]
    refine (kc_le_add_L1 (fun i => bk_step hdm (fun α β => -v i α β))
      (fun i => bk_sub (hWb i) (bk_pullback (hUb i) hψ.1))).trans (add_le_add le_rfl ?_)
    calc _ ≤ ∑ _i : Fin k, (2 * η) := Finset.sum_le_sum fun i _ => by
          have := l1_sub_pullback hψ (hWb i) (hwb i) (hUb i) (hub i)
          refine le_trans (le_of_eq ?_) (this.trans (by linarith [hu i, hw i]))
          refine integral_congr_ae (Eventually.of_forall fun q => ?_)
          simp only [hv, hd]
          rw [abs_sub_comm]; ring_nf
      _ = k * (2 * η) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbdd : BddBelow {r | ∃ ψ : I → I, MeasurePreserving ψ volume volume ∧
      r = kCutNormDist k W (fun i => pullback ψ (U i))} :=
    ⟨0, by rintro _ ⟨ψ, _, rfl⟩; rw [kCutNormDist_eq]; exact kc_nonneg' _⟩
  have hfin : kCutDist k W U ≤ kCutNormDist k W (fun i => pullback ψ (U i)) :=
    csInf_le hbdd ⟨ψ, hψ, rfl⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [hfin, hC, hB, hA, hlt, hηε]

/-! ## Symmetry -/

/-- **Symmetry of `δ_{□_k}`** (Checkpoint B condition Q3, symmetry half, `k`-colour version): for
`[k]`-graphons `U, W`, `δ_{□_k}(U, W) = δ_{□_k}(W, U)`, where `δ_{□_k}` is the infimum over one
measure-preserving map `φ : [0,1] → [0,1]` acting on all colours of `d_{□_k}(U, W^φ)`. -/
theorem kCutDist_comm {k : ℕ} {U W : Fin k → I → I → ℝ} (hU : IsKGraphon k U)
    (hW : IsKGraphon k W) : kCutDist k U W = kCutDist k W U :=
  le_antisymm (kCutDist_le_swap (isDigraphon_coord hW) (isDigraphon_coord hU))
    (kCutDist_le_swap (isDigraphon_coord hU) (isDigraphon_coord hW))

/-- The cut norm of `U - V` is the one-colour `d_{□_1}` of `U` and `V`. -/
lemma cutNorm_eq_kCutNormDist_one (U V : I → I → ℝ) :
    cutNorm (fun x y => U x y - V x y) = kCutNormDist 1 (fun _ => U) (fun _ => V) := by
  unfold cutNorm kCutNormDist
  simp only [Fin.sum_univ_one]

/-- `δ_□^{map}(U, W)` is the one-colour `δ_{□_1}` of `U` and `W`. -/
lemma cutDistMap_eq_kCutDist_one (U W : I → I → ℝ) :
    cutDistMap U W = kCutDist 1 (fun _ => U) (fun _ => W) := by
  unfold cutDistMap kCutDist
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, rfl⟩; exact ⟨φ, hφ, cutNorm_eq_kCutNormDist_one U (pullback φ W)⟩
  · rintro ⟨φ, hφ, rfl⟩; exact ⟨φ, hφ, (cutNorm_eq_kCutNormDist_one U (pullback φ W)).symm⟩

/-- **Symmetry of `δ_□^{map}`** (Checkpoint B condition Q3, symmetry half): for digraphons `U, W`,
`δ_□^{map}(U, W) = δ_□^{map}(W, U)`, where `δ_□^{map}(U, W)` is the infimum over
measure-preserving maps `φ : [0,1] → [0,1]` of `‖U - W^φ‖_□`. -/
theorem cutDistMap_comm {U W : I → I → ℝ} (hU : IsDigraphon U) (hW : IsDigraphon W) :
    cutDistMap U W = cutDistMap W U := by
  rw [cutDistMap_eq_kCutDist_one, cutDistMap_eq_kCutDist_one]
  exact le_antisymm (kCutDist_le_swap (fun _ => hW) (fun _ => hU))
    (kCutDist_le_swap (fun _ => hU) (fun _ => hW))

end KCutSymm
end NieWeiOrientedSidorenko
