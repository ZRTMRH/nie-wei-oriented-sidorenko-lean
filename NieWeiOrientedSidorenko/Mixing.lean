import NieWeiOrientedSidorenko.Witnesses

/-!
# An explicit mixing sequence of measure-preserving bijections

For `p ≥ 1` cut `[0, 1)` into `p²` half-open blocks `[m/p², (m+1)/p²)`, `m = i·p + j`, and let
`φ_p` translate block `(i, j)` onto block `(j, i)` (fixing the point `1`). This is a measurable,
measure-preserving involution of `I = [0,1]`, and `∫_A φ_p → |A|/2` for every measurable `A`
(proved on the π-system `{[0, a]}` by explicit block estimates, then extended by the π-λ
theorem). Consequently `W^{φ_p} → ∫ W` weak* for `W(x, y) = (x + y)/2`, which removes the
literature hypothesis from the `StructLT` witness of `Witnesses.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace NieWeiOrientedSidorenko

namespace Witnesses

namespace Mixing

/-! ## The index transposition `i·p + j ↦ j·p + i` -/

/-- The transposition of base-`p` digits of `m < p²`. -/
def tr (p m : ℕ) : ℕ := (m % p) * p + m / p

lemma tr_lt {p m : ℕ} (hm : m < p * p) : tr p m < p * p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have h1 : m % p + 1 ≤ p := Nat.mod_lt _ hp
  have h2 : m / p < p := (Nat.div_lt_iff_lt_mul hp).2 hm
  unfold tr
  calc m % p * p + m / p < m % p * p + p := by omega
    _ = (m % p + 1) * p := by ring
    _ ≤ p * p := Nat.mul_le_mul_right _ h1

lemma tr_mod {p m : ℕ} (hm : m < p * p) : tr p m % p = m / p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have h2 : m / p < p := (Nat.div_lt_iff_lt_mul hp).2 hm
  unfold tr
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]

lemma tr_div {p m : ℕ} (hm : m < p * p) : tr p m / p = m % p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have h2 : m / p < p := (Nat.div_lt_iff_lt_mul hp).2 hm
  unfold tr
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h2, zero_add]

lemma tr_tr {p m : ℕ} (hm : m < p * p) : tr p (tr p m) = m := by
  show tr p m % p * p + tr p m / p = m
  rw [tr_mod hm, tr_div hm]
  exact Nat.div_add_mod' m p

/-! ## The piecewise translation on `ℝ` -/

/-- The block `[m/p², (m+1)/p²)`. -/
noncomputable def blk (p m : ℕ) : Set ℝ := Ico ((m : ℝ) / ((p : ℝ) * p)) (((m : ℝ) + 1) / ((p : ℝ) * p))

/-- The block index `⌊p² x⌋`. -/
noncomputable def idx (p : ℕ) (x : ℝ) : ℕ := ⌊((p : ℝ) * p) * x⌋₊

/-- The piecewise translation: block `m` is moved onto block `tr p m`; identity off `[0,1)`. -/
noncomputable def g (p : ℕ) (x : ℝ) : ℝ :=
  if x ∈ Ico (0 : ℝ) 1 then
    x + (tr p (idx p x) : ℝ) / ((p : ℝ) * p) - (idx p x : ℝ) / ((p : ℝ) * p)
  else x

variable {p : ℕ}

lemma N_pos (hp : 0 < p) : (0 : ℝ) < (p : ℝ) * p := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  positivity

lemma mem_blk_iff (hp : 0 < p) (m : ℕ) (x : ℝ) :
    x ∈ blk p m ↔ (m : ℝ) ≤ ((p : ℝ) * p) * x ∧ ((p : ℝ) * p) * x < m + 1 := by
  have hN := N_pos hp
  simp only [blk, mem_Ico, div_le_iff₀ hN, lt_div_iff₀ hN]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma idx_of_mem (hp : 0 < p) {m : ℕ} {x : ℝ} (hx : x ∈ blk p m) : idx p x = m := by
  rw [mem_blk_iff hp] at hx
  have hN := N_pos hp
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact (Nat.floor_eq_iff (by linarith)).2 hx

lemma blk_subset (hp : 0 < p) {m : ℕ} (hm : m < p * p) : blk p m ⊆ Ico 0 1 := by
  intro x hx
  rw [mem_blk_iff hp] at hx
  have hN := N_pos hp
  have hm' : (m : ℝ) + 1 ≤ (p : ℝ) * p := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith

lemma mem_blk_idx (hp : 0 < p) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    x ∈ blk p (idx p x) ∧ idx p x < p * p := by
  have hN := N_pos hp
  have h0 : 0 ≤ ((p : ℝ) * p) * x := mul_nonneg hN.le hx.1
  refine ⟨(mem_blk_iff hp _ _).2 ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩, ?_⟩
  have : ((p : ℝ) * p) * x < (p : ℝ) * p := by nlinarith [hx.2]
  have := (Nat.floor_lt h0).2 (by exact_mod_cast this : ((p : ℝ) * p) * x < ((p * p : ℕ) : ℝ))
  exact this

lemma g_of_mem (hp : 0 < p) {m : ℕ} (hm : m < p * p) {x : ℝ} (hx : x ∈ blk p m) :
    g p x = x + (tr p m : ℝ) / ((p : ℝ) * p) - (m : ℝ) / ((p : ℝ) * p) := by
  simp only [g, blk_subset hp hm hx, ite_true, idx_of_mem hp hx]

lemma mem_blk_shift (p m m' : ℕ) (x : ℝ) :
    x + (m' : ℝ) / ((p : ℝ) * p) - (m : ℝ) / ((p : ℝ) * p) ∈ blk p m' ↔ x ∈ blk p m := by
  simp only [blk, mem_Ico, add_div]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma g_mem_blk (hp : 0 < p) {m : ℕ} (hm : m < p * p) {x : ℝ} (hx : x ∈ blk p m) :
    g p x ∈ blk p (tr p m) := by
  rw [g_of_mem hp hm hx, mem_blk_shift]; exact hx

lemma g_g (hp : 0 < p) (x : ℝ) : g p (g p x) = x := by
  by_cases hx : x ∈ Ico (0 : ℝ) 1
  · obtain ⟨hb, hm⟩ := mem_blk_idx hp hx
    have h1 := g_mem_blk hp hm hb
    rw [g_of_mem hp (tr_lt hm) h1, tr_tr hm, g_of_mem hp hm hb]
    ring
  · have e : g p x = x := by simp [g, hx]
    rw [e, e]

lemma g_mem_Ico (hp : 0 < p) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : g p x ∈ Ico (0 : ℝ) 1 := by
  obtain ⟨hb, hm⟩ := mem_blk_idx hp hx
  exact blk_subset hp (tr_lt hm) (g_mem_blk hp hm hb)

lemma g_mem_Icc (hp : 0 < p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : g p x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : x ∈ Ico (0 : ℝ) 1
  · exact Ico_subset_Icc_self (g_mem_Ico hp h)
  · have e : g p x = x := by simp [g, h]
    rw [e]; exact hx

lemma measurable_g (p : ℕ) : Measurable (g p) := by
  unfold g
  refine Measurable.ite measurableSet_Ico ?_ measurable_id
  have hi : Measurable (idx p) := Nat.measurable_floor.comp (measurable_const.mul measurable_id)
  exact (measurable_id.add ((measurable_from_nat (f := fun k => (tr p k : ℝ) / ((p : ℝ) * p))).comp
    hi)).sub ((measurable_from_nat (f := fun k => (k : ℝ) / ((p : ℝ) * p))).comp hi)

/-! ## Measure preservation on `ℝ` -/

lemma blk_disj (hp : 0 < p) : Pairwise (Function.onFun Disjoint (blk p)) := by
  intro m m' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x h1 h2
  exact hne ((idx_of_mem hp h1).symm.trans (idx_of_mem hp h2))

lemma Ico_eq_biUnion (hp : 0 < p) :
    Ico (0 : ℝ) 1 = ⋃ m ∈ Finset.range (p * p), blk p m := by
  ext x
  simp only [mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro hx; exact ⟨_, (mem_blk_idx hp hx).2, (mem_blk_idx hp hx).1⟩
  · rintro ⟨m, hm, hx⟩; exact blk_subset hp hm hx

lemma vol_inter_Ico (hp : 0 < p) (U : Set ℝ) (hU : MeasurableSet U) :
    volume (U ∩ Ico 0 1) = ∑ m ∈ Finset.range (p * p), volume (U ∩ blk p m) := by
  rw [Ico_eq_biUnion hp, Set.inter_iUnion₂]
  exact measure_biUnion_finset
    (fun m _ m' _ h => (blk_disj hp h).mono inf_le_right inf_le_right)
    (fun m _ => hU.inter measurableSet_Ico)

lemma preim_blk (hp : 0 < p) {m : ℕ} (hm : m < p * p) (T : Set ℝ) :
    g p ⁻¹' T ∩ blk p m =
      (fun x => x + ((tr p m : ℝ) / ((p : ℝ) * p) - (m : ℝ) / ((p : ℝ) * p))) ⁻¹'
        (T ∩ blk p (tr p m)) := by
  ext x
  simp only [mem_inter_iff, mem_preimage]
  have e : x + ((tr p m : ℝ) / ((p : ℝ) * p) - (m : ℝ) / ((p : ℝ) * p)) =
      x + (tr p m : ℝ) / ((p : ℝ) * p) - (m : ℝ) / ((p : ℝ) * p) := by ring
  rw [e, mem_blk_shift]
  constructor
  · rintro ⟨h1, h2⟩; rw [← g_of_mem hp hm h2]; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; rw [← g_of_mem hp hm h2] at h1; exact ⟨h1, h2⟩

lemma vol_preim (hp : 0 < p) (T : Set ℝ) (hT : MeasurableSet T) :
    volume (g p ⁻¹' T ∩ Ico 0 1) = volume (T ∩ Ico 0 1) := by
  rw [vol_inter_Ico hp _ ((measurable_g p) hT), vol_inter_Ico hp _ hT]
  rw [Finset.sum_congr rfl (fun m hm => by
    rw [preim_blk hp (Finset.mem_range.1 hm), measure_preimage_add_right])]
  exact Finset.sum_nbij' (tr p) (tr p)
    (fun m hm => Finset.mem_range.2 (tr_lt (Finset.mem_range.1 hm)))
    (fun m hm => Finset.mem_range.2 (tr_lt (Finset.mem_range.1 hm)))
    (fun m hm => tr_tr (Finset.mem_range.1 hm)) (fun m hm => tr_tr (Finset.mem_range.1 hm))
    (fun _ _ => rfl)

/-! ## The block estimate on `ℝ` -/

lemma g_bounds (hp : 0 < p) {m : ℕ} (hm : m < p * p) {x : ℝ} (hx : x ∈ blk p m) :
    ((m % p : ℕ) : ℝ) / p ≤ g p x ∧ g p x ≤ (((m % p : ℕ) : ℝ) + 1) / p := by
  have hb := g_mem_blk hp hm hx
  rw [blk, mem_Ico] at hb
  have hN := N_pos hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : ((m % p : ℕ) : ℝ) * p ≤ (tr p m : ℝ) := by
    exact_mod_cast (show m % p * p ≤ tr p m from Nat.le_add_right _ _)
  have h2 : (tr p m : ℝ) + 1 ≤ (((m % p : ℕ) : ℝ) + 1) * p := by
    have h3 : m / p < p := (Nat.div_lt_iff_lt_mul hp).2 hm
    have : tr p m + 1 ≤ (m % p + 1) * p := by
      show m % p * p + m / p + 1 ≤ (m % p + 1) * p
      rw [Nat.add_mul, one_mul, Nat.add_assoc]
      exact Nat.add_le_add_left h3 _
    exact_mod_cast this
  constructor
  · calc ((m % p : ℕ) : ℝ) / p = ((m % p : ℕ) : ℝ) * p / ((p : ℝ) * p) := by field_simp
      _ ≤ (tr p m : ℝ) / ((p : ℝ) * p) := div_le_div_of_nonneg_right h1 hN.le
      _ ≤ g p x := hb.1
  · calc g p x ≤ ((tr p m : ℝ) + 1) / ((p : ℝ) * p) := hb.2.le
      _ ≤ (((m % p : ℕ) : ℝ) + 1) * p / ((p : ℝ) * p) := div_le_div_of_nonneg_right h2 hN.le
      _ = _ := by field_simp

lemma g_norm_le (hp : 0 < p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖g p x‖ ≤ 1 := by
  have := g_mem_Icc hp hx
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [this.1, this.2]

lemma integrableOn_g (hp : 0 < p) : IntegrableOn (g p) (Icc 0 1) volume :=
  Integrable.mono' (integrable_const (1 : ℝ)) (measurable_g p).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Icc fun _ hx => g_norm_le hp hx)

lemma intervalIntegrable_g (hp : 0 < p) {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) : IntervalIntegrable (g p) volume u v :=
  ((integrableOn_g hp).mono_set (uIcc_subset_Icc hu hv)).intervalIntegrable

lemma blk_end_mem (hp : 0 < p) {m : ℕ} (hm : m ≤ p * p) :
    (m : ℝ) / ((p : ℝ) * p) ∈ Icc (0 : ℝ) 1 := by
  have hN := N_pos hp
  refine ⟨by positivity, (div_le_one hN).2 ?_⟩
  exact_mod_cast hm

lemma blk_int (hp : 0 < p) {m : ℕ} (hm : m < p * p) :
    ((m % p : ℕ) : ℝ) / p * (1 / ((p : ℝ) * p)) ≤
        ∫ x in (m : ℝ) / ((p : ℝ) * p)..((m + 1 : ℕ) : ℝ) / ((p : ℝ) * p), g p x ∧
      ∫ x in (m : ℝ) / ((p : ℝ) * p)..((m + 1 : ℕ) : ℝ) / ((p : ℝ) * p), g p x ≤
        (((m % p : ℕ) : ℝ) + 1) / p * (1 / ((p : ℝ) * p)) := by
  have hN := N_pos hp
  have hle : (m : ℝ) / ((p : ℝ) * p) ≤ ((m + 1 : ℕ) : ℝ) / ((p : ℝ) * p) :=
    div_le_div_of_nonneg_right (by push_cast; linarith) hN.le
  have hI := intervalIntegrable_g hp (blk_end_mem hp hm.le) (blk_end_mem hp hm)
  have hlen : ((m + 1 : ℕ) : ℝ) / ((p : ℝ) * p) - (m : ℝ) / ((p : ℝ) * p) = 1 / ((p : ℝ) * p) := by
    push_cast; ring
  have hsub : ∀ x ∈ Ioo ((m : ℝ) / ((p : ℝ) * p)) (((m + 1 : ℕ) : ℝ) / ((p : ℝ) * p)),
      x ∈ blk p m := by
    intro x hx; rw [blk]; push_cast at hx ⊢; exact Ioo_subset_Ico_self hx
  constructor
  · have := intervalIntegral.integral_mono_on_of_le_Ioo hle intervalIntegrable_const hI
      (fun x hx => (g_bounds hp hm (hsub x hx)).1)
    rwa [intervalIntegral.integral_const, hlen, smul_eq_mul, mul_comm] at this
  · have := intervalIntegral.integral_mono_on_of_le_Ioo hle hI intervalIntegrable_const
      (fun x hx => (g_bounds hp hm (hsub x hx)).2)
    rwa [intervalIntegral.integral_const, hlen, smul_eq_mul, mul_comm (1 / _)] at this

lemma sum_mod (p k : ℕ) : (∑ m ∈ Finset.range (k * p), m % p) * 2 = k * (p * (p - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, add_mul, ih]
    have : ∑ x ∈ Finset.range p, (k * p + x) % p = ∑ x ∈ Finset.range p, x := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.1 hj)]
    rw [this, Finset.sum_range_id_mul_two]
    ring

lemma sum_mod_real (hp : 0 < p) (k : ℕ) :
    (∑ m ∈ Finset.range (k * p), ((m % p : ℕ) : ℝ)) = k * (p * ((p : ℝ) - 1)) / 2 := by
  have h := sum_mod p k
  have := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hp.ne')] at this
  linarith

/-- The block estimate: `|∫_0^a g_p − a/2| ≤ 2/p` for `a ∈ [0, 1]`. -/
lemma est (hp : 0 < p) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |(∫ x in (0 : ℝ)..a, g p x) - a / 2| ≤ 2 / p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hN := N_pos hp
  set k := ⌊(p : ℝ) * a⌋₊ with hk
  have hk1 : (k : ℝ) ≤ p * a := Nat.floor_le (by positivity)
  have hk2 : (p : ℝ) * a < k + 1 := Nat.lt_floor_add_one _
  set b := (k : ℝ) / p with hb
  have hb0 : 0 ≤ b := by positivity
  have hba : b ≤ a := by rw [hb, div_le_iff₀ hp']; linarith
  have hab : a - b ≤ 1 / p := by
    have : a < b + 1 / p := by rw [hb, ← add_div, lt_div_iff₀ hp']; linarith
    linarith
  have hkp : k * p ≤ p * p := by
    have : (k : ℝ) ≤ p := le_trans hk1 (by nlinarith)
    have : k ≤ p := by exact_mod_cast this
    exact Nat.mul_le_mul_right _ this
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨hb0, hba.trans ha1⟩
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha0, ha1⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_g hp h0I hbI) (intervalIntegrable_g hp hbI haI)
  -- the tail `[b, a]`
  have htail : |∫ x in b..a, g p x| ≤ 1 / p := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := a) (C := 1)
      (f := g p) (fun x hx => by
        rw [uIoc_of_le hba] at hx
        exact g_norm_le hp ⟨hb0.trans hx.1.le, hx.2.trans ha1⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hba), one_mul] at this
    linarith
  -- the full rows `[0, b]`
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g p)
    (a := fun m : ℕ => (m : ℝ) / ((p : ℝ) * p)) (n := k * p)
    (fun m hm => intervalIntegrable_g hp (blk_end_mem hp (by omega)) (blk_end_mem hp (by omega)))
  have e0 : ((0 : ℕ) : ℝ) / ((p : ℝ) * p) = 0 := by simp
  have eb : ((k * p : ℕ) : ℝ) / ((p : ℝ) * p) = b := by
    rw [hb]; push_cast; field_simp
  simp only [e0, eb] at hsum
  set sm := ∑ m ∈ Finset.range (k * p), ((m % p : ℕ) : ℝ) with hsm
  have hsmv := sum_mod_real hp k
  have hlow : sm / p * (1 / ((p : ℝ) * p)) ≤ ∫ x in (0 : ℝ)..b, g p x := by
    rw [← hsum, hsm, Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_le_sum fun m hm => (blk_int hp (by
      have := Finset.mem_range.1 hm; omega)).1
  have hup : ∫ x in (0 : ℝ)..b, g p x ≤ (sm + (k * p : ℕ)) / p * (1 / ((p : ℝ) * p)) := by
    have e : sm + (k * p : ℕ) = ∑ m ∈ Finset.range (k * p), (((m % p : ℕ) : ℝ) + 1) := by
      rw [Finset.sum_add_distrib, hsm]; simp
    rw [← hsum, e, Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_le_sum fun m hm => (blk_int hp (by
      have := Finset.mem_range.1 hm; omega)).2
  have hL : sm / p * (1 / ((p : ℝ) * p)) = b / 2 - b / (2 * p) := by
    rw [hsm, hsmv, hb]; field_simp
  have hU : (sm + (k * p : ℕ)) / p * (1 / ((p : ℝ) * p)) = b / 2 + b / (2 * p) := by
    rw [hsm, hsmv, hb]; push_cast; field_simp; ring
  have hbp : b / (2 * p) ≤ 1 / (2 * p) :=
    div_le_div_of_nonneg_right (hba.trans ha1) (by positivity)
  have e2 : (2 : ℝ) / p = 1 / p + 1 / (2 * p) + 1 / (2 * p) := by field_simp; ring
  have e3 : (1 : ℝ) / p = 1 / (2 * p) + 1 / (2 * p) := by field_simp; ring
  rw [← hsplit, e2]
  rw [abs_le] at htail ⊢
  constructor <;> linarith

/-! ## The bijections of `I` -/

/-- The measure-preserving involution `φ_p` of `I`, with `p + 1` in place of `p`. -/
noncomputable def phi (p : ℕ) : I → I := fun x => ⟨g (p + 1) x, g_mem_Icc p.succ_pos x.2⟩

lemma phi_val (p : ℕ) (x : I) : (phi p x : ℝ) = g (p + 1) x := rfl

lemma measurable_phi (p : ℕ) : Measurable (phi p) :=
  ((measurable_g _).comp measurable_subtype_coe).subtype_mk

lemma phi_phi (p : ℕ) (x : I) : phi p (phi p x) = x :=
  Subtype.ext (g_g p.succ_pos x)

lemma image_preim_phi (p : ℕ) (S : Set I) :
    Subtype.val '' (phi p ⁻¹' S) = g (p + 1) ⁻¹' (Subtype.val '' S) ∩ Icc 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨phi p x, hx, rfl⟩, x.2⟩
  · rintro ⟨⟨z, hz, hzy⟩, hy⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    have : phi p ⟨y, hy⟩ = z := Subtype.ext hzy.symm
    show phi p ⟨y, hy⟩ ∈ S
    rw [this]; exact hz

lemma measurePreserving_phi (p : ℕ) : MeasurePreserving (phi p) volume volume := by
  refine ⟨measurable_phi p, Measure.ext fun S hS => ?_⟩
  rw [Measure.map_apply (measurable_phi p) hS, unitInterval.volume_apply,
    unitInterval.volume_apply, image_preim_phi]
  have hS' : MeasurableSet (Subtype.val '' S : Set ℝ) := measurableSet_Icc.subtype_image hS
  have hsub : (Subtype.val '' S : Set ℝ) ⊆ Icc 0 1 := by rintro _ ⟨x, -, rfl⟩; exact x.2
  calc volume (g (p + 1) ⁻¹' (Subtype.val '' S) ∩ Icc 0 1)
      = volume (g (p + 1) ⁻¹' (Subtype.val '' S) ∩ Ico 0 1) :=
        measure_congr (EventuallyEqSet.inter (by rfl) Ico_ae_eq_Icc.symm)
    _ = volume ((Subtype.val '' S : Set ℝ) ∩ Ico 0 1) := vol_preim p.succ_pos _ hS'
    _ = volume ((Subtype.val '' S : Set ℝ) ∩ Icc 0 1) :=
        measure_congr (EventuallyEqSet.inter (by rfl) Ico_ae_eq_Icc)
    _ = volume (Subtype.val '' S : Set ℝ) := by rw [inter_eq_left.2 hsub]

/-- `φ_p` as a measure-preserving bijection. -/
noncomputable def phiMP (p : ℕ) : MPBij :=
  ⟨{ toFun := phi p
     invFun := phi p
     left_inv := phi_phi p
     right_inv := phi_phi p
     measurable_toFun := measurable_phi p
     measurable_invFun := measurable_phi p }, measurePreserving_phi p⟩

lemma phiMP_apply (p : ℕ) (x : I) : (phiMP p).1 x = phi p x := rfl

/-! ## Mixing on `I`: `∫_A φ_p → |A|/2` -/

lemma integral_Iic (f : ℝ → ℝ) (a : I) :
    ∫ x in Iic a, f (x : ℝ) = ∫ y in (0 : ℝ)..a, f y := by
  have h := unitInterval.measurePreserving_coe.setIntegral_preimage_emb
    unitInterval.measurableEmbedding_coe f (Icc 0 (a : ℝ))
  have e : ((↑) : I → ℝ) ⁻¹' Icc 0 (a : ℝ) = Iic a := by
    ext x; simp only [mem_preimage, mem_Icc, mem_Iic, x.2.1, true_and]; rfl
  rw [e] at h
  rw [h, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.2 (Icc_subset_Icc le_rfl a.2.2), intervalIntegral.integral_of_le a.2.1,
    integral_Icc_eq_integral_Ioc]

lemma Iic_one : Iic (1 : I) = univ := eq_univ_of_forall fun x => (x.2.2 : (x : ℝ) ≤ 1)

lemma integral_val : ∫ x : I, (x : ℝ) = 1 / 2 := by
  have h := integral_Iic id 1
  rw [Iic_one, Measure.restrict_univ] at h
  simp only [id] at h
  rw [h, integral_id]
  norm_num

lemma norm_val_le (x : I) : ‖(x : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [x.2.1, x.2.2]

lemma integrable_comp_val {f : I → I} (hf : Measurable f) :
    Integrable (fun x => (f x : ℝ)) (volume : Measure I) :=
  Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_subtype_coe.comp hf).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_val_le (f x))

/-- The sets `A` along which `∫_A φ_p → |A|/2`. -/
def Good (A : Set I) : Prop :=
  Tendsto (fun n => ∫ x in A, (phi n x : ℝ)) atTop (𝓝 ((volume : Measure I).real A / 2))

lemma good_Iic (a : I) : Good (Iic a) := by
  have hv : (volume : Measure I).real (Iic a) = a := by
    rw [measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal a.2.1]
  unfold Good
  rw [hv, tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2
  rw [show (fun x : I => (phi n x : ℝ)) = fun x : I => g (n + 1) (x : ℝ) from rfl,
    integral_Iic (g (n + 1)) a, Real.norm_eq_abs]
  calc _ ≤ 2 / ((n + 1 : ℕ) : ℝ) := est n.succ_pos a.2.1 a.2.2
    _ = 2 * (1 / ((n : ℝ) + 1)) := by push_cast; ring

lemma integral_phi (n : ℕ) : ∫ x : I, (phi n x : ℝ) = 1 / 2 := by
  rw [← integral_val]
  exact (measurePreserving_phi n).integral_comp (phiMP n).1.measurableEmbedding
    (fun y : I => (y : ℝ))

lemma good_compl {t : Set I} (ht : MeasurableSet t) (h : Good t) : Good tᶜ := by
  unfold Good at *
  have e : ∀ n, ∫ x in tᶜ, (phi n x : ℝ) = 1 / 2 - ∫ x in t, (phi n x : ℝ) := fun n => by
    rw [← integral_phi n, ← integral_add_compl ht (integrable_comp_val (measurable_phi n))]
    ring
  simp only [e, probReal_compl_eq_one_sub ht]
  convert (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h using 2
  ring

lemma good_iUnion (f : ℕ → Set I) (hd : Pairwise (Function.onFun Disjoint f))
    (hfm : ∀ i, MeasurableSet (f i)) (h : ∀ i, Good (f i)) : Good (⋃ i, f i) := by
  unfold Good at *
  have e : ∀ n, ∫ x in ⋃ i, f i, (phi n x : ℝ) = ∑' i, ∫ x in f i, (phi n x : ℝ) := fun n =>
    integral_iUnion hfm hd (integrable_comp_val (measurable_phi n)).integrableOn
  have hs := hasSum_integral_iUnion (f := fun _ : I => (1 : ℝ)) (μ := volume) hfm hd
    (integrable_const _).integrableOn
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hs
  simp only [e, hs.tsum_eq.symm, ← tsum_div_const]
  refine tendsto_tsum_of_dominated_convergence hs.summable h (Eventually.of_forall fun n i => ?_)
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := f i)
    (f := fun x : I => (phi n x : ℝ)) (C := 1) (measure_lt_top _ _) fun x _ => norm_val_le _
  rwa [one_mul] at this

lemma good_all {A : Set I} (hA : MeasurableSet A) : Good A := by
  refine MeasurableSpace.induction_on_inter (C := fun A _ => Good A)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic I)) isPiSystem_Iic ?_ ?_
    (fun t ht h => good_compl ht h) (fun f hd hfm h => good_iUnion f hd hfm h) A hA
  · unfold Good; simp
  · rintro _ ⟨a, rfl⟩; exact good_Iic a

/-! ## Rectangle integrals of `(f x + f y)/2` -/

lemma prod_avg (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : I → ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) :
    ∫ z, (f z.1 + f z.2) / 2 ∂(μ.prod ν) =
      (ν.real univ * (∫ x, f x ∂μ) + μ.real univ * ∫ x, f x ∂ν) / 2 := by
  have h1 : Integrable (fun z : I × I => f z.1) (μ.prod ν) :=
    Integrable.mono' (integrable_const 1) (hf.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun z => hb _)
  have h2 : Integrable (fun z : I × I => f z.2) (μ.prod ν) :=
    Integrable.mono' (integrable_const 1) (hf.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun z => hb _)
  rw [integral_div, integral_add h1 h2, integral_fun_fst, integral_fun_snd, smul_eq_mul,
    smul_eq_mul]

lemma rect_avg {f : I → ℝ} (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) (A B : Set I) :
    ∫ z in A ×ˢ B, (f z.1 + f z.2) / 2 =
      ((volume : Measure I).real B * (∫ x in A, f x) +
        (volume : Measure I).real A * ∫ x in B, f x) / 2 := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, prod_avg _ _ hf hb,
    measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]

lemma meanW_eq : meanW = 1 / 2 := by
  have h := prod_avg volume volume (f := fun x : I => (x : ℝ)) measurable_subtype_coe norm_val_le
  rw [probReal_univ, integral_val] at h
  rw [meanW, show (fun p : I × I => avgW p.1 p.2) = fun z : I × I => ((z.1 : ℝ) + z.2) / 2 from rfl,
    h]
  norm_num

end Mixing

open Mixing in
/-- **An explicit mixing sequence.** There is a sequence of measure-preserving bijections `φ_n` of
`[0, 1]` with `W^{φ_n} → ∫ W` weak* for `W(x, y) = (x + y)/2` (in the proof, the block
transpositions `Mixing.phiMP n`). -/
theorem exists_mixing :
    ∃ φ : ℕ → MPBij, WeakStarTendsto (fun n => pullback (φ n).1 avgW) constW := by
  refine ⟨phiMP, fun A B hA hB => ?_⟩
  have e1 : (fun n => ∫ p in A ×ˢ B, pullback (phiMP n).1 avgW p.1 p.2) = fun n =>
      ((volume : Measure I).real B * (∫ x in A, (phi n x : ℝ)) +
        (volume : Measure I).real A * ∫ x in B, (phi n x : ℝ)) / 2 := funext fun n =>
    rect_avg (f := fun x => (phi n x : ℝ)) (measurable_subtype_coe.comp (measurable_phi n))
      (fun x => norm_val_le _) A B
  have e2 : ∫ p in A ×ˢ B, constW p.1 p.2 =
      ((volume : Measure I).real B * ((volume : Measure I).real A / 2) +
        (volume : Measure I).real A * ((volume : Measure I).real B / 2)) / 2 := by
    rw [show (fun p : I × I => constW p.1 p.2) = fun _ => (1 / 2 : ℝ) from
      funext fun _ => meanW_eq, setIntegral_const, Measure.volume_eq_prod, measureReal_prod_prod,
      smul_eq_mul]
    ring
  rw [e1, e2]
  have := (((good_all hA).const_mul ((volume : Measure I).real B)).add
    ((good_all hB).const_mul ((volume : Measure I).real A))).div_const 2
  exact this

/-- **Unconditional witness that `StructLT` can hold**: the constant graphon `∫ W` is strictly
below `W(x, y) = (x + y)/2` in the structural order (no literature hypothesis). -/
theorem structLT_const_avgW' : StructLT constW avgW :=
  structLT_const_avgW_of_mixing exists_mixing

/-- **Non-vacuity of `CutDistIdentifying`** (unconditional): there are graphons `U, W` with
`StructLT U W`. -/
theorem exists_structLT' :
    ∃ U W : I → I → ℝ, IsGraphon volume U ∧ IsGraphon volume W ∧ StructLT U W :=
  ⟨constW, avgW, isGraphon_of_symm isSymmGraphon_constW,
    isGraphon_of_symm isSymmGraphon_avgW, structLT_const_avgW'⟩

/-- **Non-vacuity of `CutDistIdentifying`** (unconditional): the constant parameter `θ = 0` is
not cut distance identifying. -/
theorem not_cutDistIdentifying_zero' : ¬ CutDistIdentifying (fun _ => (0 : ℝ)) := by
  intro h
  exact lt_irrefl (0 : ℝ) (h constW avgW (isGraphon_of_symm isSymmGraphon_constW)
    (isGraphon_of_symm isSymmGraphon_avgW) structLT_const_avgW')


end Witnesses

end NieWeiOrientedSidorenko
