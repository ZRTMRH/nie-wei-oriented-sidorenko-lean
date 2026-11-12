import NieWeiOrientedSidorenko.Section1Aux
import NieWeiOrientedSidorenko.S1Bridges

/-!
# Theorem 1.7 and Proposition 1.8: the family `D_t` and the triangle example

Proofs of `OrientedGraph.thm_1_7`, `OrientedGraph.thm_1_7_kernel`, `OrientedGraph.prop_1_8` and
`OrientedGraph.prop_1_8_kernel` of `Section1.lean` (as `*_proof`, in the namespace
`NieWeiOrientedSidorenko.S1Dt`), following Section 5 of the paper.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace S1Dt

open OrientedGraph

/-! ## Densities of graphs on `α ⊕ β` with no arcs inside `β` -/

section Split

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The factor contributed by the pair `(inl a, inr b)`. -/
noncomputable def kab (D : OrientedGraph (α ⊕ β)) (U : I → I → ℝ) (a : α) (b : β) (s y : I) :
    ℝ := by
  classical
  exact if D.Adj (.inl a) (.inr b) then U s y else if D.Adj (.inr b) (.inl a) then U y s else 1

/-- The product, over all ordered pairs `(a, a')` of `α`, of the factors of the arcs
`inl a → inl a'`. -/
noncomputable def kaa (D : OrientedGraph (α ⊕ β)) (U : I → I → ℝ) (x : α → I) : ℝ := by
  classical
  exact ∏ p : α × α, if D.Adj (.inl p.1) (.inl p.2) then U (x p.1) (x p.2) else 1

lemma prod_arcs_split (D : OrientedGraph (α ⊕ β)) (hβ : ∀ b b', ¬ D.Adj (.inr b) (.inr b'))
    (U : I → I → ℝ) (z : α ⊕ β → I) :
    ∏ p ∈ D.arcs, U (z p.1) (z p.2) =
      kaa D U (fun a => z (.inl a)) * ∏ b, ∏ a, kab D U a b (z (.inl a)) (z (.inr b)) := by
  classical
  have harcs : D.arcs = Finset.univ.filter (fun p : (α ⊕ β) × (α ⊕ β) => D.Adj p.1 p.2) := by
    ext p; simp [Section6Aux.mem_arcs_iff]
  have hk : ∀ a b, kab D U a b (z (.inl a)) (z (.inr b)) =
      (if D.Adj (.inl a) (.inr b) then U (z (.inl a)) (z (.inr b)) else 1) *
      (if D.Adj (.inr b) (.inl a) then U (z (.inr b)) (z (.inl a)) else 1) := by
    intro a b
    unfold kab
    by_cases h1 : D.Adj (.inl a) (.inr b)
    · have h2 : ¬ D.Adj (.inr b) (.inl a) := D.asymm _ _ h1
      simp [h1, h2]
    · by_cases h2 : D.Adj (.inr b) (.inl a) <;> simp [h1, h2]
  rw [harcs, Finset.prod_filter, Fintype.prod_prod_type, Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type, hk, Finset.prod_mul_distrib, hβ, ite_false,
    Finset.prod_const_one, mul_one]
  unfold kaa
  rw [Fintype.prod_prod_type, Finset.prod_comm (s := (Finset.univ : Finset β))
    (t := (Finset.univ : Finset α))
    (f := fun b a => if D.Adj (.inl a) (.inr b) then U (z (.inl a)) (z (.inr b)) else 1)]
  ring

/-- The density of a directed graph on `α ⊕ β` with no arcs inside `β`: integrate the `β`
vertices out first. -/
lemma t_split (D : OrientedGraph (α ⊕ β)) (hβ : ∀ b b', ¬ D.Adj (.inr b) (.inr b'))
    (U : I → I → ℝ) (hU : IsDigraphon U) :
    t D U = ∫ x, kaa D U x * ∏ b, (∫ y, ∏ a, kab D U a b (x a) y)
      ∂(Measure.pi fun _ : α => (volume : Measure I)) := by
  classical
  have hmp := measurePreserving_sumPiEquivProdPi_symm (fun _ : α ⊕ β => (volume : Measure I))
  set F : (α ⊕ β → I) → ℝ := fun z => ∏ p ∈ D.arcs, U (z p.1) (z p.2) with hF
  have hFi : Integrable F (Measure.pi fun _ => (volume : Measure I)) :=
    Section1Aux.integrable_arcs D hU
  have hint := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hFi
  unfold t tDir
  rw [← hmp.integral_comp']
  refine (integral_prod _ hint).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF]
  simp_rw [prod_arcs_split D hβ U]
  show ∫ y : β → I, kaa D U x * ∏ b, ∏ a, kab D U a b (x a) (y b)
      ∂(Measure.pi fun _ => (volume : Measure I)) = _
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun b yb => ∏ a, kab D U a b (x a) yb)

end Split

/-! ## AM-GM with natural exponents -/

section AMGM

variable {ι : Type*} [Fintype ι]

lemma geom_eq_rpow (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ^ ((Fintype.card ι : ℝ)⁻¹) = (∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
  Real.finsetProd_rpow _ _ (fun i _ => hz i) _

lemma amgm_weighted (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) [Nonempty ι] :
    ∏ i, z i ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * z i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => by positivity) ?_
    (fun i _ => hz i)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **AM-GM**: `∏ z_i ≤ ((∑ z_i) / n)^n`. -/
lemma amgm (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) [Nonempty ι] :
    ∏ i, z i ≤ ((∑ i, z i) / Fintype.card ι) ^ Fintype.card ι := by
  have hn0 : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hP : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  have h1 := amgm_weighted z hz
  rw [geom_eq_rpow z hz, ← Finset.mul_sum, inv_mul_eq_div] at h1
  calc ∏ i, z i = ((∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹)) ^ Fintype.card ι :=
        (Real.rpow_inv_natCast_pow hP hn0).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hP _) h1 _

/-- **AM-GM, equality case**: equality forces all `z_i` to be equal. -/
lemma amgm_eq (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) [Nonempty ι]
    (h : ∏ i, z i = ((∑ i, z i) / Fintype.card ι) ^ Fintype.card ι) : ∀ i j, z i = z j := by
  have hn0 : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm : 0 ≤ (∑ i, z i) / Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun i _ => hz i) hn.le
  have h2 : ∏ i, z i ^ ((Fintype.card ι : ℝ)⁻¹) = ∑ i, (Fintype.card ι : ℝ)⁻¹ * z i := by
    rw [geom_eq_rpow z hz, h, Real.pow_rpow_inv_natCast hm hn0, ← Finset.mul_sum,
      inv_mul_eq_div]
  have := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos Finset.univ
    (fun _ => (Fintype.card ι : ℝ)⁻¹) z (fun i _ => by positivity) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun i _ => hz i)).mp h2
  intro i j
  exact this i (Finset.mem_univ _) j (Finset.mem_univ _)

end AMGM

/-! ## Relabelling the vertices -/

section Relabel

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The directed graph `D` with its vertices relabelled along `e`. -/
def relabel (D : OrientedGraph V) (e : V ≃ W) : OrientedGraph W where
  Adj a b := D.Adj (e.symm a) (e.symm b)
  irrefl _ := D.irrefl _
  asymm _ _ h := D.asymm _ _ h

lemma t_relabel (D : OrientedGraph V) (e : V ≃ W) (U : I → I → ℝ) :
    t (relabel D e) U = t D U := by
  classical
  set Φ : (V → I) ≃ᵐ (W → I) := MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl I) with hΦ
  have hmp : MeasurePreserving Φ (Measure.pi fun _ : V => (volume : Measure I))
      (Measure.pi fun _ : W => (volume : Measure I)) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ => MeasurePreserving.id _)
  have hz : ∀ x : V → I, Φ x = fun w => x (e.symm w) := fun x => by
    funext w; simp [hΦ, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  unfold t tDir
  rw [← hmp.integral_comp']
  congr 1
  funext x
  rw [hz]
  refine Finset.prod_nbij' (fun p => (e.symm p.1, e.symm p.2)) (fun p => (e p.1, e p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Section6Aux.mem_arcs_iff] at hp ⊢
    exact hp
  · intro p hp
    rw [Section6Aux.mem_arcs_iff] at hp ⊢
    simpa [relabel] using hp
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

omit [Fintype V] [Fintype W] in
lemma relabel_adj (D : OrientedGraph V) (e : V ≃ W) (a b : V) :
    (relabel D e).Adj (e a) (e b) ↔ D.Adj a b := by
  simp [relabel]

lemma isOASK_relabel (D : OrientedGraph V) (e : V ≃ W) (h : D.IsOASK) : (relabel D e).IsOASK :=
  fun U hU => by rw [t_relabel, t_relabel]; exact h U hU

end Relabel

/-! ## The family `D_t` -/

section Dt

/-- `W_σ`: `W` for `σ = 1` (`true`), `W^T` for `σ = -1` (`false`). -/
def Wb (U : I → I → ℝ) (b : Bool) (s y : I) : ℝ := if b then U s y else U y s

/-- `P_ε(x) = ∫ ∏_i W_{ε_i}(x_i, y) dy`. -/
noncomputable def P {n : ℕ} (U : I → I → ℝ) (ε : Fin n → Bool) (x : Fin n → I) : ℝ :=
  ∫ y, ∏ i, Wb U (ε i) (x i) y

/-- `Q(x) = ∫ ∏_i S(x_i, y) dy`, `S = (W + W^T)/2`. -/
noncomputable def Q {n : ℕ} (U : I → I → ℝ) (x : Fin n → I) : ℝ :=
  ∫ y, ∏ i, symmetrize U (x i) y

lemma Dt_no_inr (n : ℕ) : ∀ b b', ¬ (Dt n).Adj (.inr b) (.inr b') := by
  intro b b'; simp [Dt]

lemma kab_Dt (n : ℕ) (U : I → I → ℝ) (i : Fin n) (ε : Fin n → Bool) (s y : I) :
    kab (Dt n) U i ε s y = Wb U (ε i) s y := by
  unfold kab Wb
  cases h : ε i <;> simp [Dt, h]

lemma kaa_Dt (n : ℕ) (U : I → I → ℝ) (x : Fin n → I) : kaa (Dt n) U x = 1 := by
  unfold kaa
  simp [Dt]

lemma t_Dt (n : ℕ) (U : I → I → ℝ) (hU : IsDigraphon U) :
    t (Dt n) U = ∫ x, ∏ ε, P U ε x ∂(Measure.pi fun _ : Fin n => (volume : Measure I)) := by
  rw [t_split (Dt n) (Dt_no_inr n) U hU]
  simp only [kaa_Dt, kab_Dt, one_mul, P]

lemma Wb_symm (U : I → I → ℝ) (b : Bool) (s y : I) :
    Wb (symmetrize U) b s y = symmetrize U s y := by
  cases b
  · simp only [Wb, symmetrize]; ring_nf; simp
  · rfl

lemma card_eps (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

lemma t_Dt_symm (n : ℕ) (U : I → I → ℝ) (hU : IsDigraphon U) :
    t (Dt n) (symmetrize U) =
      ∫ x, Q U x ^ (2 ^ n) ∂(Measure.pi fun _ : Fin n => (volume : Measure I)) := by
  rw [t_Dt n _ (Section1Aux.isDigraphon_symmetrize hU)]
  simp only [P, Wb_symm, Finset.prod_const, Finset.card_univ, card_eps]
  rfl

lemma Wb_mem {U : I → I → ℝ} (hU : IsDigraphon U) (b : Bool) (s y : I) :
    0 ≤ Wb U b s y ∧ Wb U b s y ≤ 1 := by
  cases b
  · exact hU.2 y s
  · exact hU.2 s y

lemma measurable_Wb {U : I → I → ℝ} (hU : IsDigraphon U) (b : Bool) :
    Measurable (fun p : I × I => Wb U b p.1 p.2) := by
  cases b
  · exact hU.1.comp measurable_swap
  · exact hU.1

lemma measurable_prodWb {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (ε : Fin n → Bool) :
    Measurable (Function.uncurry fun (x : Fin n → I) (y : I) => ∏ i, Wb U (ε i) (x i) y) := by
  refine Finset.measurable_prod _ fun i _ => ?_
  have hm : Measurable (fun q : (Fin n → I) × I => (q.1 i, q.2)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  exact (measurable_Wb hU (ε i)).comp hm

lemma prodWb_mem {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (ε : Fin n → Bool)
    (x : Fin n → I) (y : I) :
    0 ≤ ∏ i, Wb U (ε i) (x i) y ∧ ∏ i, Wb U (ε i) (x i) y ≤ 1 :=
  Section2Aux.prod_mem_01 _ _ (fun _ => (Wb_mem hU _ _ _).1) (fun _ => (Wb_mem hU _ _ _).2)

lemma integrable_prodWb {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (ε : Fin n → Bool)
    (x : Fin n → I) : Integrable (fun y => ∏ i, Wb U (ε i) (x i) y) :=
  Section2Aux.integrable_of_01 ((measurable_prodWb hU ε).comp measurable_prodMk_left)
    (fun y => (prodWb_mem hU ε x y).1) (fun y => (prodWb_mem hU ε x y).2)

lemma P_mem {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (ε : Fin n → Bool) (x : Fin n → I) :
    0 ≤ P U ε x ∧ P U ε x ≤ 1 := by
  constructor
  · exact integral_nonneg fun y => (prodWb_mem hU ε x y).1
  · calc P U ε x ≤ ∫ _y : I, (1 : ℝ) :=
          integral_mono (integrable_prodWb hU ε x) (integrable_const _)
            fun y => (prodWb_mem hU ε x y).2
      _ = 1 := by simp

lemma measurable_P {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (ε : Fin n → Bool) :
    Measurable (P U ε) :=
  ((measurable_prodWb hU ε).stronglyMeasurable.integral_prod_right
    (ν := (volume : Measure I))).measurable

lemma Q_eq_P (U : I → I → ℝ) {n : ℕ} (x : Fin n → I) :
    Q U x = P (symmetrize U) (fun _ => true) x := by
  simp only [Q, P, Wb_symm]

lemma Q_mem {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (x : Fin n → I) :
    0 ≤ Q U x ∧ Q U x ≤ 1 := by
  rw [Q_eq_P]; exact P_mem (Section1Aux.isDigraphon_symmetrize hU) _ x

lemma measurable_Q {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} :
    Measurable (Q U : (Fin n → I) → ℝ) := by
  have : (Q U : (Fin n → I) → ℝ) = P (symmetrize U) (fun _ => true) := funext (Q_eq_P U)
  rw [this]; exact measurable_P (Section1Aux.isDigraphon_symmetrize hU) _

lemma sum_Wb (U : I → I → ℝ) (s y : I) : ∑ b, Wb U b s y = 2 * symmetrize U s y := by
  simp only [Fintype.sum_bool, Wb, symmetrize, ite_true]
  simp; ring

/-- Equation `(eq:Dt-sf1)`: `2^{-t} ∑_ε P_ε = Q`. -/
lemma sum_P {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (x : Fin n → I) :
    ∑ ε, P U ε x = 2 ^ n * Q U x := by
  classical
  unfold P Q
  rw [← integral_finsetSum _ (fun ε _ => integrable_prodWb hU ε x), ← integral_const_mul]
  congr 1
  funext y
  rw [← Fintype.prod_sum (fun i b => Wb U b (x i) y)]
  simp only [sum_Wb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

lemma integrable_pi_01 {n : ℕ} {g : (Fin n → I) → ℝ} (hg : Measurable g)
    (h : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable g (Measure.pi fun _ : Fin n => (volume : Measure I)) :=
  Section2Aux.integrable_of_01 hg (fun x => (h x).1) (fun x => (h x).2)

/-- Pointwise AM-GM: `∏_ε P_ε(x) ≤ Q(x)^{2^t}`. -/
lemma prodP_le {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (x : Fin n → I) :
    ∏ ε, P U ε x ≤ Q U x ^ (2 ^ n) := by
  have := amgm (fun ε => P U ε x) (fun ε => (P_mem hU ε x).1)
  rw [sum_P hU x, card_eps] at this
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rwa [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ h2] at this

lemma measurable_prodP {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} :
    Measurable (fun x : Fin n → I => ∏ ε, P U ε x) :=
  Finset.measurable_prod _ fun ε _ => measurable_P hU ε

lemma prodP_mem {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (x : Fin n → I) :
    0 ≤ ∏ ε, P U ε x ∧ ∏ ε, P U ε x ≤ 1 :=
  Section2Aux.prod_mem_01 _ _ (fun ε => (P_mem hU ε x).1) (fun ε => (P_mem hU ε x).2)

lemma powQ_mem {U : I → I → ℝ} (hU : IsDigraphon U) {n : ℕ} (x : Fin n → I) :
    0 ≤ Q U x ^ (2 ^ n) ∧ Q U x ^ (2 ^ n) ≤ 1 :=
  ⟨pow_nonneg (Q_mem hU x).1 _, pow_le_one₀ (Q_mem hU x).1 (Q_mem hU x).2⟩

/-- `D_t` is OAS (digraphon form), for every `t`. -/
lemma Dt_oask (n : ℕ) : (Dt n).IsOASK := by
  intro U hU
  rw [t_Dt n U hU, t_Dt_symm n U hU]
  exact integral_mono (integrable_pi_01 (measurable_prodP hU) (prodP_mem hU))
    (integrable_pi_01 ((measurable_Q hU).pow_const _) (powQ_mem hU)) (prodP_le hU)

end Dt

/-! ## `D_t` is symmetry-forcing -/

section Forcing

variable {n : ℕ}

/-- The sign `σ ∈ {1, -1}` of a Boolean. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

/-- The coefficients `ε_1 ε_2` of `(eq:Dt-sf2)`, one factor per coordinate. -/
noncomputable def cf (i : Fin (n + 2)) (b : Bool) : ℝ := if (i : ℕ) < 2 then sg b else 1

/-- `∑_σ c_i(σ) W_σ`: `W - W^T = 2A` for the first two coordinates, `W + W^T = 2S` otherwise. -/
noncomputable def hk (U : I → I → ℝ) (i : Fin (n + 2)) (s y : I) : ℝ :=
  if (i : ℕ) < 2 then U s y - U y s else U s y + U y s

lemma sum_cf_Wb (U : I → I → ℝ) (i : Fin (n + 2)) (s y : I) :
    ∑ b, cf i b * Wb U b s y = hk U i s y := by
  unfold cf hk Wb sg
  split_ifs <;> simp
  ring

lemma sum_coef : ∑ ε : Fin (n + 2) → Bool, ∏ i, cf i (ε i) = 0 := by
  classical
  rw [← Fintype.prod_sum (fun i b => cf i b)]
  apply Finset.prod_eq_zero (Finset.mem_univ 0)
  simp [cf, sg]

lemma integral_prod_hk {U : I → I → ℝ} (hU : IsDigraphon U) (x : Fin (n + 2) → I) :
    ∫ y, ∏ i, hk U i (x i) y = ∑ ε, (∏ i, cf i (ε i)) * P U ε x := by
  classical
  have h : ∀ y, ∏ i, hk U i (x i) y =
      ∑ ε : Fin (n + 2) → Bool, (∏ i, cf i (ε i)) * ∏ i, Wb U (ε i) (x i) y := by
    intro y
    simp_rw [← sum_cf_Wb]
    rw [Fintype.prod_sum (fun i b => cf i b * Wb U b (x i) y)]
    simp_rw [Finset.prod_mul_distrib]
  simp_rw [h]
  rw [integral_finsetSum _ (fun ε _ => (integrable_prodWb hU ε x).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

/-- Equality in the AM-GM step forces `P_ε(x) = Q(x)` for all `ε`, for almost every `x`. -/
lemma ae_P_eq {m : ℕ} {U : I → I → ℝ} (hU : IsDigraphon U)
    (h : t (Dt m) U = t (Dt m) (symmetrize U)) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin m => (volume : Measure I)), ∀ ε, P U ε x = Q U x := by
  rw [t_Dt m U hU, t_Dt_symm m U hU] at h
  have hi1 := integrable_pi_01 (measurable_prodP hU (n := m)) (prodP_mem hU)
  have hi2 := integrable_pi_01 ((measurable_Q hU (n := m)).pow_const (2 ^ m)) (powQ_mem hU)
  have h0 : ∫ x, (Q U x ^ (2 ^ m) - ∏ ε, P U ε x)
      ∂(Measure.pi fun _ : Fin m => (volume : Measure I)) = 0 := by
    rw [integral_sub hi2 hi1, h, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.mpr (prodP_le hU x))
    (hi2.sub hi1)).mp h0
  filter_upwards [hae] with x hx
  have hx' : ∏ ε, P U ε x = Q U x ^ (2 ^ m) := by
    simp only [Pi.zero_apply] at hx; linarith
  have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
  have heq := amgm_eq (fun ε => P U ε x) (fun ε => (P_mem hU ε x).1) (by
    rw [sum_P hU x, card_eps, Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ h2]
    exact hx')
  intro ε
  have hs := sum_P hU x
  have h3 : ∑ ε', P U ε' x = 2 ^ m * P U ε x := by
    rw [Finset.sum_congr rfl (fun ε' _ => heq ε' ε), Finset.sum_const, Finset.card_univ,
      card_eps, nsmul_eq_mul]
    push_cast; ring
  exact mul_left_cancel₀ h2 (h3.symm.trans hs)

/-- Equation `(eq:Dt-sf2)`: `∫ A(x_1, y) A(x_2, y) ∏_{i ≥ 3} S(x_i, y) dy = 0` (up to the factor
`2^t`), for almost every `x`. -/
lemma ae_hk_zero {U : I → I → ℝ} (hU : IsDigraphon U)
    (h : t (Dt (n + 2)) U = t (Dt (n + 2)) (symmetrize U)) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 2) => (volume : Measure I)),
      ∫ y, ∏ i, hk U i (x i) y = 0 := by
  filter_upwards [ae_P_eq hU h] with x hx
  rw [integral_prod_hk hU x]
  simp_rw [hx]
  rw [← Finset.sum_mul, sum_coef, zero_mul]

/-- The test function `f(x_1) f(x_2)` with `f = 1_S`, as one factor per coordinate. -/
noncomputable def fS (S : Set I) (i : Fin (n + 2)) (s : I) : ℝ :=
  if (i : ℕ) < 2 then S.indicator 1 s else 1

lemma measurable_hk {U : I → I → ℝ} (hU : IsDigraphon U) (i : Fin (n + 2)) :
    Measurable (fun p : I × I => hk U i p.1 p.2) := by
  unfold hk
  split_ifs
  · exact hU.1.sub (hU.1.comp measurable_swap)
  · exact hU.1.add (hU.1.comp measurable_swap)

lemma abs_hk_le {U : I → I → ℝ} (hU : IsDigraphon U) (i : Fin (n + 2)) (s y : I) :
    |hk U i s y| ≤ 2 := by
  have h1 := hU.2 s y
  have h2 := hU.2 y s
  simp only [Set.mem_Icc] at h1 h2
  unfold hk
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma measurable_fS {S : Set I} (hS : MeasurableSet S) (i : Fin (n + 2)) :
    Measurable (fS S i) := by
  unfold fS
  split_ifs
  · exact measurable_const.indicator hS
  · exact measurable_const

lemma abs_fS_le (S : Set I) (i : Fin (n + 2)) (s : I) : |fS S i s| ≤ 1 := by
  unfold fS
  split_ifs
  · by_cases h : s ∈ S <;> simp [h]
  · simp

/-- Fubini for the test integral. -/
lemma test_fubini {U : I → I → ℝ} (hU : IsDigraphon U) {S : Set I} (hS : MeasurableSet S) :
    ∫ x, (∏ i, fS S i (x i)) * (∫ y, ∏ i, hk U i (x i) y)
        ∂(Measure.pi fun _ : Fin (n + 2) => (volume : Measure I)) =
      ∫ y, ∏ i : Fin (n + 2), ∫ s, fS S i s * hk U i s y := by
  set K : (Fin (n + 2) → I) → I → ℝ := fun x y => ∏ i, (fS S i (x i) * hk U i (x i) y) with hK
  have hKm : Measurable (Function.uncurry K) := by
    refine Finset.measurable_prod _ fun i _ => ?_
    have hm : Measurable (fun q : (Fin (n + 2) → I) × I => (q.1 i, q.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact ((measurable_fS hS i).comp ((measurable_pi_apply i).comp measurable_fst)).mul
      ((measurable_hk hU i).comp hm)
  have hKi : Integrable (Function.uncurry K)
      ((Measure.pi fun _ : Fin (n + 2) => (volume : Measure I)).prod volume) := by
    refine Integrable.of_bound hKm.aestronglyMeasurable (2 ^ (n + 2))
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs]
    simp only [Function.uncurry, hK, Finset.abs_prod]
    calc ∏ i, |fS S i (q.1 i) * hk U i (q.1 i) q.2| ≤ ∏ _i : Fin (n + 2), (2 : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => by
            rw [abs_mul]
            nlinarith [abs_fS_le S i (q.1 i), abs_hk_le hU i (q.1 i) q.2, abs_nonneg (fS S i (q.1 i)),
              abs_nonneg (hk U i (q.1 i) q.2)]
      _ = 2 ^ (n + 2) := by simp
  have h1 : ∀ x, (∏ i, fS S i (x i)) * ∫ y, ∏ i, hk U i (x i) y = ∫ y, K x y := by
    intro x
    rw [← integral_const_mul]
    simp only [hK, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [integral_integral_swap hKi]
  congr 1
  funext y
  exact integral_fintype_prod_eq_prod (fun i s => fS S i s * hk U i s y)

/-- The product of the coordinate integrals: `(∫_S A(·, y))^2 (∫ S(·, y))^{t-2}`, up to powers of
`2`. -/
lemma prod_coord (U : I → I → ℝ) (S : Set I) (y : I) :
    ∏ i : Fin (n + 2), ∫ s, fS S i s * hk U i s y =
      (∫ s, S.indicator 1 s * (U s y - U y s)) ^ 2 * (∫ s, (U s y + U y s)) ^ n := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h0 : ((0 : Fin (n + 2)) : ℕ) < 2 := by simp
  have h1 : (((0 : Fin (n + 1)).succ : Fin (n + 2)) : ℕ) < 2 := by simp
  have h2 : ∀ j : Fin n, ¬ ((j.succ.succ : Fin (n + 2)) : ℕ) < 2 := by
    intro j; simp [Fin.val_succ]
  simp only [fS, hk, h0, h1, h2, ite_true, ite_false, one_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-- Column integrals of a bounded measurable kernel: measurable, and bounded by the same bound. -/
lemma colInt {g : I → I → ℝ} (hg : Measurable (Function.uncurry g)) {C : ℝ}
    (hC : ∀ s y, |g s y| ≤ C) :
    Measurable (fun y => ∫ s, g s y) ∧ ∀ y, |∫ s, g s y| ≤ C := by
  refine ⟨(hg.stronglyMeasurable.integral_prod_left (μ := (volume : Measure I))).measurable,
    fun y => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure I)) (f := fun s => g s y)
    (C := C) (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hC s y)
  simpa [Real.norm_eq_abs] using this

/-- `a_S(y) = ∫_S (W - W^T)(s, y) ds`. -/
noncomputable def aS (U : I → I → ℝ) (S : Set I) (y : I) : ℝ :=
  ∫ s, S.indicator 1 s * (U s y - U y s)

/-- `m(y) = ∫ (W + W^T)(s, y) ds = 2 ∫ S(s, y) ds`. -/
noncomputable def mS (U : I → I → ℝ) (y : I) : ℝ := ∫ s, (U s y + U y s)

lemma meas_diff {U : I → I → ℝ} (hU : IsDigraphon U) :
    Measurable (fun p : I × I => U p.1 p.2 - U p.2 p.1) :=
  hU.1.sub (hU.1.comp measurable_swap)

lemma meas_sum {U : I → I → ℝ} (hU : IsDigraphon U) :
    Measurable (fun p : I × I => U p.1 p.2 + U p.2 p.1) :=
  hU.1.add (hU.1.comp measurable_swap)

lemma abs_diff_le {U : I → I → ℝ} (hU : IsDigraphon U) (s y : I) : |U s y - U y s| ≤ 1 := by
  have h1 := hU.2 s y
  have h2 := hU.2 y s
  simp only [Set.mem_Icc] at h1 h2
  rw [abs_le]; constructor <;> linarith

lemma sum_mem {U : I → I → ℝ} (hU : IsDigraphon U) (s y : I) :
    0 ≤ U s y + U y s ∧ U s y + U y s ≤ 2 := by
  have h1 := hU.2 s y
  have h2 := hU.2 y s
  simp only [Set.mem_Icc] at h1 h2
  constructor <;> linarith

lemma aS_props {U : I → I → ℝ} (hU : IsDigraphon U) {S : Set I} (hS : MeasurableSet S) :
    Measurable (aS U S) ∧ ∀ y, |aS U S y| ≤ 1 := by
  refine colInt (g := fun s y => S.indicator 1 s * (U s y - U y s)) ?_ ?_
  · exact ((measurable_const.indicator hS).comp measurable_fst).mul (meas_diff hU)
  · intro s y
    rw [abs_mul]
    have := abs_diff_le hU s y
    by_cases h : s ∈ S <;> simp [h, this]

lemma mS_props {U : I → I → ℝ} (hU : IsDigraphon U) :
    Measurable (mS U) ∧ ∀ y, 0 ≤ mS U y ∧ mS U y ≤ 2 := by
  have h := colInt (g := fun s y => U s y + U y s) (meas_sum hU) (C := 2) (fun s y => by
    rw [abs_le]; constructor <;> linarith [sum_mem hU s y])
  refine ⟨h.1, fun y => ⟨integral_nonneg fun s => (sum_mem hU s y).1, ?_⟩⟩
  exact (abs_le.mp (h.2 y)).2

/-- `∫ (∫_S A(·, y))^2 (∫ S(·, y))^{t-2} dy = 0` (up to powers of `2`). -/
lemma integral_aS_sq {U : I → I → ℝ} (hU : IsDigraphon U)
    (h : t (Dt (n + 2)) U = t (Dt (n + 2)) (symmetrize U)) {S : Set I} (hS : MeasurableSet S) :
    ∫ y, aS U S y ^ 2 * mS U y ^ n = 0 := by
  have e : ∀ y, aS U S y ^ 2 * mS U y ^ n = ∏ i : Fin (n + 2), ∫ s, fS S i s * hk U i s y :=
    fun y => (prod_coord U S y).symm
  simp_rw [e]
  rw [← test_fubini hU hS]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_hk_zero hU h] with x hx
  simp [hx]

lemma ae_aS_mul {U : I → I → ℝ} (hU : IsDigraphon U)
    (h : t (Dt (n + 2)) U = t (Dt (n + 2)) (symmetrize U)) {S : Set I} (hS : MeasurableSet S) :
    ∀ᵐ y, aS U S y * mS U y ^ n = 0 := by
  obtain ⟨ha, hab⟩ := aS_props hU hS
  obtain ⟨hm, hmb⟩ := mS_props hU
  have hint : Integrable (fun y => aS U S y ^ 2 * mS U y ^ n) := by
    refine Integrable.of_bound ((ha.pow_const 2).mul (hm.pow_const n)).aestronglyMeasurable
      (2 ^ n) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, abs_of_nonneg (hmb y).1]
    have h1 : |aS U S y| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hab y)
    have h2 : mS U y ^ n ≤ 2 ^ n := pow_le_pow_left₀ (hmb y).1 (hmb y).2 n
    nlinarith [pow_nonneg (hmb y).1 n, pow_nonneg (abs_nonneg (aS U S y)) 2]
  have h0 := (integral_eq_zero_iff_of_nonneg (fun y => mul_nonneg (sq_nonneg _)
    (pow_nonneg (hmb y).1 n)) hint).mp (integral_aS_sq hU h hS)
  filter_upwards [h0] with y hy
  simp only [Pi.zero_apply] at hy
  rcases mul_eq_zero.mp hy with h1 | h1
  · rw [pow_eq_zero_iff two_ne_zero] at h1; simp [h1]
  · simp [h1]

/-- The kernel `F(s, y) = (W - W^T)(s, y) m(y)^{t-2}`. -/
noncomputable def Fk (U : I → I → ℝ) (s y : I) : ℝ := (U s y - U y s) * mS U y ^ n

lemma isKernel_Fk {U : I → I → ℝ} (hU : IsDigraphon U) : IsKernel (Fk (n := n) U) := by
  obtain ⟨hm, hmb⟩ := mS_props hU
  refine ⟨(meas_diff hU).mul ((hm.comp measurable_snd).pow_const n), 2 ^ n, fun s y => ?_⟩
  unfold Fk
  rw [abs_mul, abs_pow, abs_of_nonneg (hmb y).1]
  have h2 : mS U y ^ n ≤ 2 ^ n := pow_le_pow_left₀ (hmb y).1 (hmb y).2 n
  nlinarith [abs_diff_le hU s y, pow_nonneg (hmb y).1 n, abs_nonneg (U s y - U y s)]

lemma rect_Fk {U : I → I → ℝ} (hU : IsDigraphon U)
    (h : t (Dt (n + 2)) U = t (Dt (n + 2)) (symmetrize U)) (S T : Set I) (hS : MeasurableSet S)
    (hT : MeasurableSet T) : ∫ p in S ×ˢ T, Fk (n := n) U p.1 p.2 = 0 := by
  rw [← integral_indicator (hS.prod hT)]
  have e : (S ×ˢ T).indicator (fun p : I × I => Fk (n := n) U p.1 p.2) =
      fun p => T.indicator 1 p.2 * (S.indicator 1 p.1 * (U p.1 p.2 - U p.2 p.1)) *
        mS U p.2 ^ n := by
    funext p
    unfold Fk
    by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ T <;> simp [h1, h2, Set.indicator, Set.mem_prod]
  have hint : Integrable ((S ×ˢ T).indicator fun p : I × I => Fk (n := n) U p.1 p.2)
      ((volume : Measure I).prod volume) := by
    obtain ⟨M, hM⟩ := (isKernel_Fk (n := n) hU).2
    refine Integrable.indicator ?_ (hS.prod hT)
    exact Integrable.of_bound (isKernel_Fk (n := n) hU).1.aestronglyMeasurable M
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hM p.1 p.2)
  rw [e] at hint ⊢
  rw [show (volume : Measure (I × I)) = (volume : Measure I).prod volume from rfl,
    integral_prod_symm _ hint]
  have e2 : ∀ y : I, ∫ s, T.indicator 1 (s, y).2 * (S.indicator 1 (s, y).1 *
      (U (s, y).1 (s, y).2 - U (s, y).2 (s, y).1)) * mS U (s, y).2 ^ n =
      T.indicator 1 y * (aS U S y * mS U y ^ n) := by
    intro y
    simp only
    rw [integral_mul_const, integral_const_mul, aS]
    ring
  simp_rw [e2]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_aS_mul hU h hS] with y hy
  simp [hy]

/-- On the set where `m(y) = 0`, `W(s, y) = W(y, s)` for almost every `(s, y)`. -/
lemma ae_zero_region {U : I → I → ℝ} (hU : IsDigraphon U) :
    ∀ᵐ p ∂((volume : Measure I).prod volume), mS U p.2 = 0 → U p.1 p.2 = U p.2 p.1 := by
  obtain ⟨hm, hmb⟩ := mS_props hU
  set Z : Set I := {y | mS U y = 0} with hZ
  have hZm : MeasurableSet Z := hm (measurableSet_singleton 0)
  set G : I × I → ℝ := fun p => Z.indicator 1 p.2 * (U p.1 p.2 + U p.2 p.1) with hG
  have hG0 : 0 ≤ G := fun p => mul_nonneg (by by_cases h : p.2 ∈ Z <;> simp [h])
    (sum_mem hU p.1 p.2).1
  have hGi : Integrable G ((volume : Measure I).prod volume) := by
    refine Integrable.of_bound (((measurable_const.indicator hZm).comp measurable_snd).mul
      (meas_sum hU)).aestronglyMeasurable 2 (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
    have := sum_mem hU p.1 p.2
    by_cases h : p.2 ∈ Z <;> simp [hG, h]
    linarith
  have hint0 : ∫ p, G p ∂((volume : Measure I).prod volume) = 0 := by
    rw [integral_prod_symm _ hGi]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    simp only [hG]
    rw [integral_const_mul]
    by_cases h : y ∈ Z
    · have : mS U y = 0 := h
      simp only [mS] at this
      simp [this]
    · simp [h]
  have hae := (integral_eq_zero_iff_of_nonneg hG0 hGi).mp hint0
  filter_upwards [hae] with p hp hmp
  have hz : p.2 ∈ Z := hmp
  simp only [hG, Pi.zero_apply, Set.indicator_of_mem hz, Pi.one_apply, one_mul] at hp
  have h1 := (hU.2 p.1 p.2).1
  have h2 := (hU.2 p.2 p.1).1
  linarith

/-- `D_t` (`t = n + 2`) is symmetry-forcing (digraphon form). -/
lemma Dt_sfk (n : ℕ) : (Dt (n + 2)).IsSymmetryForcingK := by
  intro U hU h
  have hF := S1Bridges.ae_zero_of_rect (isKernel_Fk (n := n) hU) (rect_Fk hU h)
  have hZ := ae_zero_region hU
  show ∀ᵐ p ∂((volume : Measure I).prod volume), U p.1 p.2 = U p.2 p.1
  filter_upwards [hF, hZ] with p hp hz
  by_cases hm : mS U p.2 = 0
  · exact hz hm
  · have : mS U p.2 ^ n ≠ 0 := pow_ne_zero _ hm
    unfold Fk at hp
    have := (mul_eq_zero.mp hp).resolve_right this
    linarith

end Forcing

/-! ## Theorem 1.7 -/

/-- **Theorem 1.7**, digraphon form. -/
theorem thm_1_7_kernel_proof (t : ℕ) (ht : 2 ≤ t) :
    (Dt t).IsOASK ∧ (Dt t).IsSymmetryForcingK := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  exact ⟨Dt_oask _, Dt_sfk k⟩

/-- **Theorem 1.7.** For every `t ≥ 2`, `D_t` is OAS and symmetry-forcing. Conditional on
`FHMZThm18Hyp` and `FHMZCompactHyp` (through the symmetry-forcing bridge
`S1Bridges.isSymmetryForcing_iff_isSymmetryForcingK_proof`) and on `FHMZThm13Hyp`, which the proof
passes to the bridge but does not need (only its digraphon-to-sequence half is used). -/
theorem thm_1_7_proof (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0}) (hcpt : FHMZCompactHyp)
    (t : ℕ) (ht : 2 ≤ t) :
    (Dt t).IsOAS ∧ (Dt t).IsSymmetryForcing := by
  obtain ⟨h1, h2⟩ := thm_1_7_kernel_proof t ht
  exact ⟨(S1Bridges.isOAS_iff_isOASK_proof _).mpr h1,
    (S1Bridges.isSymmetryForcing_iff_isSymmetryForcingK_proof h13 h18 hcpt _).mpr h2⟩

/-! ## Proposition 1.8: `D̃_2 = D_2 + (u_1 → u_2)` -/

section Triangle

/-- `D̃_2`: `D_2` with the extra arc `u_1 → u_2`. -/
def Dtil : OrientedGraph (Fin 2 ⊕ (Fin 2 → Bool)) where
  Adj a b := (Dt 2).Adj a b ∨ (a = .inl 0 ∧ b = .inl 1)
  irrefl v := by
    rintro (h | ⟨rfl, h⟩)
    · exact (Dt 2).irrefl v h
    · simp at h
  asymm u v h := by
    rcases h with h | ⟨rfl, rfl⟩
    · rintro (h' | ⟨rfl, rfl⟩)
      · exact (Dt 2).asymm _ _ h h'
      · simp [Dt] at h
    · rintro (h' | ⟨h1, _⟩)
      · simp [Dt] at h'
      · simp at h1

lemma Dtil_no_inr : ∀ b b', ¬ Dtil.Adj (.inr b) (.inr b') := by
  intro b b'; simp [Dtil, Dt]

lemma kab_Dtil (U : I → I → ℝ) (i : Fin 2) (ε : Fin 2 → Bool) (s y : I) :
    kab Dtil U i ε s y = Wb U (ε i) s y := by
  rw [← kab_Dt 2 U i ε s y]
  unfold kab
  have h1 : Dtil.Adj (.inl i) (.inr ε) ↔ (Dt 2).Adj (.inl i) (.inr ε) := by
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact h
      · cases h
    · exact Or.inl
  have h2 : Dtil.Adj (.inr ε) (.inl i) ↔ (Dt 2).Adj (.inr ε) (.inl i) := by
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact h
      · cases h
    · exact Or.inl
  by_cases g1 : (Dt 2).Adj (.inl i) (.inr ε)
  · rw [ite_eq_left (h1.mpr g1), ite_eq_left g1]
  · rw [ite_eq_right (fun h => g1 (h1.mp h)), ite_eq_right g1]
    by_cases g2 : (Dt 2).Adj (.inr ε) (.inl i)
    · rw [ite_eq_left (h2.mpr g2), ite_eq_left g2]
    · rw [ite_eq_right (fun h => g2 (h2.mp h)), ite_eq_right g2]

lemma kaa_Dtil (U : I → I → ℝ) (x : Fin 2 → I) : kaa Dtil U x = U (x 0) (x 1) := by
  unfold kaa
  rw [Fintype.prod_prod_type, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  simp [Dtil, Dt]

lemma t_Dtil (U : I → I → ℝ) (hU : IsDigraphon U) :
    t Dtil U = ∫ x, U (x 0) (x 1) * ∏ ε, P U ε x
      ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) := by
  rw [t_split Dtil Dtil_no_inr U hU]
  simp only [kaa_Dtil, kab_Dtil, P]

/-- The swap of `u_1, u_2`. -/
def sw : Equiv.Perm (Fin 2) := Equiv.swap 0 1

lemma P_swap (U : I → I → ℝ) (ε : Fin 2 → Bool) (x : Fin 2 → I) :
    P U ε (fun i => x (sw i)) = P U (fun i => ε (sw i)) x := by
  unfold P
  congr 1
  funext y
  simp [Fin.prod_univ_two, sw, mul_comm]

lemma R_swap (U : I → I → ℝ) (x : Fin 2 → I) :
    ∏ ε, P U ε (fun i => x (sw i)) = ∏ ε, P U ε x := by
  simp_rw [P_swap]
  refine Finset.prod_nbij' (fun ε i => ε (sw i)) (fun ε i => ε (sw i)) ?_ ?_ ?_ ?_ ?_
  · intro ε _; exact Finset.mem_univ _
  · intro ε _; exact Finset.mem_univ _
  · intro ε _; funext i; simp [sw, Equiv.swap_apply_self]
  · intro ε _; funext i; simp [sw, Equiv.swap_apply_self]
  · intro ε _; rfl

lemma integral_swap2 (F : (Fin 2 → I) → ℝ) :
    ∫ x, F (fun i => x (sw i)) ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) =
      ∫ x, F x ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) := by
  set Φ : (Fin 2 → I) ≃ᵐ (Fin 2 → I) := MeasurableEquiv.arrowCongr' sw (MeasurableEquiv.refl I)
    with hΦ
  have hmp : MeasurePreserving Φ (Measure.pi fun _ : Fin 2 => (volume : Measure I))
      (Measure.pi fun _ : Fin 2 => (volume : Measure I)) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ => MeasurePreserving.id _)
  have hz : ∀ x : Fin 2 → I, Φ x = fun i => x (sw i) := fun x => by
    funext i; simp [hΦ, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, sw]
  rw [← hmp.integral_comp']
  simp_rw [hz]
  simp only [sw, Equiv.swap_apply_self]

lemma measurable_pair2 {U : I → I → ℝ} (hU : IsDigraphon U) (a b : Fin 2) :
    Measurable (fun x : Fin 2 → I => U (x a) (x b)) :=
  Section1Aux.measurable_pair hU.1 a b

lemma Dtil_oask : Dtil.IsOASK := by
  intro U hU
  have hS := Section1Aux.isDigraphon_symmetrize hU
  rw [t_Dtil U hU, t_Dtil _ hS]
  have hPS : ∀ (ε : Fin 2 → Bool) (x : Fin 2 → I), P (symmetrize U) ε x = Q U x := by
    intro ε x; simp only [P, Q, Wb_symm]
  simp_rw [hPS, Finset.prod_const, Finset.card_univ, card_eps]
  set R : (Fin 2 → I) → ℝ := fun x => ∏ ε, P U ε x with hR
  have hRm : Measurable R := measurable_prodP hU
  have hRb := prodP_mem hU (n := 2)
  have hint : ∀ a b : Fin 2, Integrable (fun x => U (x a) (x b) * R x)
      (Measure.pi fun _ : Fin 2 => (volume : Measure I)) := by
    intro a b
    refine integrable_pi_01 ((measurable_pair2 hU a b).mul hRm) fun x => ?_
    have := hU.2 (x a) (x b)
    exact ⟨mul_nonneg this.1 (hRb x).1, by nlinarith [this.1, this.2, (hRb x).1, (hRb x).2]⟩
  -- the swap `x ↦ x ∘ sw` exchanges `W(x_1, x_2)` and `W(x_2, x_1)` and fixes `R`
  have hswap : ∫ x, U (x 1) (x 0) * R x ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) =
      ∫ x, U (x 0) (x 1) * R x ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) := by
    rw [← integral_swap2 (fun x => U (x 1) (x 0) * R x)]
    congr 1
    funext x
    simp only [hR, R_swap]
    simp [sw]
  have hsym : ∫ x, U (x 0) (x 1) * R x ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) =
      ∫ x, symmetrize U (x 0) (x 1) * R x
        ∂(Measure.pi fun _ : Fin 2 => (volume : Measure I)) := by
    have e : ∀ x : Fin 2 → I, symmetrize U (x 0) (x 1) * R x =
        (1 / 2 : ℝ) * (U (x 0) (x 1) * R x) + (1 / 2 : ℝ) * (U (x 1) (x 0) * R x) := by
      intro x; simp only [symmetrize]; ring
    simp_rw [e]
    rw [integral_add ((hint 0 1).const_mul _) ((hint 1 0).const_mul _), integral_const_mul,
      integral_const_mul, hswap]
    ring
  rw [hsym]
  refine integral_mono ?_ ?_ fun x => ?_
  · refine integrable_pi_01 ((measurable_pair2 hS 0 1).mul hRm) fun x => ?_
    have := hS.2 (x 0) (x 1)
    exact ⟨mul_nonneg this.1 (hRb x).1, by nlinarith [this.1, this.2, (hRb x).1, (hRb x).2]⟩
  · refine integrable_pi_01 ((measurable_pair2 hS 0 1).mul ((measurable_Q hU).pow_const _))
      fun x => ?_
    have := hS.2 (x 0) (x 1)
    have hq := powQ_mem hU x
    exact ⟨mul_nonneg this.1 hq.1, by nlinarith [this.1, this.2, hq.1, hq.2]⟩
  · exact mul_le_mul_of_nonneg_left (prodP_le hU x) (hS.2 (x 0) (x 1)).1

/-- The triangle `u_1 u_2 v_{(1,1)}` of `D̃_2`, transported along a relabelling. -/
lemma relabel_Dtil_triangle {W : Type*} (e : (Fin 2 ⊕ (Fin 2 → Bool)) ≃ W) :
    ∃ a b c : W, (relabel Dtil e).underlying.Adj a b ∧ (relabel Dtil e).underlying.Adj b c ∧
      (relabel Dtil e).underlying.Adj a c := by
  have hadj : ∀ u v, Dtil.Adj u v → (relabel Dtil e).underlying.Adj (e u) (e v) := by
    intro u v h
    rw [OrientedGraph.underlying, SimpleGraph.fromRel_adj]
    refine ⟨fun huv => ?_, Or.inl ((relabel_adj Dtil e u v).mpr h)⟩
    rw [e.injective huv] at h
    exact Dtil.irrefl v h
  refine ⟨e (.inl 0), e (.inl 1), e (.inr fun _ => true), hadj _ _ (Or.inr ⟨rfl, rfl⟩),
    hadj _ _ (Or.inl ?_), hadj _ _ (Or.inl ?_)⟩ <;> simp [Dt]

end Triangle

/-! ## Proposition 1.8 -/

/-- **Proposition 1.8**, digraphon form. -/
theorem prop_1_8_kernel_proof : ∃ (n : ℕ) (D : OrientedGraph (Fin n)), D.IsOASK ∧
    ∃ a b c : Fin n, D.underlying.Adj a b ∧ D.underlying.Adj b c ∧ D.underlying.Adj a c :=
  ⟨_, relabel Dtil (Fintype.equivFin _), isOASK_relabel _ _ Dtil_oask,
    relabel_Dtil_triangle _⟩

/-- **Proposition 1.8.** There is an OAS directed graph whose underlying graph contains a
triangle. -/
theorem prop_1_8_proof : ∃ (n : ℕ) (D : OrientedGraph (Fin n)), D.IsOAS ∧
    ∃ a b c : Fin n, D.underlying.Adj a b ∧ D.underlying.Adj b c ∧ D.underlying.Adj a c := by
  obtain ⟨n, D, hD, h⟩ := prop_1_8_kernel_proof
  exact ⟨n, D, (S1Bridges.isOAS_iff_isOASK_proof D).mpr hD, h⟩

end S1Dt

end NieWeiOrientedSidorenko
