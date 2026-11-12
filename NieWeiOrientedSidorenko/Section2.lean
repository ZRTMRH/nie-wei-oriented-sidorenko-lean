import NieWeiOrientedSidorenko.Families
import NieWeiOrientedSidorenko.Section2Aux

/-!
# Section 2: Claim 2.1, Lemma 2.2, Lemma 2.3

Finite step digraphons, the doubled host `W ⊕ W^T` with its paired partition `𝒬_W`, the paired
stepping formulation of OS (Claim 2.1), the weak Hölder inequality (Lemma 2.2) and the convexity
characterizations of (weakly) norming graphs (Lemma 2.3).
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal

namespace NieWeiOrientedSidorenko

/-- A **finite step digraphon** (convention C12): a finite partition of `[0, 1]` into measurable
parts of positive measure, and a `[0, 1]`-valued value on each pair of parts. -/
structure StepDigraphon where
  /-- The partition into steps. -/
  P : PosPartition (volume : Measure I)
  /-- The value on `P_i × P_j`. -/
  a : Fin P.k → Fin P.k → ℝ
  mem : ∀ i j, a i j ∈ Icc (0 : ℝ) 1

namespace StepDigraphon

/-- The function of a finite step digraphon: `a_{ij}` on `P_i × P_j`. -/
noncomputable def toFun (W : StepDigraphon) : I → I → ℝ :=
  fun x y => ∑ i, ∑ j, (W.P.part i).indicator (fun _ => (1 : ℝ)) x *
    (W.P.part j).indicator (fun _ => (1 : ℝ)) y * W.a i j

end StepDigraphon

/-- The uniform probability measure on the copy label `{false, true}`. -/
noncomputable def halfCount : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure halfCount := ⟨by
  simp [halfCount, Measure.count_apply_finite _ (Set.toFinite _)]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- The probability measure on the two copies `[0, 1] × {false, true}` of the vertex space: each
copy has measure `1/2` (the "equal-measure disjoint union"). -/
noncomputable def twoCopies : Measure (I × Bool) := (volume : Measure I).prod halfCount

instance : IsProbabilityMeasure twoCopies := by
  unfold twoCopies
  infer_instance

/-- The doubled host `W ⊕ W^T` on `[0, 1] × {false, true}`: `W` on the `true` copy, `W^T` on the
`false` copy, and `0` on the two off-diagonal blocks. -/
def doubled (U : I → I → ℝ) : I × Bool → I × Bool → ℝ :=
  fun p q => if p.2 = q.2 then (if p.2 then U p.1 q.1 else U q.1 p.1) else 0

/-- The paired partition `𝒬_W` of `[0, 1] × {false, true}`, merging corresponding step parts of
the two copies: its parts are `P_i × {false, true}`. -/
noncomputable def pairedPartition (W : StepDigraphon) : PosPartition twoCopies where
  k := W.P.k
  part i := W.P.part i ×ˢ univ
  measurableSet_part i := (W.P.measurableSet_part i).prod MeasurableSet.univ
  pos i := by
    unfold twoCopies
    rw [Measure.prod_prod]
    refine ENNReal.mul_pos (W.P.pos i).ne' ?_
    rw [measure_univ]
    exact one_ne_zero
  disjoint i j hij := by
    exact Disjoint.set_prod_left (W.P.disjoint hij) _ _
  cover := by
    rw [← Set.iUnion_prod_const, W.P.cover, Set.univ_prod_univ]

namespace Section2Aux

/-! ### Claim 2.1: step digraphons, the doubled host and its stepping -/

lemma indicator_sum {Ω : Type*} {k : ℕ} (part : Fin k → Set Ω)
    (hdisj : Pairwise fun i j => Disjoint (part i) (part j)) {x : Ω} {i : Fin k}
    (hx : x ∈ part i) (g : Fin k → ℝ) :
    ∑ i', (part i').indicator (fun _ => (1 : ℝ)) x * g i' = g i := by
  rw [Finset.sum_eq_single i]
  · simp [hx]
  · intro j _ hj
    have : x ∉ part j := fun hxj => (hdisj hj).ne_of_mem hxj hx rfl
    simp [this]
  · simp

lemma sd_toFun_eq (W : StepDigraphon) {x y : I} {i j : Fin W.P.k}
    (hx : x ∈ W.P.part i) (hy : y ∈ W.P.part j) : W.toFun x y = W.a i j := by
  unfold StepDigraphon.toFun
  have e : ∀ i', ∑ j', (W.P.part i').indicator (fun _ => (1 : ℝ)) x *
      (W.P.part j').indicator (fun _ => (1 : ℝ)) y * W.a i' j' =
      (W.P.part i').indicator (fun _ => (1 : ℝ)) x * W.a i' j := by
    intro i'
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, indicator_sum W.P.part W.P.disjoint hy]
  simp_rw [e]
  exact indicator_sum W.P.part W.P.disjoint hx _

lemma pp_exists_mem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (P : PosPartition μ) (x : Ω) : ∃ i, x ∈ P.part i := by
  have : x ∈ ⋃ i, P.part i := by rw [P.cover]; exact mem_univ x
  simpa using this

lemma sd_isDigraphon (W : StepDigraphon) : IsDigraphon W.toFun := by
  refine ⟨?_, fun x y => ?_⟩
  · unfold StepDigraphon.toFun
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.mul (Measurable.mul ?_ ?_) measurable_const
    · exact (measurable_const.indicator (W.P.measurableSet_part i)).comp measurable_fst
    · exact (measurable_const.indicator (W.P.measurableSet_part j)).comp measurable_snd
  · obtain ⟨i, hi⟩ := pp_exists_mem W.P x
    obtain ⟨j, hj⟩ := pp_exists_mem W.P y
    rw [sd_toFun_eq W hi hj]
    exact W.mem i j

lemma halfCount_real (b : Bool) : halfCount.real {b} = 1 / 2 := by
  simp [halfCount, measureReal_def]

lemma piHalf_real {V : Type*} [Fintype V] (c : V → Bool) :
    (Measure.pi fun _ : V => halfCount).real {c} = (1 / 2) ^ Fintype.card V := by
  have : ({c} : Set (V → Bool)) = Set.pi univ fun v => {c v} := by
    ext d; simp [funext_iff]
  rw [this, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, halfCount_real]
  simp

open scoped Classical in
/-- The density over the doubled vertex space, as an average over the copy labels. -/
lemma tDir_twoCopies {V : Type*} [Fintype V] (D : OrientedGraph V)
    (G : I × Bool → I × Bool → ℝ) (hG : Measurable (Function.uncurry G))
    (hb : ∀ p q, |G p q| ≤ 1) :
    tDir twoCopies D G = ∑ c : V → Bool, (1 / 2) ^ Fintype.card V *
      ∫ y, ∏ p ∈ D.arcs, G (y p.1, c p.1) (y p.2, c p.2) ∂(πV V) := by
  classical
  have hmp := measurePreserving_arrowProdEquivProdArrow I Bool V (fun _ => (volume : Measure I))
    (fun _ => halfCount)
  set F : (V → I × Bool) → ℝ := fun z => ∏ p ∈ D.arcs, G (z p.1) (z p.2) with hF
  have hFm : Measurable F := Finset.measurable_prod _ fun p _ =>
    hG.comp (f := fun z : V → I × Bool => (z p.1, z p.2)) (by fun_prop)
  unfold tDir twoCopies
  rw [← hmp.symm.integral_comp' F]
  set F' : (V → I) × (V → Bool) → ℝ := fun w => F ((MeasurableEquiv.arrowProdEquivProdArrow I Bool V).symm w)
  have hF'm : Measurable F' := hFm.comp (MeasurableEquiv.measurable _)
  have hF'i : Integrable F' ((πV V).prod (Measure.pi fun _ : V => halfCount)) := by
    refine Integrable.of_bound hF'm.aestronglyMeasurable 1 (Eventually.of_forall fun w => ?_)
    simp only [F', hF, Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p _ => hb _ _
  change ∫ w, F' w ∂((πV V).prod (Measure.pi fun _ : V => halfCount)) = _
  rw [integral_prod_symm _ hF'i, integral_fintype]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [piHalf_real, smul_eq_mul]
    rfl
  · exact Integrable.of_finite

lemma measurable_doubled {U : I → I → ℝ} (hU : Measurable (Function.uncurry U)) :
    Measurable (Function.uncurry (doubled U)) := by
  have hs : MeasurableSet {pq : (I × Bool) × (I × Bool) | pq.1.2 = pq.2.2} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have ht : MeasurableSet {pq : (I × Bool) × (I × Bool) | pq.1.2 = true} :=
    (measurable_snd.comp measurable_fst) (measurableSet_singleton true)
  have h1 : Measurable fun pq : (I × Bool) × (I × Bool) => U pq.1.1 pq.2.1 :=
    hU.comp (f := fun pq : (I × Bool) × (I × Bool) => (pq.1.1, pq.2.1)) (by fun_prop)
  have h2 : Measurable fun pq : (I × Bool) × (I × Bool) => U pq.2.1 pq.1.1 :=
    hU.comp (f := fun pq : (I × Bool) × (I × Bool) => (pq.2.1, pq.1.1)) (by fun_prop)
  exact Measurable.ite hs (Measurable.ite ht h1 h2) measurable_const

lemma abs_doubled_le {U : I → I → ℝ} (hU : IsDigraphon U) (p q : I × Bool) :
    |doubled U p q| ≤ 1 := by
  unfold doubled
  split_ifs
  · rw [abs_of_nonneg (hU.2 _ _).1]; exact (hU.2 _ _).2
  · rw [abs_of_nonneg (hU.2 _ _).1]; exact (hU.2 _ _).2
  · simp

lemma tDir_twoCopies_doubled {V : Type*} [Fintype V] (D : OrientedGraph V)
    (hconn : D.IsConnected) (hsc : D.IsSelfConverse) (U : I → I → ℝ) (hU : IsDigraphon U) :
    tDir twoCopies D (doubled U) = 2 * (1 / 2) ^ Fintype.card V * t D U := by
  classical
  obtain ⟨v0⟩ := hconn.nonempty
  rw [tDir_twoCopies D _ (measurable_doubled hU.1) (abs_doubled_le hU)]
  rw [Fintype.sum_eq_add (fun _ => true) (fun _ => false)]
  · have h1 : ∫ y, ∏ p ∈ D.arcs, doubled U (y p.1, true) (y p.2, true) ∂(πV V) = t D U := by
      simp [doubled, t, tDir]
    have h2 : ∫ y, ∏ p ∈ D.arcs, doubled U (y p.1, false) (y p.2, false) ∂(πV V) = t D U := by
      rw [← t_transpose_eq D hsc U]
      simp [doubled]
    rw [h1, h2]; ring
  · intro h
    have := congrFun h v0
    simp at this
  · rintro c ⟨hc1, hc2⟩
    have : ∃ p ∈ D.arcs, c p.1 ≠ c p.2 := by
      by_contra hno
      push Not at hno
      have hconst := const_of_connected D hconn c hno
      rcases hb : c v0 with _ | _
      · exact hc2 (funext fun v => by rw [hconst v v0, hb])
      · exact hc1 (funext fun v => by rw [hconst v v0, hb])
    obtain ⟨p, hp, hne⟩ := this
    have : ∀ y : V → I, ∏ q ∈ D.arcs, doubled U (y q.1, c q.1) (y q.2, c q.2) = 0 := fun y =>
      Finset.prod_eq_zero hp (by simp [doubled, hne])
    simp [this]

lemma tDir_twoCopies_fst {V : Type*} [Fintype V] (D : OrientedGraph V) (g : I → I → ℝ)
    (hg : Measurable (Function.uncurry g)) (hb : ∀ x y, |g x y| ≤ 1) :
    tDir twoCopies D (fun p q => g p.1 q.1) = t D g := by
  classical
  have hm : Measurable (Function.uncurry fun (p q : I × Bool) => g p.1 q.1) :=
    hg.comp (f := fun pq : (I × Bool) × (I × Bool) => (pq.1.1, pq.2.1)) (by fun_prop)
  rw [tDir_twoCopies D (fun p q => g p.1 q.1) hm fun p q => hb _ _]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
  rw [← mul_assoc]
  push_cast
  rw [← mul_pow]; norm_num
  rfl

lemma indicator_sum2 {Ω : Type*} {k : ℕ} (part : Fin k → Set Ω)
    (hdisj : Pairwise fun i j => Disjoint (part i) (part j)) {x y : Ω} {i j : Fin k}
    (hx : x ∈ part i) (hy : y ∈ part j) (g : Fin k → Fin k → ℝ) :
    ∑ i', ∑ j', (part i').indicator (fun _ => (1 : ℝ)) x *
      (part j').indicator (fun _ => (1 : ℝ)) y * g i' j' = g i j := by
  have e : ∀ i', ∑ j', (part i').indicator (fun _ => (1 : ℝ)) x *
      (part j').indicator (fun _ => (1 : ℝ)) y * g i' j' =
      (part i').indicator (fun _ => (1 : ℝ)) x * g i' j := by
    intro i'
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, indicator_sum part hdisj hy]
  simp_rw [e]
  exact indicator_sum part hdisj hx _

lemma halfProd_real (b b' : Bool) : (halfCount.prod halfCount).real {(b, b')} = 1 / 4 := by
  rw [← Set.singleton_prod_singleton, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul,
    ← measureReal_def, ← measureReal_def, halfCount_real, halfCount_real]
  norm_num

lemma setIntegral_doubled (W : StepDigraphon) (i j : Fin W.P.k) :
    ∫ r in (W.P.part i ×ˢ (univ : Set Bool)) ×ˢ (W.P.part j ×ˢ (univ : Set Bool)),
        doubled W.toFun r.1 r.2 ∂(twoCopies.prod twoCopies) =
      (volume (W.P.part i)).toReal * (volume (W.P.part j)).toReal *
        ((W.a i j + W.a j i) / 4) := by
  classical
  set S := (W.P.part i ×ˢ (univ : Set Bool)) ×ˢ (W.P.part j ×ˢ (univ : Set Bool)) with hS
  have hSm : MeasurableSet S :=
    ((W.P.measurableSet_part i).prod MeasurableSet.univ).prod
      ((W.P.measurableSet_part j).prod MeasurableSet.univ)
  set h : Bool × Bool → ℝ := fun bb => if bb.1 = bb.2 then (if bb.1 then W.a i j else W.a j i)
    else 0 with hh
  set Fi : I × I → ℝ := fun xy => (W.P.part i).indicator (fun _ => (1 : ℝ)) xy.1 *
    (W.P.part j).indicator (fun _ => (1 : ℝ)) xy.2 with hFi
  have step1 : ∫ r in S, doubled W.toFun r.1 r.2 ∂(twoCopies.prod twoCopies) =
      ∫ r in S, h (r.1.2, r.2.2) ∂(twoCopies.prod twoCopies) := by
    refine setIntegral_congr_fun hSm fun r hr => ?_
    obtain ⟨⟨hx, -⟩, ⟨hy, -⟩⟩ := hr
    simp only [doubled, hh, sd_toFun_eq W hx hy, sd_toFun_eq W hy hx]
  have step2 : ∫ r in S, h (r.1.2, r.2.2) ∂(twoCopies.prod twoCopies) =
      ∫ r, Fi (r.1.1, r.2.1) * h (r.1.2, r.2.2) ∂(twoCopies.prod twoCopies) := by
    rw [← integral_indicator hSm]
    congr 1
    funext r
    by_cases hr : r ∈ S
    · rw [indicator_of_mem hr]
      obtain ⟨⟨hx, -⟩, ⟨hy, -⟩⟩ := hr
      simp [hFi, hx, hy]
    · rw [indicator_of_notMem hr]
      have : ¬ (r.1.1 ∈ W.P.part i ∧ r.2.1 ∈ W.P.part j) := fun h' =>
        hr ⟨⟨h'.1, mem_univ _⟩, ⟨h'.2, mem_univ _⟩⟩
      by_cases h1 : r.1.1 ∈ W.P.part i
      · have h2 : r.2.1 ∉ W.P.part j := fun h2 => this ⟨h1, h2⟩
        simp [hFi, h2]
      · simp [hFi, h1]
  have hT := mp_prodProdProdComm (volume : Measure I) halfCount (volume : Measure I) halfCount
  have hFim : Measurable Fi :=
    ((measurable_const.indicator (W.P.measurableSet_part i)).comp measurable_fst).mul
      ((measurable_const.indicator (W.P.measurableSet_part j)).comp measurable_snd)
  have hhm : Measurable h := measurable_of_finite h
  have step3 : ∫ r, Fi (r.1.1, r.2.1) * h (r.1.2, r.2.2) ∂(twoCopies.prod twoCopies) =
      ∫ w, Fi w.1 * h w.2 ∂(((volume : Measure I).prod volume).prod (halfCount.prod halfCount)) := by
    rw [← hT.map_eq, integral_map (f := fun w => Fi w.1 * h w.2) hT.measurable.aemeasurable
      ((hFim.comp measurable_fst).mul (hhm.comp measurable_snd)).aestronglyMeasurable]
    rfl
  have step4 : ∫ w, Fi w ∂((volume : Measure I).prod volume) =
      (volume (W.P.part i)).toReal * (volume (W.P.part j)).toReal := by
    rw [hFi, integral_prod_mul (f := fun x : I => (W.P.part i).indicator (fun _ => (1 : ℝ)) x)
      (g := fun y : I => (W.P.part j).indicator (fun _ => (1 : ℝ)) y),
      integral_indicator_const _ (W.P.measurableSet_part i),
      integral_indicator_const _ (W.P.measurableSet_part j)]
    simp [measureReal_def]
  have step5 : ∫ bb, h bb ∂(halfCount.prod halfCount) = (W.a i j + W.a j i) / 4 := by
    rw [integral_fintype Integrable.of_finite]
    simp only [halfProd_real, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool, hh]
    simp
    ring
  rw [step1, step2, step3, integral_prod_mul, step4, step5]

lemma twoCopies_part (W : StepDigraphon) (i : Fin W.P.k) :
    twoCopies (W.P.part i ×ˢ (univ : Set Bool)) = volume (W.P.part i) := by
  unfold twoCopies
  rw [Measure.prod_prod, measure_univ, mul_one]

lemma stepAvg_paired (W : StepDigraphon) (p q : I × Bool) :
    stepAvg (pairedPartition W) (doubled W.toFun) p q = symmetrize W.toFun p.1 q.1 / 2 := by
  obtain ⟨i, hi⟩ := pp_exists_mem W.P p.1
  obtain ⟨j, hj⟩ := pp_exists_mem W.P q.1
  have hp : p ∈ (pairedPartition W).part i := ⟨hi, mem_univ _⟩
  have hq : q ∈ (pairedPartition W).part j := ⟨hj, mem_univ _⟩
  unfold stepAvg
  rw [indicator_sum2 (pairedPartition W).part (pairedPartition W).disjoint hp hq]
  change (∫ r in (W.P.part i ×ˢ (univ : Set Bool)) ×ˢ (W.P.part j ×ˢ (univ : Set Bool)),
      doubled W.toFun r.1 r.2 ∂(twoCopies.prod twoCopies)) /
      ((twoCopies (W.P.part i ×ˢ (univ : Set Bool))).toReal *
        (twoCopies (W.P.part j ×ˢ (univ : Set Bool))).toReal) = _
  rw [setIntegral_doubled, twoCopies_part, twoCopies_part]
  have hpi : 0 < (volume (W.P.part i)).toReal :=
    ENNReal.toReal_pos (W.P.pos i).ne' (measure_ne_top _ _)
  have hpj : 0 < (volume (W.P.part j)).toReal :=
    ENNReal.toReal_pos (W.P.pos j).ne' (measure_ne_top _ _)
  simp only [symmetrize, sd_toFun_eq W hi hj, sd_toFun_eq W hj hi]
  field_simp
  ring

lemma t_smul {V : Type*} [Fintype V] (D : OrientedGraph V) (U : I → I → ℝ) (c : ℝ) :
    t D (fun x y => c * U x y) = c ^ D.arcs.card * t D U := by
  unfold t tDir
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  exact integral_const_mul _ _

lemma t_nonneg {V : Type*} [Fintype V] (D : OrientedGraph V) (U : I → I → ℝ)
    (hU : ∀ x y, 0 ≤ U x y) : 0 ≤ t D U :=
  integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => hU _ _

lemma claim_lhs {V : Type*} [Fintype V] (D : OrientedGraph V) (W : StepDigraphon) :
    tDir twoCopies D (stepAvg (pairedPartition W) (doubled W.toFun)) =
      (1 / 2) ^ D.arcs.card * t D (symmetrize W.toFun) := by
  have hS := isDigraphon_symmetrize (sd_isDigraphon W)
  have e : stepAvg (pairedPartition W) (doubled W.toFun) =
      fun p q => (fun x y => (1 / 2 : ℝ) * symmetrize W.toFun x y) p.1 q.1 := by
    funext p q; rw [stepAvg_paired]; ring
  rw [e, tDir_twoCopies_fst D (fun x y => (1 / 2 : ℝ) * symmetrize W.toFun x y)
    (hS.1.const_mul _) fun x y => ?_, t_smul]
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (hS.2 x y).1)]
  linarith [(hS.2 x y).2]

lemma card_le_arcs_add_one {V : Type*} [Fintype V] (D : OrientedGraph V)
    (hconn : D.IsConnected) : Fintype.card V ≤ D.arcs.card + 1 := by
  classical
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have h2 : Nat.card D.underlying.edgeSet ≤ Nat.card {p // p ∈ D.arcs} := by
    refine Nat.card_le_card_of_surjective (fun p : {p // p ∈ D.arcs} =>
      (⟨s(p.1.1, p.1.2), ?_⟩ : D.underlying.edgeSet)) ?_
    · rw [SimpleGraph.mem_edgeSet]
      have := (mem_arcs D p.1).1 p.2
      simp only [OrientedGraph.underlying, SimpleGraph.fromRel_adj]
      exact ⟨fun h => D.irrefl p.1.1 (by rwa [← h] at this), Or.inl this⟩
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at he
        simp only [OrientedGraph.underlying, SimpleGraph.fromRel_adj] at he
        rcases he.2 with h | h
        · exact ⟨⟨(u, v), (mem_arcs D _).2 h⟩, rfl⟩
        · exact ⟨⟨(v, u), (mem_arcs D _).2 h⟩, Subtype.ext Sym2.eq_swap⟩
  rw [Nat.card_eq_fintype_card] at h1
  rw [Nat.card_eq_fintype_card (α := {p // p ∈ D.arcs}), Fintype.card_coe] at h2
  omega

/-- The transported tensor square of a finite step digraphon. -/
noncomputable def sqSD {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (W : StepDigraphon) : StepDigraphon where
  P :=
    { k := W.P.k * W.P.k
      part := fun l => φ ⁻¹' (W.P.part (finProdFinEquiv.symm l).1 ×ˢ
        W.P.part (finProdFinEquiv.symm l).2)
      measurableSet_part := fun l => hφ.measurable
        ((W.P.measurableSet_part _).prod (W.P.measurableSet_part _))
      pos := fun l => by
        rw [hφ.measure_preimage ((W.P.measurableSet_part _).prod
          (W.P.measurableSet_part _)).nullMeasurableSet, Measure.prod_prod]
        exact ENNReal.mul_pos (W.P.pos _).ne' (W.P.pos _).ne'
      disjoint := fun l l' hll' => by
        refine Disjoint.preimage _ ?_
        have : finProdFinEquiv.symm l ≠ finProdFinEquiv.symm l' :=
          fun h => hll' (finProdFinEquiv.symm.injective h)
        rcases Prod.ext_iff.not.1 this |> not_and_or.1 with h | h
        · exact Disjoint.set_prod_left (W.P.disjoint h) _ _
        · exact Disjoint.set_prod_right (W.P.disjoint h) _ _
      cover := by
        ext x
        simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
        obtain ⟨i, hi⟩ := pp_exists_mem W.P (φ x).1
        obtain ⟨j, hj⟩ := pp_exists_mem W.P (φ x).2
        exact ⟨finProdFinEquiv (i, j), by simpa using ⟨hi, hj⟩⟩ }
  a := fun l l' => W.a (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l').1 *
    W.a (finProdFinEquiv.symm l).2 (finProdFinEquiv.symm l').2
  mem := fun l l' => ⟨mul_nonneg (W.mem _ _).1 (W.mem _ _).1,
    by
      have h1 := W.mem (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l').1
      have h2 := W.mem (finProdFinEquiv.symm l).2 (finProdFinEquiv.symm l').2
      nlinarith [h1.1, h1.2, h2.1, h2.2]⟩

lemma sqSD_toFun {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    (W : StepDigraphon) : (sqSD hφ W).toFun = sqK φ W.toFun := by
  funext x y
  obtain ⟨i, hi⟩ := pp_exists_mem W.P (φ x).1
  obtain ⟨j, hj⟩ := pp_exists_mem W.P (φ x).2
  obtain ⟨i', hi'⟩ := pp_exists_mem W.P (φ y).1
  obtain ⟨j', hj'⟩ := pp_exists_mem W.P (φ y).2
  have hx : x ∈ (sqSD hφ W).P.part (finProdFinEquiv (i, j)) := by
    change φ x ∈ _ ×ˢ _; simpa using ⟨hi, hj⟩
  have hy : y ∈ (sqSD hφ W).P.part (finProdFinEquiv (i', j')) := by
    change φ y ∈ _ ×ˢ _; simpa using ⟨hi', hj'⟩
  rw [sd_toFun_eq _ hx hy, sqK, sd_toFun_eq W hi hi', sd_toFun_eq W hj hj']
  simp [sqSD]

/-- The grid step digraphon. -/
noncomputable def gridSD (n : ℕ) (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hh : ∀ i j, h i j ∈ Icc (0 : ℝ) 1) : StepDigraphon where
  P :=
    { k := n + 1
      part := fun i => gridIdx n ⁻¹' {i}
      measurableSet_part := fun i => measurable_gridIdx n (measurableSet_singleton i)
      pos := fun i => volume_gridIdx_pos n i
      disjoint := fun i j hij => by
        refine Disjoint.preimage _ ?_
        simpa using hij
      cover := by ext x; simp }
  a := h
  mem := hh

lemma gridSD_toFun (n : ℕ) (h : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hh : ∀ i j, h i j ∈ Icc (0 : ℝ) 1) (x y : I) :
    (gridSD n h hh).toFun x y = h (gridIdx n x) (gridIdx n y) :=
  sd_toFun_eq (gridSD n h hh) (i := gridIdx n x) (j := gridIdx n y) rfl rfl

lemma t_symm_eq {V : Type*} [Fintype V] (D : OrientedGraph V) (U : I → I → ℝ)
    (hU : IsDigraphon U) :
    t D (symmetrize U) = (1 / 2) ^ D.arcs.card * ∑ F ∈ D.arcs.powerset, revDens D.arcs F U :=
  t_symmetrize D.arcs U hU

/-- The converse direction for finite step digraphons: the tensor-power argument. -/
lemma step_OS {V : Type*} [Fintype V] (D : OrientedGraph V) {C : ℝ}
    (hC : ∀ W : StepDigraphon, t D (symmetrize W.toFun) ≤ C * t D W.toFun)
    (W : StepDigraphon) : t D (symmetrize W.toFun) ≤ t D W.toFun := by
  classical
  obtain ⟨φ, hφ⟩ := exists_split
  have hsq : ∀ W : StepDigraphon, t D (symmetrize W.toFun) ^ 2 ≤
      t D (symmetrize (sqSD hφ W).toFun) := by
    intro W
    have hk : IsKernel W.toFun := ⟨(sd_isDigraphon W).1, 1, fun x y => by
      rw [abs_of_nonneg ((sd_isDigraphon W).2 x y).1]; exact ((sd_isDigraphon W).2 x y).2⟩
    rw [t_symm_eq D _ (sd_isDigraphon W), t_symm_eq D _ (sd_isDigraphon _), sqSD_toFun]
    simp_rw [revDens_sqK hφ _ _ _ hk]
    have hcs := sq_sum_le_card_mul_sum_sq (s := D.arcs.powerset)
      (f := fun F => revDens D.arcs F W.toFun)
    rw [Finset.card_powerset] at hcs
    have h2 : ((1 / 2 : ℝ) ^ D.arcs.card) ^ 2 * (2 : ℝ) ^ D.arcs.card = (1 / 2) ^ D.arcs.card := by
      rw [sq, mul_assoc, ← mul_pow]; norm_num
    calc ((1 / 2 : ℝ) ^ D.arcs.card * ∑ F ∈ D.arcs.powerset, revDens D.arcs F W.toFun) ^ 2
        = ((1 / 2 : ℝ) ^ D.arcs.card) ^ 2 * (∑ F ∈ D.arcs.powerset, revDens D.arcs F W.toFun) ^ 2 :=
          by ring
      _ ≤ ((1 / 2 : ℝ) ^ D.arcs.card) ^ 2 * (((2 ^ D.arcs.card : ℕ) : ℝ) *
            ∑ F ∈ D.arcs.powerset, revDens D.arcs F W.toFun ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (1 / 2) ^ D.arcs.card * ∑ F ∈ D.arcs.powerset, revDens D.arcs F W.toFun ^ 2 := by
          push_cast; rw [← mul_assoc, h2]
  have htsq : ∀ W : StepDigraphon, t D (sqSD hφ W).toFun = t D W.toFun ^ 2 := by
    intro W
    have hk : IsKernel W.toFun := ⟨(sd_isDigraphon W).1, 1, fun x y => by
      rw [abs_of_nonneg ((sd_isDigraphon W).2 x y).1]; exact ((sd_isDigraphon W).2 x y).2⟩
    rw [sqSD_toFun, t_eq_revDens, t_eq_revDens, revDens_sqK hφ _ _ _ hk]
  have key : ∀ j : ℕ, ∀ W : StepDigraphon,
      t D (symmetrize W.toFun) ^ (2 ^ j) ≤ C * t D W.toFun ^ (2 ^ j) := by
    intro j
    induction j with
    | zero => intro W; simpa using hC W
    | succ j ih =>
      intro W
      have h1 := ih (sqSD hφ W)
      rw [htsq, ← pow_mul, ← pow_succ'] at h1
      refine le_trans ?_ h1
      rw [pow_succ', pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) (hsq W) _
  set a := t D (symmetrize W.toFun)
  set b := t D W.toFun
  have ha : 0 ≤ a := t_nonneg D _ fun x y => ((isDigraphon_symmetrize (sd_isDigraphon W)).2 x y).1
  have hb : 0 ≤ b := t_nonneg D _ fun x y => ((sd_isDigraphon W).2 x y).1
  by_contra hab
  replace hab := not_le.mp hab
  rcases hb.eq_or_lt with hb0 | hb0
  · have h0 : a ^ 2 ^ 0 ≤ C * b ^ 2 ^ 0 := key 0 W
    rw [← hb0] at h0
    simp at h0
    linarith
  · have hr : 1 < a / b := (one_lt_div hb0).2 hab
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hr
    have h1 := key k W
    have h2 : (a / b) ^ k ≤ (a / b) ^ (2 ^ k) := pow_le_pow_right₀ hr.le Nat.lt_two_pow_self.le
    have h3 : (a / b) ^ (2 ^ k) ≤ C := by
      rw [div_pow, div_le_iff₀ (pow_pos hb0 _)]; exact h1
    linarith

/-- Step digraphons approximate: the OS inequality passes from step digraphons to all
digraphons. -/
lemma OS_of_step {V : Type*} [Fintype V] (D : OrientedGraph V)
    (h : ∀ W : StepDigraphon, t D (symmetrize W.toFun) ≤ t D W.toFun) : D.IsOSK := by
  intro U hU
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set M : ℝ := (D.numArcs : ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  set δ := ε / (2 * (M + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n, g, hg, hint⟩ := exists_grid_approx U hU hδ0
  set W := gridSD n g hg
  have hWf : W.toFun = fun x y => g (gridIdx n x) (gridIdx n y) := by
    funext x y; exact gridSD_toFun n g hg x y
  have hWd := sd_isDigraphon W
  have hint' : ∫ q, |W.toFun q.1 q.2 - U q.1 q.2| ∂((volume : Measure I).prod volume) ≤ δ := by
    rw [hWf]; exact hint
  have hint'' : ∫ q, |U q.1 q.2 - W.toFun q.1 q.2| ∂((volume : Measure I).prod volume) ≤ δ := by
    simp_rw [abs_sub_comm (U _ _)]; exact hint'
  have e1 := abs_t_sub_le D _ _ (isDigraphon_symmetrize hU) (isDigraphon_symmetrize hWd)
  have e2 := integral_symm_sub_le U W.toFun hU hWd
  have e3 := abs_t_sub_le D _ _ hWd hU
  have e4 := h W
  have hMδ : M * δ ≤ ε / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  have i1 : t D (symmetrize U) ≤ t D (symmetrize W.toFun) + M * δ := by
    have := (le_abs_self _).trans e1
    have := mul_le_mul_of_nonneg_left (e2.trans hint'') hM
    linarith
  have i2 : t D W.toFun ≤ t D U + M * δ := by
    have := (le_abs_self _).trans e3
    have := mul_le_mul_of_nonneg_left hint' hM
    linarith
  linarith

end Section2Aux

/-- **Claim 2.1.** Let `D` be a connected directed graph with `D ≅ D^T`. Then `D` is OS if and
only if `t(D, (W ⊕ W^T)_{𝒬_W}) ≤ t(D, W ⊕ W^T)` for every finite step digraphon `W`. (OS in the
digraphon formulation of Section 2.) -/
theorem claim_2_1 {V : Type*} [Fintype V] (D : OrientedGraph V) (hconn : D.IsConnected)
    (hsc : D.IsSelfConverse) :
    D.IsOSK ↔ ∀ W : StepDigraphon,
      tDir twoCopies D (stepAvg (pairedPartition W) (doubled W.toFun)) ≤
        tDir twoCopies D (doubled W.toFun) := by
  open Section2Aux in
  have hrhs : ∀ W : StepDigraphon, tDir twoCopies D (doubled W.toFun) =
      2 * (1 / 2) ^ Fintype.card V * t D W.toFun := fun W =>
    tDir_twoCopies_doubled D hconn hsc _ (sd_isDigraphon W)
  constructor
  · intro hOS W
    rw [Section2Aux.claim_lhs, hrhs]
    have h1 := hOS W.toFun (Section2Aux.sd_isDigraphon W)
    have h0 := Section2Aux.t_nonneg D W.toFun fun x y => ((Section2Aux.sd_isDigraphon W).2 x y).1
    have hn := Section2Aux.card_le_arcs_add_one D hconn
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 hconn.nonempty
    have hc : (1 / 2 : ℝ) ^ D.arcs.card ≤ 2 * (1 / 2) ^ Fintype.card V := by
      have e : 2 * (1 / 2 : ℝ) ^ Fintype.card V = (1 / 2) ^ (Fintype.card V - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ]
        ring
      rw [e]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc (1 / 2 : ℝ) ^ D.arcs.card * t D (symmetrize W.toFun)
        ≤ (1 / 2) ^ D.arcs.card * t D W.toFun := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * (1 / 2) ^ Fintype.card V * t D W.toFun := mul_le_mul_of_nonneg_right hc h0
  · intro h
    refine Section2Aux.OS_of_step D (Section2Aux.step_OS D
      (C := 2 * (1 / 2) ^ Fintype.card V / (1 / 2) ^ D.arcs.card) fun W => ?_)
    have h1 := h W
    rw [Section2Aux.claim_lhs, hrhs] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
    exact h1

/-- **Lemma 2.2 (weak Hölder inequality).** Let `H = (X ∪ Y, E)` be weakly norming and
`𝐔 = (U_e)_{e ∈ E(H)}` a decoration of `H` by kernels. Then
`|t_bi(H; 𝐔)| ≤ ∏_{e ∈ E(H)} t_bi(H, |U_e|)^{1/e(H)}`. -/
theorem lemma_2_2 {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (hE : IsWeaklyNorming E) (U : X × Y → I → I → ℝ) (hU : ∀ p ∈ E, IsKernel (U p)) :
    |tBiDec volume E U| ≤ ∏ p ∈ E, tb E (fun x y => |U p x y|) ^ ((1 : ℝ) / E.card) := by
  exact Section2Aux.weak_holder E hE U hU

/-- **Lemma 2.3(1).** For a bipartite graph `H = (X ∪ Y, E)` with a fixed bipartition and
`e(H) > 0`: `H` is weakly norming if and only if `t_bi(H, ·)` is convex on nonnegative
kernels. -/
theorem lemma_2_3_1 {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (hE : 0 < E.card) : IsWeaklyNorming E ↔ ConvexOnNonnegKernels E := by
  exact Section2Aux.lemma_2_3_1_aux E hE

/-- **Lemma 2.3(2).** For a bipartite graph `H = (X ∪ Y, E)` with a fixed bipartition and
`e(H) > 0`: `H` is norming if and only if `t_bi(H, ·)` is strictly convex on real-valued
kernels. -/
theorem lemma_2_3_2 {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (hE : 0 < E.card) : IsNorming E ↔ StrictConvexOnKernels E := by
  exact Section2Aux.lemma_2_3_2_aux E hE

end NieWeiOrientedSidorenko
