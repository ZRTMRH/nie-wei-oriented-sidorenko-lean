import NieWeiOrientedSidorenko.Section6

/-!
# Auxiliary lemmas for Section 1

Proof material for the results of `NieWeiOrientedSidorenko/Section1.lean` (moved here unchanged).
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace Section1Aux


lemma tb_map_equiv {X Y X' Y' : Type*} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (e1 : X ≃ X') (e2 : Y ≃ Y') (E : Finset (X × Y)) (U : I → I → ℝ) :
    tb (E.map (e1.prodCongr e2).toEmbedding) U = tb E U := by
  unfold tb tBi
  set Φ : (X → I) × (Y → I) ≃ᵐ (X' → I) × (Y' → I) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.arrowCongr' e1 (MeasurableEquiv.refl I))
      (MeasurableEquiv.arrowCongr' e2 (MeasurableEquiv.refl I)) with hΦ
  have hmp : MeasurePreserving Φ ((Measure.pi fun _ : X => (volume : Measure I)).prod
      (Measure.pi fun _ : Y => (volume : Measure I)))
      ((Measure.pi fun _ : X' => (volume : Measure I)).prod
      (Measure.pi fun _ : Y' => (volume : Measure I))) := by
    refine MeasurePreserving.prod ?_ ?_
    · exact measurePreserving_arrowCongr' _ _ e1 _ (fun _ => MeasurePreserving.id _)
    · exact measurePreserving_arrowCongr' _ _ e2 _ (fun _ => MeasurePreserving.id _)
  rw [← hmp.integral_comp']
  have hz : ∀ z, Φ z = (fun x => z.1 (e1.symm x), fun y => z.2 (e2.symm y)) := fun z => rfl
  congr 1
  funext z
  rw [Finset.prod_map, hz]
  simp

lemma isWeaklyNorming_map_equiv {X Y X' Y' : Type*} [Fintype X] [Fintype Y] [Fintype X']
    [Fintype Y'] (e1 : X ≃ X') (e2 : Y ≃ Y') (E : Finset (X × Y)) :
    IsWeaklyNorming (E.map (e1.prodCongr e2).toEmbedding) ↔ IsWeaklyNorming E := by
  have : rNorm (E.map (e1.prodCongr e2).toEmbedding) = rNorm E := by
    funext U
    simp only [rNorm, tb_map_equiv, Finset.card_map]
  unfold IsWeaklyNorming
  rw [this]

/-- A property preserved along edges of a connected graph is constant. -/
lemma connected_const {V : Type*} {G : SimpleGraph V} (hG : G.Connected) (P : V → Prop)
    (hP : ∀ u v, G.Adj u v → (P u ↔ P v)) (u v : V) : P u ↔ P v := by
  obtain ⟨w⟩ := hG.preconnected u v
  induction w with
  | nil => exact Iff.rfl
  | cons h _ ih => exact (hP _ _ h).trans ih


lemma mem_sideEdges {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → Prop)
    (p : {v // s v} × {v // ¬ s v}) : p ∈ sideEdges H s ↔ H.Adj p.1 p.2 := by
  classical
  unfold sideEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma isWeaklyNorming_sideEdges_comp {V : Type*} [Fintype V] (H : SimpleGraph V) (g : V ≃ V)
    (hg : ∀ u v, H.Adj (g u) (g v) ↔ H.Adj u v) (s : V → Prop) :
    (letI := Classical.decPred (fun v => s (g v));
      IsWeaklyNorming (sideEdges H (fun v => s (g v)))) ↔
    (letI := Classical.decPred s;
      IsWeaklyNorming (sideEdges H s)) := by
  classical
  set e1 : {v // s (g v)} ≃ {v // s v} := g.subtypeEquiv (fun _ => Iff.rfl)
  set e2 : {v // ¬ s (g v)} ≃ {v // ¬ s v} := g.subtypeEquiv (fun _ => Iff.rfl)
  have hE : sideEdges H s = (sideEdges H (fun v => s (g v))).map (e1.prodCongr e2).toEmbedding := by
    ext p
    simp only [Finset.mem_map, mem_sideEdges, Equiv.coe_toEmbedding, Equiv.prodCongr_apply]
    constructor
    · intro h
      refine ⟨(e1.symm p.1, e2.symm p.2), ?_, ?_⟩
      · rw [← hg]
        simpa [e1, e2] using h
      · simp
    · rintro ⟨q, hq, rfl⟩
      simpa [e1, e2, hg] using hq
  show IsWeaklyNorming _ ↔ IsWeaklyNorming _
  rw [hE, isWeaklyNorming_map_equiv]


open OrientedGraph in
lemma oneDirection_of_hom {V : Type*} (D : OrientedGraph V) (h : D.HomToDirEdge) :
    D.IsOneDirection := by
  obtain ⟨f, hf⟩ := h
  refine ⟨{u | f u = 0}, fun u v huv => ⟨(hf u v huv).1, ?_⟩⟩
  simp only [Set.mem_ofPred_eq, (hf u v huv).2]
  decide

open OrientedGraph in
lemma hom_of_oneDirection {V : Type*} (D : OrientedGraph V) (h : D.IsOneDirection) :
    D.HomToDirEdge := by
  classical
  obtain ⟨A, hA⟩ := h
  refine ⟨fun u => if u ∈ A then 0 else 1, fun u v huv => ?_⟩
  simp [(hA u v huv).1, (hA u v huv).2]

open OrientedGraph in
lemma underlying_adj_iff' {V : Type*} (D : OrientedGraph V) (a b : V) :
    D.underlying.Adj a b ↔ D.Adj a b ∨ D.Adj b a := by
  simp only [OrientedGraph.underlying, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · rintro (h | h)
    · exact ⟨fun hab => D.irrefl a (hab ▸ h), Or.inl h⟩
    · exact ⟨fun hab => D.irrefl a (hab ▸ h), Or.inr h⟩

open OrientedGraph in
lemma underlying_iso_of_selfConverse {V : Type*} (D : OrientedGraph V) (g : D.Iso D.transpose)
    (u v : V) : D.underlying.Adj (g.toEquiv u) (g.toEquiv v) ↔ D.underlying.Adj u v := by
  have h := g.map_adj_iff
  simp only [OrientedGraph.transpose] at h
  rw [underlying_adj_iff', underlying_adj_iff', h, h]
  exact or_comm

open OrientedGraph in
/-- From (a), (b), (c) of Theorem 1.2: a weakly norming bipartition with all arcs from the first
part to the second (the hypothesis (c) of Theorem 4.1). -/
lemma exists_side {V : Type*} [Fintype V] (D : OrientedGraph V) (hconn : D.IsConnected)
    (hone : D.IsOneDirection) (g : D.Iso D.transpose)
    (hwn : IsWeaklyNormingGraph D.underlying) :
    ∃ s : V → Prop, (∀ u v, D.Adj u v → s u ∧ ¬ s v) ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges D.underlying s) := by
  obtain ⟨s, hs, hw⟩ := hwn
  obtain ⟨A, hA⟩ := hone
  have hP : ∀ u v, D.underlying.Adj u v → ((s u ↔ u ∈ A) ↔ (s v ↔ v ∈ A)) := by
    intro u v huv
    have h1 := hs u v huv
    have h2 : (u ∈ A ↔ ¬ v ∈ A) := by
      rcases (underlying_adj_iff' D u v).mp huv with h | h
      · exact ⟨fun _ => (hA u v h).2, fun _ => (hA u v h).1⟩
      · exact ⟨fun hu => absurd hu (hA v u h).2, fun hv => absurd (hA v u h).1 hv⟩
    tauto
  have hconst := connected_const hconn _ hP
  obtain ⟨v0⟩ := hconn.nonempty
  by_cases h0 : (s v0 ↔ v0 ∈ A)
  · refine ⟨s, fun u v huv => ?_, hw⟩
    have hu := (hconst u v0).mpr h0
    have hv := (hconst v v0).mpr h0
    exact ⟨hu.mpr (hA u v huv).1, fun h => (hA u v huv).2 (hv.mp h)⟩
  · have hall : ∀ u, (s u ↔ u ∉ A) := fun u => by
      have := (not_congr (hconst u v0)).mpr h0
      tauto
    refine ⟨fun v => s (g.toEquiv v), fun u v huv => ?_, ?_⟩
    · have h' : D.Adj (g.toEquiv v) (g.toEquiv u) := by
        have := (g.map_adj_iff u v).mpr huv
        simpa [OrientedGraph.transpose] using this
      exact ⟨(hall _).mpr (hA _ _ h').2, fun h => ((hall _).mp h) (hA _ _ h').1⟩
    · exact (isWeaklyNorming_sideEdges_comp D.underlying g.toEquiv
        (underlying_iso_of_selfConverse D g) s).mpr hw

open OrientedGraph in
theorem osk_char {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (he : 1 ≤ D.numArcs) :
    D.IsOSK ↔ D.IsOneDirection ∧ D.IsSelfConverse ∧ IsWeaklyNormingGraph D.underlying := by
  constructor
  · intro hD
    exact ⟨oneDirection_of_hom D (lemma_4_2 D hD), lemma_4_4 hA1 D hconn hD,
      lemma_4_5 hA1 D hconn he hD⟩
  · rintro ⟨hone, ⟨g⟩, hwn⟩
    exact thm_4_1 D (hom_of_oneDirection D hone) ⟨g⟩ (exists_side D hconn hone g hwn)

/-- Glue a value at `c` with values elsewhere. -/
def glue {V : Type*} [DecidableEq V] (c : V) (a : I) (y : {v // v ≠ c} → I) : V → I :=
  fun v => if h : v = c then a else y ⟨v, h⟩

lemma integral_split {V : Type*} [Fintype V] [DecidableEq V] (c : V) (F : (V → I) → ℝ)
    (hF : Integrable F (Measure.pi fun _ => (volume : Measure I))) :
    ∫ x, F x ∂(Measure.pi fun _ => (volume : Measure I)) =
      ∫ a : I, ∫ y, F (glue c a y) ∂(Measure.pi fun _ : {v // v ≠ c} => (volume : Measure I)) := by
  have hmp := measurePreserving_piEquivPiSubtypeProd (α := fun _ : V => (I : Type))
    (fun _ => (volume : Measure I)) (fun v => v = c)
  have hmps := hmp.symm
  rw [← hmps.integral_comp']
  have hint : Integrable (fun z => F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => (I : Type))
      (fun v => v = c)).symm z)) _ :=
    (hmps.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hF
  rw [integral_prod _ hint]
  have hu : MeasurePreserving (MeasurableEquiv.funUnique {v // v = c} I).symm
      (volume : Measure I) (@Measure.pi {v // v = c} (fun _ => I) (Subtype.fintype _) _
        (fun _ => (volume : Measure I))) := by
    convert (measurePreserving_funUnique (volume : Measure I) {v // v = c}).symm
  exact (hu.integral_comp' _).symm


lemma prod_ne_center {V : Type*} [Fintype V] [DecidableEq V] (c : V) (f : V → ℝ) (hf : f c = 1) :
    ∏ v : {v // v ≠ c}, f v = ∏ v, f v := by
  rw [← Finset.prod_erase Finset.univ hf]
  exact (Finset.prod_subtype (p := fun v => v ≠ c) (Finset.univ.erase c) (fun v => by simp) f).symm

lemma glue_ne {V : Type*} [DecidableEq V] (c : V) (a : I) (y : {v // v ≠ c} → I) (v : {v // v ≠ c}) :
    glue c a y v = y v := by
  simp [glue, v.2]

lemma glue_self {V : Type*} [DecidableEq V] (c : V) (a : I) (y : {v // v ≠ c} → I) :
    glue c a y c = a := by
  simp [glue]

lemma measurable_pair {V : Type*} {U : I → I → ℝ} (hU : Measurable (Function.uncurry U))
    (a b : V) : Measurable (fun x : V → I => U (x a) (x b)) :=
  show Measurable (Function.uncurry U ∘ fun x : V → I => (x a, x b)) from
    hU.comp ((measurable_pi_apply a).prodMk (measurable_pi_apply b))

lemma integrable_arcs {V : Type*} [Fintype V] (D : OrientedGraph V) {U : I → I → ℝ}
    (hU : IsDigraphon U) :
    Integrable (fun x : V → I => ∏ p ∈ D.arcs, U (x p.1) (x p.2))
      (Measure.pi fun _ => (volume : Measure I)) := by
  refine Integrable.of_bound (Finset.measurable_prod _ fun p _ => measurable_pair hU.1 _ _
    ).aestronglyMeasurable 1 (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p _ => by
    rw [abs_le]; constructor <;> linarith [(hU.2 (x p.1) (x p.2)).1, (hU.2 (x p.1) (x p.2)).2]

open OrientedGraph in
/-- Density of a directed graph all of whose arcs meet the vertex `c`. -/
lemma t_center {V : Type*} [Fintype V] [DecidableEq V] (D : OrientedGraph V) (c : V)
    (hc : ∀ u v, D.Adj u v → u = c ∨ v = c) (U : I → I → ℝ) (hU : IsDigraphon U) :
    t D U = ∫ a : I, (∫ b, U a b) ^ D.outDeg c * (∫ b, U b a) ^ D.inDeg c := by
  classical
  set k : V → I → I → ℝ := fun v a b =>
    if D.Adj c v then U a b else if D.Adj v c then U b a else 1 with hk
  have hprod : ∀ x : V → I, ∏ p ∈ D.arcs, U (x p.1) (x p.2) = ∏ v, k v (x c) (x v) := by
    intro x
    have harcs : D.arcs = ((Finset.univ.filter fun v => D.Adj c v).map
        ⟨fun v => (c, v), fun _ _ h => (Prod.ext_iff.mp h).2⟩).disjUnion
        ((Finset.univ.filter fun v => D.Adj v c).map
        ⟨fun v => (v, c), fun _ _ h => (Prod.ext_iff.mp h).1⟩) (by
          rw [Finset.disjoint_left]
          intro p h1 h2
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            ] at h1 h2
          obtain ⟨v, hv, rfl⟩ := h1
          obtain ⟨w, hw, hw'⟩ := h2
          have e1 : w = c := congrArg Prod.fst hw'
          have e2 : c = v := congrArg Prod.snd hw'
          rw [e1] at hw
          exact D.irrefl _ hw) := by
      ext p
      simp only [Section6Aux.mem_arcs_iff, Finset.disjUnion_eq_union, Finset.mem_union,
        Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        ]
      constructor
      · intro h
        rcases hc _ _ h with h1 | h1
        · exact Or.inl ⟨p.2, h1 ▸ h, Prod.ext h1.symm rfl⟩
        · exact Or.inr ⟨p.1, h1 ▸ h, Prod.ext rfl h1.symm⟩
      · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) <;> exact hv
    rw [harcs, Finset.prod_disjUnion, Finset.prod_map, Finset.prod_map]
    simp only [hk]
    rw [Finset.prod_ite, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_filter]
    congr 1
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨D.asymm _ _ h, h⟩
    · intro h; exact h.2
  unfold t tDir
  simp_rw [hprod]
  rw [integral_split c]
  · congr 1
    funext a
    have hk1 : ∀ y : {v // v ≠ c} → I, ∏ v, k v (glue c a y c) (glue c a y v) =
        ∏ v : {v // v ≠ c}, k v a (y v) := by
      intro y
      rw [← prod_ne_center c (fun v => k v (glue c a y c) (glue c a y v)) (by
        simp [hk, D.irrefl])]
      simp only [glue_self, glue_ne]
    simp_rw [hk1]
    rw [integral_fintype_prod_eq_prod (fun (v : {v // v ≠ c}) b => k v a b)]
    have hk2 : ∀ v : V, ∫ b, k v a b = if D.Adj c v then ∫ b, U a b else
        if D.Adj v c then ∫ b, U b a else 1 := by
      intro v
      simp only [hk]
      split_ifs <;> simp
    simp_rw [hk2]
    rw [prod_ne_center c (fun v => if D.Adj c v then ∫ b, U a b else
        if D.Adj v c then ∫ b, U b a else 1) (by simp [D.irrefl])]
    rw [Finset.prod_ite, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_filter,
      Finset.prod_const, Finset.prod_const]
    congr 2
    · simp only [OrientedGraph.inDeg]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨D.asymm _ _ h, h⟩
  · have := integrable_arcs D hU
    simp_rw [hprod] at this
    exact this


lemma isDigraphon_symmetrize {U : I → I → ℝ} (hU : IsDigraphon U) :
    IsDigraphon (symmetrize U) := by
  refine ⟨?_, fun x y => ?_⟩
  · have h2 : Measurable (fun p : I × I => U p.2 p.1) := hU.1.comp measurable_swap
    exact (hU.1.add h2).div_const 2
  · have h1 := hU.2 x y
    have h2 := hU.2 y x
    simp only [symmetrize, Set.mem_Icc] at *
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma integrable_row {U : I → I → ℝ} (hU : IsDigraphon U) (a : I) :
    Integrable (fun b => U a b) := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun b => ?_)
  · exact (show Measurable (Function.uncurry U ∘ fun b : I => (a, b)) from
      hU.1.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hU.2 a b).1, (hU.2 a b).2]

lemma integrable_col {U : I → I → ℝ} (hU : IsDigraphon U) (a : I) :
    Integrable (fun b => U b a) := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun b => ?_)
  · exact (show Measurable (Function.uncurry U ∘ fun b : I => (b, a)) from
      hU.1.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hU.2 b a).1, (hU.2 b a).2]

lemma integral_row_symm {U : I → I → ℝ} (hU : IsDigraphon U) (a : I) :
    ∫ b, symmetrize U a b = ((∫ b, U a b) + ∫ b, U b a) / 2 := by
  simp only [symmetrize]
  rw [integral_div, integral_add (integrable_row hU a) (integrable_col hU a)]

lemma integral_col_symm {U : I → I → ℝ} (hU : IsDigraphon U) (a : I) :
    ∫ b, symmetrize U b a = ((∫ b, U a b) + ∫ b, U b a) / 2 := by
  simp only [symmetrize]
  rw [integral_div, integral_add (integrable_col hU a) (integrable_row hU a), add_comm]

lemma integral_row_mem {U : I → I → ℝ} (hU : IsDigraphon U) (a : I) :
    0 ≤ ∫ b, U a b ∧ ∫ b, U a b ≤ 1 := by
  constructor
  · exact integral_nonneg fun b => (hU.2 a b).1
  · calc ∫ b, U a b ≤ ∫ _b : I, (1 : ℝ) :=
          integral_mono (integrable_row hU a) (integrable_const _) fun b => (hU.2 a b).2
      _ = 1 := by simp

lemma integral_col_mem {U : I → I → ℝ} (hU : IsDigraphon U) (a : I) :
    0 ≤ ∫ b, U b a ∧ ∫ b, U b a ≤ 1 := by
  constructor
  · exact integral_nonneg fun b => (hU.2 b a).1
  · calc ∫ b, U b a ≤ ∫ _b : I, (1 : ℝ) :=
          integral_mono (integrable_col hU a) (integrable_const _) fun b => (hU.2 b a).2
      _ = 1 := by simp

lemma measurable_row_int {U : I → I → ℝ} (hU : IsDigraphon U) :
    Measurable (fun a => ∫ b, U a b) :=
  (hU.1.stronglyMeasurable.integral_prod_right (ν := (volume : Measure I))).measurable

lemma measurable_col_int {U : I → I → ℝ} (hU : IsDigraphon U) :
    Measurable (fun a => ∫ b, U b a) :=
  (hU.1.stronglyMeasurable.integral_prod_left (μ := (volume : Measure I))).measurable

lemma integrable_bdd {f : I → ℝ} (hf : Measurable f) (h : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    Integrable f := by
  refine Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(h a).1, (h a).2]

lemma integral_integral_transpose {U : I → I → ℝ} (hU : IsDigraphon U) :
    ∫ a, ∫ b, U b a = ∫ a, ∫ b, U a b := by
  have hint : Integrable (Function.uncurry U) ((volume : Measure I).prod volume) := by
    refine Integrable.of_bound hU.1.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_le]
    show -1 ≤ U p.1 p.2 ∧ U p.1 p.2 ≤ 1
    constructor <;> linarith [(hU.2 p.1 p.2).1, (hU.2 p.1 p.2).2]
  exact (integral_integral_swap hint).symm

lemma amgm_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    a ^ k * b ^ k ≤ ((a + b) / 2) ^ k * ((a + b) / 2) ^ k := by
  rw [← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (mul_nonneg ha hb)
  nlinarith [sq_nonneg (a - b)]

open OrientedGraph in
lemma t_center_symm {V : Type*} [Fintype V] [DecidableEq V] (D : OrientedGraph V) (c : V)
    (hc : ∀ u v, D.Adj u v → u = c ∨ v = c) (U : I → I → ℝ) (hU : IsDigraphon U) :
    t D (symmetrize U) = ∫ a : I, (((∫ b, U a b) + ∫ b, U b a) / 2) ^ D.outDeg c *
      (((∫ b, U a b) + ∫ b, U b a) / 2) ^ D.inDeg c := by
  rw [t_center D c hc _ (isDigraphon_symmetrize hU)]
  simp_rw [integral_row_symm hU, integral_col_symm hU]

open OrientedGraph in
lemma t_center_le_symm {V : Type*} [Fintype V] [DecidableEq V] (D : OrientedGraph V) (c : V)
    (hc : ∀ u v, D.Adj u v → u = c ∨ v = c) (hdeg : D.inDeg c = D.outDeg c) (U : I → I → ℝ)
    (hU : IsDigraphon U) : t D U ≤ t D (symmetrize U) := by
  rw [t_center D c hc U hU, t_center_symm D c hc U hU, hdeg]
  have hP := integral_row_mem hU
  have hM := integral_col_mem hU
  refine integral_mono_of_nonneg (Eventually.of_forall fun a => ?_) ?_
    (Eventually.of_forall fun a => amgm_pow _ _ (hP a).1 (hM a).1 _)
  · exact mul_nonneg (pow_nonneg (hP a).1 _) (pow_nonneg (hM a).1 _)
  · refine integrable_bdd ?_ fun a => ?_
    · exact (((measurable_row_int hU).add (measurable_col_int hU)).div_const 2).pow_const _ |>.mul
        ((((measurable_row_int hU).add (measurable_col_int hU)).div_const 2).pow_const _)
    · have h0 : 0 ≤ ((∫ b, U a b) + ∫ b, U b a) / 2 := by linarith [(hP a).1, (hM a).1]
      have h1 : ((∫ b, U a b) + ∫ b, U b a) / 2 ≤ 1 := by linarith [(hP a).2, (hM a).2]
      exact ⟨mul_nonneg (pow_nonneg h0 _) (pow_nonneg h0 _),
        by nlinarith [pow_le_one₀ h0 h1 (n := D.outDeg c), pow_nonneg h0 (D.outDeg c)]⟩

open OrientedGraph in
lemma t_center_one {V : Type*} [Fintype V] [DecidableEq V] (D : OrientedGraph V) (c : V)
    (hc : ∀ u v, D.Adj u v → u = c ∨ v = c) (hdeg : D.outDeg c + D.inDeg c = 1)
    (U : I → I → ℝ) (hU : IsDigraphon U) : t D U = t D (symmetrize U) := by
  rw [t_center D c hc U hU, t_center_symm D c hc U hU]
  have hP := integrable_bdd (measurable_row_int hU) (integral_row_mem hU)
  have hM := integrable_bdd (measurable_col_int hU) (integral_col_mem hU)
  rcases Nat.add_eq_one_iff.mp hdeg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp only [pow_one, pow_zero, one_mul]
    rw [integral_div, integral_add hP hM, integral_integral_transpose hU]
    ring
  · rw [h1, h2]
    simp only [pow_one, pow_zero, mul_one]
    rw [integral_div, integral_add hP hM, integral_integral_transpose hU]
    ring


open OrientedGraph in
lemma outDeg_eq {V : Type*} [Fintype V] (D : OrientedGraph V) [DecidableRel D.Adj] (c : V) :
    D.outDeg c = (Finset.univ.filter fun v => D.Adj c v).card := by
  unfold OrientedGraph.outDeg; convert rfl

open OrientedGraph in
lemma inDeg_eq {V : Type*} [Fintype V] (D : OrientedGraph V) [DecidableRel D.Adj] (c : V) :
    D.inDeg c = (Finset.univ.filter fun v => D.Adj v c).card := by
  unfold OrientedGraph.inDeg; convert rfl

open OrientedGraph in
lemma numArcs_center {V : Type*} [Fintype V] [DecidableEq V] (D : OrientedGraph V) (c : V)
    (hc : ∀ u v, D.Adj u v → u = c ∨ v = c) : D.numArcs = D.outDeg c + D.inDeg c := by
  classical
  have h1 : D.arcs.filter (fun p => p.1 = c) =
      (Finset.univ.filter fun v => D.Adj c v).map
        ⟨fun v => (c, v), fun _ _ h => (Prod.ext_iff.mp h).2⟩ := by
    ext p
    simp only [Finset.mem_filter, Section6Aux.mem_arcs_iff, Finset.mem_map, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h, h1⟩; exact ⟨p.2, h1 ▸ h, Prod.ext h1.symm rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨hv, rfl⟩
  have h2 : D.arcs.filter (fun p => ¬ p.1 = c) =
      (Finset.univ.filter fun v => D.Adj v c).map
        ⟨fun v => (v, c), fun _ _ h => (Prod.ext_iff.mp h).1⟩ := by
    ext p
    simp only [Finset.mem_filter, Section6Aux.mem_arcs_iff, Finset.mem_map, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h, h1⟩
      have h2 : p.2 = c := (hc _ _ h).resolve_left h1
      exact ⟨p.1, h2 ▸ h, Prod.ext rfl h2.symm⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨hv, fun h => D.irrefl _ (h ▸ hv)⟩
  unfold OrientedGraph.numArcs
  rw [← Finset.card_filter_add_card_filter_not (fun p : V × V => p.1 = c), h1, h2,
    Finset.card_map, Finset.card_map, outDeg_eq, inDeg_eq]

open OrientedGraph in
lemma star_hc {V : Type*} [Fintype V] {D : OrientedGraph V} {c : V} (hstar : D.IsOrientedStar c)
    (u v : V) (h : D.Adj u v) : u = c ∨ v = c := by
  classical exact ((hstar.1 u v).mp ((Section6Aux.underlying_adj_iff D u v).mpr (Or.inl h))).2

open OrientedGraph in
lemma star_connected {V : Type*} [Fintype V] {D : OrientedGraph V} {c : V}
    (hstar : D.IsOrientedStar c) : D.IsConnected := by
  have hr : ∀ v, D.underlying.Reachable v c := by
    intro v
    by_cases hv : v = c
    · rw [hv]
    · exact ((hstar.1 v c).mpr ⟨hv, Or.inr rfl⟩).reachable
  have : Nonempty V := ⟨c⟩
  exact ⟨fun u v => (hr u).trans (hr v).symm⟩

open OrientedGraph in
lemma star_two_nbrs {V : Type*} [Fintype V] [DecidableEq V] {D : OrientedGraph V} {c : V}
    (hstar : D.IsOrientedStar c) (h2 : 2 ≤ D.numArcs) :
    ∃ v w, v ≠ w ∧ v ≠ c ∧ w ≠ c := by
  classical
  rw [numArcs_center D c (star_hc hstar), outDeg_eq, inDeg_eq,
    ← Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact D.asymm _ _ h1 h2)] at h2
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp h2
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
  refine ⟨v, w, hvw, ?_, ?_⟩
  · rintro rfl; rcases hv with h | h <;> exact D.irrefl _ h
  · rintro rfl; rcases hw with h | h <;> exact D.irrefl _ h

open OrientedGraph in
lemma star_aut_fix {V : Type*} [Fintype V] [DecidableEq V] {D : OrientedGraph V} {c : V}
    (hstar : D.IsOrientedStar c) (h2 : 2 ≤ D.numArcs) (g : V ≃ V)
    (hg : ∀ a b, D.underlying.Adj (g a) (g b) ↔ D.underlying.Adj a b) : g c = c := by
  by_contra hgc
  obtain ⟨v, w, hvw, hv, hw⟩ := star_two_nbrs hstar h2
  have hv' : g v = c := by
    have := (hg c v).mpr ((hstar.1 c v).mpr ⟨fun h => hv h.symm, Or.inl rfl⟩)
    exact (((hstar.1 _ _).mp this).2).resolve_left hgc
  have hw' : g w = c := by
    have := (hg c w).mpr ((hstar.1 c w).mpr ⟨fun h => hw h.symm, Or.inl rfl⟩)
    exact (((hstar.1 _ _).mp this).2).resolve_left hgc
  exact hvw (g.injective (hv'.trans hw'.symm))

open OrientedGraph in
/-- An automorphism of the underlying graph from `D ≅ D^T`. -/
def undIso {V : Type*} (D : OrientedGraph V) (g : D.Iso D.transpose) :
    D.underlying ≃g D.underlying :=
  ⟨g.toEquiv, fun {a b} => underlying_iso_of_selfConverse D g a b⟩

open OrientedGraph in
lemma star_not_osk {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) {D : OrientedGraph V}
    {c : V} (hstar : D.IsOrientedStar c) (h2 : 2 ≤ D.numArcs) : ¬ D.IsOSK := by
  classical
  intro hD
  obtain ⟨f, hf⟩ := lemma_4_2 D hD
  obtain ⟨g⟩ := lemma_4_4 hA1 D (star_connected hstar) hD
  have hgc : g.toEquiv c = c :=
    star_aut_fix hstar h2 g.toEquiv (underlying_iso_of_selfConverse D g)
  have hne : D.arcs.Nonempty := Finset.card_pos.mp (by unfold OrientedGraph.numArcs at h2; omega)
  obtain ⟨p, hp⟩ := hne
  have hp' : D.Adj p.1 p.2 := (Section6Aux.mem_arcs_iff D p).mp hp
  have hT : ∀ a b, D.Adj a b → D.Adj (g.toEquiv b) (g.toEquiv a) := fun a b h => by
    have := (g.map_adj_iff a b).mpr h
    simpa [OrientedGraph.transpose] using this
  rcases star_hc hstar _ _ hp' with h | h
  · have h1 := hT _ _ hp'
    rw [h, hgc] at h1
    have e1 := (hf _ _ hp').1
    have e2 := (hf _ _ h1).2
    rw [h] at e1
    rw [e1] at e2
    exact absurd e2 (by decide)
  · have h1 := hT _ _ hp'
    rw [h, hgc] at h1
    have e1 := (hf _ _ hp').2
    have e2 := (hf _ _ h1).1
    rw [h] at e1
    rw [e1] at e2
    exact absurd e2 (by decide)

open OrientedGraph in
lemma star_oask_deg {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) {D : OrientedGraph V}
    {c : V} (hstar : D.IsOrientedStar c) (h2 : 2 ≤ D.numArcs) (hD : D.IsOASK) :
    D.inDeg c = D.outDeg c := by
  classical
  have hiso : ∀ v, ∃ u, D.underlying.Adj v u := by
    intro v
    obtain ⟨a, b, hab, ha, hb⟩ := star_two_nbrs hstar h2
    by_cases hv : v = c
    · exact ⟨a, (hstar.1 v a).mpr ⟨fun h => ha (h ▸ hv), Or.inl hv⟩⟩
    · exact ⟨c, (hstar.1 v c).mpr ⟨hv, Or.inr rfl⟩⟩
  obtain ⟨f, hf⟩ := lemma_4_3 hA1 D (Or.inr hD) hiso
  have hfix : ∀ g : D.underlying ≃g D.underlying, g c = c := fun g =>
    star_aut_fix hstar h2 g.toEquiv (fun a b => g.map_adj_iff)
  -- out-arcs go to in-arcs and conversely
  have hout : ∀ e : {p // p ∈ D.arcs}, e.1.1 = c → (f e).1.2 = c := by
    intro e he
    obtain ⟨g, hg1, _⟩ := hf e
    rw [← hg1, he, hfix]
  have hin : ∀ e : {p // p ∈ D.arcs}, e.1.2 = c → (f e).1.1 = c := by
    intro e he
    obtain ⟨g, _, hg2⟩ := hf e
    rw [← hg2, he, hfix]
  have mem1 : ∀ v, D.Adj c v → (c, v) ∈ D.arcs := fun v h => (Section6Aux.mem_arcs_iff D _).mpr h
  have mem2 : ∀ v, D.Adj v c → (v, c) ∈ D.arcs := fun v h => (Section6Aux.mem_arcs_iff D _).mpr h
  have arcAdj : ∀ e : {p // p ∈ D.arcs}, D.Adj e.1.1 e.1.2 :=
    fun e => (Section6Aux.mem_arcs_iff D _).mp e.2
  rw [inDeg_eq, outDeg_eq]
  apply le_antisymm
  · -- in-arcs inject into out-arcs
    refine Finset.card_le_card_of_injOn
      (fun v => if h : D.Adj v c then (f ⟨(v, c), mem2 v h⟩).1.2 else c) ?_ ?_
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hv, ↓reduceDIte]
      have h := arcAdj (f ⟨(v, c), mem2 v hv⟩)
      rwa [hin ⟨(v, c), mem2 v hv⟩ rfl] at h
    · intro v hv w hw hvw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
      simp only [hv, hw, ↓reduceDIte] at hvw
      have h1 := hin ⟨(v, c), mem2 v hv⟩ rfl
      have h2 := hin ⟨(w, c), mem2 w hw⟩ rfl
      have : f ⟨(v, c), mem2 v hv⟩ = f ⟨(w, c), mem2 w hw⟩ :=
        Subtype.ext (Prod.ext (h1.trans h2.symm) hvw)
      have := congrArg (fun e => e.1.1) (f.injective this)
      simpa using this
  · refine Finset.card_le_card_of_injOn
      (fun v => if h : D.Adj c v then (f ⟨(c, v), mem1 v h⟩).1.1 else c) ?_ ?_
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hv, ↓reduceDIte]
      have h := arcAdj (f ⟨(c, v), mem1 v hv⟩)
      rwa [hout ⟨(c, v), mem1 v hv⟩ rfl] at h
    · intro v hv w hw hvw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
      simp only [hv, hw, ↓reduceDIte] at hvw
      have h1 := hout ⟨(c, v), mem1 v hv⟩ rfl
      have h2 := hout ⟨(c, w), mem1 w hw⟩ rfl
      have : f ⟨(c, v), mem1 v hv⟩ = f ⟨(c, w), mem1 w hw⟩ :=
        Subtype.ext (Prod.ext hvw (h1.trans h2.symm))
      have := congrArg (fun e => e.1.2) (f.injective this)
      simpa using this

open OrientedGraph in
lemma star_kernel {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (c : V) (hstar : D.IsOrientedStar c) :
    (D.numArcs = 1 → D.IsOSK ∧ D.IsOASK) ∧
    (2 ≤ D.numArcs → ¬ D.IsOSK ∧ (D.IsOASK ↔ D.inDeg c = D.outDeg c)) := by
  classical
  have hc := star_hc hstar
  refine ⟨fun h1 => ?_, fun h2 => ⟨star_not_osk hA1 hstar h2,
    ⟨star_oask_deg hA1 hstar h2, fun hdeg U hU => t_center_le_symm D c hc hdeg U hU⟩⟩⟩
  have hdeg : D.outDeg c + D.inDeg c = 1 := (numArcs_center D c hc).symm.trans h1
  exact ⟨fun U hU => (t_center_one D c hc hdeg U hU).symm.le,
    fun U hU => (t_center_one D c hc hdeg U hU).le⟩

/-- The oriented graph on `X ⊕ Y` with arcs `inl x → inr y` for `(x, y) ∈ E`. -/
def bipOG {X Y : Type*} (E : Finset (X × Y)) : OrientedGraph (X ⊕ Y) where
  Adj a b := ∃ x y, a = Sum.inl x ∧ b = Sum.inr y ∧ (x, y) ∈ E
  irrefl v := by
    rintro ⟨x, y, rfl, h, _⟩
    exact Sum.inl_ne_inr h
  asymm u v := by
    rintro ⟨x, y, rfl, rfl, _⟩ ⟨x', y', h1, _, _⟩
    exact Sum.inr_ne_inl h1

lemma bipOG_underlying {X Y : Type*} (E : Finset (X × Y)) :
    (bipOG E).underlying = bipGraph E := rfl

lemma bipOG_arcs {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y)) :
    (bipOG E).arcs = E.map ⟨fun q => (Sum.inl q.1, Sum.inr q.2), fun q q' h => by
      simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h
      exact Prod.ext h.1 h.2⟩ := by
  classical
  ext p
  simp only [Section6Aux.mem_arcs_iff, Finset.mem_map]
  constructor
  · rintro ⟨x, y, h1, h2, h⟩
    exact ⟨(x, y), h, Prod.ext h1.symm h2.symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, q.2, rfl, rfl, hq⟩

lemma tb_eq_t_bipOG {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (K : I → I → ℝ) : tb E K = t (bipOG E) K := by
  unfold tb tBi t tDir
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : X ⊕ Y => (I : Type)) (fun _ => (volume : Measure I))
  rw [← hmp.integral_comp']
  congr 1
  funext z
  rw [bipOG_arcs, Finset.prod_map]
  rfl

open OrientedGraph in
/-- For an orientation of a forest, the density in every test kernel `testK c φ` is
`2^{-e(D)}` (only the zero circulation survives in the Fourier expansion). -/
lemma t_testK_acyclic {V : Type*} [Fintype V] (D : OrientedGraph V)
    (hacyc : D.underlying.IsAcyclic) (c φ : ℝ) :
    t D (Section6Aux.testK c φ) = (1 / 2) ^ D.numArcs := by
  classical
  rw [Section6Aux.t_testK]
  rw [Finset.sum_eq_single (0 : Section6Aux.Arc D → ℤ)]
  · have h0 : ∀ v, Section6Aux.flow D 0 v = 0 := fun v => by simp [Section6Aux.flow]
    simp only [h0, implies_true, ↓reduceIte]
    have hs : Section6Aux.suppCard (D := D) 0 = 0 := by simp [Section6Aux.suppCard]
    simp [hs]
  · intro ζ hζ hne
    split_ifs with hflow
    · exfalso
      have hc : ζ ∈ Section6Aux.Circ D := Finset.mem_filter.mpr ⟨hζ, hflow⟩
      obtain ⟨u, w, hw, _⟩ := Section6Aux.circ_exists_cycle D hc hne
      exact hacyc w hw
    · rfl
  · intro h
    exact absurd (Fintype.mem_piFinset.mpr fun _ => by simp [Section6Aux.signs]) h

/-- Interval in `[0, 1]` (as a subset of `I`). -/
def ivl (a b : ℝ) : Set I := {x | (x : ℝ) ∈ Icc a b}

lemma measurableSet_ivl (a b : ℝ) : MeasurableSet (ivl a b) :=
  measurableSet_Icc.preimage measurable_subtype_coe

lemma volume_ivl {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) : volume (ivl a b) = ENNReal.ofReal (b - a) := by
  rw [unitInterval.volume_def, (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
  have : Subtype.val '' ivl a b = Icc a b := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro h
      exact ⟨⟨r, ⟨by linarith [h.1], by linarith [h.2]⟩⟩, h, rfl⟩
  rw [this, Real.volume_Icc]

lemma not_aeEq_of_rect {U U' : I → I → ℝ} {a b a' b' : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (ha' : 0 ≤ a') (hab' : a' < b') (hb' : b' ≤ 1)
    (h : ∀ x ∈ ivl a b, ∀ y ∈ ivl a' b', U x y ≠ U' x y) : ¬ AEEq volume U U' := by
  intro hae
  unfold AEEq at hae
  rw [ae_iff] at hae
  have hsub : ivl a b ×ˢ ivl a' b' ⊆ {p : I × I | ¬ U p.1 p.2 = U' p.1 p.2} :=
    fun p hp => h p.1 hp.1 p.2 hp.2
  have hpos : 0 < ((volume : Measure I).prod volume) (ivl a b ×ˢ ivl a' b') := by
    rw [Measure.prod_prod, volume_ivl ha hb, volume_ivl ha' hb']
    exact ENNReal.mul_pos (by simp; linarith) (by simp; linarith)
  exact absurd (measure_mono_null hsub hae) hpos.ne'

lemma isKernel_lin {U V : I → I → ℝ} (hU : IsKernel U) (hV : IsKernel V) (a b : ℝ) :
    IsKernel (fun x y => a * U x y + b * V x y) := by
  obtain ⟨mU, M, hM⟩ := hU
  obtain ⟨mV, N, hN⟩ := hV
  refine ⟨(mU.const_mul a).add (mV.const_mul b), |a| * M + |b| * N, fun x y => ?_⟩
  calc |a * U x y + b * V x y| ≤ |a * U x y| + |b * V x y| := abs_add_le _ _
    _ = |a| * |U x y| + |b| * |V x y| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * M + |b| * N := add_le_add (mul_le_mul_of_nonneg_left (hM x y) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hN x y) (abs_nonneg _))

lemma isKernel_const_mul' {U : I → I → ℝ} (hU : IsKernel U) (a : ℝ) :
    IsKernel (fun x y => a * U x y) := by
  obtain ⟨mU, M, hM⟩ := hU
  refine ⟨mU.const_mul a, |a| * M, fun x y => ?_⟩
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM x y) (abs_nonneg _)

lemma isKernel_of_isDigraphon {U : I → I → ℝ} (hU : IsDigraphon U) : IsKernel U :=
  ⟨hU.1, 1, fun x y => by
    rw [abs_le]; constructor <;> linarith [(hU.2 x y).1, (hU.2 x y).2]⟩

lemma tb_nonneg {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y)) {W : I → I → ℝ}
    (hW : ∀ x y, 0 ≤ W x y) : 0 ≤ tb E W :=
  integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => hW _ _

lemma rNorm_of_nonneg {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    {W : I → I → ℝ} (hW : ∀ x y, 0 ≤ W x y) :
    rNorm E W = tb E W ^ ((1 : ℝ) / E.card) := by
  unfold rNorm
  congr 2
  funext x y
  exact abs_of_nonneg (hW x y)

lemma tb_congr_ae {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y)) {U U' : I → I → ℝ}
    (h : AEEq volume U U') : tb E U = tb E U' := by
  unfold tb tBi
  apply integral_congr_ae
  have : ∀ p ∈ E, ∀ᵐ z ∂((Measure.pi fun _ : X => (volume : Measure I)).prod
      (Measure.pi fun _ : Y => (volume : Measure I))),
      U (z.1 p.1) (z.2 p.2) = U' (z.1 p.1) (z.2 p.2) := by
    intro p _
    have hmp : MeasurePreserving (Prod.map (Function.eval p.1) (Function.eval p.2))
        ((Measure.pi fun _ : X => (volume : Measure I)).prod
          (Measure.pi fun _ : Y => (volume : Measure I)))
        ((volume : Measure I).prod volume) :=
      (measurePreserving_eval _ p.1).prod (measurePreserving_eval _ p.2)
    exact hmp.quasiMeasurePreserving.ae h
  filter_upwards [(Filter.eventually_all_finset E).mpr this] with z hz
  exact Finset.prod_congr rfl hz

lemma card_ge_three_of_cycle {X Y : Type*} (E : Finset (X × Y))
    (hcyc : ¬ (bipGraph E).IsAcyclic) : 3 ≤ E.card := by
  classical
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hcyc
  obtain ⟨u, w, hw⟩ := hcyc
  have h3 := hw.three_le_length
  have hsub : w.edges.toFinset ⊆ E.image fun q => s(Sum.inl q.1, Sum.inr q.2) := by
    intro e he
    have he' := w.edges_subset_edgeSet (List.mem_toFinset.mp he)
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he'
      simp only [bipGraph, SimpleGraph.fromRel_adj] at he'
      rw [Finset.mem_image]
      rcases he'.2 with ⟨x, y, rfl, rfl, hxy⟩ | ⟨x, y, rfl, rfl, hxy⟩
      · exact ⟨(x, y), hxy, rfl⟩
      · exact ⟨(x, y), hxy, Sym2.eq_swap⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hw.edges_nodup, SimpleGraph.Walk.length_edges] at this
  exact h3.trans (this.trans Finset.card_image_le)

lemma thm16_forward {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (hE : 0 < E.card) (hWN : IsWeaklyNorming E) (hcyc : ¬ (bipGraph E).IsAcyclic) :
    StrictConvexOnNonnegKernels E := by
  have hconv := (lemma_2_3_1 E hE).mp hWN
  have hm2 : 2 ≤ E.card := le_trans (by norm_num) (card_ge_three_of_cycle E hcyc)
  -- strict midpoint convexity
  have hmid : ∀ U V : I → I → ℝ, IsKernel U → IsKernel V → (∀ x y, 0 ≤ U x y) →
      (∀ x y, 0 ≤ V x y) → ¬ AEEq volume U V →
      tb E (fun x y => (1 / 2 : ℝ) * U x y + (1 / 2 : ℝ) * V x y) <
        (tb E U + tb E V) / 2 := by
    intro U V hU hV hU0 hV0 hne
    set S : I → I → ℝ := fun x y => (1 / 2 : ℝ) * U x y + (1 / 2 : ℝ) * V x y with hSdef
    have hS0 : ∀ x y, 0 ≤ S x y := fun x y => by
      simp only [hSdef]; linarith [hU0 x y, hV0 x y]
    have hle : tb E S ≤ (tb E U + tb E V) / 2 := by
      have := hconv U V hU hV hU0 hV0 (1 / 2) ⟨by norm_num, by norm_num⟩
      have e : (fun x y => (1 / 2 : ℝ) * U x y + (1 - 1 / 2) * V x y) = S := by
        funext x y; simp only [hSdef]; ring
      rw [e] at this; linarith
    refine lt_of_le_of_ne hle fun heq => hne ?_
    -- weak norm triangle inequality
    set m : ℕ := E.card with hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    set u := tb E U ^ ((1 : ℝ) / m)
    set v := tb E V ^ ((1 : ℝ) / m)
    set s := tb E S ^ ((1 : ℝ) / m)
    have hu0 : 0 ≤ u := Real.rpow_nonneg (tb_nonneg E hU0) _
    have hv0 : 0 ≤ v := Real.rpow_nonneg (tb_nonneg E hV0) _
    have hs0 : 0 ≤ s := Real.rpow_nonneg (tb_nonneg E hS0) _
    have htri : s ≤ (u + v) / 2 := by
      have h := hWN.2.1 (fun x y => (1 / 2 : ℝ) * U x y) (fun x y => (1 / 2 : ℝ) * V x y)
        (isKernel_const_mul' hU _) (isKernel_const_mul' hV _)
      rw [hWN.1 U hU, hWN.1 V hV] at h
      rw [rNorm_of_nonneg E hS0, rNorm_of_nonneg E hU0, rNorm_of_nonneg E hV0] at h
      have h12 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [h12] at h
      change s ≤ 1 / 2 * u + 1 / 2 * v at h
      linarith
    have hpow : ∀ (z : ℝ), 0 ≤ z → (z ^ ((1 : ℝ) / m)) ^ m = z := fun z hz => by
      rw [one_div]; exact Real.rpow_inv_natCast_pow hz (by omega)
    have hU' : tb E U = u ^ m := (hpow _ (tb_nonneg E hU0)).symm
    have hV' : tb E V = v ^ m := (hpow _ (tb_nonneg E hV0)).symm
    have hS' : tb E S = s ^ m := (hpow _ (tb_nonneg E hS0)).symm
    have huv : u = v := by
      by_contra huv
      have hstrict := (strictConvexOn_pow hm2).2 (Set.mem_Ici.mpr hu0) (Set.mem_Ici.mpr hv0) huv
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hstrict
      have h1 : s ^ m ≤ ((u + v) / 2) ^ m := pow_le_pow_left₀ hs0 htri m
      have h2 : ((u + v) / 2) = 1 / 2 * u + 1 / 2 * v := by ring
      rw [h2] at h1
      rw [hU', hV', hS'] at heq
      linarith
    have hUS : tb E U = tb E S := by
      rw [hU', hV', huv] at heq; rw [hU', huv]; linarith
    have hVS : tb E V = tb E S := by
      rw [hU', hV', huv] at heq; rw [hV']; linarith
    -- the equality lemma
    set A : I → I → ℝ := fun x y => (1 / 2 : ℝ) * U x y + (-(1 / 2) : ℝ) * V x y with hA
    have hSA : ∀ x y, |A x y| ≤ S x y := fun x y => by
      simp only [hA, hSdef]
      rw [abs_le]; constructor <;> linarith [hU0 x y, hV0 x y]
    have hplus : (fun x y => S x y + A x y) = U := by
      funext x y; simp only [hA, hSdef]; ring
    have hminus : (fun x y => S x y - A x y) = V := by
      funext x y; simp only [hA, hSdef]; ring
    have h0 := lemma_4_6 E hWN hcyc S A (isKernel_lin hU hV _ _) (isKernel_lin hU hV _ _) hSA
      (by rw [hplus]; exact hUS) (by rw [hminus]; exact hVS)
    unfold AEEq at h0 ⊢
    filter_upwards [h0] with p hp
    simp only [hA] at hp
    linarith
  intro U V hU hV hU0 hV0 hne a ha
  set S : I → I → ℝ := fun x y => (1 / 2 : ℝ) * U x y + (1 / 2 : ℝ) * V x y with hSdef
  have hS : IsKernel S := isKernel_lin hU hV _ _
  have hS0 : ∀ x y, 0 ≤ S x y := fun x y => by
    simp only [hSdef]; linarith [hU0 x y, hV0 x y]
  have hm := hmid U V hU hV hU0 hV0 hne
  rcases le_or_gt a (1 / 2) with hle | hgt
  · have e : (fun x y => a * U x y + (1 - a) * V x y) =
        fun x y => (2 * a) * S x y + (1 - 2 * a) * V x y := by
      funext x y; simp only [hSdef]; ring
    rw [e]
    have := hconv S V hS hV hS0 hV0 (2 * a) ⟨by linarith [ha.1], by linarith⟩
    have h2a : 0 < 2 * a := by linarith [ha.1]
    nlinarith
  · have e : (fun x y => a * U x y + (1 - a) * V x y) =
        fun x y => (2 * (1 - a)) * S x y + (1 - 2 * (1 - a)) * U x y := by
      funext x y; simp only [hSdef]; ring
    rw [e]
    have := hconv S U hS hU hS0 hU0 (2 * (1 - a)) ⟨by linarith [ha.2], by linarith⟩
    have h2a : 0 < 2 * (1 - a) := by linarith [ha.2]
    nlinarith

lemma testK_mem (c φ : ℝ) (hc : |c| ≤ 1 / 2) (x y : I) :
    0 ≤ Section6Aux.testK c φ x y ∧ Section6Aux.testK c φ x y ≤ 1 :=
  (Section6Aux.testK_isDigraphon φ hc).2 x y

lemma thm16_backward {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (hE : 0 < E.card) (h : StrictConvexOnNonnegKernels E) :
    IsWeaklyNorming E ∧ ¬ (bipGraph E).IsAcyclic := by
  constructor
  · rw [lemma_2_3_1 E hE]
    intro U V hU hV hU0 hV0 a ha
    rcases eq_or_lt_of_le ha.1 with h0 | h0
    · subst h0; simp
    rcases eq_or_lt_of_le ha.2 with h1 | h1
    · subst h1; simp
    by_cases hae : AEEq volume U V
    · have e1 : tb E (fun x y => a * U x y + (1 - a) * V x y) = tb E U := by
        apply tb_congr_ae
        unfold AEEq at hae ⊢
        filter_upwards [hae] with p hp
        rw [hp]; ring
      rw [e1, tb_congr_ae E hae]; linarith
    · exact (h U V hU hV hU0 hV0 hae a ⟨h0, h1⟩).le
  · intro hacyc
    have hac : (bipOG E).underlying.IsAcyclic := hacyc
    set U := Section6Aux.testK (1 / 2) 0
    set V := Section6Aux.testK (-(1 / 2)) 0
    have hUd := Section6Aux.testK_isDigraphon (c := 1 / 2) 0 (by norm_num)
    have hVd := Section6Aux.testK_isDigraphon (c := -(1 / 2)) 0 (by norm_num)
    have hmix : (fun x y => (1 / 2 : ℝ) * U x y + (1 - 1 / 2) * V x y) =
        Section6Aux.testK 0 0 := by
      funext x y; simp only [U, V, Section6Aux.testK]; ring
    have hne : ¬ AEEq volume U V := by
      refine not_aeEq_of_rect (a := 0) (b := 1 / 8) (a' := 0) (b' := 1 / 8) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
      intro x hx y hy hxy
      simp only [U, V, Section6Aux.testK, add_zero] at hxy
      have hc : 0 < Real.cos (2 * Real.pi * ((x : ℝ) - y)) := by
        apply Real.cos_pos_of_mem_Ioo
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨hy1, hy2⟩ := hy
        constructor <;> nlinarith [Real.pi_pos]
      linarith
    have := h U V (isKernel_of_isDigraphon hUd) (isKernel_of_isDigraphon hVd)
      (fun x y => (hUd.2 x y).1) (fun x y => (hVd.2 x y).1) hne (1 / 2) ⟨by norm_num, by norm_num⟩
    rw [hmix, tb_eq_t_bipOG, tb_eq_t_bipOG, tb_eq_t_bipOG, t_testK_acyclic _ hac,
      t_testK_acyclic _ hac, t_testK_acyclic _ hac] at this
    linarith

open OrientedGraph in
lemma t_eq_tb_side {V : Type*} [Fintype V] (D : OrientedGraph V) (s : V → Prop) [DecidablePred s]
    (hs : ∀ u v, D.Adj u v → s u ∧ ¬ s v) (W : I → I → ℝ) :
    t D W = tb (sideEdges D.underlying s) W := by
  classical
  unfold t tDir tb tBi
  have hmp := (measurePreserving_piEquivPiSubtypeProd (α := fun _ : V => (I : Type))
    (fun _ => (volume : Measure I)) s).symm
  rw [← hmp.integral_comp']
  congr 1
  funext z
  have harcs : D.arcs = (sideEdges D.underlying s).map
      ⟨fun q => (q.1.1, q.2.1), fun q q' h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)⟩ := by
    ext p
    simp only [Section6Aux.mem_arcs_iff, Finset.mem_map]
    constructor
    · intro h
      refine ⟨(⟨p.1, (hs _ _ h).1⟩, ⟨p.2, (hs _ _ h).2⟩), ?_, rfl⟩
      rw [mem_sideEdges]
      exact (underlying_adj_iff' D _ _).mpr (Or.inl h)
    · rintro ⟨q, hq, rfl⟩
      rw [mem_sideEdges] at hq
      rcases (underlying_adj_iff' D _ _).mp hq with h | h
      · exact h
      · exact absurd (hs _ _ h).1 q.2.2
  have h1 : ∀ v (hv : s v),
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => (I : Type)) s).symm z v = z.1 ⟨v, hv⟩ :=
    fun v hv => by
      simp only [MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.symm_mk,
        MeasurableEquiv.coe_mk, Equiv.piEquivPiSubtypeProd_symm_apply, hv, ↓reduceDIte]
  have h2 : ∀ v (hv : ¬ s v),
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => (I : Type)) s).symm z v = z.2 ⟨v, hv⟩ :=
    fun v hv => by
      simp only [MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.symm_mk,
        MeasurableEquiv.coe_mk, Equiv.piEquivPiSubtypeProd_symm_apply, hv, ↓reduceDIte]
  rw [harcs, Finset.prod_map]
  refine Finset.prod_congr rfl fun q _ => ?_
  show W ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => (I : Type)) s).symm z q.1.1)
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => (I : Type)) s).symm z q.2.1) = _
  rw [h1 _ q.1.2, h2 _ q.2.2]

open OrientedGraph in
lemma t_transpose_of_iso {V : Type*} [Fintype V] (D : OrientedGraph V) (g : D.Iso D.transpose)
    (W : I → I → ℝ) : t D (kTranspose W) = t D W := by
  classical
  have hT : ∀ a b, D.Adj a b ↔ D.Adj (g.toEquiv b) (g.toEquiv a) := fun a b => by
    have := g.map_adj_iff a b
    simp only [OrientedGraph.transpose] at this
    exact this.symm
  set Φ : (V → I) ≃ᵐ (V → I) :=
    MeasurableEquiv.arrowCongr' g.toEquiv.symm (MeasurableEquiv.refl I) with hΦ
  have hmp : MeasurePreserving Φ (Measure.pi fun _ : V => (volume : Measure I))
      (Measure.pi fun _ : V => (volume : Measure I)) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ => MeasurePreserving.id _)
  have hz : ∀ x : V → I, Φ x = fun v => x (g.toEquiv v) := fun x => by
    funext v; simp [hΦ, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  unfold t tDir
  rw [← hmp.integral_comp']
  congr 1
  funext x
  rw [hz]
  simp only [kTranspose]
  refine Finset.prod_nbij' (fun p => (g.toEquiv p.2, g.toEquiv p.1))
    (fun p => (g.toEquiv.symm p.2, g.toEquiv.symm p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Section6Aux.mem_arcs_iff] at hp ⊢
    exact (hT _ _).mp hp
  · intro p hp
    rw [Section6Aux.mem_arcs_iff] at hp ⊢
    rw [hT]; simpa using hp
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

lemma bipGraph_hom_inj {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → Prop)
    [DecidablePred s] (hs : ∀ u v, H.Adj u v → (s u ↔ ¬ s v)) :
    ∃ f : H →g bipGraph (sideEdges H s), Function.Injective f := by
  classical
  let f0 : V → {v // s v} ⊕ {v // ¬ s v} := fun v =>
    if h : s v then Sum.inl ⟨v, h⟩ else Sum.inr ⟨v, h⟩
  have hinj : Function.Injective f0 := by
    intro a b hab
    simp only [f0] at hab
    split_ifs at hab with h1 h2 h2
    all_goals (simp at hab; try exact hab)
  refine ⟨⟨f0, fun {a b} hab => ?_⟩, hinj⟩
  simp only [bipGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, ?_⟩
  · have hne := hab.ne
    exact hne (hinj h)
  have hab' := hs a b hab
  by_cases ha : s a
  · have hb : ¬ s b := hab'.mp ha
    left
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [f0, ha], by simp [f0, hb], ?_⟩
    rw [mem_sideEdges]; exact hab
  · have hb : s b := by tauto
    right
    refine ⟨⟨b, hb⟩, ⟨a, ha⟩, by simp [f0, hb], by simp [f0, ha], ?_⟩
    rw [mem_sideEdges]; exact hab.symm

open OrientedGraph in
lemma thm13k {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (hD : D.IsOSK) :
    D.IsSymmetryForcingK ↔ ¬ D.underlying.IsAcyclic := by
  classical
  constructor
  · intro hSF hacyc
    set W := Section6Aux.testK (1 / 2) (Real.pi / 2) with hWdef
    have hW := Section6Aux.testK_isDigraphon (c := 1 / 2) (Real.pi / 2) (by norm_num)
    have heq : t D W = t D (symmetrize W) := by
      rw [hWdef, Section6Aux.symmetrize_testK, t_testK_acyclic D hacyc, t_testK_acyclic D hacyc]
    have hae := hSF W hW heq
    refine not_aeEq_of_rect (a := 1 / 4) (b := 3 / 8) (a' := 0) (b' := 1 / 8) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hae
    intro x hx y hy hxy
    simp only [hWdef, kTranspose, Section6Aux.testK] at hxy
    have e1 : 2 * Real.pi * ((y : ℝ) - x) + Real.pi / 2 =
        -(2 * Real.pi * ((x : ℝ) - y)) + Real.pi / 2 := by ring
    rw [e1, Real.cos_add_pi_div_two, Real.cos_add_pi_div_two, Real.sin_neg] at hxy
    have hpos : 0 < Real.sin (2 * Real.pi * ((x : ℝ) - y)) := by
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [Real.pi_pos]
    linarith
  · intro hcyc W hW heq
    by_contra hne
    have he : 1 ≤ D.numArcs := by
      simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hcyc
      obtain ⟨u, w, hw⟩ := hcyc
      have hnn : ¬ w.Nil := hw.not_nil
      have hadj := w.adj_snd hnn
      unfold OrientedGraph.numArcs
      rcases (underlying_adj_iff' D _ _).mp hadj with h | h
      · exact Finset.card_pos.mpr ⟨_, (Section6Aux.mem_arcs_iff D (u, w.snd)).mpr h⟩
      · exact Finset.card_pos.mpr ⟨_, (Section6Aux.mem_arcs_iff D (w.snd, u)).mpr h⟩
    obtain ⟨hone, ⟨g⟩, hwn⟩ := (osk_char hA1 D hconn he).mp hD
    obtain ⟨s, hs, hws⟩ := exists_side D hconn hone g hwn
    let _ := Classical.decPred s
    have hbip : ∀ u v, D.underlying.Adj u v → (s u ↔ ¬ s v) := by
      intro u v huv
      rcases (underlying_adj_iff' D u v).mp huv with h | h
      · exact ⟨fun _ => (hs u v h).2, fun _ => (hs u v h).1⟩
      · exact ⟨fun hu => absurd hu (hs v u h).2, fun hv => absurd (hs v u h).1 hv⟩
    obtain ⟨f, hf⟩ := bipGraph_hom_inj D.underlying s hbip
    have hcycE : ¬ (bipGraph (sideEdges D.underlying s)).IsAcyclic := fun h =>
      hcyc (h.comap f hf)
    have hE : 0 < (sideEdges D.underlying s).card :=
      lt_of_lt_of_le (by norm_num) (card_ge_three_of_cycle _ hcycE)
    have hstrict := thm16_forward _ hE hws hcycE
    have hWT : IsDigraphon (kTranspose W) :=
      ⟨hW.1.comp measurable_swap, fun x y => hW.2 y x⟩
    have := hstrict W (kTranspose W) (isKernel_of_isDigraphon hW) (isKernel_of_isDigraphon hWT)
      (fun x y => (hW.2 x y).1) (fun x y => (hW.2 y x).1) hne (1 / 2) ⟨by norm_num, by norm_num⟩
    have hmix : (fun x y => (1 / 2 : ℝ) * W x y + (1 - 1 / 2) * kTranspose W x y) =
        symmetrize W := by
      funext x y; simp only [symmetrize, kTranspose]; ring
    rw [hmix, ← t_eq_tb_side D s hs, ← t_eq_tb_side D s hs, ← t_eq_tb_side D s hs,
      t_transpose_of_iso D g, ← heq] at this
    linarith

lemma integral_cube_zero : ∫ x : I, (2 * (x : ℝ) - 1) ^ 3 = 0 := by
  rw [unitInterval.volume_def,
    integral_subtype_comap measurableSet_Icc (fun x : ℝ => (2 * x - 1) ^ 3),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => (2 * x - 1) ^ 4 / 8) ((2 * x - 1) ^ 3) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul 2).sub_const 1).pow 4 |>.div_const 8
    exact h.congr_deriv (by simp only [id]; push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => (2 * x - 1) ^ 3).intervalIntegrable _ _)]
  norm_num

lemma edgeFinset_K23 :
    letI := Classical.decRel (completeBipartiteGraph (Fin 2) (Fin 3)).Adj
    (completeBipartiteGraph (Fin 2) (Fin 3)).edgeFinset =
      (Finset.univ : Finset (Fin 2 × Fin 3)).image fun p => s(Sum.inl p.1, Sum.inr p.2) := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, completeBipartiteGraph_adj,
      Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · cases a with
        | inl i => cases b with
          | inl j => simp at hb
          | inr j => exact ⟨i, j, rfl⟩
        | inr i => simp at ha
      · cases a with
        | inl i => simp at ha
        | inr i => cases b with
          | inl j => exact ⟨j, i, Sym2.eq_swap⟩
          | inr j => simp at hb
    · rintro ⟨i, j, h⟩
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; simp
      · right; simp

lemma prod_out_symm {α : Type*} {U : I → I → ℝ} (hU : ∀ x y, U x y = U y x) (x : α → I)
    (a b : α) : U (x (Quot.out s(a, b)).1) (x (Quot.out s(a, b)).2) = U (x a) (x b) := by
  have h : s((Quot.out s(a, b)).1, (Quot.out s(a, b)).2) = s(a, b) := Quot.out_eq _
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, hU]

lemma k23_not_norming_symm' :
    ¬ IsNormOn IsSymmKernel
      (fun U => |tU (completeBipartiteGraph (Fin 2) (Fin 3)) U| ^ ((1 : ℝ) / 6)) := by
  classical
  intro hN
  set f : I → ℝ := fun x => 2 * (x : ℝ) - 1 with hf
  set U : I → I → ℝ := fun x y => f x * f y with hUdef
  have hUsymm : ∀ x y, U x y = U y x := fun x y => by simp only [hUdef]; ring
  have hfb : ∀ x : I, |f x| ≤ 1 := fun x => by
    simp only [hf]; rw [abs_le]
    constructor <;> linarith [x.2.1, x.2.2]
  have hUk : IsSymmKernel U := by
    refine ⟨⟨?_, 1, fun x y => ?_⟩, hUsymm⟩
    · apply Continuous.measurable
      simp only [hUdef, hf, Function.uncurry_def]
      fun_prop
    · simp only [hUdef]; rw [abs_mul]
      nlinarith [hfb x, hfb y, abs_nonneg (f x), abs_nonneg (f y)]
  have ht : tU (completeBipartiteGraph (Fin 2) (Fin 3)) U = 0 := by
    unfold tU tUndir
    have hprod : ∀ x : Fin 2 ⊕ Fin 3 → I,
        ∏ e ∈ (completeBipartiteGraph (Fin 2) (Fin 3)).edgeFinset,
          U (x (Quot.out e).1) (x (Quot.out e).2) =
        ∏ v : Fin 2 ⊕ Fin 3, (Sum.elim (fun _ (t : I) => f t ^ 3) (fun _ (t : I) => f t ^ 2) v)
          (x v) := by
      intro x
      rw [edgeFinset_K23, Finset.prod_image (fun p _ q _ h => by
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
        · exact absurd h1 Sum.inl_ne_inr)]
      simp only [prod_out_symm hUsymm]
      simp only [hUdef, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_prod_type]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_pow, Finset.prod_pow]
    simp_rw [hprod]
    rw [integral_fintype_prod_eq_prod]
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hf, integral_cube_zero]
    simp
  have h0 : (fun U => |tU (completeBipartiteGraph (Fin 2) (Fin 3)) U| ^ ((1 : ℝ) / 6)) U = 0 := by
    simp only [ht, abs_zero]
    exact Real.zero_rpow (by norm_num)
  have hae := hN.2 U hUk h0
  refine not_aeEq_of_rect (a := 3 / 4) (b := 1) (a' := 3 / 4) (b' := 1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hae
  intro x hx y hy hxy
  simp only [hUdef, hf] at hxy
  obtain ⟨hx1, _⟩ := hx
  obtain ⟨hy1, _⟩ := hy
  have : 0 < (2 * (x : ℝ) - 1) * (2 * (y : ℝ) - 1) := by
    apply mul_pos <;> linarith
  linarith



lemma measurePreserving_pair {V : Type*} [Fintype V] [DecidableEq V] {a b : V} (hab : a ≠ b) :
    MeasurePreserving (fun x : V → I => (x a, x b))
      (Measure.pi fun _ : V => (volume : Measure I)) ((volume : Measure I).prod volume) := by
  have hmeas : Measurable (fun x : V → I => (x a, x b)) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply b)
  refine ⟨hmeas, ?_⟩
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hpre : (fun x : V → I => (x a, x b)) ⁻¹' (s ×ˢ t) =
      Set.pi Set.univ (fun v => if v = a then s else if v = b then t else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ v
      split_ifs with h3 h4
      · subst h3; exact h1
      · subst h4; exact h2
      · trivial
    · intro h
      refine ⟨by simpa using h a, ?_⟩
      simpa [hab.symm] using h b
  rw [hpre, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  rw [Finset.prod_eq_one]
  · simp [hab.symm]
  · intro v hv
    have h1 : v ≠ b := (Finset.mem_erase.mp hv).1
    have h2 : v ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    simp [h1, h2]

lemma tU_congr_ae {V : Type*} [Fintype V] (H : SimpleGraph V) {U U' : I → I → ℝ}
    (h : AEEq volume U U') : tU H U = tU H U' := by
  classical
  unfold tU tUndir
  apply integral_congr_ae
  have : ∀ e ∈ H.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => (volume : Measure I)),
      U (x (Quot.out e).1) (x (Quot.out e).2) = U' (x (Quot.out e).1) (x (Quot.out e).2) := by
    intro e hmem
    have he : (Quot.out e).1 ≠ (Quot.out e).2 := by
      intro he
      have hd : (s((Quot.out e).1, (Quot.out e).2)).IsDiag := Sym2.mk_isDiag_iff.mpr he
      rw [show s((Quot.out e).1, (Quot.out e).2) = e from Quot.out_eq e] at hd
      exact H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp hmem) hd
    exact (measurePreserving_pair he).quasiMeasurePreserving.ae h
  filter_upwards [(Filter.eventually_all_finset _).mpr this] with x hx
  exact Finset.prod_congr rfl hx

/-- An everywhere-symmetric version of a kernel. -/
noncomputable def symmVersion (U : I → I → ℝ) : I → I → ℝ := by
  classical exact fun x y => if U x y = U y x then U x y else 0

lemma symmVersion_spec {U : I → I → ℝ} (hU : IsGraphon volume U) :
    IsSymmGraphon (symmVersion U) ∧ AEEq volume U (symmVersion U) := by
  classical
  have hm : Measurable (Function.uncurry U) := hU.1.1
  have hms : MeasurableSet {p : I × I | U p.1 p.2 = U p.2 p.1} :=
    measurableSet_eq_fun hm (hm.comp measurable_swap)
  refine ⟨⟨⟨?_, fun x y => ?_⟩, fun x y => ?_⟩, ?_⟩
  · have : Function.uncurry (symmVersion U) =
        {p : I × I | U p.1 p.2 = U p.2 p.1}.piecewise (Function.uncurry U) (fun _ => 0) := by
      funext p
      simp only [symmVersion, Function.uncurry, Set.piecewise, Set.mem_ofPred_eq]
    rw [this]
    exact Measurable.piecewise hms hm measurable_const
  · simp only [symmVersion]
    split_ifs
    · exact hU.1.2 x y
    · exact ⟨le_refl 0, zero_le_one⟩
  · simp only [symmVersion]
    split_ifs with h1 h2 h2
    · exact h1
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  · unfold AEEq
    filter_upwards [hU.2] with p hp
    simp only [kTranspose] at hp
    simp only [symmVersion, hp, ↓reduceIte]

lemma stepAvg_congr_ae (P : PosPartition (volume : Measure I)) {U U' : I → I → ℝ}
    (h : AEEq volume U U') : stepAvg P U = stepAvg P U' := by
  funext x y
  simp only [stepAvg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  exact integral_congr_ae (ae_restrict_of_ae h)

lemma stepSid_of_symm {V : Type*} [Fintype V] {H : SimpleGraph V} (h : IsStepSidorenkoSymm H) :
    IsStepSidorenko H := by
  intro U hU P
  obtain ⟨hs, hae⟩ := symmVersion_spec hU
  rw [stepAvg_congr_ae P hae, tU_congr_ae H hae]
  exact h _ hs P

lemma symm_of_stepSid {V : Type*} [Fintype V] {H : SimpleGraph V} (h : IsStepSidorenko H) :
    IsStepSidorenkoSymm H := fun U hU P =>
  h U ⟨hU.1, Filter.Eventually.of_forall fun p => hU.2 p.1 p.2⟩ P

open OrientedGraph in
lemma edgeFinset_eq_image {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (D : OrientedGraph V) (hD : D.underlying = H) :
    H.edgeFinset = D.arcs.image fun p => s(p.1, p.2) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, ← hD, underlying_adj_iff',
      Finset.mem_image]
    constructor
    · rintro (h | h)
      · exact ⟨(a, b), (Section6Aux.mem_arcs_iff D _).mpr h, rfl⟩
      · exact ⟨(b, a), (Section6Aux.mem_arcs_iff D _).mpr h, Sym2.eq_swap⟩
    · rintro ⟨p, hp, he⟩
      have hp' := (Section6Aux.mem_arcs_iff D p).mp hp
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [← h1, ← h2]; exact hp'
      · right; rw [← h1, ← h2]; exact hp'

open OrientedGraph in
lemma injOn_arcs_edge {V : Type*} [Fintype V] (D : OrientedGraph V) :
    Set.InjOn (fun p : V × V => s(p.1, p.2)) D.arcs := by
  classical
  intro p hp q hq h
  have hp' := (Section6Aux.mem_arcs_iff D p).mp hp
  have hq' := (Section6Aux.mem_arcs_iff D q).mp hq
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · rw [h1, h2] at hp'; exact absurd hq' (D.asymm _ _ hp')

open OrientedGraph in
lemma tU_eq_t {V : Type*} [Fintype V] (H : SimpleGraph V) (D : OrientedGraph V)
    (hD : D.underlying = H) {K : I → I → ℝ} (hK : ∀ x y, K x y = K y x) :
    tU H K = t D K := by
  classical
  unfold tU tUndir t tDir
  congr 1
  funext x
  rw [edgeFinset_eq_image H D hD, Finset.prod_image (injOn_arcs_edge D)]
  exact Finset.prod_congr rfl fun p _ => prod_out_symm hK x p.1 p.2

open OrientedGraph in
lemma card_edgeFinset_eq {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (D : OrientedGraph V) (hD : D.underlying = H) : H.edgeFinset.card = D.numArcs := by
  classical
  rw [edgeFinset_eq_image H D hD, Finset.card_image_of_injOn (injOn_arcs_edge D)]
  rfl

/-- The orientation of `H` from the side `s` to its complement. -/
def sideOG {V : Type*} (H : SimpleGraph V) (s : V → Prop) : OrientedGraph V where
  Adj a b := H.Adj a b ∧ s a ∧ ¬ s b
  irrefl v h := H.loopless.irrefl v h.1
  asymm _ _ h h' := h'.2.2 h.2.1

lemma sideOG_underlying {V : Type*} (H : SimpleGraph V) (s : V → Prop)
    (hbip : IsBipartition H s) : (sideOG H s).underlying = H := by
  ext a b
  rw [underlying_adj_iff']
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1.symm
  · intro h
    by_cases ha : s a
    · exact Or.inl ⟨h, ha, (hbip a b h).mp ha⟩
    · exact Or.inr ⟨h.symm, by have := hbip a b h; tauto, ha⟩

open OrientedGraph in
lemma card_sideEdges {V : Type*} [Fintype V] (D : OrientedGraph V) (s : V → Prop)
    (hs : ∀ u v, D.Adj u v → s u ∧ ¬ s v) :
    (sideEdges D.underlying s).card = D.numArcs := by
  classical
  unfold OrientedGraph.numArcs
  symm
  have harcs : D.arcs = (sideEdges D.underlying s).map
      ⟨fun q => (q.1.1, q.2.1), fun q q' h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)⟩ := by
    ext p
    simp only [Section6Aux.mem_arcs_iff, Finset.mem_map]
    constructor
    · intro h
      refine ⟨(⟨p.1, (hs _ _ h).1⟩, ⟨p.2, (hs _ _ h).2⟩), ?_, rfl⟩
      rw [mem_sideEdges]
      exact (underlying_adj_iff' D _ _).mpr (Or.inl h)
    · rintro ⟨q, hq, rfl⟩
      rw [mem_sideEdges] at hq
      rcases (underlying_adj_iff' D _ _).mp hq with h | h
      · exact h
      · exact absurd (hs _ _ h).1 q.2.2
  rw [harcs, Finset.card_map]

lemma weakNormFn_eq_rNorm {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → Prop)
    [DecidablePred s] (hbip : IsBipartition H s) {U : I → I → ℝ} (hU : ∀ x y, U x y = U y x) :
    weakNormFn H U = rNorm (sideEdges H s) U := by
  classical
  have hD := sideOG_underlying H s hbip
  have hs : ∀ u v, (sideOG H s).Adj u v → s u ∧ ¬ s v := fun u v h => h.2
  have h1 := tU_eq_t H (sideOG H s) hD (K := fun x y => |U x y|) (fun x y => by rw [hU])
  have h2 := t_eq_tb_side (sideOG H s) s hs (fun x y => |U x y|)
  have h3 := card_sideEdges (sideOG H s) s hs
  have h4 := card_edgeFinset_eq H (sideOG H s) hD
  rw [hD] at h2 h3
  unfold weakNormFn rNorm
  rw [h1, h2, h3, ← h4]

lemma isSymmKernel_smul {U : I → I → ℝ} (hU : IsSymmKernel U) (c : ℝ) :
    IsSymmKernel (fun x y => c * U x y) :=
  ⟨isKernel_const_mul' hU.1 c, fun x y => by show c * U x y = c * U y x; rw [hU.2]⟩

lemma isSymmKernel_add {U W : I → I → ℝ} (hU : IsSymmKernel U) (hW : IsSymmKernel W) :
    IsSymmKernel (fun x y => U x y + W x y) := by
  have := isKernel_lin hU.1 hW.1 1 1
  simp only [one_mul] at this
  exact ⟨this, fun x y => by show U x y + W x y = U y x + W y x; rw [hU.2, hW.2]⟩

lemma seminorm_of_wnGraph {V : Type*} [Fintype V] {H : SimpleGraph V}
    (h : IsWeaklyNormingGraph H) : IsWeaklySeminormingSymm H := by
  classical
  obtain ⟨s, hbip, hwn⟩ := h
  refine ⟨fun U hU c => ?_, fun U W hU hW => ?_⟩
  · rw [weakNormFn_eq_rNorm H s hbip (isSymmKernel_smul hU c).2,
      weakNormFn_eq_rNorm H s hbip hU.2]
    exact hwn.1 U hU.1 c
  · rw [weakNormFn_eq_rNorm H s hbip (isSymmKernel_add hU hW).2,
      weakNormFn_eq_rNorm H s hbip hU.2, weakNormFn_eq_rNorm H s hbip hW.2]
    exact hwn.2.1 U W hU.1 hW.1

/-- The one-part partition of `[0, 1]`. -/
noncomputable def trivPart : PosPartition (volume : Measure I) where
  k := 1
  part _ := Set.univ
  measurableSet_part _ := MeasurableSet.univ
  pos _ := by rw [measure_univ]; exact one_pos
  disjoint i j hij := absurd (Subsingleton.elim i j) hij
  cover := Set.iUnion_const _

lemma stepAvg_trivPart (U : I → I → ℝ) (x y : I) :
    stepAvg trivPart U x y = ∫ p, U p.1 p.2 ∂((volume : Measure I).prod volume) := by
  unfold stepAvg
  change ∑ i : Fin 1, ∑ j : Fin 1, (Set.univ : Set I).indicator (fun _ => (1 : ℝ)) x *
    (Set.univ : Set I).indicator (fun _ => (1 : ℝ)) y *
    ((∫ p in (Set.univ : Set I) ×ˢ (Set.univ : Set I), U p.1 p.2 ∂((volume : Measure I).prod volume)) /
      (((volume : Measure I) Set.univ).toReal * ((volume : Measure I) Set.univ).toReal)) = _
  simp

lemma tU_const {V : Type*} [Fintype V] (H : SimpleGraph V) (c : ℝ) :
    tU H (fun _ _ => c) = c ^ (letI := Classical.decRel H.Adj; H.edgeFinset.card) := by
  classical
  unfold tU tUndir
  simp only [Finset.prod_const]
  rw [integral_const]
  simp

lemma tU_smul {V : Type*} [Fintype V] (H : SimpleGraph V) (c : ℝ) (U : I → I → ℝ) :
    tU H (fun x y => c * U x y) =
      c ^ (letI := Classical.decRel H.Adj; H.edgeFinset.card) * tU H U := by
  classical
  unfold tU tUndir
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  rw [integral_const_mul]

lemma tU_nonneg {V : Type*} [Fintype V] (H : SimpleGraph V) {U : I → I → ℝ}
    (hU : ∀ x y, 0 ≤ U x y) : 0 ≤ tU H U := by
  classical
  unfold tU tUndir
  exact integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => hU _ _

/-- Definiteness of the weak-norm functional from step Sidorenko (via the one-part partition). -/
lemma normFn_of_seminorm {V : Type*} [Fintype V] {H : SimpleGraph V}
    (hsemi : IsWeaklySeminormingSymm H) (hss : IsStepSidorenkoSymm H) :
    IsWeaklyNormingSymmFn H := by
  classical
  refine ⟨hsemi, fun U hU h0 => ?_⟩
  set m := (letI := Classical.decRel H.Adj; H.edgeFinset.card) with hm
  have hz : tU H (fun x y => |U x y|) = 0 := by
    unfold weakNormFn at h0
    have h0' := (Real.rpow_eq_zero_iff_of_nonneg (tU_nonneg H fun x y => abs_nonneg (U x y))).mp
      (by convert h0 using 1)
    exact h0'.1
  obtain ⟨⟨hmeas, M, hM⟩, hsym⟩ := hU
  set M' := M + 1 + |M| with hM'
  have hM'pos : 0 < M' := by have := neg_abs_le M; linarith
  have hle : ∀ x y, |U x y| ≤ M' := fun x y => by
    have := hM x y; have := abs_nonneg M; linarith
  set G : I → I → ℝ := fun x y => M'⁻¹ * |U x y| with hG
  have hGmeas : Measurable (Function.uncurry G) :=
    (hmeas.abs).const_mul _
  have hGsymm : IsSymmGraphon G := by
    refine ⟨⟨hGmeas, fun x y => ⟨?_, ?_⟩⟩, fun x y => by simp only [hG]; rw [hsym]⟩
    · exact mul_nonneg (inv_nonneg.mpr hM'pos.le) (abs_nonneg _)
    · simp only [hG]
      rw [inv_mul_le_iff₀ hM'pos, mul_one]; exact hle x y
  have hGz : tU H G = 0 := by rw [hG, tU_smul, hz, mul_zero]
  have hstep := hss G hGsymm trivPart
  have hc : stepAvg trivPart G = fun _ _ => ∫ p, G p.1 p.2 ∂((volume : Measure I).prod volume) := by
    funext x y; exact stepAvg_trivPart G x y
  rw [hc, tU_const, hGz] at hstep
  set c := ∫ p, G p.1 p.2 ∂((volume : Measure I).prod volume) with hcdef
  have hG0 : ∀ p : I × I, 0 ≤ G p.1 p.2 := fun p =>
    mul_nonneg (inv_nonneg.mpr hM'pos.le) (abs_nonneg _)
  have hc0 : 0 ≤ c := integral_nonneg hG0
  have hcz : c = 0 := by
    by_contra hne
    have : 0 < c ^ m := pow_pos (lt_of_le_of_ne hc0 (Ne.symm hne)) _
    linarith
  have hGint : Integrable (fun p : I × I => G p.1 p.2) ((volume : Measure I).prod volume) := by
    refine Integrable.of_bound hGmeas.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
    show M'⁻¹ * |U p.1 p.2| ≤ 1
    rw [inv_mul_le_iff₀ hM'pos, mul_one]; exact hle _ _
  have hae := (integral_eq_zero_iff_of_nonneg hG0 hGint).mp hcz
  unfold AEEq
  filter_upwards [hae] with p hp
  simp only [Pi.zero_apply, hG] at hp
  have := mul_eq_zero.mp hp
  rcases this with h | h
  · exact absurd h (inv_ne_zero hM'pos.ne')
  · exact abs_eq_zero.mp h

lemma bipartite_of_stepSid {V : Type*} [Fintype V] {H : SimpleGraph V}
    (hss : IsStepSidorenkoSymm H) : ∃ s : V → Prop, IsBipartition H s := by
  classical
  by_contra hno
  set W : I → I → ℝ := fun x y => if ((x : ℝ) < 1 / 2 ↔ (y : ℝ) < 1 / 2) then 0 else 1 with hW
  have hWsymm : ∀ x y, W x y = W y x := fun x y => by
    simp only [hW]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)
  have hset : MeasurableSet {p : I × I | ((p.1 : ℝ) < 1 / 2 ↔ (p.2 : ℝ) < 1 / 2)} := by
    have h1 : MeasurableSet {p : I × I | (p.1 : ℝ) < 1 / 2} :=
      measurableSet_lt (measurable_subtype_coe.comp measurable_fst) measurable_const
    have h2 : MeasurableSet {p : I × I | (p.2 : ℝ) < 1 / 2} :=
      measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_const
    have : {p : I × I | ((p.1 : ℝ) < 1 / 2 ↔ (p.2 : ℝ) < 1 / 2)} =
        ({p : I × I | (p.1 : ℝ) < 1 / 2} ∩ {p | (p.2 : ℝ) < 1 / 2}) ∪
        ({p : I × I | (p.1 : ℝ) < 1 / 2}ᶜ ∩ {p | (p.2 : ℝ) < 1 / 2}ᶜ) := by
      ext p; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    rw [this]
    exact (h1.inter h2).union (h1.compl.inter h2.compl)
  have hWmeas : Measurable (Function.uncurry W) := by
    have : Function.uncurry W = {p : I × I | ((p.1 : ℝ) < 1 / 2 ↔ (p.2 : ℝ) < 1 / 2)}.piecewise
        (fun _ => 0) (fun _ => 1) := by
      funext p; simp only [hW, Function.uncurry, Set.piecewise, Set.mem_ofPred_eq]
    rw [this]
    exact Measurable.piecewise hset measurable_const measurable_const
  have hW01 : ∀ x y, 0 ≤ W x y ∧ W x y ≤ 1 := fun x y => by
    simp only [hW]; split_ifs <;> norm_num
  have hWg : IsSymmGraphon W := ⟨⟨hWmeas, fun x y => hW01 x y⟩, hWsymm⟩
  have hzero : tU H W = 0 := by
    unfold tU tUndir
    have : ∀ x : V → I, ∏ e ∈ H.edgeFinset, W (x (Quot.out e).1) (x (Quot.out e).2) = 0 := by
      intro x
      have hnb : ¬ IsBipartition H (fun v => ((x v : I) : ℝ) < 1 / 2) := fun h => hno ⟨_, h⟩
      unfold IsBipartition at hnb
      push Not at hnb
      obtain ⟨u, v, huv, hn⟩ := hnb
      refine Finset.prod_eq_zero (i := s(u, v)) (SimpleGraph.mem_edgeFinset.mpr huv) ?_
      rw [prod_out_symm hWsymm]
      simp only [hW]
      split_ifs with h
      · rfl
      · exfalso
        rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h ⟨fun _ => h2, fun _ => h1⟩
        · exact h ⟨fun h3 => absurd h3 (not_lt.mpr h1), fun h3 => absurd h3 (not_lt.mpr h2)⟩
    simp_rw [this]
    simp
  have hstep := hss W hWg trivPart
  have hc : stepAvg trivPart W = fun _ _ => ∫ p, W p.1 p.2 ∂((volume : Measure I).prod volume) := by
    funext x y; exact stepAvg_trivPart W x y
  rw [hc, tU_const, hzero] at hstep
  set c := ∫ p, W p.1 p.2 ∂((volume : Measure I).prod volume) with hcdef
  have hcpos : 0 < c := by
    set R : Set (I × I) := ivl 0 (1 / 4) ×ˢ ivl (3 / 4) 1 with hR
    have hRm : MeasurableSet R := (measurableSet_ivl _ _).prod (measurableSet_ivl _ _)
    have hle : R.indicator (fun _ => (1 : ℝ)) ≤ fun p => W p.1 p.2 := by
      intro p
      by_cases hp : p ∈ R
      · rw [Set.indicator_of_mem hp]
        obtain ⟨⟨_, h1⟩, ⟨h2, _⟩⟩ := hp
        simp only [hW]
        split_ifs with h
        · exfalso; have := h.mp (by linarith); linarith
        · rfl
      · rw [Set.indicator_of_notMem hp]; exact (hW01 _ _).1
    have hWint : Integrable (fun p : I × I => W p.1 p.2) ((volume : Measure I).prod volume) := by
      refine Integrable.of_bound hWmeas.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hW01 p.1 p.2).1, (hW01 p.1 p.2).2]
    have h1 := integral_mono ((integrable_const (1 : ℝ)).indicator hRm) hWint hle
    rw [integral_indicator hRm, setIntegral_const, smul_eq_mul, mul_one] at h1
    have hpos : 0 < ((volume : Measure I).prod volume).real R := by
      rw [measureReal_def, hR, Measure.prod_prod, volume_ivl (le_refl 0) (by norm_num),
        volume_ivl (by norm_num) (le_refl 1)]
      norm_num
    linarith
  have : 0 < c ^ (letI := Classical.decRel H.Adj; H.edgeFinset.card) := pow_pos hcpos _
  linarith

/-- The orientation of a simple graph given by the representative pairs of its edges. -/
def orientOut {V : Type*} (H : SimpleGraph V) : OrientedGraph V where
  Adj a b := H.Adj a b ∧ Quot.out s(a, b) = (a, b)
  irrefl v h := H.loopless.irrefl v h.1
  asymm a b h h' := by
    have e : Quot.out s(b, a) = Quot.out s(a, b) := by rw [Sym2.eq_swap]
    rw [h'.2, h.2] at e
    exact H.ne_of_adj h.1 (Prod.ext_iff.mp e).2

lemma orientOut_underlying {V : Type*} (H : SimpleGraph V) : (orientOut H).underlying = H := by
  ext a b
  rw [underlying_adj_iff']
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1.symm
  · intro h
    have hq : s((Quot.out s(a, b)).1, (Quot.out s(a, b)).2) = s(a, b) := Quot.out_eq _
    rcases Sym2.eq_iff.mp hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h, Prod.ext h1 h2⟩
    · refine Or.inr ⟨h.symm, ?_⟩
      have e : Quot.out s(b, a) = Quot.out s(a, b) := by rw [Sym2.eq_swap]
      rw [e]; exact Prod.ext h1 h2

lemma integral_cos_two_pi : ∫ x : I, Real.cos (2 * Real.pi * (x : ℝ)) = 0 := by
  rw [unitInterval.volume_def,
    integral_subtype_comap measurableSet_Icc (fun x : ℝ => Real.cos (2 * Real.pi * x)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (by positivity), integral_cos]
  simp

lemma integral_sin_two_pi : ∫ x : I, Real.sin (2 * Real.pi * (x : ℝ)) = 0 := by
  rw [unitInterval.volume_def,
    integral_subtype_comap measurableSet_Icc (fun x : ℝ => Real.sin (2 * Real.pi * x)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) (by positivity), integral_sin]
  simp

lemma integral_testK_half :
    ∫ p : I × I, Section6Aux.testK (1 / 2) 0 p.1 p.2 ∂((volume : Measure I).prod volume) = 1 / 2 := by
  have hc : Continuous fun t : I => Real.cos (2 * Real.pi * (t : ℝ)) := by fun_prop
  have hs : Continuous fun t : I => Real.sin (2 * Real.pi * (t : ℝ)) := by fun_prop
  have hci : Integrable (fun t : I => Real.cos (2 * Real.pi * (t : ℝ))) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsi : Integrable (fun t : I => Real.sin (2 * Real.pi * (t : ℝ))) :=
    hs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : (fun p : I × I => Section6Aux.testK (1 / 2) 0 p.1 p.2) = fun p =>
      1 / 2 + (1 / 2) * (Real.cos (2 * Real.pi * (p.1 : ℝ)) * Real.cos (2 * Real.pi * (p.2 : ℝ)))
        + (1 / 2) * (Real.sin (2 * Real.pi * (p.1 : ℝ)) * Real.sin (2 * Real.pi * (p.2 : ℝ))) := by
    funext p
    simp only [Section6Aux.testK, add_zero]
    rw [show 2 * Real.pi * ((p.1 : ℝ) - p.2) = 2 * Real.pi * p.1 - 2 * Real.pi * p.2 by ring,
      Real.cos_sub]
    ring
  rw [e]
  have h1 := hci.mul_prod hci
  have h2 := hsi.mul_prod hsi
  have hA : Integrable (fun p : I × I => (1 / 2 : ℝ) +
      1 / 2 * (Real.cos (2 * Real.pi * (p.1 : ℝ)) * Real.cos (2 * Real.pi * (p.2 : ℝ))))
      ((volume : Measure I).prod volume) := (integrable_const _).add (h1.const_mul _)
  have hB : Integrable (fun p : I × I =>
      1 / 2 * (Real.sin (2 * Real.pi * (p.1 : ℝ)) * Real.sin (2 * Real.pi * (p.2 : ℝ))))
      ((volume : Measure I).prod volume) := h2.const_mul _
  have hC : Integrable (fun p : I × I =>
      1 / 2 * (Real.cos (2 * Real.pi * (p.1 : ℝ)) * Real.cos (2 * Real.pi * (p.2 : ℝ))))
      ((volume : Measure I).prod volume) := h1.const_mul _
  rw [integral_add hA hB, integral_add (integrable_const _) hC, integral_const_mul,
    integral_const_mul,
    integral_prod_mul (fun t : I => Real.cos (2 * Real.pi * (t : ℝ)))
      (fun t : I => Real.cos (2 * Real.pi * (t : ℝ))),
    integral_prod_mul (fun t : I => Real.sin (2 * Real.pi * (t : ℝ)))
      (fun t : I => Real.sin (2 * Real.pi * (t : ℝ))),
    integral_cos_two_pi, integral_sin_two_pi]
  simp

lemma testK_half_symm (x y : I) :
    Section6Aux.testK (1 / 2) 0 x y = Section6Aux.testK (1 / 2) 0 y x := by
  simp only [Section6Aux.testK, add_zero]
  rw [show 2 * Real.pi * ((y : ℝ) - x) = -(2 * Real.pi * ((x : ℝ) - y)) by ring, Real.cos_neg]

lemma stepSid_of_stepForcing {V : Type*} [Fintype V] {H : SimpleGraph V} (h : IsStepForcing H) :
    IsStepSidorenko H := by
  intro U hU P
  by_cases hae : AEEq volume U (stepAvg P U)
  · rw [tU_congr_ae H hae]
  · exact (h U hU P hae).le

lemma not_acyclic_of_stepForcing {V : Type*} [Fintype V] {H : SimpleGraph V}
    (h : IsStepForcing H) : ¬ H.IsAcyclic := by
  intro hacyc
  have hD := orientOut_underlying H
  have hac : (orientOut H).underlying.IsAcyclic := by rw [hD]; exact hacyc
  set U := Section6Aux.testK (1 / 2) 0 with hUdef
  have hUd := Section6Aux.testK_isDigraphon (c := 1 / 2) 0 (by norm_num)
  have hUg : IsGraphon volume U :=
    ⟨hUd, Filter.Eventually.of_forall fun p => testK_half_symm p.1 p.2⟩
  have hstep : stepAvg trivPart U = Section6Aux.testK 0 0 := by
    funext x y
    rw [stepAvg_trivPart, integral_testK_half]
    simp [Section6Aux.testK]
  have hne : ¬ AEEq volume U (stepAvg trivPart U) := by
    rw [hstep]
    refine not_aeEq_of_rect (a := 0) (b := 1 / 8) (a' := 0) (b' := 1 / 8) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    intro x hx y hy hxy
    simp only [hUdef, Section6Aux.testK, add_zero, zero_mul] at hxy
    have hc : 0 < Real.cos (2 * Real.pi * ((x : ℝ) - y)) := by
      apply Real.cos_pos_of_mem_Ioo
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      constructor <;> nlinarith [Real.pi_pos]
    linarith
  have := h U hUg trivPart hne
  rw [hstep, tU_eq_t H (orientOut H) hD (fun x y => by simp [Section6Aux.testK]),
    tU_eq_t H (orientOut H) hD testK_half_symm, t_testK_acyclic _ hac,
    t_testK_acyclic _ hac] at this
  exact lt_irrefl _ this

lemma edgeSet_nonempty_of_cycle {V : Type*} {H : SimpleGraph V} (h : ¬ H.IsAcyclic) :
    H.edgeSet.Nonempty := by
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at h
  obtain ⟨u, w, hw⟩ := h
  exact ⟨s(u, w.snd), w.adj_snd hw.not_nil⟩

lemma wnGraph_of_stepSid {V : Type u} [Fintype V] (hA3 : DGHRRThm325Hyp.{u})
    (hA4 : LeeSidorenkoThm13Hyp.{u}) {H : SimpleGraph V} (hconn : H.Connected)
    (hne : H.edgeSet.Nonempty) (h : IsStepSidorenko H) : IsWeaklyNormingGraph H := by
  have hs := symm_of_stepSid h
  exact hA4 V H hconn hne (bipartite_of_stepSid hs)
    (normFn_of_seminorm (hA3 V H hconn hne hs) hs)

open OrientedGraph in
lemma osk_iff_stepSid {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u})
    (hA2 : DGHRRCor324Hyp.{u}) (hA3 : DGHRRThm325Hyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (D : OrientedGraph V) (hconn : D.IsConnected) (hone : D.IsOneDirection)
    (hsc : D.IsSelfConverse) (he : 1 ≤ D.numArcs) :
    D.IsOSK ↔ IsStepSidorenko D.underlying := by
  classical
  constructor
  · intro hD
    obtain ⟨_, _, hwn⟩ := (osk_char hA1 D hconn he).mp hD
    exact stepSid_of_symm (hA2 V _ (seminorm_of_wnGraph hwn))
  · intro h
    have hne : D.underlying.edgeSet.Nonempty := by
      have hpos : 0 < D.arcs.card := by unfold OrientedGraph.numArcs at he; omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      exact ⟨s(p.1, p.2), (underlying_adj_iff' D _ _).mpr
        (Or.inl ((Section6Aux.mem_arcs_iff D p).mp hp))⟩
    exact (osk_char hA1 D hconn he).mpr ⟨hone, hsc, wnGraph_of_stepSid hA3 hA4 hconn hne h⟩

end Section1Aux

end NieWeiOrientedSidorenko
