import NieWeiOrientedSidorenko.Section1Aux

/-!
# Theorems 1.1, 1.10 and 1.11 (part B)

Isomorphism invariance of directed densities, and Theorem 1.10 (oriented paths), for
`S1Families.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace S1Families

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OrientedGraph

/-! ## Isomorphism tools -/

section IsoTools

variable {V W X : Type*}

/-- The inverse isomorphism. -/
def isoSymm {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D') : D'.Iso D where
  toEquiv := g.toEquiv.symm
  map_adj_iff u v := by
    rw [← g.map_adj_iff]; simp

/-- Composition of isomorphisms. -/
def isoTrans {D : OrientedGraph V} {D' : OrientedGraph W} {D'' : OrientedGraph X}
    (g : D.Iso D') (h : D'.Iso D'') : D.Iso D'' where
  toEquiv := g.toEquiv.trans h.toEquiv
  map_adj_iff u v := by
    simp only [Equiv.trans_apply]
    rw [h.map_adj_iff, g.map_adj_iff]

/-- Transport of an oriented graph along a bijection. -/
def transp (D : OrientedGraph V) (e : V ≃ W) : OrientedGraph W where
  Adj a b := D.Adj (e.symm a) (e.symm b)
  irrefl a := D.irrefl _
  asymm a b := D.asymm _ _

/-- The transport is isomorphic to the original. -/
def transpIso (D : OrientedGraph V) (e : V ≃ W) : D.Iso (transp D e) where
  toEquiv := e
  map_adj_iff u v := by simp [transp]

lemma transp_underlying_adj (D : OrientedGraph V) (e : V ≃ W) (a b : W) :
    (transp D e).underlying.Adj a b ↔ D.underlying.Adj (e.symm a) (e.symm b) := by
  rw [Section1Aux.underlying_adj_iff', Section1Aux.underlying_adj_iff']
  rfl

lemma transp_underlying_eq (D : OrientedGraph V) {G : SimpleGraph W} (φ : D.underlying ≃g G) :
    (transp D φ.toEquiv).underlying = G := by
  ext a b
  rw [transp_underlying_adj]
  have := φ.map_adj_iff (v := φ.symm a) (w := φ.symm b)
  simp only [RelIso.apply_symm_apply] at this
  exact this.symm.trans (by rfl)

lemma underlying_adj_of_iso {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D')
    (a b : V) : D'.underlying.Adj (g.toEquiv a) (g.toEquiv b) ↔ D.underlying.Adj a b := by
  rw [Section1Aux.underlying_adj_iff', Section1Aux.underlying_adj_iff', g.map_adj_iff,
    g.map_adj_iff]

variable [Fintype V] [Fintype W]

lemma t_iso {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D') (U : I → I → ℝ) :
    t D U = t D' U := by
  classical
  set Φ : (V → I) ≃ᵐ (W → I) :=
    MeasurableEquiv.arrowCongr' g.toEquiv (MeasurableEquiv.refl I) with hΦ
  have hmp : MeasurePreserving Φ (Measure.pi fun _ : V => (volume : Measure I))
      (Measure.pi fun _ : W => (volume : Measure I)) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ => MeasurePreserving.id _)
  have hz : ∀ x : V → I, Φ x = fun w => x (g.toEquiv.symm w) := fun x => by
    funext w; simp [hΦ, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  unfold t tDir
  rw [← hmp.integral_comp']
  congr 1
  funext x
  rw [hz]
  refine Finset.prod_nbij' (fun p => (g.toEquiv p.1, g.toEquiv p.2))
    (fun p => (g.toEquiv.symm p.1, g.toEquiv.symm p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Section6Aux.mem_arcs_iff] at hp ⊢
    exact (g.map_adj_iff _ _).mpr hp
  · intro p hp
    rw [Section6Aux.mem_arcs_iff] at hp ⊢
    rw [← g.map_adj_iff]; simpa using hp
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

lemma isOSK_iso {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D') :
    D.IsOSK ↔ D'.IsOSK := by
  unfold IsOSK
  simp only [t_iso g]

lemma isOASK_iso {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D') :
    D.IsOASK ↔ D'.IsOASK := by
  unfold IsOASK
  simp only [t_iso g]

lemma numArcs_iso {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D') :
    D.numArcs = D'.numArcs := by
  classical
  unfold numArcs
  refine Finset.card_nbij' (fun p => (g.toEquiv p.1, g.toEquiv p.2))
    (fun p => (g.toEquiv.symm p.1, g.toEquiv.symm p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Section6Aux.mem_arcs_iff] at hp ⊢
    exact (g.map_adj_iff _ _).mpr hp
  · intro p hp
    simp only [Finset.mem_coe, Section6Aux.mem_arcs_iff] at hp ⊢
    rw [← g.map_adj_iff]; simpa using hp
  · intro p _; simp
  · intro p _; simp

end IsoTools

/-! ## Weakly norming bipartite graphs are biregular (KEY A7, from Lemma 2.2) -/

section Biregular

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The swap of the two sides. -/
def swapEmb : X × Y ↪ Y × X := ⟨Prod.swap, Prod.swap_injective⟩

lemma tb_swap (E : Finset (X × Y)) (U : I → I → ℝ) :
    tb (E.map swapEmb) U = tb E (kTranspose U) := by
  unfold tb tBi
  have hmp := (MeasurableEquiv.prodComm (α := X → I) (β := Y → I)).measurableEmbedding
  rw [← (Measure.measurePreserving_swap (μ := Measure.pi fun _ : X => (volume : Measure I))
    (ν := Measure.pi fun _ : Y => (volume : Measure I))).integral_comp hmp]
  congr 1; funext z
  rw [Finset.prod_map]
  rfl

lemma isKernel_T {U : I → I → ℝ} (hU : IsKernel U) : IsKernel (kTranspose U) := by
  obtain ⟨hm, M, hM⟩ := hU
  exact ⟨hm.comp measurable_swap, M, fun x y => hM y x⟩

lemma wn_swap {E : Finset (X × Y)} (hE : IsWeaklyNorming E) :
    IsWeaklyNorming (E.map swapEmb) := by
  have hr : ∀ U, rNorm (E.map swapEmb) U = rNorm E (kTranspose U) := fun U => by
    simp only [rNorm, tb_swap, Finset.card_map]; rfl
  obtain ⟨h1, h2, h3⟩ := hE
  refine ⟨fun U hU c => ?_, fun U V hU hV => ?_, fun U hU h0 => ?_⟩
  · rw [hr, hr]; exact h1 _ (isKernel_T hU) c
  · rw [hr, hr, hr]; exact h2 _ _ (isKernel_T hU) (isKernel_T hV)
  · rw [hr] at h0
    have h := h3 _ (isKernel_T hU) h0
    unfold AEEq at h ⊢
    have := (Measure.measurePreserving_swap (μ := (volume : Measure I))
      (ν := (volume : Measure I))).quasiMeasurePreserving.ae h
    simpa [kTranspose] using this

/-- The degree of `x ∈ X` in `E`. -/
noncomputable def degX (E : Finset (X × Y)) (x : X) : ℕ := by
  classical exact (E.filter fun p => p.1 = x).card

omit [Fintype X] [Fintype Y] in
lemma degX_def [DecidableEq X] (E : Finset (X × Y)) (x : X) :
    degX E x = (E.filter fun p => p.1 = x).card := by
  unfold degX; convert rfl

omit [Fintype Y] in
lemma prod_fst_pow (E : Finset (X × Y)) (h : X → ℝ) :
    ∏ p ∈ E, h p.1 = ∏ x, h x ^ degX E x := by
  classical
  rw [← Finset.prod_fiberwise E Prod.fst (fun p => h p.1)]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]), Finset.prod_const,
    degX_def]

/-- The half-interval indicator. -/
noncomputable def gHalf : I → ℝ := (Section1Aux.ivl 0 (1 / 2)).indicator fun _ => 1

lemma gHalf_meas : Measurable gHalf :=
  measurable_const.indicator (Section1Aux.measurableSet_ivl 0 (1 / 2))

lemma gHalf_01 (x : I) : gHalf x = 0 ∨ gHalf x = 1 := by
  unfold gHalf
  by_cases h : x ∈ Section1Aux.ivl 0 (1 / 2)
  · right; exact Set.indicator_of_mem h _
  · left; exact Set.indicator_of_notMem h _

lemma gHalf_pow (x : I) {k : ℕ} (hk : 1 ≤ k) : gHalf x ^ k = gHalf x := by
  rcases gHalf_01 x with h | h <;> rw [h]
  · exact zero_pow (by omega)
  · exact one_pow k

lemma integral_gHalf : ∫ x, gHalf x = 1 / 2 := by
  unfold gHalf
  change ∫ x, (Section1Aux.ivl 0 (1 / 2)).indicator 1 x = 1 / 2
  rw [integral_indicator_one (Section1Aux.measurableSet_ivl 0 (1 / 2)), Measure.real,
    Section1Aux.volume_ivl le_rfl (by norm_num)]
  norm_num

lemma integral_fst_pi (F : (X → I) → ℝ) :
    ∫ z, F z.1 ∂((Measure.pi fun _ : X => (volume : Measure I)).prod
      (Measure.pi fun _ : Y => (volume : Measure I))) =
      ∫ xs, F xs ∂(Measure.pi fun _ : X => (volume : Measure I)) := by
  rw [integral_fun_fst]; simp

/-- **KEY A7, one side.** In a weakly norming bipartite graph without isolated vertices in `X`,
`deg(x₀) · |X| ≤ e(H)` for every `x₀ ∈ X`. -/
lemma deg_le_of_wn (E : Finset (X × Y)) (hE : IsWeaklyNorming E) (hdeg : ∀ x, 1 ≤ degX E x)
    (x0 : X) : degX E x0 * Fintype.card X ≤ E.card := by
  classical
  have hm : 0 < E.card := by
    have h := hdeg x0
    rw [degX_def] at h
    exact lt_of_lt_of_le h (Finset.card_le_card (Finset.filter_subset _ _))
  set Ud : X × Y → I → I → ℝ := fun p x y => if p.1 = x0 then gHalf x else 1 with hUd
  have hker : ∀ p ∈ E, IsKernel (Ud p) := by
    intro p _
    by_cases hp : p.1 = x0
    · simp only [hUd, hp, ↓reduceIte]
      refine ⟨gHalf_meas.comp measurable_fst, 1, fun x y => ?_⟩
      rcases gHalf_01 x with h | h <;> simp [h]
    · simp only [hUd, hp, ↓reduceIte]
      exact ⟨measurable_const, 1, fun x y => by simp⟩
  have hH := lemma_2_2 E hE Ud hker
  -- the left-hand side is `1/2`
  have hL : tBiDec volume E Ud = 1 / 2 := by
    unfold tBiDec
    have : ∀ z : (X → I) × (Y → I), ∏ p ∈ E, Ud p (z.1 p.1) (z.2 p.2) =
        ∏ x, (if x = x0 then gHalf (z.1 x) else 1) := by
      intro z
      simp only [hUd]
      rw [prod_fst_pow E (fun x => if x = x0 then gHalf (z.1 x) else 1)]
      refine Finset.prod_congr rfl fun x _ => ?_
      by_cases hx : x = x0
      · simp only [hx, ↓reduceIte]; exact gHalf_pow _ (hdeg x0)
      · simp [hx]
    simp_rw [this]
    rw [integral_fst_pi (fun xs => ∏ x, (if x = x0 then gHalf (xs x) else 1))]
    rw [integral_fintype_prod_eq_prod (fun x a => if x = x0 then gHalf a else 1)]
    rw [Finset.prod_eq_single x0 (fun x _ hx => by simp [hx]) (by simp)]
    simp [integral_gHalf]
  -- the factors of the right-hand side
  have hR1 : tb E (fun x y => |gHalf x|) = (1 / 2) ^ Fintype.card X := by
    unfold tb tBi
    have : ∀ z : (X → I) × (Y → I), ∏ p ∈ E, |gHalf (z.1 p.1)| = ∏ x, gHalf (z.1 x) := by
      intro z
      rw [prod_fst_pow E (fun x => |gHalf (z.1 x)|)]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [abs_of_nonneg (by rcases gHalf_01 (z.1 x) with h | h <;> rw [h] <;> norm_num)]
      exact gHalf_pow _ (hdeg x)
    simp_rw [this]
    rw [integral_fst_pi (fun xs => ∏ x, gHalf (xs x)),
      integral_fintype_prod_eq_pow gHalf, integral_gHalf]
  have hR2 : tb E (fun x y => |(1 : ℝ)|) = 1 := by
    unfold tb tBi; simp
  have hR : ∏ p ∈ E, tb E (fun x y => |Ud p x y|) ^ ((1 : ℝ) / E.card) =
      (((1 / 2 : ℝ) ^ Fintype.card X) ^ ((1 : ℝ) / E.card)) ^ degX E x0 := by
    have hpt : ∀ p ∈ E, tb E (fun x y => |Ud p x y|) ^ ((1 : ℝ) / E.card) =
        if p.1 = x0 then ((1 / 2 : ℝ) ^ Fintype.card X) ^ ((1 : ℝ) / E.card) else 1 := by
      intro p _
      by_cases hp : p.1 = x0
      · simp only [hUd, hp, ↓reduceIte]; rw [hR1]
      · simp only [hUd, hp, ↓reduceIte]; rw [hR2, Real.one_rpow]
    rw [Finset.prod_congr rfl hpt, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
      mul_one]
    rfl
  rw [hL, hR, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hH
  -- `1/2 ≤ (1/2)^{|X| deg / m}` gives `|X| deg / m ≤ 1`
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  rw [← Real.rpow_natCast ((1 / 2 : ℝ)) (Fintype.card X), ← Real.rpow_mul hpos.le,
    ← Real.rpow_natCast _ (degX E x0), ← Real.rpow_mul hpos.le] at hH
  have h1 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ ((Fintype.card X : ℝ) * (1 / E.card) *
      (degX E x0 : ℝ)) := by rwa [Real.rpow_one]
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hpos (by norm_num)] at h1
  have hm' : (0 : ℝ) < E.card := by exact_mod_cast hm
  rw [show (Fintype.card X : ℝ) * (1 / E.card) * (degX E x0 : ℝ) =
    (degX E x0 * Fintype.card X : ℝ) / E.card by ring, div_le_one hm'] at h1
  exact_mod_cast h1

omit [Fintype Y] in
lemma sum_degX (E : Finset (X × Y)) : ∑ x, degX E x = E.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp only [degX_def]

/-- **KEY A7.** A weakly norming bipartite graph without isolated vertices in `X` has all
degrees in `X` equal. -/
lemma degX_eq_of_wn (E : Finset (X × Y)) (hE : IsWeaklyNorming E) (hdeg : ∀ x, 1 ≤ degX E x)
    (x1 x2 : X) : degX E x1 = degX E x2 := by
  classical
  have hle := deg_le_of_wn E hE hdeg
  have hN : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x1⟩
  have hall : ∀ x, degX E x * Fintype.card X = E.card := by
    intro x
    by_contra hne
    have hlt : degX E x * Fintype.card X < E.card := lt_of_le_of_ne (hle x) hne
    have := Finset.sum_lt_sum (s := Finset.univ) (f := fun x => degX E x * Fintype.card X)
      (g := fun _ => E.card) (fun x _ => hle x) ⟨x, Finset.mem_univ _, hlt⟩
    rw [← Finset.sum_mul, sum_degX, Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    linarith [mul_comm (Fintype.card X) E.card]
  have h1 := hall x1
  have h2 := hall x2
  exact Nat.eq_of_mul_eq_mul_right hN (h1.trans h2.symm)

omit [Fintype X] [Fintype Y] in
lemma degX_swap [DecidableEq Y] (E : Finset (X × Y)) (y : Y) :
    degX (E.map swapEmb) y = (E.filter fun p : X × Y => p.2 = y).card := by
  classical
  rw [degX_def, Finset.filter_map, Finset.card_map]
  congr 1

end Biregular

section SideDeg

variable {V : Type*} [Fintype V]

lemma degX_sideEdges (H : SimpleGraph V) [DecidableRel H.Adj] (s : V → Prop) (hbip : IsBipartition H s)
    (x : {v // s v}) : degX (sideEdges H s) x = H.degree x.1 := by
  classical
  rw [degX_def, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun p _ => p.2.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    rw [SimpleGraph.mem_neighborFinset, ← hp2]
    exact (Section1Aux.mem_sideEdges H s p).mp hp1
  · intro p hp q hq h
    have e1 := (Finset.mem_filter.mp hp).2
    have e2 := (Finset.mem_filter.mp hq).2
    exact Prod.ext (e1.trans e2.symm) (Subtype.ext h)
  · intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    have hsv : ¬ s v := (hbip _ _ hv).mp x.2
    refine ⟨(x, ⟨v, hsv⟩), Finset.mem_filter.mpr ⟨(Section1Aux.mem_sideEdges H s _).mpr hv, rfl⟩,
      rfl⟩

lemma degY_sideEdges (H : SimpleGraph V) [DecidableRel H.Adj] (s : V → Prop) [DecidablePred s] (hbip : IsBipartition H s)
    (y : {v // ¬ s v}) : degX ((sideEdges H s).map swapEmb) y = H.degree y.1 := by
  classical
  rw [degX_swap, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun (p : {v // s v} × {v // ¬ s v}) _ => p.1.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    rw [SimpleGraph.mem_neighborFinset, ← hp2]
    exact ((Section1Aux.mem_sideEdges H s p).mp hp1).symm
  · intro p hp q hq h
    have e1 := (Finset.mem_filter.mp hp).2
    have e2 := (Finset.mem_filter.mp hq).2
    exact Prod.ext (Subtype.ext h) (e1.trans e2.symm)
  · intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    have hsv : s v := by
      have := hbip _ _ hv
      by_contra h; exact y.2 (this.mpr h)
    refine ⟨(⟨v, hsv⟩, y), Finset.mem_filter.mpr ⟨(Section1Aux.mem_sideEdges H s _).mpr hv.symm,
      rfl⟩, rfl⟩

/-- A weakly norming bipartite graph without isolated vertices: any two vertices on the same side
have the same degree. -/
lemma degree_eq_of_wnGraph (H : SimpleGraph V) [DecidableRel H.Adj] (s : V → Prop) [DecidablePred s] (hbip : IsBipartition H s)
    (hwn : IsWeaklyNorming (sideEdges H s)) (hpos : ∀ v, 1 ≤ H.degree v) (u v : V)
    (hu : s u ↔ s v) : H.degree u = H.degree v := by
  classical
  by_cases h : s u
  · have := degX_eq_of_wn (sideEdges H s) hwn
      (fun x => by rw [degX_sideEdges H s hbip]; exact hpos _) ⟨u, h⟩ ⟨v, hu.mp h⟩
    rwa [degX_sideEdges H s hbip, degX_sideEdges H s hbip] at this
  · have hv : ¬ s v := fun h' => h (hu.mpr h')
    have := degX_eq_of_wn ((sideEdges H s).map swapEmb) (wn_swap hwn)
      (fun y => by rw [degY_sideEdges H s hbip]; exact hpos _) ⟨u, h⟩ ⟨v, hv⟩
    rwa [degY_sideEdges H s hbip, degY_sideEdges H s hbip] at this

end SideDeg

section PathDeg

lemma pathGraph_degree_zero (n : ℕ) (hn : 2 ≤ n) :
    (SimpleGraph.pathGraph n).degree ⟨0, by omega⟩ = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one]
  refine ⟨⟨1, by omega⟩, ?_⟩
  ext b
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, Finset.mem_singleton,
    Fin.ext_iff]
  omega

lemma pathGraph_degree_two (n : ℕ) (hn : 4 ≤ n) :
    (SimpleGraph.pathGraph n).degree ⟨2, by omega⟩ = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_two]
  refine ⟨⟨1, by omega⟩, ⟨3, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  ext b
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff]
  omega

lemma pathGraph_degree_pos (n : ℕ) (hn : 2 ≤ n) (v : Fin n) :
    1 ≤ (SimpleGraph.pathGraph n).degree v := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, SimpleGraph.degree_pos_iff_exists_adj]
  by_cases h : v.val + 1 < n
  · exact ⟨⟨v.val + 1, h⟩, by simp [SimpleGraph.pathGraph_adj]⟩
  · refine ⟨⟨v.val - 1, by omega⟩, ?_⟩
    rw [SimpleGraph.pathGraph_adj]; right; show v.val - 1 + 1 = v.val; omega

end PathDeg

/-! ## Paths with at least three edges are not OAS (tex l.1302-1353) -/

section PathOAS

/-- `S^k 1` for a `3 × 3` matrix. -/
noncomputable def uvec (S : Fin 3 → Fin 3 → ℝ) : ℕ → Fin 3 → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun a => ∑ b, S a b * uvec S k b

lemma sum_cons_split {k : ℕ} (F : (Fin (k + 1) → Fin 3) → ℝ) :
    ∑ f, F f = ∑ a, ∑ g : Fin k → Fin 3, F (Fin.cons a g) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  rfl

lemma transfer (S : Fin 3 → Fin 3 → ℝ) (k : ℕ) (a : Fin 3) :
    ∑ g : Fin k → Fin 3, ∏ i : Fin k, S ((Fin.cons a g : Fin (k + 1) → Fin 3) i.castSucc)
      ((Fin.cons a g : Fin (k + 1) → Fin 3) i.succ) = uvec S k a := by
  induction k generalizing a with
  | zero => simp [uvec]
  | succ k ih =>
    rw [sum_cons_split]
    simp only [uvec]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← ih b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Fin.prod_univ_succ]
    congr 1

lemma transfer_total (S : Fin 3 → Fin 3 → ℝ) (k : ℕ) :
    ∑ f : Fin (k + 1) → Fin 3, ∏ i : Fin k, S (f i.castSucc) (f i.succ) = ∑ a, uvec S k a := by
  rw [sum_cons_split]
  exact Finset.sum_congr rfl fun a _ => transfer S k a

/-- The symmetrized test matrix, with `δ = ε³/2` and `η = ε²/2` in the application. -/
noncomputable def Smat (δ η : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![1, δ, 0], ![δ, 0, η], ![0, η, 0]]

lemma uvec_succ (δ η : ℝ) (k : ℕ) :
    uvec (Smat δ η) (k + 1) 0 = uvec (Smat δ η) k 0 + δ * uvec (Smat δ η) k 1 ∧
    uvec (Smat δ η) (k + 1) 1 = δ * uvec (Smat δ η) k 0 + η * uvec (Smat δ η) k 2 ∧
    uvec (Smat δ η) (k + 1) 2 = η * uvec (Smat δ η) k 1 := by
  simp [uvec, Fin.sum_univ_three, Smat]

/-- The error bounds of the transfer vectors, from `k = 3` on. -/
lemma uvec_bound (δ η E : ℝ) (hd0 : 0 ≤ δ) (hd : δ ≤ 1 / 16) (he0 : 0 ≤ η) (he : η ≤ 1 / 8)
    (hdd : δ * δ ≤ E / 4) (hdee : δ * η * η ≤ E / 8) (heee : η * η * η ≤ E / 8)
    (k : ℕ) (hk : 3 ≤ k) :
    0 ≤ uvec (Smat δ η) k 0 - (1 + δ + δ * η) ∧
      uvec (Smat δ η) k 0 - (1 + δ + δ * η) ≤ ((2 : ℝ) ^ k - 1) * E ∧
    0 ≤ uvec (Smat δ η) k 1 - δ ∧ uvec (Smat δ η) k 1 - δ ≤ ((2 : ℝ) ^ k - 1) * E ∧
    0 ≤ uvec (Smat δ η) k 2 - δ * η ∧
      uvec (Smat δ η) k 2 - δ * η ≤ ((2 : ℝ) ^ k - 1) * E := by
  have hE : 0 ≤ E := by nlinarith [mul_nonneg hd0 hd0]
  have hdde : δ * δ * η ≤ E / 32 := by nlinarith [mul_nonneg hd0 hd0]
  have hddd : δ * δ * δ ≤ E / 64 := by nlinarith [mul_nonneg hd0 hd0]
  induction k, hk using Nat.le_induction with
  | base =>
    have a1 : uvec (Smat δ η) 1 0 = 1 + δ := by simp [uvec, Fin.sum_univ_three, Smat]
    have b1 : uvec (Smat δ η) 1 1 = δ + η := by simp [uvec, Fin.sum_univ_three, Smat]
    have c1 : uvec (Smat δ η) 1 2 = η := by simp [uvec, Fin.sum_univ_three, Smat]
    obtain ⟨a2, b2, c2⟩ := uvec_succ δ η 1
    obtain ⟨a3, b3, c3⟩ := uvec_succ δ η 2
    rw [a3, b3, c3, a2, b2, c2, a1, b1, c1]
    norm_num
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  | succ k hk ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    obtain ⟨a, b, c⟩ := uvec_succ δ η k
    rw [a, b, c]
    set B := ((2 : ℝ) ^ k - 1) * E with hB
    have hB0 : 0 ≤ B := by
      rw [hB]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      exact mul_nonneg (by linarith) hE
    have hB' : ((2 : ℝ) ^ (k + 1) - 1) * E = 2 * B + E := by rw [hB]; ring
    rw [hB']
    set x := uvec (Smat δ η) k 0
    set y := uvec (Smat δ η) k 1
    set z := uvec (Smat δ η) k 2
    have hy0 : 0 ≤ y := by linarith
    have hz0 : 0 ≤ z := by nlinarith [mul_nonneg hd0 he0]
    have p1 : δ * y ≤ δ * (δ + B) := mul_le_mul_of_nonneg_left (by linarith) hd0
    have p2 : δ * x ≤ δ * (1 + δ + δ * η + B) := mul_le_mul_of_nonneg_left (by linarith) hd0
    have p3 : η * z ≤ η * (δ * η + B) := mul_le_mul_of_nonneg_left (by linarith) he0
    have p4 : η * y ≤ η * (δ + B) := mul_le_mul_of_nonneg_left (by linarith) he0
    have p5 : δ * 1 ≤ δ * x := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hd0 he0]) hd0
    have p6 : η * δ ≤ η * y := mul_le_mul_of_nonneg_left (by linarith) he0
    have q1 : δ * B ≤ B / 16 := by nlinarith
    have q2 : η * B ≤ B / 8 := by nlinarith
    have q4 : 0 ≤ η * z := mul_nonneg he0 hz0
    have q5 : 0 ≤ δ * y := mul_nonneg hd0 hy0
    have r1 : δ * (δ + B) = δ * δ + δ * B := by ring
    have r2 : δ * (1 + δ + δ * η + B) = δ + δ * δ + δ * δ * η + δ * B := by ring
    have r3 : η * (δ * η + B) = δ * η * η + η * B := by ring
    have r4 : η * (δ + B) = η * δ + η * B := by ring
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

variable {N : ℕ}

lemma prod_arcs_of (D' : OrientedGraph (Fin (N + 1))) (f : Fin (N + 1) → Fin 3)
    (M : Fin 3 → Fin 3 → ℝ) (h00 : M 0 0 = 1) (T : Finset (Fin (N + 1) × Fin (N + 1)))
    (hT : T ⊆ D'.arcs) (hf : ∀ p ∈ D'.arcs, p ∉ T → f p.1 = 0 ∧ f p.2 = 0) :
    ∏ p ∈ D'.arcs, M (f p.1) (f p.2) = ∏ p ∈ T, M (f p.1) (f p.2) :=
  (Finset.prod_subset hT (fun p hp hpT => by
    obtain ⟨h1, h2⟩ := hf p hp hpT; rw [h1, h2, h00])).symm

lemma mem_arcs' (D' : OrientedGraph (Fin (N + 1))) {a b : Fin (N + 1)} (h : D'.Adj a b) :
    (a, b) ∈ D'.arcs := (Section6Aux.mem_arcs_iff D' _).mpr h

/-- The three assignments of the lower bound. -/
lemma wsum_lower (D' : OrientedGraph (Fin (N + 1))) (M : Fin 3 → Fin 3 → ℝ)
    (hM : ∀ a b, 0 ≤ M a b) (f1 f2 f3 : Fin (N + 1) → Fin 3) (h12 : f1 ≠ f2) (h13 : f1 ≠ f3)
    (h23 : f2 ≠ f3) (v1 v2 v3 : ℝ)
    (hv1 : ∏ p ∈ D'.arcs, M (f1 p.1) (f1 p.2) = v1)
    (hv2 : ∏ p ∈ D'.arcs, M (f2 p.1) (f2 p.2) = v2)
    (hv3 : ∏ p ∈ D'.arcs, M (f3 p.1) (f3 p.2) = v3) :
    v1 + v2 + v3 ≤ ∑ f : Fin (N + 1) → Fin 3, ∏ p ∈ D'.arcs, M (f p.1) (f p.2) := by
  classical
  have hsub : ({f1, f2, f3} : Finset (Fin (N + 1) → Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun f _ _ => Finset.prod_nonneg fun p _ => hM _ _))
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23, hv1, hv2, hv3, add_assoc]

/-- Products of a symmetric matrix over the arcs of an oriented path. -/
lemma prod_arcs_path (D' : OrientedGraph (Fin (N + 1)))
    (hU : D'.underlying = SimpleGraph.pathGraph (N + 1)) (S : Fin 3 → Fin 3 → ℝ)
    (hS : ∀ a b, S a b = S b a) (f : Fin (N + 1) → Fin 3) :
    ∏ p ∈ D'.arcs, S (f p.1) (f p.2) = ∏ i : Fin N, S (f i.castSucc) (f i.succ) := by
  classical
  have hadj : ∀ a b : Fin (N + 1), D'.underlying.Adj a b ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val :=
    fun a b => by rw [hU, SimpleGraph.pathGraph_adj]
  symm
  refine Finset.prod_bij (fun i _ => if D'.Adj i.castSucc i.succ then (i.castSucc, i.succ)
    else (i.succ, i.castSucc)) ?_ ?_ ?_ ?_
  · intro i _
    split_ifs with h
    · exact mem_arcs' D' h
    · have hu : D'.underlying.Adj i.castSucc i.succ := (hadj _ _).mpr (Or.inl (by simp))
      rcases (Section1Aux.underlying_adj_iff' D' _ _).mp hu with h' | h'
      · exact absurd h' h
      · exact mem_arcs' D' h'
  · intro i _ j _ hij
    split_ifs at hij with h1 h2 h2 <;> simp only [Prod.mk.injEq] at hij
    · exact Fin.castSucc_injective _ hij.1
    · have := congrArg Fin.val hij.1; have := congrArg Fin.val hij.2; simp at *; omega
    · have := congrArg Fin.val hij.1; have := congrArg Fin.val hij.2; simp at *; omega
    · exact Fin.succ_injective _ hij.1
  · intro p hp
    have hp' := (Section6Aux.mem_arcs_iff D' p).mp hp
    rcases (hadj _ _).mp ((Section1Aux.underlying_adj_iff' D' _ _).mpr (Or.inl hp')) with e | e
    · refine ⟨⟨p.1.val, by omega⟩, Finset.mem_univ _, ?_⟩
      have h1 : (⟨p.1.val, by omega⟩ : Fin N).castSucc = p.1 := Fin.ext rfl
      have h2 : (⟨p.1.val, by omega⟩ : Fin N).succ = p.2 := Fin.ext (by simp; omega)
      rw [h1, h2]; simp only [hp', ↓reduceIte]
    · refine ⟨⟨p.2.val, by omega⟩, Finset.mem_univ _, ?_⟩
      have h1 : (⟨p.2.val, by omega⟩ : Fin N).castSucc = p.2 := Fin.ext rfl
      have h2 : (⟨p.2.val, by omega⟩ : Fin N).succ = p.1 := Fin.ext (by simp; omega)
      have hn : ¬ D'.Adj p.2 p.1 := fun h => D'.asymm _ _ h hp'
      rw [h1, h2]; simp only [hn, ↓reduceIte]
  · intro i _
    split_ifs
    · rfl
    · exact hS _ _

/-- The `S`-side sum of the test kernel. -/
lemma ssum_upper (hN : 3 ≤ N) (D' : OrientedGraph (Fin (N + 1)))
    (hU : D'.underlying = SimpleGraph.pathGraph (N + 1)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    ∑ f : Fin (N + 1) → Fin 3, ∏ p ∈ D'.arcs, Smat (ε ^ 3 / 2) (ε ^ 2 / 2) (f p.1) (f p.2) ≤
      1 + ε ^ 3 + ε ^ 5 / 2 + 3 * ((2 : ℝ) ^ N - 1) * ε ^ 6 := by
  have hS : ∀ a b, Smat (ε ^ 3 / 2) (ε ^ 2 / 2) a b = Smat (ε ^ 3 / 2) (ε ^ 2 / 2) b a := by
    intro a b; fin_cases a <;> fin_cases b <;> rfl
  simp_rw [prod_arcs_path D' hU _ hS]
  rw [transfer_total, Fin.sum_univ_three]
  have h3 : ε ^ 3 ≤ 1 / 8 := by nlinarith [pow_le_pow_left₀ hε0 hε 3]
  have h2 : ε ^ 2 ≤ 1 / 4 := by nlinarith [pow_le_pow_left₀ hε0 hε 2]
  have h7 : ε ^ 7 ≤ ε ^ 6 := pow_le_pow_of_le_one hε0 (by linarith) (by norm_num)
  obtain ⟨-, b1, -, b2, -, b3⟩ := uvec_bound (ε ^ 3 / 2) (ε ^ 2 / 2) (ε ^ 6) (by positivity)
    (by linarith) (by positivity) (by linarith) (by ring_nf; linarith)
    (by ring_nf; nlinarith [pow_nonneg hε0 7]) (by ring_nf; linarith) N hN
  have : ε ^ 3 / 2 * (ε ^ 2 / 2) = ε ^ 5 / 4 := by ring
  rw [this] at b1 b3
  linarith

lemma pathM_digraphon {M : Fin 3 → Fin 3 → ℝ} (hM : ∀ a b, M a b ∈ Icc (0 : ℝ) 1) :
    IsDigraphon (Section4Aux.stepK 3 (by norm_num) M) :=
  ⟨Section4Aux.measurable_stepK 3 _ M, fun x y => hM _ _⟩

/-- The conclusion from the OAS inequality for a `3`-step kernel. -/
lemma sum_le_of_oask (D' : OrientedGraph (Fin (N + 1))) (hD : D'.IsOASK)
    (M S : Fin 3 → Fin 3 → ℝ) (hM : ∀ a b, M a b ∈ Icc (0 : ℝ) 1)
    (hMS : ∀ a b, (M a b + M b a) / 2 = S a b) :
    ∑ f : Fin (N + 1) → Fin 3, ∏ p ∈ D'.arcs, M (f p.1) (f p.2) ≤
      ∑ f : Fin (N + 1) → Fin 3, ∏ p ∈ D'.arcs, S (f p.1) (f p.2) := by
  classical
  have h := hD _ (pathM_digraphon hM)
  have hsym : symmetrize (Section4Aux.stepK 3 (by norm_num) M) =
      Section4Aux.stepK 3 (by norm_num) S := by
    funext x y; simp only [symmetrize, Section4Aux.stepK, hMS]
  rw [hsym, Section4Aux.t_stepK, Section4Aux.t_stepK] at h
  exact le_of_mul_le_mul_left h (by positivity)

lemma pair_mem_of_vals {T : Finset (Fin (N + 1) × Fin (N + 1))} {p : Fin (N + 1) × Fin (N + 1)}
    {i j : ℕ} (hi : i < N + 1) (hj : j < N + 1) (h1 : p.1.val = i) (h2 : p.2.val = j)
    (hT : ((⟨i, hi⟩ : Fin (N + 1)), (⟨j, hj⟩ : Fin (N + 1))) ∈ T) : p ∈ T := by
  have : p = (⟨i, hi⟩, ⟨j, hj⟩) := Prod.ext (Fin.ext h1) (Fin.ext h2)
  rw [this]; exact hT

lemma adj_of_vals (D' : OrientedGraph (Fin (N + 1))) {p : Fin (N + 1) × Fin (N + 1)}
    {i j : ℕ} (hi : i < N + 1) (hj : j < N + 1) (h1 : p.1.val = i) (h2 : p.2.val = j)
    (h : D'.Adj p.1 p.2) : D'.Adj ⟨i, hi⟩ ⟨j, hj⟩ := by
  have e1 : p.1 = ⟨i, hi⟩ := Fin.ext h1
  have e2 : p.2 = ⟨j, hj⟩ := Fin.ext h2
  rw [← e1, ← e2]; exact h

lemma pow_mem_Icc {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (k : ℕ) : ε ^ k ∈ Icc (0 : ℝ) 1 :=
  ⟨pow_nonneg h0 k, pow_le_one₀ h0 h1⟩

/-- **The core of Theorem 1.10, OAS part, ≥ 3 edges** (tex l.1310-1353): for an oriented path on
`{0, …, N}` (`N ≥ 3`) whose end arcs are as given by the palindrome condition, the `3`-step
digraphon of the paper violates the OAS inequality.
True only vacuously: an oriented path with at least three edges is never OAS (`path_not_oask`);
this is the contradiction step of tex l.1302. -/
lemma path_fin_false (hN : 3 ≤ N) (D' : OrientedGraph (Fin (N + 1)))
    (hU : D'.underlying = SimpleGraph.pathGraph (N + 1)) (hD : D'.IsOASK)
    (hcase : (D'.Adj ⟨N - 2, by omega⟩ ⟨N - 1, by omega⟩ ∧ D'.Adj ⟨N - 1, by omega⟩ ⟨N, by omega⟩) ∨
      (D'.Adj ⟨0, by omega⟩ ⟨1, by omega⟩ ∧ D'.Adj ⟨N - 1, by omega⟩ ⟨N - 2, by omega⟩ ∧
        D'.Adj ⟨N - 1, by omega⟩ ⟨N, by omega⟩)) : False := by
  classical
  have hadj : ∀ p : Fin (N + 1) × Fin (N + 1), D'.Adj p.1 p.2 →
      p.1.val + 1 = p.2.val ∨ p.2.val + 1 = p.1.val := fun p h => by
    have := (Section1Aux.underlying_adj_iff' D' p.1 p.2).mpr (Or.inl h)
    rw [hU, SimpleGraph.pathGraph_adj] at this; exact this
  have hlt : ∀ p : Fin (N + 1) × Fin (N + 1), p.1.val < N + 1 ∧ p.2.val < N + 1 :=
    fun p => ⟨p.1.2, p.2.2⟩
  set ε : ℝ := 1 / (12 * 2 ^ N) with hεdef
  have hpow : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hε0 : 0 < ε := by positivity
  have hε : ε ≤ 1 / 2 := by
    rw [hεdef, div_le_iff₀ (by positivity)]; nlinarith
  have hε1 : ε ≤ 1 := by linarith
  have hupper := ssum_upper hN D' hU ε hε0.le hε
  have hlower : 1 + ε ^ 3 + ε ^ 5 ≤ ∑ f : Fin (N + 1) → Fin 3,
      ∏ p ∈ D'.arcs, Smat (ε ^ 3 / 2) (ε ^ 2 / 2) (f p.1) (f p.2) := by
    rcases hcase with ⟨e1, e2⟩ | ⟨e0, e1, e2⟩
    · -- case `(N-2, N-1), (N-1, N)`
      set M : Fin 3 → Fin 3 → ℝ := ![![1, ε ^ 3, 0], ![0, 0, ε ^ 2], ![0, 0, 0]] with hMdef
      have hM : ∀ a b, M a b ∈ Icc (0 : ℝ) 1 := by
        intro a b
        fin_cases a <;> fin_cases b <;> simp only [M] <;>
          first | exact pow_mem_Icc hε0.le hε1 _ | simp
      have hMS : ∀ a b, (M a b + M b a) / 2 = Smat (ε ^ 3 / 2) (ε ^ 2 / 2) a b := by
        intro a b; fin_cases a <;> fin_cases b <;> simp [M, Smat]
      refine le_trans ?_ (sum_le_of_oask D' hD M _ hM hMS)
      have h00 : M 0 0 = 1 := rfl
      set f2 : Fin (N + 1) → Fin 3 := fun v => if v.val = N then 1 else 0 with hf2
      set f3 : Fin (N + 1) → Fin 3 :=
        fun v => if v.val = N then 2 else if v.val = N - 1 then 1 else 0 with hf3
      refine wsum_lower D' M (fun a b => (hM a b).1) (fun _ => 0) f2 f3 ?_ ?_ ?_ 1 (ε ^ 3) (ε ^ 5)
        ?_ ?_ ?_
      · intro h; have := congrFun h ⟨N, by omega⟩; simp [hf2] at this
      · intro h; have := congrFun h ⟨N, by omega⟩; simp [hf3] at this
      · intro h; have := congrFun h ⟨N, by omega⟩; simp [hf2, hf3] at this
      · exact Finset.prod_eq_one fun _ _ => h00
      · rw [prod_arcs_of D' f2 M h00 {(⟨N - 1, by omega⟩, ⟨N, by omega⟩)}
          (Finset.singleton_subset_iff.mpr (mem_arcs' D' e2)) ?_, Finset.prod_singleton]
        · have a1 : f2 ⟨N - 1, by omega⟩ = 0 := by
            show (if N - 1 = N then (1 : Fin 3) else 0) = 0; rw [if_neg (by omega)]
          have a2 : f2 ⟨N, by omega⟩ = 1 := by
            show (if N = N then (1 : Fin 3) else 0) = 1; rw [if_pos rfl]
          rw [a1, a2]; rfl
        · intro p hp hpT
          have hp' := (Section6Aux.mem_arcs_iff D' p).mp hp
          have hab := hadj p hp'
          obtain ⟨l1, l2⟩ := hlt p
          have n1 : p.2.val ≠ N := fun h =>
            hpT (pair_mem_of_vals (i := N - 1) (j := N) (by omega) (by omega) (by omega) h (Finset.mem_singleton_self _))
          have n2 : p.1.val ≠ N := fun h =>
            D'.asymm _ _ e2 (adj_of_vals D' (i := N) (j := N - 1) (by omega) (by omega) h (by omega) hp')
          exact ⟨by show (if p.1.val = N then (1 : Fin 3) else 0) = 0; rw [if_neg n2],
            by show (if p.2.val = N then (1 : Fin 3) else 0) = 0; rw [if_neg n1]⟩
      · rw [prod_arcs_of D' f3 M h00 {(⟨N - 2, by omega⟩, ⟨N - 1, by omega⟩),
          (⟨N - 1, by omega⟩, ⟨N, by omega⟩)} ?_ ?_, Finset.prod_pair ?_]
        · have a1 : f3 ⟨N - 2, by omega⟩ = 0 := by
            show (if N - 2 = N then (2 : Fin 3) else if N - 2 = N - 1 then 1 else 0) = 0
            rw [if_neg (by omega), if_neg (by omega)]
          have a2 : f3 ⟨N - 1, by omega⟩ = 1 := by
            show (if N - 1 = N then (2 : Fin 3) else if N - 1 = N - 1 then 1 else 0) = 1
            rw [if_neg (by omega), if_pos rfl]
          have a3 : f3 ⟨N, by omega⟩ = 2 := by
            show (if N = N then (2 : Fin 3) else if N = N - 1 then 1 else 0) = 2
            rw [if_pos rfl]
          rw [a1, a2, a3]; simp only [M]; norm_num; ring
        · simp [Fin.ext_iff]; omega
        · intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact mem_arcs' D' e1
          · exact mem_arcs' D' e2
        · intro p hp hpT
          have hp' := (Section6Aux.mem_arcs_iff D' p).mp hp
          have hab := hadj p hp'
          obtain ⟨l1, l2⟩ := hlt p
          have n1 : p.2.val ≠ N := fun h =>
            hpT (pair_mem_of_vals (i := N - 1) (j := N) (by omega) (by omega) (by omega) h (by simp))
          have n2 : p.1.val ≠ N := fun h =>
            D'.asymm _ _ e2 (adj_of_vals D' (i := N) (j := N - 1) (by omega) (by omega) h (by omega) hp')
          have n3 : p.2.val ≠ N - 1 := fun h =>
            hpT (pair_mem_of_vals (i := N - 2) (j := N - 1) (by omega) (by omega) (by omega) h (by simp))
          have n4 : p.1.val ≠ N - 1 := fun h =>
            D'.asymm _ _ e1 (adj_of_vals D' (i := N - 1) (j := N - 2) (by omega) (by omega) h (by omega) hp')
          exact ⟨by
              show (if p.1.val = N then (2 : Fin 3) else if p.1.val = N - 1 then 1 else 0) = 0
              rw [if_neg n2, if_neg n4],
            by
              show (if p.2.val = N then (2 : Fin 3) else if p.2.val = N - 1 then 1 else 0) = 0
              rw [if_neg n1, if_neg n3]⟩
    · -- case `(0, 1), (N-1, N-2), (N-1, N)`
      set M : Fin 3 → Fin 3 → ℝ := ![![1, 0, 0], ![ε ^ 3, 0, ε ^ 2], ![0, 0, 0]] with hMdef
      have hM : ∀ a b, M a b ∈ Icc (0 : ℝ) 1 := by
        intro a b
        fin_cases a <;> fin_cases b <;> simp only [M] <;>
          first | exact pow_mem_Icc hε0.le hε1 _ | simp
      have hMS : ∀ a b, (M a b + M b a) / 2 = Smat (ε ^ 3 / 2) (ε ^ 2 / 2) a b := by
        intro a b; fin_cases a <;> fin_cases b <;> simp [M, Smat]
      refine le_trans ?_ (sum_le_of_oask D' hD M _ hM hMS)
      have h00 : M 0 0 = 1 := rfl
      set f2 : Fin (N + 1) → Fin 3 := fun v => if v.val = 0 then 1 else 0 with hf2
      set f3 : Fin (N + 1) → Fin 3 :=
        fun v => if v.val = N then 2 else if v.val = N - 1 then 1 else 0 with hf3
      refine wsum_lower D' M (fun a b => (hM a b).1) (fun _ => 0) f2 f3 ?_ ?_ ?_ 1 (ε ^ 3) (ε ^ 5)
        ?_ ?_ ?_
      · intro h; have := congrFun h ⟨0, by omega⟩; simp [hf2] at this
      · intro h; have := congrFun h ⟨N, by omega⟩; simp [hf3] at this
      · intro h
        have h' := congrFun h ⟨N, by omega⟩
        have hN0 : N ≠ 0 := by omega
        simp [hf2, hf3, hN0] at h'
      · exact Finset.prod_eq_one fun _ _ => h00
      · rw [prod_arcs_of D' f2 M h00 {(⟨0, by omega⟩, ⟨1, by omega⟩)}
          (Finset.singleton_subset_iff.mpr (mem_arcs' D' e0)) ?_, Finset.prod_singleton]
        · have a1 : f2 ⟨0, by omega⟩ = 1 := by
            show (if 0 = 0 then (1 : Fin 3) else 0) = 1; rw [if_pos rfl]
          have a2 : f2 ⟨1, by omega⟩ = 0 := by
            show (if 1 = 0 then (1 : Fin 3) else 0) = 0; rw [if_neg (by omega)]
          rw [a1, a2]; rfl
        · intro p hp hpT
          have hp' := (Section6Aux.mem_arcs_iff D' p).mp hp
          have hab := hadj p hp'
          obtain ⟨l1, l2⟩ := hlt p
          have n1 : p.1.val ≠ 0 := fun h =>
            hpT (pair_mem_of_vals (i := 0) (j := 1) (by omega) (by omega) h (by omega) (Finset.mem_singleton_self _))
          have n2 : p.2.val ≠ 0 := fun h =>
            D'.asymm _ _ e0 (adj_of_vals D' (i := 1) (j := 0) (by omega) (by omega) (by omega) h hp')
          exact ⟨by show (if p.1.val = 0 then (1 : Fin 3) else 0) = 0; rw [if_neg n1],
            by show (if p.2.val = 0 then (1 : Fin 3) else 0) = 0; rw [if_neg n2]⟩
      · rw [prod_arcs_of D' f3 M h00 {(⟨N - 1, by omega⟩, ⟨N - 2, by omega⟩),
          (⟨N - 1, by omega⟩, ⟨N, by omega⟩)} ?_ ?_, Finset.prod_pair ?_]
        · have a1 : f3 ⟨N - 2, by omega⟩ = 0 := by
            show (if N - 2 = N then (2 : Fin 3) else if N - 2 = N - 1 then 1 else 0) = 0
            rw [if_neg (by omega), if_neg (by omega)]
          have a2 : f3 ⟨N - 1, by omega⟩ = 1 := by
            show (if N - 1 = N then (2 : Fin 3) else if N - 1 = N - 1 then 1 else 0) = 1
            rw [if_neg (by omega), if_pos rfl]
          have a3 : f3 ⟨N, by omega⟩ = 2 := by
            show (if N = N then (2 : Fin 3) else if N = N - 1 then 1 else 0) = 2
            rw [if_pos rfl]
          rw [a1, a2, a3]; simp only [M]; norm_num; ring
        · simp [Fin.ext_iff]; omega
        · intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact mem_arcs' D' e1
          · exact mem_arcs' D' e2
        · intro p hp hpT
          have hp' := (Section6Aux.mem_arcs_iff D' p).mp hp
          have hab := hadj p hp'
          obtain ⟨l1, l2⟩ := hlt p
          have n1 : p.2.val ≠ N := fun h =>
            hpT (pair_mem_of_vals (i := N - 1) (j := N) (by omega) (by omega) (by omega) h (by simp))
          have n2 : p.1.val ≠ N := fun h =>
            D'.asymm _ _ e2 (adj_of_vals D' (i := N) (j := N - 1) (by omega) (by omega) h (by omega) hp')
          have n3 : p.1.val ≠ N - 1 := fun h =>
            hpT (pair_mem_of_vals (i := N - 1) (j := N - 2) (by omega) (by omega) h (by omega) (by simp))
          have n4 : p.2.val ≠ N - 1 := fun h =>
            D'.asymm _ _ e1 (adj_of_vals D' (i := N - 2) (j := N - 1) (by omega) (by omega) (by omega) h hp')
          exact ⟨by
              show (if p.1.val = N then (2 : Fin 3) else if p.1.val = N - 1 then 1 else 0) = 0
              rw [if_neg n2, if_neg n3],
            by
              show (if p.2.val = N then (2 : Fin 3) else if p.2.val = N - 1 then 1 else 0) = 0
              rw [if_neg n1, if_neg n4]⟩
  have key : ε ^ 5 / 2 ≤ 3 * ((2 : ℝ) ^ N - 1) * ε ^ 6 := by linarith
  have h5 : 0 < ε ^ 5 := by positivity
  have : ε ^ 6 = ε ^ 5 * ε := by ring
  rw [this] at key
  have h3 : 3 * ((2 : ℝ) ^ N - 1) * ε < 1 / 2 := by
    have : 3 * (2 : ℝ) ^ N * ε = 1 / 4 := by rw [hεdef]; field_simp; ring
    nlinarith
  nlinarith

lemma t_transpose {V : Type*} [Fintype V] (D : OrientedGraph V) (U : I → I → ℝ) :
    t D.transpose U = t D (kTranspose U) := by
  classical
  unfold t tDir
  congr 1; funext x
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Section6Aux.mem_arcs_iff] at hp ⊢; exact hp
  · intro p hp
    simp only [Finset.mem_coe, Section6Aux.mem_arcs_iff] at hp ⊢; exact hp
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

lemma oask_transpose {V : Type*} [Fintype V] {D : OrientedGraph V} (hD : D.IsOASK) :
    D.transpose.IsOASK := by
  intro U hU
  have hUT : IsDigraphon (kTranspose U) :=
    ⟨hU.1.comp measurable_swap, fun x y => hU.2 y x⟩
  have h1 : symmetrize (kTranspose U) = symmetrize U := by
    funext x y; simp only [symmetrize, kTranspose]; ring
  have h2 : kTranspose (symmetrize U) = symmetrize U := by
    funext x y; simp only [symmetrize, kTranspose]; ring
  rw [t_transpose, t_transpose, h2, ← h1]
  exact hD _ hUT

lemma transpose_underlying {V : Type*} (D : OrientedGraph V) :
    D.transpose.underlying = D.underlying := by
  ext a b
  rw [Section1Aux.underlying_adj_iff', Section1Aux.underlying_adj_iff']
  exact or_comm

/-- Automorphisms of a path fix or reverse its first three vertices. -/
lemma path_aut (hN : 2 ≤ N) (ψ : SimpleGraph.pathGraph (N + 1) ≃g SimpleGraph.pathGraph (N + 1)) :
    ((ψ ⟨0, by omega⟩).val = 0 ∧ (ψ ⟨1, by omega⟩).val = 1 ∧ (ψ ⟨2, by omega⟩).val = 2) ∨
    ((ψ ⟨0, by omega⟩).val = N ∧ (ψ ⟨1, by omega⟩).val = N - 1 ∧
      (ψ ⟨2, by omega⟩).val = N - 2) := by
  classical
  have hadj : ∀ a b : Fin (N + 1), (SimpleGraph.pathGraph (N + 1)).Adj a b ↔
      a.val + 1 = b.val ∨ b.val + 1 = a.val := fun a b => SimpleGraph.pathGraph_adj
  have h01 : (SimpleGraph.pathGraph (N + 1)).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    rw [hadj]; left; rfl
  have h12 : (SimpleGraph.pathGraph (N + 1)).Adj ⟨1, by omega⟩ ⟨2, by omega⟩ := by
    rw [hadj]; left; rfl
  have a01 := (hadj _ _).mp (ψ.map_adj_iff.mpr h01)
  have a12 := (hadj _ _).mp (ψ.map_adj_iff.mpr h12)
  have hne : (ψ ⟨2, by omega⟩).val ≠ (ψ ⟨0, by omega⟩).val := by
    intro h
    have := ψ.injective (Fin.ext h)
    simp [Fin.ext_iff] at this
  -- the image of the end vertex `0` is an end vertex
  have hend : (ψ ⟨0, by omega⟩).val = 0 ∨ (ψ ⟨0, by omega⟩).val = N := by
    by_contra hc
    push_neg at hc
    set w := ψ ⟨0, by omega⟩
    have hdeg : (SimpleGraph.pathGraph (N + 1)).degree w = 1 := by
      rw [ψ.degree_eq]; exact pathGraph_degree_zero (N + 1) (by omega)
    have h2 : 2 ≤ (SimpleGraph.pathGraph (N + 1)).degree w := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      have hsub : ({⟨w.val - 1, by omega⟩, ⟨w.val + 1, by omega⟩} : Finset (Fin (N + 1))) ⊆
          (SimpleGraph.pathGraph (N + 1)).neighborFinset w := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rw [SimpleGraph.mem_neighborFinset, hadj]
        rcases hb with rfl | rfl
        · right; simp; omega
        · left; rfl
      have := Finset.card_le_card hsub
      rw [Finset.card_pair (by simp only [ne_eq, Fin.ext_iff]; omega)] at this
      exact this
    omega
  have l0 := (ψ ⟨0, by omega⟩).2
  have l1 := (ψ ⟨1, by omega⟩).2
  have l2 := (ψ ⟨2, by omega⟩).2
  rcases hend with h | h
  · left; refine ⟨h, by omega, by omega⟩
  · right; refine ⟨h, by omega, by omega⟩

/-- From Lemma 4.3 (the palindrome condition at the ends) to the hypothesis of
`path_fin_false`.
True only vacuously: an oriented path with at least three edges is never OAS (`path_not_oask`);
this is the contradiction step of tex l.1302. -/
lemma path_fin_false' (hN : 3 ≤ N) (D' : OrientedGraph (Fin (N + 1)))
    (hU : D'.underlying = SimpleGraph.pathGraph (N + 1)) (hD : D'.IsOASK)
    (P' : ∀ u w, D'.Adj u w →
      ∃ ψ : SimpleGraph.pathGraph (N + 1) ≃g SimpleGraph.pathGraph (N + 1), D'.Adj (ψ w) (ψ u))
    (h01 : D'.Adj ⟨0, by omega⟩ ⟨1, by omega⟩) : False := by
  have hfin : ∀ (a : Fin (N + 1)) (k : ℕ) (hk : k < N + 1), a.val = k → a = ⟨k, hk⟩ :=
    fun a k hk h => Fin.ext h
  -- the last arc
  obtain ⟨ψ, hψ⟩ := P' _ _ h01
  have e2 : D'.Adj ⟨N - 1, by omega⟩ ⟨N, by omega⟩ := by
    rcases path_aut (by omega) ψ with ⟨a0, a1, -⟩ | ⟨a0, a1, -⟩
    · rw [hfin _ _ (by omega) a0, hfin _ _ (by omega) a1] at hψ
      exact absurd hψ (D'.asymm _ _ h01)
    · rwa [hfin _ _ (by omega) a0, hfin _ _ (by omega) a1] at hψ
  have hu12 : D'.underlying.Adj ⟨1, by omega⟩ ⟨2, by omega⟩ := by
    rw [hU, SimpleGraph.pathGraph_adj]; left; rfl
  by_cases h12 : D'.Adj ⟨1, by omega⟩ ⟨2, by omega⟩
  · obtain ⟨ψ', hψ'⟩ := P' _ _ h12
    rcases path_aut (by omega) ψ' with ⟨-, a1, a2⟩ | ⟨-, a1, a2⟩
    · rw [hfin _ _ (by omega) a1, hfin _ _ (by omega) a2] at hψ'
      exact D'.asymm _ _ h12 hψ'
    · rw [hfin _ _ (by omega) a1, hfin _ _ (by omega) a2] at hψ'
      exact path_fin_false hN D' hU hD (Or.inl ⟨hψ', e2⟩)
  · have h21 : D'.Adj ⟨2, by omega⟩ ⟨1, by omega⟩ := by
      rcases (Section1Aux.underlying_adj_iff' D' _ _).mp hu12 with h | h
      · exact absurd h h12
      · exact h
    obtain ⟨ψ', hψ'⟩ := P' _ _ h21
    rcases path_aut (by omega) ψ' with ⟨-, a1, a2⟩ | ⟨-, a1, a2⟩
    · rw [hfin _ _ (by omega) a1, hfin _ _ (by omega) a2] at hψ'
      exact h12 hψ'
    · rw [hfin _ _ (by omega) a1, hfin _ _ (by omega) a2] at hψ'
      exact path_fin_false hN D' hU hD (Or.inr ⟨h01, hψ', e2⟩)

end PathOAS

/-! ## Oriented paths -/

section Paths

variable {V W : Type*} [Fintype V] [Fintype W]

lemma inDeg_iso {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D') (c : V) :
    D'.inDeg (g.toEquiv c) = D.inDeg c := by
  classical
  rw [Section1Aux.inDeg_eq, Section1Aux.inDeg_eq]
  refine Finset.card_nbij' (fun u => g.toEquiv.symm u) (fun u => g.toEquiv u) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    rw [← g.map_adj_iff]; simpa using hu
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    exact (g.map_adj_iff _ _).mpr hu
  · intro u _; simp
  · intro u _; simp

lemma outDeg_iso {D : OrientedGraph V} {D' : OrientedGraph W} (g : D.Iso D') (c : V) :
    D'.outDeg (g.toEquiv c) = D.outDeg c := by
  classical
  rw [Section1Aux.outDeg_eq, Section1Aux.outDeg_eq]
  refine Finset.card_nbij' (fun u => g.toEquiv.symm u) (fun u => g.toEquiv u) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    rw [← g.map_adj_iff]; simpa using hu
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    exact (g.map_adj_iff _ _).mpr hu
  · intro u _; simp
  · intro u _; simp

lemma path_numArcs (D : OrientedGraph V) (hpath : D.IsOrientedPath) :
    D.numArcs + 1 = Fintype.card V := by
  classical
  obtain ⟨⟨φ⟩, h2⟩ := hpath
  rw [← Section1Aux.card_edgeFinset_eq D.underlying D rfl]
  have ht := (SimpleGraph.isTree_pathGraph.mpr (by omega : Fintype.card V ≠ 0)).card_edgeFinset
  rw [Fintype.card_fin] at ht
  rw [← ht]
  congr 1
  convert φ.card_edgeFinset_eq

/-- The orientation of the path on `Fin n` in which `o i` says the edge `{i, i+1}` points
`i → i+1`. -/
def pathOr (n : ℕ) (o : Fin n → Bool) : OrientedGraph (Fin n) where
  Adj a b := (a.val + 1 = b.val ∧ o a = true) ∨ (b.val + 1 = a.val ∧ o b = false)
  irrefl a := by
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
  asymm a b h h' := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      first | omega | simp_all

instance (n : ℕ) (o : Fin n → Bool) : DecidableRel (pathOr n o).Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val + 1 = b.val ∧ o a = true) ∨ (b.val + 1 = a.val ∧ o b = false)))

instance : DecidableRel dirPath3.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3))))

/-- An orientation of the path on `Fin n` is some `pathOr n o`. -/
noncomputable def isoPathOr {n : ℕ} (D' : OrientedGraph (Fin n))
    (hU : D'.underlying = SimpleGraph.pathGraph n) :
    D'.Iso (pathOr n (fun i => @decide (∃ j : Fin n, i.val + 1 = j.val ∧ D'.Adj i j)
      (Classical.propDecidable _))) where
  toEquiv := Equiv.refl _
  map_adj_iff a b := by
    classical
    have hadj : ∀ a b : Fin n, D'.underlying.Adj a b ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val := by
      intro a b; rw [hU, SimpleGraph.pathGraph_adj]
    simp only [Equiv.refl_apply]
    show (a.val + 1 = b.val ∧ _ = true) ∨ (b.val + 1 = a.val ∧ _ = false) ↔ D'.Adj a b
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_exists, not_and]
    constructor
    · rintro (⟨h, j, hj, hj'⟩ | ⟨h, h'⟩)
      · have : j = b := Fin.ext (by omega)
        exact this ▸ hj'
      · have hu := (hadj a b).mpr (Or.inr h)
        rcases (Section1Aux.underlying_adj_iff' D' a b).mp hu with h'' | h''
        · exact h''
        · exact absurd h'' (h' a h)
    · intro h
      rcases (hadj a b).mp ((Section1Aux.underlying_adj_iff' D' a b).mpr (Or.inl h)) with e | e
      · exact Or.inl ⟨e, b, e, h⟩
      · refine Or.inr ⟨e, fun j hj hbj => ?_⟩
        have : j = a := Fin.ext (by omega)
        subst this
        exact D'.asymm _ _ h hbj

lemma star_of_path (D : OrientedGraph V) {n : ℕ} (φ : D.underlying ≃g SimpleGraph.pathGraph n)
    (c0 : Fin n)
    (hkey : ∀ a b : Fin n, (SimpleGraph.pathGraph n).Adj a b ↔ a ≠ b ∧ (a = c0 ∨ b = c0))
    (h1 : 1 ≤ D.numArcs) : D.IsOrientedStar (φ.symm c0) := by
  have e : ∀ u, (u = φ.symm c0 ↔ φ u = c0) := fun u =>
    ⟨fun h => h ▸ φ.apply_symm_apply c0, fun h => h ▸ (φ.symm_apply_apply u).symm⟩
  refine ⟨fun u v => ?_, h1⟩
  rw [← φ.map_adj_iff, hkey, e, e, φ.injective.ne_iff]

def dihedral3 : List (Fin 3 → Fin 3) := [fun i => i, fun i => 2 - i]

lemma dihedral3_inj : ∀ f ∈ dihedral3, Function.Injective f := by decide +kernel

lemma path3_deg : ∀ o : Fin 3 → Bool,
    (Finset.univ.filter fun u => (pathOr 3 o).Adj u 1).card =
      (Finset.univ.filter fun v => (pathOr 3 o).Adj 1 v).card →
    ∃ f ∈ dihedral3, ∀ a b, dirPath3.Adj (f a) (f b) ↔ (pathOr 3 o).Adj a b := by
  decide +kernel

lemma dirPath3_oask : dirPath3.IsOASK := by
  classical
  refine fun U hU => Section1Aux.t_center_le_symm dirPath3 1 (by decide) ?_ U hU
  rw [Section1Aux.inDeg_eq, Section1Aux.outDeg_eq]
  decide

lemma path3_iso (D : OrientedGraph V) (φ : D.underlying ≃g SimpleGraph.pathGraph 3)
    (hdeg : D.inDeg (φ.symm 1) = D.outDeg (φ.symm 1)) : Nonempty (D.Iso dirPath3) := by
  classical
  set D' := transp D φ.toEquiv with hD'
  have hU : D'.underlying = SimpleGraph.pathGraph 3 := transp_underlying_eq D φ
  set o := (fun i : Fin 3 => @decide (∃ j : Fin 3, i.val + 1 = j.val ∧ D'.Adj i j)
      (Classical.propDecidable _)) with ho
  have h0 := inDeg_iso (transpIso D φ.toEquiv) (φ.symm 1)
  have h0' := outDeg_iso (transpIso D φ.toEquiv) (φ.symm 1)
  have hc : (transpIso D φ.toEquiv).toEquiv (φ.symm 1) = 1 := by
    show φ (φ.symm 1) = 1; simp
  rw [hc] at h0 h0'
  have h1 := inDeg_iso (isoPathOr D' hU) 1
  have h1' := outDeg_iso (isoPathOr D' hU) 1
  have hdeg' : (pathOr 3 o).inDeg 1 = (pathOr 3 o).outDeg 1 := by
    have e1 : (isoPathOr D' hU).toEquiv 1 = 1 := rfl
    rw [e1] at h1 h1'
    rw [h1, h1', h0, h0', hdeg]
  rw [Section1Aux.inDeg_eq, Section1Aux.outDeg_eq] at hdeg'
  obtain ⟨f, hfL, hf⟩ := path3_deg o (by convert hdeg')
  have hfb : Function.Bijective f := Finite.injective_iff_bijective.mp (dihedral3_inj f hfL)
  let g2 : (pathOr 3 o).Iso dirPath3 :=
    { toEquiv := Equiv.ofBijective f hfb
      map_adj_iff := fun a b => hf a b }
  exact ⟨isoTrans (isoTrans (transpIso D φ.toEquiv) (isoPathOr D' hU)) g2⟩

end Paths

/-- **Theorem 1.10 for paths with at least three edges, OS part.** -/
lemma path_not_osk {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hpath : D.IsOrientedPath) (h4 : 4 ≤ Fintype.card V) : ¬ D.IsOSK := by
  classical
  intro hD
  have hnum := path_numArcs D hpath
  obtain ⟨⟨φ⟩, h2⟩ := hpath
  have hconn : D.IsConnected :=
    φ.connected_iff.mpr (SimpleGraph.connected_pathGraph.mpr (by omega))
  have he : 1 ≤ D.numArcs := by omega
  obtain ⟨-, -, s, hbip, hwn⟩ := (Section1Aux.osk_char hA1 D hconn he).mp hD
  have hdeg : ∀ v, D.underlying.degree v = (SimpleGraph.pathGraph _).degree (φ v) := fun v => by
    rw [φ.degree_eq v]
  have hpos : ∀ v, 1 ≤ D.underlying.degree v := fun v => by
    rw [hdeg]; exact pathGraph_degree_pos _ (by omega) _
  set a0 : Fin (Fintype.card V) := ⟨0, by omega⟩
  set a1 : Fin (Fintype.card V) := ⟨1, by omega⟩
  set a2 : Fin (Fintype.card V) := ⟨2, by omega⟩
  have h01 : D.underlying.Adj (φ.symm a0) (φ.symm a1) :=
    φ.symm.map_adj_iff.mpr (by simp [SimpleGraph.pathGraph_adj, a0, a1])
  have h12 : D.underlying.Adj (φ.symm a1) (φ.symm a2) :=
    φ.symm.map_adj_iff.mpr (by simp [SimpleGraph.pathGraph_adj, a1, a2])
  have hs : s (φ.symm a0) ↔ s (φ.symm a2) := by
    have e1 := hbip _ _ h01; have e2 := hbip _ _ h12; tauto
  have := degree_eq_of_wnGraph D.underlying s hbip hwn hpos _ _ hs
  rw [hdeg, hdeg, RelIso.apply_symm_apply, RelIso.apply_symm_apply] at this
  have d0 : (SimpleGraph.pathGraph _).degree a0 = 1 := pathGraph_degree_zero (Fintype.card V) (by omega)
  have d2 : (SimpleGraph.pathGraph _).degree a2 = 2 := pathGraph_degree_two (Fintype.card V) h4
  have : (SimpleGraph.pathGraph _).degree a0 = (SimpleGraph.pathGraph _).degree a2 := by
    convert this using 1
  omega

/-- **Theorem 1.10 for paths with at least three edges, OAS part** (tex l.1302-1353). -/
lemma path_not_oask {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hpath : D.IsOrientedPath) (h4 : 4 ≤ Fintype.card V) : ¬ D.IsOASK := by
  classical
  intro hD
  obtain ⟨⟨φ0⟩, h2⟩ := hpath
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card V = N + 1 := ⟨Fintype.card V - 1, by omega⟩
  have hN3 : 3 ≤ N := by omega
  have φ : D.underlying ≃g SimpleGraph.pathGraph (N + 1) := hN ▸ φ0
  -- no isolated vertices
  have hiso : ∀ v, ∃ u, D.underlying.Adj v u := by
    intro v
    have h1 := pathGraph_degree_pos (N + 1) (by omega) (φ v)
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, SimpleGraph.degree_pos_iff_exists_adj] at h1
    obtain ⟨b, hb⟩ := h1
    refine ⟨φ.symm b, ?_⟩
    rw [← φ.map_adj_iff, RelIso.apply_symm_apply]
    exact hb
  obtain ⟨f, hf⟩ := lemma_4_3 hA1 D (Or.inr hD) hiso
  have PD : ∀ a b, D.Adj a b → ∃ g : D.underlying ≃g D.underlying, D.Adj (g b) (g a) := by
    intro a b hab
    obtain ⟨g, hg1, hg2⟩ := hf ⟨(a, b), (Section6Aux.mem_arcs_iff D _).mpr hab⟩
    refine ⟨g, ?_⟩
    simp only at hg1 hg2
    rw [hg1, hg2]
    exact (Section6Aux.mem_arcs_iff D _).mp (f _).2
  set D' := transp D φ.toEquiv with hD'def
  have hU : D'.underlying = SimpleGraph.pathGraph (N + 1) := transp_underlying_eq D φ
  have hD' : D'.IsOASK := (isOASK_iso (transpIso D φ.toEquiv)).mp hD
  have P' : ∀ u w, D'.Adj u w →
      ∃ ψ : SimpleGraph.pathGraph (N + 1) ≃g SimpleGraph.pathGraph (N + 1),
        D'.Adj (ψ w) (ψ u) := by
    intro u w h
    obtain ⟨g, hg⟩ := PD _ _ h
    refine ⟨(φ.symm.trans g).trans φ, ?_⟩
    have key : ∀ y, φ.toEquiv.symm (φ y) = y := fun y => φ.toEquiv.symm_apply_apply y
    show D.Adj (φ.toEquiv.symm (φ (g (φ.toEquiv.symm w))))
      (φ.toEquiv.symm (φ (g (φ.toEquiv.symm u))))
    rw [key, key]
    exact hg
  by_cases h01 : D'.Adj ⟨0, by omega⟩ ⟨1, by omega⟩
  · exact path_fin_false' hN3 D' hU hD' P' h01
  · have hu01 : D'.underlying.Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      rw [hU, SimpleGraph.pathGraph_adj]; left; rfl
    have h10 : D'.transpose.Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      rcases (Section1Aux.underlying_adj_iff' D' _ _).mp hu01 with h | h
      · exact absurd h h01
      · exact h
    refine path_fin_false' hN3 D'.transpose (by rw [transpose_underlying, hU])
      (oask_transpose hD') (fun u w h => ?_) h10
    obtain ⟨ψ, hψ⟩ := P' w u h
    exact ⟨ψ, hψ⟩

lemma path_kernel {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hpath : D.IsOrientedPath) :
    (D.numArcs = 1 → D.IsOSK ∧ D.IsOASK) ∧
    (2 ≤ D.numArcs → ¬ D.IsOSK ∧ (D.IsOASK ↔ Nonempty (D.Iso dirPath3))) := by
  classical
  have hnum := path_numArcs D hpath
  obtain ⟨⟨φ0⟩, hV2⟩ := hpath
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · have hn : Fintype.card V = 2 := by omega
    have φ : D.underlying ≃g SimpleGraph.pathGraph 2 := hn ▸ φ0
    have hstar := star_of_path D φ 0 (by decide) (by omega)
    exact (Section1Aux.star_kernel hA1 D _ hstar).1 h1
  · by_cases h3 : Fintype.card V = 3
    · have φ : D.underlying ≃g SimpleGraph.pathGraph 3 := h3 ▸ φ0
      have hstar := star_of_path D φ 1 (by decide) (by omega)
      obtain ⟨hnot, hiff⟩ := (Section1Aux.star_kernel hA1 D _ hstar).2 h2
      exact ⟨hnot, fun hD => path3_iso D φ (hiff.mp hD),
        fun ⟨g⟩ => (isOASK_iso g).mpr dirPath3_oask⟩
    · have h4 : 4 ≤ Fintype.card V := by omega
      refine ⟨path_not_osk hA1 D ⟨⟨φ0⟩, hV2⟩ h4,
        fun hD => absurd hD (path_not_oask hA1 D ⟨⟨φ0⟩, hV2⟩ h4), ?_⟩
      rintro ⟨g⟩
      have := Fintype.card_congr g.toEquiv
      simp at this
      omega

end S1Families

end NieWeiOrientedSidorenko
