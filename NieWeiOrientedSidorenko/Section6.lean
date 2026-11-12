import NieWeiOrientedSidorenko.Section4

/-!
# Section 6: stars, paths and cycles

Lemma 6.1 (the girth condition for OAS directed graphs), in the digraphon language of Section 2.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace NieWeiOrientedSidorenko

/-! ## Auxiliary material for Lemma 6.1 (the Fourier expansion around `1/2`) -/

namespace Section6Aux

set_option linter.unusedSectionVars false

open OrientedGraph

lemma integral_exp_int (n : ℤ) :
    ∫ x : I, Complex.exp ((2 * Real.pi * Complex.I * n) * ((x : ℝ) : ℂ)) =
      if n = 0 then 1 else 0 := by
  rw [unitInterval.volume_def,
    integral_subtype_comap measurableSet_Icc
      (fun x : ℝ => Complex.exp ((2 * Real.pi * Complex.I * n) * (x : ℂ))),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hn
  · subst hn; simp
  · have hc : (2 * Real.pi * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, Complex.I_ne_zero, this]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * Real.pi * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨n, by push_cast; ring⟩
    rw [this]; simp

lemma integrable_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => hC _ (mem_image_of_mem _ (mem_univ x)))


variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The arcs of `D` as a type. -/
abbrev Arc (D : OrientedGraph V) := {p // p ∈ D.arcs}

/-- Net flow of an arc labelling at a vertex. -/
noncomputable def flow (D : OrientedGraph V) (ζ : Arc D → ℤ) (v : V) : ℤ :=
  ∑ p, ζ p * ((if p.1.1 = v then 1 else 0) - (if p.1.2 = v then 1 else 0))

/-- Size of the support of an arc labelling. -/
noncomputable def suppCard {D : OrientedGraph V} (ζ : Arc D → ℤ) : ℕ :=
  (Finset.univ.filter fun p => ζ p ≠ 0).card

/-- The admissible labels. -/
def signs : Finset ℤ := {-1, 0, 1}

/-- The test kernel `1/2 + c cos(2π(x-y) + φ)`. -/
noncomputable def testK (c φ : ℝ) : I → I → ℝ :=
  fun x y => 1 / 2 + c * Real.cos (2 * Real.pi * ((x : ℝ) - y) + φ)

/-- One Fourier term. -/
noncomputable def termC (c φ : ℝ) (s : ℤ) (a b : ℝ) : ℂ :=
  (1 / 2) * (c : ℂ) ^ (if s = 0 then 0 else 1) *
    Complex.exp (((s : ℝ) * (φ + 2 * Real.pi * (a - b)) : ℝ) * Complex.I)

lemma testK_eq_sum (c φ : ℝ) (x y : I) :
    ((testK c φ x y : ℝ) : ℂ) = ∑ s ∈ signs, termC c φ s x y := by
  simp only [testK, signs, termC]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have h2 := Complex.two_cos ((2 * Real.pi * ((x : ℝ) - y) + φ : ℝ) : ℂ)
  push_cast at h2 ⊢
  have e1 : Complex.exp (1 * ((φ : ℂ) + 2 * Real.pi * (((x : ℝ) : ℂ) - ((y : ℝ) : ℂ))) * Complex.I) =
      Complex.exp ((2 * Real.pi * (((x : ℝ) : ℂ) - ((y : ℝ) : ℂ)) + φ) * Complex.I) := by
    congr 1; ring
  have e2 : Complex.exp (-1 * ((φ : ℂ) + 2 * Real.pi * (((x : ℝ) : ℂ) - ((y : ℝ) : ℂ))) * Complex.I) =
      Complex.exp (-(2 * Real.pi * (((x : ℝ) : ℂ) - ((y : ℝ) : ℂ)) + φ) * Complex.I) := by
    congr 1; ring
  have e0 : Complex.exp (0 * ((φ : ℂ) + 2 * Real.pi * (((x : ℝ) : ℂ) - ((y : ℝ) : ℂ))) * Complex.I) =
      1 := by simp
  linear_combination (c / 2 : ℂ) * h2 - (c / 2 : ℂ) * e1 - (c / 2 : ℂ) * e2 - (1 / 2 : ℂ) * e0

lemma sum_flow_mul (D : OrientedGraph V) (ζ : Arc D → ℤ) (x : V → ℝ) :
    ∑ v, (flow D ζ v : ℝ) * x v = ∑ p : Arc D, (ζ p : ℝ) * (x p.1.1 - x p.1.2) := by
  simp only [flow]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
  simp [ite_mul]

lemma prod_termC (D : OrientedGraph V) (c φ : ℝ) (ζ : Arc D → ℤ) (x : V → I) :
    ∏ p : Arc D, termC c φ (ζ p) (x p.1.1) (x p.1.2) =
      (1 / 2) ^ D.numArcs * (c : ℂ) ^ suppCard ζ *
        Complex.exp (((φ * ∑ p, (ζ p : ℝ)) : ℝ) * Complex.I) *
        ∏ v, Complex.exp ((2 * Real.pi * Complex.I * (flow D ζ v)) * (((x v : I) : ℝ) : ℂ)) := by
  simp only [termC, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, Finset.prod_pow_eq_pow_sum]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  have hk : (∑ p : Arc D, if ζ p = 0 then 0 else 1) = suppCard ζ := by
    simp only [suppCard, Finset.card_filter]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp_all
  rw [hk, mul_assoc ((1 / 2 : ℂ) ^ _ * _), ← Complex.exp_add]
  congr 1
  have h := sum_flow_mul D ζ (fun v => ((x v : I) : ℝ))
  have hc := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at hc ⊢
  have e : ∑ v, 2 * (Real.pi : ℂ) * Complex.I * (flow D ζ v : ℂ) * (((x v : I) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * ∑ v, (flow D ζ v : ℂ) * (((x v : I) : ℝ) : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  rw [e, hc, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The Fourier expansion of `t(D, testK c φ)`: a sum over labellings `E(D) → {-1, 0, 1}` that are
circulations. -/
lemma t_testK (D : OrientedGraph V) (c φ : ℝ) :
    t D (testK c φ) = ∑ ζ ∈ Fintype.piFinset (fun _ : Arc D => signs),
      (if ∀ v, flow D ζ v = 0 then
        (1 / 2) ^ D.numArcs * c ^ suppCard ζ * Real.cos (φ * ∑ p, (ζ p : ℝ)) else 0) := by
  have key : ((t D (testK c φ) : ℝ) : ℂ) = ∑ ζ ∈ Fintype.piFinset (fun _ : Arc D => signs),
      (if ∀ v, flow D ζ v = 0 then
        (((1 / 2) ^ D.numArcs * c ^ suppCard ζ : ℝ) : ℂ) *
          Complex.exp (((φ * ∑ p, (ζ p : ℝ)) : ℝ) * Complex.I) else 0) := by
    simp only [t, tDir]
    rw [← integral_complex_ofReal]
    have hpt : ∀ x : V → I, (((∏ p ∈ D.arcs, testK c φ (x p.1) (x p.2) : ℝ)) : ℂ) =
        ∑ ζ ∈ Fintype.piFinset (fun _ : Arc D => signs),
          (((1 / 2) ^ D.numArcs * c ^ suppCard ζ : ℝ) : ℂ) *
            Complex.exp (((φ * ∑ p, (ζ p : ℝ)) : ℝ) * Complex.I) *
            ∏ v, Complex.exp ((2 * Real.pi * Complex.I * (flow D ζ v)) *
              (((x v : I) : ℝ) : ℂ)) := by
      intro x
      rw [Complex.ofReal_prod, ← Finset.prod_coe_sort]
      simp_rw [testK_eq_sum]
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      rw [prod_termC]
      push_cast; ring
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun ζ _ => ?_
      rw [integral_const_mul,
        integral_fintype_prod_eq_prod
          (f := fun v (y : I) => Complex.exp ((2 * Real.pi * Complex.I * (flow D ζ v)) *
            ((y : ℝ) : ℂ)))]
      simp_rw [integral_exp_int]
      rw [Finset.prod_ite_zero]
      simp only [Finset.prod_const_one, mul_ite, mul_one, mul_zero, Finset.mem_univ, true_imp_iff]
    · intro ζ _
      refine Integrable.const_mul ?_ _
      refine integrable_of_continuous _ ?_
      fun_prop
  have := congrArg Complex.re key
  rw [Complex.ofReal_re] at this
  rw [this, Complex.re_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  split_ifs
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · simp

section Graph
open SimpleGraph

lemma exists_leaf {W : Type*} [Finite W] (H : SimpleGraph W) (hH : H.IsAcyclic) {a b : W}
    (hab : H.Adj a b) : ∃ u x, H.Adj u x ∧ ∀ y, H.Adj u y → y = x := by
  have : Nonempty W := ⟨a⟩
  classical
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length H
  have hnil : ¬ p.Nil := by
    intro hn
    have := hmax _ _ (Walk.cons hab Walk.nil) (by simp [hab.ne])
    rw [hn.length_eq_zero] at this
    simp at this
  refine ⟨u, p.snd, p.adj_snd hnil, fun y hy => ?_⟩
  apply hH.eq_snd_of_adj_start hp hy
  by_contra hy'
  have := hmax _ _ (p.cons hy.symm) (hp.cons hy')
  simp at this

/-- A finite nonempty set of edges of `G` with no vertex of degree one contains a cycle of `G`. -/
lemma exists_cycle_of_no_leaf {W : Type*} [Finite W] (G : SimpleGraph W) (F : Set (Sym2 W))
    (hFG : F ⊆ G.edgeSet) {a b : W} (hab : s(a, b) ∈ F)
    (hleaf : ∀ u x, s(u, x) ∈ F → ∃ y, y ≠ x ∧ s(u, y) ∈ F) :
    ∃ (u : W) (w : G.Walk u u), w.IsCycle ∧ ∀ e ∈ w.edges, e ∈ F := by
  classical
  set H := SimpleGraph.fromEdgeSet F
  have hHG : H ≤ G := by
    intro x y h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact hFG h.1
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet (hFG he)
  have hHadj : ∀ x y, s(x, y) ∈ F → H.Adj x y := fun x y h => by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨h, fun hxy => hnd _ h (by simp [hxy])⟩
  have hcyc : ¬ H.IsAcyclic := by
    intro hH
    obtain ⟨u, x, hux, hu⟩ := exists_leaf H hH (hHadj a b hab)
    rw [SimpleGraph.fromEdgeSet_adj] at hux
    obtain ⟨y, hyx, hy⟩ := hleaf u x hux.1
    exact hyx (hu y (hHadj u y hy))
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hcyc
  obtain ⟨u, w, hw⟩ := hcyc
  refine ⟨u, w.mapLe hHG, hw.mapLe hHG, fun e he => ?_⟩
  simp only [Walk.mapLe, Walk.edges_map] at he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  have := w.edges_subset_edgeSet he'
  rw [SimpleGraph.edgeSet_fromEdgeSet] at this
  simpa using this.1

end Graph

section Comb

/-! ### Arcs, edges and circulations -/

omit [DecidableEq V] in
lemma mem_arcs_iff (D : OrientedGraph V) (q : V × V) : q ∈ D.arcs ↔ D.Adj q.1 q.2 := by
  classical
  simp [OrientedGraph.arcs]

omit [Fintype V] [DecidableEq V] in
lemma underlying_adj_iff (D : OrientedGraph V) (a b : V) :
    D.underlying.Adj a b ↔ D.Adj a b ∨ D.Adj b a := by
  simp only [OrientedGraph.underlying, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · rintro (h | h)
    · exact ⟨fun hab => D.irrefl a (hab ▸ h), Or.inl h⟩
    · exact ⟨fun hab => D.irrefl a (hab ▸ h), Or.inr h⟩

/-- The underlying edge of an arc. -/
def aEdge {D : OrientedGraph V} (p : Arc D) : Sym2 V := s(p.1.1, p.1.2)

omit [DecidableEq V] in
lemma aEdge_injective (D : OrientedGraph V) : Function.Injective (aEdge (D := D)) := by
  intro p p' h
  simp only [aEdge, Sym2.eq_iff] at h
  have hp := (mem_arcs_iff D _).mp p.2
  have hp' := (mem_arcs_iff D _).mp p'.2
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subtype.ext (Prod.ext h1 h2)
  · rw [h1, h2] at hp
    exact absurd hp' (D.asymm _ _ hp)

omit [DecidableEq V] in
lemma aEdge_mem_edgeSet {D : OrientedGraph V} (p : Arc D) : aEdge p ∈ D.underlying.edgeSet := by
  simp only [aEdge, SimpleGraph.mem_edgeSet, underlying_adj_iff]
  exact Or.inl ((mem_arcs_iff D _).mp p.2)

omit [DecidableEq V] in
lemma arc_fst_ne_snd {D : OrientedGraph V} (p : Arc D) : p.1.1 ≠ p.1.2 := fun h =>
  D.irrefl _ (h ▸ (mem_arcs_iff D _).mp p.2)

/-- The underlying edges of the support of a labelling. -/
noncomputable def Phi {D : OrientedGraph V} (ζ : Arc D → ℤ) : Finset (Sym2 V) :=
  (Finset.univ.filter fun p => ζ p ≠ 0).image aEdge

lemma card_Phi {D : OrientedGraph V} (ζ : Arc D → ℤ) : (Phi ζ).card = suppCard ζ :=
  Finset.card_image_of_injective _ (aEdge_injective D)

lemma mem_Phi {D : OrientedGraph V} (ζ : Arc D → ℤ) (e : Sym2 V) :
    e ∈ Phi ζ ↔ ∃ p, ζ p ≠ 0 ∧ aEdge p = e := by
  simp [Phi]

/-- The circulations with values in `{-1, 0, 1}`. -/
noncomputable def Circ (D : OrientedGraph V) : Finset (Arc D → ℤ) :=
  (Fintype.piFinset fun _ : Arc D => signs).filter fun ζ => ∀ v, flow D ζ v = 0

/-- **Every nonzero circulation contains a cycle in its support.** -/
lemma circ_exists_cycle (D : OrientedGraph V) {ζ : Arc D → ℤ} (hζ : ζ ∈ Circ D) (hne : ζ ≠ 0) :
    ∃ (u : V) (w : D.underlying.Walk u u), w.IsCycle ∧ ∀ e ∈ w.edges, e ∈ Phi ζ := by
  obtain ⟨p0, hp0⟩ := Function.ne_iff.mp hne
  have hflow := (Finset.mem_filter.mp hζ).2
  refine exists_cycle_of_no_leaf D.underlying (Phi ζ : Set (Sym2 V)) ?_
    (a := p0.1.1) (b := p0.1.2) ?_ ?_
  · intro e he
    obtain ⟨p, _, rfl⟩ := (mem_Phi ζ e).mp he
    exact aEdge_mem_edgeSet p
  · exact (mem_Phi ζ _).mpr ⟨p0, hp0, rfl⟩
  · intro u x hux
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, hpe⟩ := (mem_Phi ζ _).mp (Finset.mem_coe.mp hux)
    have hother : ∀ p' : Arc D, ζ p' ≠ 0 → ∀ y, aEdge p' = s(u, y) → p' = p := by
      intro p' hp' y hy
      have hy' : y = x := by
        by_contra hyx
        exact hcon y hyx (Finset.mem_coe.mpr ((mem_Phi ζ _).mpr ⟨p', hp', hy⟩))
      subst hy'
      exact aEdge_injective D (hy.trans hpe.symm)
    have hf := hflow u
    simp only [flow] at hf
    rw [Finset.sum_eq_single p] at hf
    · have hu : p.1.1 = u ∨ p.1.2 = u := by
        have : u ∈ aEdge p := by rw [hpe]; exact Sym2.mem_mk_left u x
        simpa [aEdge, eq_comm] using this
      have hne' := arc_fst_ne_snd p
      rcases hu with h | h
      · rw [if_pos h, if_neg (fun h' => hne' (h.trans h'.symm))] at hf
        simp [hp] at hf
      · rw [if_pos h, if_neg (fun h' => hne' (h'.trans h.symm))] at hf
        simp [hp] at hf
    · intro p' _ hp'p
      by_cases hz : ζ p' = 0
      · simp [hz]
      · have h1 : p'.1.1 ≠ u := fun h =>
          hp'p (hother p' hz p'.1.2 (by simp [aEdge, h]))
        have h2 : p'.1.2 ≠ u := fun h =>
          hp'p (hother p' hz p'.1.1 (by simp [aEdge, h, Sym2.eq_swap]))
        simp [h1, h2]
    · simp

lemma girth_le_suppCard (D : OrientedGraph V) {ζ : Arc D → ℤ} (hζ : ζ ∈ Circ D) (hne : ζ ≠ 0) :
    D.underlying.girth ≤ suppCard ζ := by
  classical
  obtain ⟨u, w, hw, hsub⟩ := circ_exists_cycle D hζ hne
  have h1 := hw.girth_le_length
  rw [← card_Phi, ← w.length_edges, ← List.toFinset_card_of_nodup hw.edges_nodup] at *
  exact h1.trans (Finset.card_le_card fun e he => hsub e (List.mem_toFinset.mp he))

lemma Phi_mem_cycles (D : OrientedGraph V) {ζ : Arc D → ℤ} (hζ : ζ ∈ Circ D) (hne : ζ ≠ 0)
    (hk : suppCard ζ = D.underlying.girth) :
    Phi ζ ∈ D.cyclesOfLength D.underlying.girth := by
  classical
  obtain ⟨u, w, hw, hsub⟩ := circ_exists_cycle D hζ hne
  have h1 := hw.girth_le_length
  have hs : w.edges.toFinset ⊆ Phi ζ := fun e he => hsub e (List.mem_toFinset.mp he)
  have hc := List.toFinset_card_of_nodup hw.edges_nodup
  rw [w.length_edges] at hc
  have hcard := Finset.card_le_card hs
  rw [card_Phi] at hcard
  have hlen : w.length = D.underlying.girth := by omega
  have heq : w.edges.toFinset = Phi ζ :=
    Finset.eq_of_subset_of_card_le hs (by rw [card_Phi]; omega)
  simp only [OrientedGraph.cyclesOfLength, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨u, w, hw, hlen, by convert heq⟩

end Comb

section Walks

/-! ### The circulation of a cycle walk -/

lemma chain_and {α : Type*} {R S : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → l.IsChain S → l.IsChain (fun a b => R a b ∧ S a b)
  | [], _, _ => .nil
  | [a], _, _ => .singleton a
  | _ :: _ :: _, h1, h2 => by
    rw [List.isChain_cons_cons] at h1 h2 ⊢
    exact ⟨⟨h1.1, h2.1⟩, chain_and h1.2 h2.2⟩

lemma chain_const {α β : Type*} (f : α → β) :
    ∀ {a : α} {l : List α}, (a :: l).IsChain (fun x y => f x = f y) → ∀ x ∈ a :: l, f x = f a
  | a, [], _ => by simp
  | a, b :: l, h => by
    rw [List.isChain_cons_cons] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · rw [chain_const f h.2 x hx, h.1]

lemma walk_sum_flow {G : SimpleGraph V} (v : V) :
    ∀ {a b : V} (p : G.Walk a b),
      (p.darts.map fun d => ((if d.fst = v then 1 else 0) - (if d.snd = v then 1 else 0) : ℤ)).sum
        = (if a = v then 1 else 0) - (if b = v then 1 else 0)
  | _, _, .nil => by simp
  | _, _, .cons h p => by
    rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, walk_sum_flow v p]
    simp only
    ring

variable (D : OrientedGraph V) {u : V} (w : D.underlying.Walk u u)

/-- The ordered pairs traversed by a walk. -/
noncomputable def DP : Finset (V × V) := (w.darts.map (·.toProd)).toFinset

/-- The arc labelling of a walk. For a trail `w`: `+1` on arcs traversed forwards, `-1` on arcs
traversed backwards, `0` elsewhere; in general the forward indicator minus the backward indicator,
so `0` on an arc traversed both ways. -/
noncomputable def sigW : Arc D → ℤ := fun p =>
  (if p.1 ∈ DP D w then 1 else 0) - (if p.1.swap ∈ DP D w then 1 else 0)

variable {D w}

omit [Fintype V] in
lemma mem_DP {q : V × V} : q ∈ DP D w ↔ ∃ d ∈ w.darts, d.toProd = q := by
  simp [DP]

omit [Fintype V] in
lemma DP_adj {q : V × V} (h : q ∈ DP D w) : D.underlying.Adj q.1 q.2 := by
  obtain ⟨d, _, rfl⟩ := mem_DP.mp h
  exact d.adj

omit [Fintype V] [DecidableEq V] in
lemma dart_edge_mem {d : D.underlying.Dart} (hd : d ∈ w.darts) : d.edge ∈ w.edges := by
  rw [SimpleGraph.Walk.edges_eq_map_darts]
  exact List.mem_map_of_mem hd

omit [Fintype V] in
lemma DP_edge {q : V × V} (h : q ∈ DP D w) : s(q.1, q.2) ∈ w.edges := by
  obtain ⟨d, hd, rfl⟩ := mem_DP.mp h
  exact dart_edge_mem hd

omit [Fintype V] in
lemma edge_DP {a b : V} (h : s(a, b) ∈ w.edges) : (a, b) ∈ DP D w ∨ (b, a) ∈ DP D w := by
  rw [SimpleGraph.Walk.edges_eq_map_darts] at h
  obtain ⟨d, hd, he⟩ := List.mem_map.mp h
  simp only [SimpleGraph.Dart.edge, Sym2.eq_iff] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact mem_DP.mpr ⟨d, hd, Prod.ext h1 h2⟩
  · right; exact mem_DP.mpr ⟨d, hd, Prod.ext h1 h2⟩

omit [Fintype V] [DecidableEq V] in
lemma darts_nodup (hw : w.IsTrail) : w.darts.Nodup := by
  have := hw.edges_nodup
  rw [SimpleGraph.Walk.edges_eq_map_darts] at this
  exact this.of_map _

omit [Fintype V] in
lemma DP_not_both (hw : w.IsTrail) {a b : V} (h : (a, b) ∈ DP D w) : (b, a) ∉ DP D w := by
  intro h'
  obtain ⟨d, hd, hd1⟩ := mem_DP.mp h
  obtain ⟨d', hd', hd2⟩ := mem_DP.mp h'
  have hn := hw.edges_nodup
  rw [SimpleGraph.Walk.edges_eq_map_darts] at hn
  have heq : d = d' := List.inj_on_of_nodup_map hn hd hd' (by
    simp only [SimpleGraph.Dart.edge, hd1, hd2]
    exact Sym2.eq_swap)
  subst heq
  rw [hd1] at hd2
  have := (DP_adj h).ne
  simp only [Prod.mk.injEq] at hd2
  exact this hd2.1

omit [Fintype V] in
lemma sum_DP (hw : w.IsTrail) {R : Type*} [AddCommMonoid R] (f : V × V → R) :
    ∑ q ∈ DP D w, f q = (w.darts.map fun d => f d.toProd).sum := by
  rw [DP, List.sum_toFinset _ ((darts_nodup hw).map SimpleGraph.Dart.toProd_injective),
    List.map_map]
  rfl

lemma sum_sigW_mul (h : V × V → ℤ) :
    ∑ p : Arc D, sigW D w p * h p.1 =
      ∑ q ∈ DP D w, (if q ∈ D.arcs then h q else -h q.swap) := by
  simp only [sigW]
  rw [Finset.sum_coe_sort D.arcs (fun q => ((if q ∈ DP D w then 1 else 0) -
    (if q.swap ∈ DP D w then 1 else 0)) * h q)]
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero, add_zero,
    add_zero, Finset.sum_ite, Finset.sum_neg_distrib]
  have h1 : D.arcs.filter (· ∈ DP D w) = (DP D w).filter (· ∈ D.arcs) := by
    ext q; simp [and_comm]
  rw [h1, sub_eq_add_neg]
  congr 2
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => Prod.swap_swap _)
    (fun _ _ => Prod.swap_swap _) (fun _ _ => by simp)
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    refine ⟨hq.2, fun h => ?_⟩
    rw [mem_arcs_iff] at h hq
    exact D.asymm _ _ hq.1 h
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    refine ⟨?_, by simpa using hq.1⟩
    have hadj := (underlying_adj_iff D _ _).mp (DP_adj hq.1)
    rw [mem_arcs_iff] at hq ⊢
    exact hadj.resolve_left hq.2

lemma sigW_mem_signs : sigW D w ∈ Fintype.piFinset fun _ : Arc D => signs := by
  rw [Fintype.mem_piFinset]
  intro p
  simp only [sigW, signs]
  split_ifs <;> decide

lemma Phi_sigW (hw : w.IsTrail) : Phi (sigW D w) = w.edges.toFinset := by
  ext e
  rw [mem_Phi, List.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [sigW] at hp
    by_cases h1 : p.1 ∈ DP D w
    · exact DP_edge h1
    · by_cases h2 : p.1.swap ∈ DP D w
      · have := DP_edge h2
        simpa [aEdge, Sym2.eq_swap] using this
      · simp [h1, h2] at hp
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
    have hadj : D.underlying.Adj a b := w.adj_of_mem_edges he
    rcases (underlying_adj_iff D a b).mp hadj with h | h
    · refine ⟨⟨(a, b), (mem_arcs_iff D _).mpr h⟩, ?_, rfl⟩
      rcases edge_DP he with h' | h'
      · simp [sigW, h', DP_not_both hw h']
      · simp [sigW, h', DP_not_both hw h']
    · refine ⟨⟨(b, a), (mem_arcs_iff D _).mpr h⟩, ?_, by simp [aEdge, Sym2.eq_swap]⟩
      rcases edge_DP he with h' | h'
      · simp [sigW, h', DP_not_both hw h']
      · simp [sigW, h', DP_not_both hw h']

lemma sum_sigW (hw : w.IsTrail) : ∑ p, sigW D w p = walkImbalance D w := by
  have := sum_sigW_mul (D := D) (w := w) (fun _ => 1)
  simp only [mul_one] at this
  rw [this, sum_DP hw, walkImbalance]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  by_cases h : D.Adj d.fst d.snd
  · simp [h, mem_arcs_iff]
  · simp [h, mem_arcs_iff]

lemma flow_sigW (hw : w.IsTrail) (v : V) : flow D (sigW D w) v = 0 := by
  have := sum_sigW_mul (D := D) (w := w)
    (fun q => (if q.1 = v then 1 else 0) - (if q.2 = v then 1 else 0))
  rw [flow, this]
  have e : ∀ q ∈ DP D w, (if q ∈ D.arcs then ((if q.1 = v then 1 else 0) -
      (if q.2 = v then 1 else 0) : ℤ) else -((if q.swap.1 = v then 1 else 0) -
      (if q.swap.2 = v then 1 else 0))) =
      (if q.1 = v then 1 else 0) - (if q.2 = v then 1 else 0) := by
    intro q _
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl e, sum_DP hw]
  have := walk_sum_flow v w
  simpa using this

lemma sigW_mem_Circ (hw : w.IsTrail) : sigW D w ∈ Circ D :=
  Finset.mem_filter.mpr ⟨sigW_mem_signs, flow_sigW hw⟩

end Walks

section Unique

/-! ### Uniqueness: a circulation supported on a cycle is `± sigW` -/

/-- The antisymmetric dart function of a labelling. -/
noncomputable def tau (D : OrientedGraph V) (ζ : Arc D → ℤ) (a b : V) : ℤ :=
  ∑ p : Arc D, ζ p * ((if p.1 = (a, b) then 1 else 0) - (if p.1 = (b, a) then 1 else 0))

lemma tau_anti (D : OrientedGraph V) (ζ : Arc D → ℤ) (a b : V) : tau D ζ b a = -tau D ζ a b := by
  simp only [tau, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma sum_tau (D : OrientedGraph V) (ζ : Arc D → ℤ) (v : V) :
    ∑ x, tau D ζ v x = flow D ζ v := by
  simp only [tau, flow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 2
  · rw [Finset.sum_eq_single p.1.2]
    · by_cases h : p.1.1 = v
      · simp [h, Prod.ext_iff]
      · simp [h, Prod.ext_iff]
    · intro b _ hb; simp [Prod.ext_iff, Ne.symm hb]
    · simp
  · rw [Finset.sum_eq_single p.1.1]
    · by_cases h : p.1.2 = v
      · simp [h, Prod.ext_iff]
      · simp [h, Prod.ext_iff]
    · intro b _ hb; simp [Prod.ext_iff, Ne.symm hb]
    · simp

lemma tau_arc (D : OrientedGraph V) (ζ : Arc D → ℤ) (p : Arc D) : tau D ζ p.1.1 p.1.2 = ζ p := by
  simp only [tau]
  rw [Finset.sum_eq_single p]
  · have : p.1 ≠ (p.1.2, p.1.1) := fun h =>
      arc_fst_ne_snd p (by have := congrArg Prod.fst h; simpa using this)
    simp [this]
  · intro p' _ hp'
    have h1 : p'.1 ≠ (p.1.1, p.1.2) := fun h => hp' (Subtype.ext h)
    have h2 : p'.1 ≠ (p.1.2, p.1.1) := by
      intro h
      have ha := (mem_arcs_iff D _).mp p'.2
      rw [h] at ha
      exact D.asymm _ _ ha ((mem_arcs_iff D _).mp p.2)
    simp [h1, h2]
  · simp

lemma tau_ne_zero (D : OrientedGraph V) (ζ : Arc D → ℤ) {a b : V} (h : tau D ζ a b ≠ 0) :
    s(a, b) ∈ Phi ζ := by
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [mem_Phi]
  refine ⟨p, fun h0 => hp (by simp [h0]), ?_⟩
  by_cases h1 : p.1 = (a, b)
  · simp [aEdge, h1]
  · by_cases h2 : p.1 = (b, a)
    · simp [aEdge, h2, Sym2.eq_swap]
    · simp [h1, h2] at hp

lemma tau_const {D : OrientedGraph V} {u : V} {w : D.underlying.Walk u u} (hw : w.IsCycle)
    {ζ : Arc D → ℤ} (hζ : ζ ∈ Circ D) (hP : Phi ζ = w.edges.toFinset) :
    ∀ d ∈ w.darts, ∀ d' ∈ w.darts, tau D ζ d.fst d.snd = tau D ζ d'.fst d'.snd := by
  have hflow := (Finset.mem_filter.mp hζ).2
  have hsupp : ∀ a b, tau D ζ a b ≠ 0 → s(a, b) ∈ w.edges := fun a b h => by
    have := tau_ne_zero D ζ h
    rw [hP, List.mem_toFinset] at this
    exact this
  have hc2 : w.darts.IsChain (fun d d' => d.edge ≠ d'.edge) := by
    have hn := hw.edges_nodup
    rw [SimpleGraph.Walk.edges_eq_map_darts] at hn
    exact (List.pairwise_map.mp hn).isChain
  have hc := List.IsChain.iff_mem.mp (chain_and w.isChain_dartAdj_darts hc2)
  have hstep : w.darts.IsChain (fun d d' => tau D ζ d.fst d.snd = tau D ζ d'.fst d'.snd) := by
    refine hc.imp ?_
    rintro d d' ⟨hd, hd', hadj, hne⟩
    have hadj : d.snd = d'.fst := hadj
    set b := d.snd with hb
    have hbs : b ∈ w.support := w.dart_snd_mem_support_of_mem_darts hd
    have hN := hw.ncard_neighborSet_toSubgraph_eq_two hbs
    have hx1 : d.fst ∈ w.toSubgraph.neighborSet b := by
      rw [SimpleGraph.Subgraph.mem_neighborSet, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
      have := dart_edge_mem hd
      simpa [SimpleGraph.Dart.edge, Sym2.eq_swap] using this
    have hx2 : d'.snd ∈ w.toSubgraph.neighborSet b := by
      rw [SimpleGraph.Subgraph.mem_neighborSet, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
      have := dart_edge_mem hd'
      simpa [SimpleGraph.Dart.edge, hadj] using this
    have hx12 : d.fst ≠ d'.snd := by
      intro h
      apply hne
      simp only [SimpleGraph.Dart.edge, ← hadj, ← hb, h]
      exact Sym2.eq_swap
    have hall : ∀ y, s(b, y) ∈ w.edges → y = d.fst ∨ y = d'.snd := by
      intro y hy
      have hy' : y ∈ w.toSubgraph.neighborSet b := by
        rw [SimpleGraph.Subgraph.mem_neighborSet, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
        exact hy
      obtain ⟨p, q, hpq, hpqN⟩ := Set.ncard_eq_two.mp hN
      rw [hpqN] at hx1 hx2 hy'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2 hy'
      grind
    have h0 := hflow b
    rw [← sum_tau, Finset.sum_eq_add d.fst d'.snd hx12] at h0
    · rw [tau_anti] at h0
      show tau D ζ d.fst b = tau D ζ d'.fst d'.snd
      rw [← hadj]
      linarith
    · intro y _ hy
      by_contra hne0
      rcases hall y (hsupp _ _ hne0) with h | h
      · exact hy.1 h
      · exact hy.2 h
    · simp
    · simp
  intro d hd d' hd'
  obtain ⟨d0, l, hl⟩ : ∃ d0 l, w.darts = d0 :: l := by
    cases h : w.darts with
    | nil => rw [h] at hd; simp at hd
    | cons d0 l => exact ⟨d0, l, rfl⟩
  rw [hl] at hstep hd hd'
  rw [chain_const (fun d : D.underlying.Dart => tau D ζ d.fst d.snd) hstep d hd,
    chain_const (fun d : D.underlying.Dart => tau D ζ d.fst d.snd) hstep d' hd']

lemma circ_eq_sigW {D : OrientedGraph V} {u : V} {w : D.underlying.Walk u u} (hw : w.IsCycle)
    {ζ : Arc D → ℤ} (hζ : ζ ∈ Circ D) (hP : Phi ζ = w.edges.toFinset) :
    ζ = sigW D w ∨ ζ = -sigW D w := by
  have hconst := tau_const hw hζ hP
  have hval : ∀ p : Arc D, ∃ c, c ∈ signs ∧ ζ p = c := fun p =>
    ⟨ζ p, Fintype.mem_piFinset.mp (Finset.mem_filter.mp hζ).1 p, rfl⟩
  -- the common value
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 ∈ w.darts := by
    cases h : w.darts with
    | nil => exact absurd (SimpleGraph.Walk.darts_eq_nil.mp h) hw.not_nil
    | cons d0 l => exact ⟨d0, by simp⟩
  set c := tau D ζ d0.fst d0.snd
  have hform : ∀ p : Arc D, ζ p = c * sigW D w p := by
    intro p
    by_cases h1 : p.1 ∈ DP D w
    · obtain ⟨d, hd, hdp⟩ := mem_DP.mp h1
      have this : p.1.swap ∉ DP D w := DP_not_both hw.isTrail (a := p.1.1) (b := p.1.2) h1
      rw [← tau_arc D ζ p, ← hdp, hconst d hd d0 hd0]
      simp [sigW, h1, this, c]
    · by_cases h2 : p.1.swap ∈ DP D w
      · obtain ⟨d, hd, hdp⟩ := mem_DP.mp h2
        rw [← tau_arc D ζ p]
        have := hconst d hd d0 hd0
        rw [hdp, Prod.fst_swap, Prod.snd_swap, tau_anti] at this
        simp only [sigW, h1, h2]
        simp only [if_false, if_true]
        linarith
      · have h0 : ζ p = 0 := by
          by_contra hz
          have : aEdge p ∈ Phi ζ := (mem_Phi ζ _).mpr ⟨p, hz, rfl⟩
          rw [hP, List.mem_toFinset] at this
          rcases edge_DP this with h | h
          · exact h1 h
          · exact h2 h
        simp [h0, sigW, h1, h2]
  -- `c = ± 1`
  obtain ⟨p, hp⟩ : ∃ p : Arc D, sigW D w p ≠ 0 := by
    have hne : (Phi (sigW D w)).Nonempty := by
      rw [Phi_sigW hw.isTrail]
      exact ⟨d0.edge, List.mem_toFinset.mpr (dart_edge_mem hd0)⟩
    obtain ⟨e, he⟩ := hne
    obtain ⟨p, hp, _⟩ := (mem_Phi _ e).mp he
    exact ⟨p, hp⟩
  have hζp : ζ p ≠ 0 := by
    have : aEdge p ∈ Phi ζ := by
      rw [hP, ← Phi_sigW hw.isTrail]
      exact (mem_Phi _ _).mpr ⟨p, hp, rfl⟩
    obtain ⟨p', hp', he⟩ := (mem_Phi ζ _).mp this
    rwa [← aEdge_injective D he]
  have hs := Fintype.mem_piFinset.mp (sigW_mem_signs (D := D) (w := w)) p
  have hz := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hζ).1 p
  rw [hform p] at hz hζp
  simp only [signs, Finset.mem_insert, Finset.mem_singleton] at hs hz
  have hc : c = 1 ∨ c = -1 := by
    rcases hs with hs | hs | hs <;> rw [hs] at hz hζp <;> simp at hζp <;> omega
  rcases hc with hc | hc
  · left; funext q; rw [hform q, hc, one_mul]
  · right; funext q; rw [hform q, hc]; simp

end Unique

section Final

/-! ### The test kernels, the limit `ε → 0`, and the fibres over the girth cycles -/

lemma testK_isDigraphon {c : ℝ} (φ : ℝ) (hc : |c| ≤ 1 / 2) : IsDigraphon (testK c φ) := by
  refine ⟨?_, fun x y => ?_⟩
  · apply Continuous.measurable
    simp only [testK, Function.uncurry_def]
    fun_prop
  · have h1 := Real.abs_cos_le_one (2 * Real.pi * ((x : ℝ) - y) + φ)
    have h2 : |c * Real.cos (2 * Real.pi * ((x : ℝ) - y) + φ)| ≤ 1 / 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg c, abs_nonneg (Real.cos (2 * Real.pi * ((x : ℝ) - y) + φ))]
    rw [abs_le] at h2
    simp only [testK, Set.mem_Icc]
    constructor <;> linarith [h2.1, h2.2]

lemma symmetrize_testK (ε θ : ℝ) : symmetrize (testK ε θ) = testK (ε * Real.cos θ) 0 := by
  funext x y
  simp only [symmetrize, testK, add_zero]
  have : 2 * Real.pi * ((y : ℝ) - x) = -(2 * Real.pi * ((x : ℝ) - y)) := by ring
  rw [this, Real.cos_add, Real.cos_add, Real.cos_neg, Real.sin_neg]
  ring

lemma coeff_nonneg {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ) (g : ℕ)
    (hk : ∀ i ∈ s, g ≤ k i) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ ε, 0 < ε → ε < δ → 0 ≤ ∑ i ∈ s, ε ^ k i * a i) :
    0 ≤ ∑ i ∈ s.filter (fun i => k i = g), a i := by
  set A := ∑ i ∈ s.filter (fun i => k i = g), a i
  set M := ∑ i ∈ s, |a i|
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have key : ∀ ε, 0 < ε → ε < δ → ε ≤ 1 → 0 ≤ A + ε * M := by
    intro ε hε hεδ hε1
    have h0 := h ε hε hεδ
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => k i = g)] at h0
    have e1 : ∑ i ∈ s.filter (fun i => k i = g), ε ^ k i * a i = ε ^ g * A := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    have e2 : ∑ i ∈ s.filter (fun i => ¬ k i = g), ε ^ k i * a i ≤ ε ^ g * (ε * M) := by
      calc ∑ i ∈ s.filter (fun i => ¬ k i = g), ε ^ k i * a i
          ≤ ∑ i ∈ s.filter (fun i => ¬ k i = g), ε ^ (g + 1) * |a i| := by
            refine Finset.sum_le_sum fun i hi => ?_
            obtain ⟨his, hne⟩ := Finset.mem_filter.mp hi
            have hgk : g + 1 ≤ k i := by have := hk i his; omega
            have hp : ε ^ k i ≤ ε ^ (g + 1) := pow_le_pow_of_le_one hε.le hε1 hgk
            calc ε ^ k i * a i ≤ ε ^ k i * |a i| :=
                  mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hε.le _)
              _ ≤ ε ^ (g + 1) * |a i| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
        _ = ε ^ (g + 1) * ∑ i ∈ s.filter (fun i => ¬ k i = g), |a i| := by rw [Finset.mul_sum]
        _ ≤ ε ^ (g + 1) * M := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hε.le _)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun i _ _ => abs_nonneg _
        _ = ε ^ g * (ε * M) := by ring
    have hpos : 0 < ε ^ g := pow_pos hε g
    have : 0 ≤ ε ^ g * (A + ε * M) := by rw [mul_add]; linarith
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hpos hneg
    linarith
  by_contra hA
  push Not at hA
  set ε := min (δ / 2) (min (1 / 2) (-A / (2 * M + 2)))
  have hε : 0 < ε := by
    apply lt_min (by linarith) (lt_min (by norm_num) (div_pos (by linarith) (by linarith)))
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hεA : ε * (2 * M + 2) ≤ -A := by
    have : ε ≤ -A / (2 * M + 2) := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by linarith)] at this
  have := key ε hε hεδ hε1
  nlinarith

lemma flow_neg (D : OrientedGraph V) (ζ : Arc D → ℤ) (v : V) : flow D (-ζ) v = -flow D ζ v := by
  simp only [flow, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma Phi_neg {D : OrientedGraph V} (ζ : Arc D → ℤ) : Phi (-ζ) = Phi ζ := by
  simp [Phi]

lemma neg_mem_Circ {D : OrientedGraph V} {ζ : Arc D → ℤ} (h : ζ ∈ Circ D) : -ζ ∈ Circ D := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
  refine Finset.mem_filter.mpr ⟨?_, fun v => by rw [flow_neg, h2 v, neg_zero]⟩
  rw [Fintype.mem_piFinset] at h1 ⊢
  intro p
  have := h1 p
  simp only [signs, Finset.mem_insert, Finset.mem_singleton] at this ⊢
  simp only [Pi.neg_apply]
  omega

end Final


section CheckpointB

/-! ### The facts on `cosImbalance` and `cyclesOfLength` asked for by Checkpoint B (Q7) -/

/-- **Choice independence** of `cosImbalance` (paper, tex l.1360-1365): for *every* cycle walk
`w` with edge set `C`, `cosImbalance θ C = cos(ω(w) θ)`. Any two such walks have labellings
`sigW` that are circulations with the same support, hence equal up to sign
(`circ_eq_sigW`); their imbalances therefore agree up to sign, and the cosine is even. -/
lemma cosImbalance_eq_of_isCycle (D : OrientedGraph V) (θ : ℝ) {v : V}
    {w : D.underlying.Walk v v} (hw : w.IsCycle) {C : Finset (Sym2 V)}
    (hC : w.edges.toFinset = C) :
    D.cosImbalance θ C = Real.cos ((walkImbalance D w : ℝ) * θ) := by
  simp only [cosImbalance]
  split
  · rename_i hh
    have hs := Classical.choose_spec (Classical.choose_spec hh)
    set w0 := Classical.choose (Classical.choose_spec hh)
    have hE0 : w0.edges.toFinset = C := by convert hs.2
    have hsame : Phi (sigW D w) = w0.edges.toFinset := by
      rw [Phi_sigW hw.isTrail, hC, hE0]
    have hsum := sum_sigW (D := D) hw.isTrail
    have hsum0 := sum_sigW (D := D) hs.1.isTrail
    rcases circ_eq_sigW hs.1 (sigW_mem_Circ hw.isTrail) hsame with h | h
    · rw [h] at hsum
      rw [← hsum0, hsum]
    · rw [h] at hsum
      simp only [Pi.neg_apply, Finset.sum_neg_distrib] at hsum
      have : walkImbalance D w0 = -walkImbalance D w := by rw [← hsum0, ← hsum, neg_neg]
      rw [this]
      push_cast
      rw [neg_mul, Real.cos_neg]
  · rename_i hno
    exact absurd ⟨v, w, hw, by convert hC⟩ hno

/-- **The fallback value `0` is unused** on `𝒞_g(D)`: every member of `cyclesOfLength g` is the
edge set of a cycle walk, so `cosImbalance` takes its `if`-branch there. -/
lemma cosImbalance_dif_cond_of_mem (D : OrientedGraph V) {g : ℕ} {C : Finset (Sym2 V)}
    (hC : C ∈ D.cyclesOfLength g) :
    ∃ (v : V) (w : D.underlying.Walk v v), w.IsCycle ∧ w.length = g ∧ w.edges.toFinset = C := by
  simp only [cyclesOfLength, Finset.mem_filter, Finset.mem_univ, true_and] at hC
  obtain ⟨v, w, hw, hl, hE⟩ := hC
  exact ⟨v, w, hw, hl, by convert hE⟩

/-- **The shortest-cycle set is nonempty** when `\bar D` contains a cycle. -/
lemma cyclesOfLength_girth_nonempty (D : OrientedGraph V) (hcyc : ¬ D.underlying.IsAcyclic) :
    (D.cyclesOfLength D.underlying.girth).Nonempty := by
  classical
  obtain ⟨v, w, hw, hl⟩ := SimpleGraph.exists_girth_eq_length.mpr hcyc
  refine ⟨w.edges.toFinset, ?_⟩
  simp only [cyclesOfLength, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, w, hw, hl.symm, by convert rfl⟩

end CheckpointB

end Section6Aux

namespace OrientedGraph

variable {V : Type*} [Fintype V]

/-- **Lemma 6.1.** Let `D` be a directed graph whose underlying graph contains a cycle, and let
`g` be the girth of `\bar D`. If `D` is OAS, then
`∑_{C ∈ 𝒞_g(D)} cos(ω_D(C) θ) ≤ |𝒞_g(D)| cos^g(θ)` for every `θ ∈ [0, 2π)`.
The range restriction hθ is the paper's; the proof does not use it, and the inequality holds for
every real θ. -/
theorem lemma_6_1 (D : OrientedGraph V) (hcyc : ¬ D.underlying.IsAcyclic) (hD : D.IsOASK)
    (θ : ℝ) (hθ : θ ∈ Ico 0 (2 * Real.pi)) :
    ∑ C ∈ D.cyclesOfLength D.underlying.girth, D.cosImbalance θ C ≤
      (D.cyclesOfLength D.underlying.girth).card * Real.cos θ ^ D.underlying.girth := by
  classical
  open Section6Aux in
  set g := D.underlying.girth with hg
  have hg3 : 3 ≤ g := SimpleGraph.three_le_girth hcyc
  -- the coefficient function
  set f : (Arc D → ℤ) → ℝ := fun ζ =>
    Real.cos θ ^ suppCard ζ - Real.cos (θ * ∑ p, (ζ p : ℝ)) with hf
  set S := (Circ D).filter (fun ζ => ζ ≠ 0) with hS
  -- Step 1: the OAS inequality for the test kernels, after the Fourier expansion
  have hineq : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → 0 ≤ ∑ ζ ∈ S, ε ^ suppCard ζ * f ζ := by
    intro ε hε hε2
    have h1 := hD (testK ε θ) (testK_isDigraphon θ (by rw [abs_of_pos hε]; linarith))
    rw [symmetrize_testK, t_testK, t_testK, ← Finset.sum_filter, ← Finset.sum_filter] at h1
    change ∑ ζ ∈ Circ D, _ ≤ ∑ ζ ∈ Circ D, _ at h1
    have h2 : 0 ≤ (1 / 2 : ℝ) ^ D.numArcs * ∑ ζ ∈ Circ D, ε ^ suppCard ζ * f ζ := by
      rw [Finset.mul_sum]
      have : ∑ ζ ∈ Circ D, (1 / 2 : ℝ) ^ D.numArcs * (ε ^ suppCard ζ * f ζ) =
          ∑ ζ ∈ Circ D, (1 / 2) ^ D.numArcs * (ε * Real.cos θ) ^ suppCard ζ *
            Real.cos (0 * ∑ p, (ζ p : ℝ)) -
          ∑ ζ ∈ Circ D, (1 / 2) ^ D.numArcs * ε ^ suppCard ζ *
            Real.cos (θ * ∑ p, (ζ p : ℝ)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ζ _ => ?_
        simp only [hf, zero_mul, Real.cos_zero, mul_one, mul_pow]
        ring
      rw [this]
      linarith
    have h3 := (mul_nonneg_iff_of_pos_left (by positivity)).mp h2
    rwa [hS, Finset.sum_filter_of_ne]
    intro ζ _ hne hz
    apply hne
    rw [hz]
    simp [hf, suppCard]
  -- Step 2: let `ε → 0`
  have hB := coeff_nonneg S suppCard f g
    (fun ζ hζ => girth_le_suppCard D (Finset.mem_filter.mp hζ).1 (Finset.mem_filter.mp hζ).2)
    (by norm_num : (0 : ℝ) < 1 / 2) hineq
  set T := S.filter (fun ζ => suppCard ζ = g) with hT
  -- Step 3: group the circulations of support size `g` by their support cycle
  have hmaps : ∀ ζ ∈ T, Phi ζ ∈ D.cyclesOfLength g := by
    intro ζ hζ
    obtain ⟨hζS, hk⟩ := Finset.mem_filter.mp hζ
    obtain ⟨hζC, hne⟩ := Finset.mem_filter.mp hζS
    exact Phi_mem_cycles D hζC hne hk
  have hfib : ∀ C ∈ D.cyclesOfLength g,
      ∑ ζ ∈ T with Phi ζ = C, f ζ = 2 * Real.cos θ ^ g - 2 * D.cosImbalance θ C := by
    intro C hC
    have hC' := hC
    simp only [cyclesOfLength, Finset.mem_filter, Finset.mem_univ, true_and] at hC'
    obtain ⟨v1, w1, hw1, hlen1, hE1⟩ := hC'
    have hcardC : C.card = g := by
      rw [← hE1, List.toFinset_card_of_nodup hw1.edges_nodup, w1.length_edges, hlen1]
    rw [cosImbalance_eq_of_isCycle D θ hw1 hE1]
    set w0 := w1
    have hs : w0.IsCycle := hw1
    have hE0 : w0.edges.toFinset = C := hE1
    have hP0 : Phi (sigW D w0) = C := (Phi_sigW hs.isTrail).trans hE0
    have hk0 : suppCard (sigW D w0) = g := by rw [← card_Phi, hP0, hcardC]
    have hne0 : sigW D w0 ≠ 0 := by
      intro h0
      rw [h0] at hk0
      simp [suppCard] at hk0
      omega
    have hfiber : T.filter (fun ζ => Phi ζ = C) = {sigW D w0, -sigW D w0} := by
      ext ζ
      simp only [hT, hS, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hcirc, _⟩, _⟩, hP⟩
        exact circ_eq_sigW hs hcirc (hP.trans hE0.symm)
      · rintro (rfl | rfl)
        · exact ⟨⟨⟨sigW_mem_Circ hs.isTrail, hne0⟩, hk0⟩, hP0⟩
        · refine ⟨⟨⟨neg_mem_Circ (sigW_mem_Circ hs.isTrail), neg_ne_zero.mpr hne0⟩, ?_⟩,
            by rw [Phi_neg, hP0]⟩
          rw [← card_Phi, Phi_neg, card_Phi, hk0]
    have hdist : sigW D w0 ≠ -sigW D w0 := by
      intro h
      apply hne0
      funext p
      have := congrFun h p
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega
    rw [hfiber, Finset.sum_pair hdist]
    have hsum := congrArg (Int.cast : ℤ → ℝ) (sum_sigW hs.isTrail)
    push_cast at hsum
    have hk0' : suppCard (-sigW D w0) = g := by rw [← card_Phi, Phi_neg, card_Phi, hk0]
    simp only [hf, hk0, hk0', Pi.neg_apply, Int.cast_neg, Finset.sum_neg_distrib, hsum,
      mul_neg, Real.cos_neg]
    rw [mul_comm θ]
    ring
  have hfw := Finset.sum_fiberwise_of_maps_to hmaps (f := f)
  rw [Finset.sum_congr rfl hfib] at hfw
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hfw
  have : ∑ ζ ∈ T, f ζ = ∑ ζ ∈ S with suppCard ζ = g, f ζ := rfl
  linarith

end OrientedGraph

end NieWeiOrientedSidorenko
