import NieWeiOrientedSidorenko.S1FamiliesB
import NieWeiOrientedSidorenko.S1Bridges

/-!
# Theorems 1.1, 1.10 and 1.11

Proofs of `OrientedGraph.thm_1_1`, `OrientedGraph.thm_1_1_kernel`, `OrientedGraph.thm_1_10`,
`OrientedGraph.thm_1_10_kernel`, `OrientedGraph.thm_1_11` and `OrientedGraph.thm_1_11_kernel` of
`NieWeiOrientedSidorenko/Section1.lean`, as `thm_1_1_proof`, …, `thm_1_11_kernel_proof`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace S1Families

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OrientedGraph

/-! ## Bridges of Section 1 (the Question 1(c) results, from `S1Bridges`) -/

/-- `OrientedGraph.isOS_iff_isOSK` of `Section1.lean` (Question 1(c)), proved in `S1Bridges`. -/
lemma isOS_iff_isOSK {V : Type u} [Fintype V] (D : OrientedGraph V) : D.IsOS ↔ D.IsOSK :=
  S1Bridges.isOS_iff_isOSK_proof D

/-- `OrientedGraph.isOAS_iff_isOASK` of `Section1.lean` (Question 1(c)), proved in `S1Bridges`. -/
lemma isOAS_iff_isOASK {V : Type u} [Fintype V] (D : OrientedGraph V) : D.IsOAS ↔ D.IsOASK :=
  S1Bridges.isOAS_iff_isOASK_proof D

/-- `OrientedGraph.isSymmetryForcing_iff_isSymmetryForcingK` of `Section1.lean`, proved in
`S1Bridges`. -/
lemma isSymmetryForcing_iff_isSymmetryForcingK {V : Type u} [Fintype V] (h13 : FHMZThm13Hyp)
    (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp) (D : OrientedGraph V) :
    D.IsSymmetryForcing ↔ D.IsSymmetryForcingK :=
  S1Bridges.isSymmetryForcing_iff_isSymmetryForcingK_proof h13 h18 hcpt D



/-! ## Oriented cycles: the OS part -/

section CycleOS

variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma alternating_of_oneDirection (D : OrientedGraph V) (h : D.IsOneDirection) :
    D.IsAlternating := by
  obtain ⟨A, hA⟩ := h
  intro v
  by_cases hv : v ∈ A
  · exact Or.inl fun u huv => (hA u v huv).2 hv
  · exact Or.inr fun u hvu => hv (hA v u hvu).1

omit [Fintype V] in
lemma oneDirection_of_alternating (D : OrientedGraph V) (h : D.IsAlternating) :
    D.IsOneDirection := by
  refine ⟨{v | ∀ u, ¬ D.Adj u v}, fun u v huv => ⟨?_, fun hv => hv u huv⟩⟩
  rcases h u with h1 | h1
  · exact h1
  · exact absurd huv (h1 v)

lemma cycle_connected (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) : D.IsConnected := by
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 := ⟨Fintype.card V - 1, by omega⟩
  have hc : (SimpleGraph.cycleGraph (Fintype.card V)).Connected := by
    rw [hm]; exact SimpleGraph.connected_cycleGraph_add_one
  exact φ.connected_iff.mpr hc

lemma cycle_even_of_oneDirection (D : OrientedGraph V) (hcyc : D.IsOrientedCycle)
    (h : D.IsOneDirection) : Even (Fintype.card V) := by
  classical
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨A, hA⟩ := h
  have hcol : (SimpleGraph.cycleGraph (Fintype.card V)).Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk (fun a => if φ.symm a ∈ A then (0 : Fin 2) else 1) ?_⟩
    intro a b hab
    have h' : D.underlying.Adj (φ.symm a) (φ.symm b) := φ.symm.map_adj_iff.mpr hab
    rcases (Section1Aux.underlying_adj_iff' D _ _).mp h' with h'' | h''
    · simp [(hA _ _ h'').1, (hA _ _ h'').2]
    · simp [(hA _ _ h'').1, (hA _ _ h'').2]
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h3' := SimpleGraph.chromaticNumber_cycleGraph_of_odd _ (by omega) hodd
  have := hcol.chromaticNumber_le
  rw [h3'] at this
  exact absurd this (by decide)

/-- An alternating oriented cycle is isomorphic to its transpose (rotation by one step). -/
lemma cycle_selfConverse (D : OrientedGraph V) (hcyc : D.IsOrientedCycle)
    (halt : D.IsAlternating) : D.IsSelfConverse := by
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
  -- the rotation of the cycle, on `V`
  set n := Fintype.card V with hn
  clear_value n
  subst hm
  set g : V ≃ V := φ.toEquiv.trans ((Equiv.addRight (1 : Fin (m + 3))).trans φ.toEquiv.symm)
    with hg
  have hgv : ∀ v, g v = φ.symm (φ v + 1) := fun v => rfl
  have hadj1 : ∀ v, D.underlying.Adj v (g v) := by
    intro v
    rw [hgv]
    have : (SimpleGraph.cycleGraph (m + 3)).Adj (φ v) (φ v + 1) := by
      rw [SimpleGraph.cycleGraph_adj]; right; simp
    have h' := φ.symm.map_adj_iff.mpr this
    simpa using h'
  have hadj2 : ∀ u v, D.underlying.Adj (g u) (g v) ↔ D.underlying.Adj u v := by
    intro u v
    have : (SimpleGraph.cycleGraph (m + 3)).Adj (φ u + 1) (φ v + 1) ↔
        (SimpleGraph.cycleGraph (m + 3)).Adj (φ u) (φ v) := by
      simp [SimpleGraph.cycleGraph_adj]
    rw [hgv, hgv, ← φ.map_adj_iff, ← φ.map_adj_iff (v := u)]
    simpa using this
  -- an arc `u → v` gives the arc `g v → g u`
  have key : ∀ u v, D.Adj u v → D.Adj (g v) (g u) := by
    intro u v huv
    have hu : ∀ w, ¬ D.Adj w u := by
      rcases halt u with h | h
      · exact h
      · exact absurd huv (h v)
    have hgu : ∀ w, ¬ D.Adj (g u) w := by
      have h1 := hadj1 u
      rcases (Section1Aux.underlying_adj_iff' D _ _).mp h1 with h2 | h2
      · rcases halt (g u) with h | h
        · exact absurd h2 (h u)
        · exact h
      · exact absurd h2 (hu _)
    have h1 := (hadj2 u v).mpr ((Section1Aux.underlying_adj_iff' D _ _).mpr (Or.inl huv))
    rcases (Section1Aux.underlying_adj_iff' D _ _).mp h1 with h2 | h2
    · exact absurd h2 (hgu _)
    · exact h2
  refine ⟨⟨g, fun u v => ?_⟩⟩
  show D.Adj (g v) (g u) ↔ D.Adj u v
  constructor
  · intro h
    have h1 := (hadj2 u v).mp ((Section1Aux.underlying_adj_iff' D _ _).mpr (Or.inr h))
    rcases (Section1Aux.underlying_adj_iff' D _ _).mp h1 with h2 | h2
    · exact h2
    · exact absurd (key v u h2) (D.asymm _ _ h)
  · exact key u v


lemma cycle_exists_adj (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) :
    ∃ a b, D.Adj a b := by
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
  set n := Fintype.card V with hn
  clear_value n
  subst hm
  have h01 : (SimpleGraph.cycleGraph (m + 3)).Adj 0 1 := by
    rw [SimpleGraph.cycleGraph_adj]; right; simp
  have h' : D.underlying.Adj (φ.symm 0) (φ.symm 1) := φ.symm.map_adj_iff.mpr h01
  rcases (Section1Aux.underlying_adj_iff' D _ _).mp h' with h | h
  · exact ⟨_, _, h⟩
  · exact ⟨_, _, h⟩

lemma one_le_numArcs_of_adj (D : OrientedGraph V) {a b : V} (h : D.Adj a b) :
    1 ≤ D.numArcs := by
  classical
  unfold numArcs
  exact Finset.card_pos.mpr ⟨(a, b), (Section6Aux.mem_arcs_iff D _).mpr h⟩

lemma card_edgeFinset_cycleGraph (m : ℕ) :
    (SimpleGraph.cycleGraph (m + 3)).edgeFinset.card = m + 3 := by
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (SimpleGraph.cycleGraph (m + 3))
  simp only [SimpleGraph.cycleGraph_degree_three_le, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  rw [SimpleGraph.edgeFinset_card] at h ⊢
  have : Fintype.card (SimpleGraph.cycleGraph (m + 3)).edgeSet = m + 3 := by
    convert (by omega : (m + 3) * 2 / 2 = m + 3) using 1
    rw [h]; convert (Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)).symm
  exact this

lemma tU_mono (H : SimpleGraph V) {K L : I → I → ℝ} (hK0 : ∀ x y, 0 ≤ K x y)
    (hKL : ∀ x y, K x y ≤ L x y) (hL : IsKernel L) : tU H K ≤ tU H L := by
  classical
  unfold tU tUndir
  obtain ⟨M, hM⟩ := hL.2
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun x => Finset.prod_nonneg fun _ _ => hK0 _ _) ?_
    (Eventually.of_forall fun x => Finset.prod_le_prod₀ (fun _ _ => hK0 _ _) fun _ _ => hKL _ _)
  refine Integrable.of_bound (Finset.measurable_prod _ fun e _ =>
    Section1Aux.measurable_pair hL.1 _ _).aestronglyMeasurable
    (M ^ H.edgeFinset.card) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ e ∈ H.edgeFinset, |L (x (Quot.out e).1) (x (Quot.out e).2)|
      ≤ ∏ _e ∈ H.edgeFinset, M :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun _ _ => hM _ _
    _ = _ := Finset.prod_const _

lemma isSymmKernel_abs {U : I → I → ℝ} (hU : IsSymmKernel U) :
    IsSymmKernel (fun x y => |U x y|) := by
  obtain ⟨⟨hm, M, hM⟩, hs⟩ := hU
  refine ⟨⟨?_, M, fun x y => ?_⟩, fun x y => by simp only [hs x y]⟩
  · exact continuous_abs.measurable.comp hm
  · rw [abs_abs]; exact hM x y

/-- Lovász's Proposition 14.2(a) (A9), transported to an even oriented cycle: the weak-norm
functional of `\bar D` is a norm on everywhere-symmetric kernels. -/
lemma wnSymmFn_of_even_cycle (hA9 : LovaszProp142aHyp) (D : OrientedGraph V)
    (hcyc : D.IsOrientedCycle) (heven : Even (Fintype.card V)) :
    IsWeaklyNormingSymmFn D.underlying := by
  classical
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨q, hq⟩ := heven
  have hq2 : 2 ≤ q := by omega
  have hn : Fintype.card V = 2 * q := by omega
  rw [hn] at φ
  set C := SimpleGraph.cycleGraph (2 * q) with hC
  obtain ⟨⟨hhom, htri⟩, hdef⟩ := hA9 q hq2
  set N : (I → I → ℝ) → ℝ := fun U => |tU C U| ^ ((1 : ℝ) / (2 * q)) with hN
  have htU : ∀ K : I → I → ℝ, (∀ x y, K x y = K y x) → tU D.underlying K = tU C K := by
    intro K hK
    rw [Section1Aux.tU_eq_t D.underlying D rfl hK,
      Section1Aux.tU_eq_t C (transp D φ.toEquiv) (transp_underlying_eq D φ) hK]
    exact t_iso (transpIso D φ.toEquiv) K
  have hcard : (D.underlying.edgeFinset.card : ℝ) = 2 * q := by
    have h1 := φ.card_edgeFinset_eq
    obtain ⟨m, hm⟩ : ∃ m, 2 * q = m + 3 := ⟨2 * q - 3, by omega⟩
    have h2 : (SimpleGraph.cycleGraph (2 * q)).edgeFinset.card = 2 * q := by
      have := card_edgeFinset_cycleGraph m
      rw [← hm] at this
      exact this
    rw [show D.underlying.edgeFinset.card = 2 * q by rw [← h2]; convert h1]
    push_cast; ring
  have hW : ∀ U : I → I → ℝ, IsSymmKernel U → weakNormFn D.underlying U =
      N (fun x y => |U x y|) := by
    intro U hU
    simp only [weakNormFn, hN]
    rw [htU _ (isSymmKernel_abs hU).2, hcard, abs_of_nonneg (Section1Aux.tU_nonneg C
      (fun x y => abs_nonneg _))]
  refine ⟨⟨fun U hU c => ?_, fun U W hU hW' => ?_⟩, fun U hU h0 => ?_⟩
  · rw [hW _ (Section1Aux.isSymmKernel_smul hU c), hW _ hU]
    have := hhom _ (isSymmKernel_abs hU) |c|
    rw [abs_abs] at this
    rw [← this]
    congr 1; funext x y; rw [abs_mul]
  · rw [hW _ (Section1Aux.isSymmKernel_add hU hW'), hW _ hU, hW _ hW']
    have hsum := Section1Aux.isSymmKernel_add (isSymmKernel_abs hU) (isSymmKernel_abs hW')
    refine le_trans ?_ (htri _ _ (isSymmKernel_abs hU) (isSymmKernel_abs hW'))
    simp only [hN]
    rw [abs_of_nonneg (Section1Aux.tU_nonneg C (fun x y => abs_nonneg _)),
      abs_of_nonneg (Section1Aux.tU_nonneg C (fun x y => by positivity))]
    refine Real.rpow_le_rpow (Section1Aux.tU_nonneg C (fun x y => abs_nonneg _)) ?_ (by positivity)
    exact tU_mono C (fun x y => abs_nonneg _) (fun x y => abs_add_le _ _) hsum.1
  · rw [hW _ hU] at h0
    have := hdef _ (isSymmKernel_abs hU) h0
    unfold AEEq at this ⊢
    filter_upwards [this] with p hp
    exact abs_eq_zero.mp hp

lemma cycle_not_acyclic (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) :
    ¬ D.underlying.IsAcyclic := by
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
  set n := Fintype.card V with hn
  clear_value n
  subst hm
  intro hac
  have hc := (SimpleGraph.cycleGraph.isCycle_cycle (n := m)).map
    (f := (φ.symm : SimpleGraph.cycleGraph (m + 3) →g D.underlying)) φ.symm.injective
  exact hac _ hc

end CycleOS

/-! ## Oriented cycles: the OAS part -/

section CycleOAS

variable {V : Type*} [Fintype V]

lemma cycle_ncard_nbr (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) (v : V) :
    (D.underlying.neighborSet v).ncard = 2 := by
  classical
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
  set n := Fintype.card V with hn
  clear_value n
  subst hm
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    ← φ.degree_eq v]
  exact SimpleGraph.cycleGraph_degree_three_le

lemma cycle_card_edgeFinset (D : OrientedGraph V) (hcyc : D.IsOrientedCycle)
    [Fintype D.underlying.edgeSet] : D.underlying.edgeFinset.card = Fintype.card V := by
  classical
  obtain ⟨⟨φ⟩, h3⟩ := hcyc
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
  set n := Fintype.card V with hn
  clear_value n
  subst hm
  rw [φ.card_edgeFinset_eq]
  convert card_edgeFinset_cycleGraph m

lemma cycle_walk_support (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) {a : V}
    {c : D.underlying.Walk a a} (hc : c.IsCycle) (v : V) : v ∈ c.support := by
  have hclosed : ∀ x y, x ∈ c.support → D.underlying.Adj x y → y ∈ c.support := by
    intro x y hx hxy
    have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hx
    have hsub := c.toSubgraph.neighborSet_subset x
    have heq : c.toSubgraph.neighborSet x = D.underlying.neighborSet x :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [h2, cycle_ncard_nbr D hcyc x])
        (Set.toFinite _)
    have hy : y ∈ c.toSubgraph.neighborSet x := by rw [heq]; exact hxy
    exact (c.mem_verts_toSubgraph).mp (c.toSubgraph.edge_vert hy.symm)
  have hwalk : ∀ x y (p : D.underlying.Walk x y), x ∈ c.support → y ∈ c.support := by
    intro x y p
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hx => ih (hclosed _ _ hx h)
  obtain ⟨w⟩ := (cycle_connected D hcyc).preconnected a v
  exact hwalk _ _ w c.start_mem_support

lemma cycle_walk_length (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) {a : V}
    {c : D.underlying.Walk a a} (hc : c.IsCycle) : c.length = Fintype.card V := by
  classical
  have hnd := hc.support_nodup
  have hall : ∀ v, v ∈ c.support.tail := by
    intro v
    by_cases hv : v = a
    · subst hv; exact SimpleGraph.Walk.end_mem_tail_support hc.not_nil
    · have := cycle_walk_support D hcyc hc v
      rw [← SimpleGraph.Walk.cons_tail_support] at this
      exact (List.mem_cons.mp this).resolve_left hv
  have h1 : c.support.tail.length = c.length := by simp [SimpleGraph.Walk.length_support]
  rw [← h1, ← List.toFinset_card_of_nodup hnd,
    show c.support.tail.toFinset = Finset.univ from
      Finset.eq_univ_of_forall fun v => List.mem_toFinset.mpr (hall v), Finset.card_univ]

lemma cycle_walk_edges (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) {a : V}
    {c : D.underlying.Walk a a} (hc : c.IsCycle) (e : Sym2 V) :
    e ∈ c.edges ↔ e ∈ D.underlying.edgeSet := by
  classical
  refine ⟨fun h => c.edges_subset_edgeSet h, fun he => ?_⟩
  by_contra hne
  have hnd := hc.isTrail.edges_nodup
  have hcard : c.edges.toFinset.card = Fintype.card V := by
    rw [List.toFinset_card_of_nodup hnd, SimpleGraph.Walk.length_edges,
      cycle_walk_length D hcyc hc]
  have hsub : c.edges.toFinset ⊆ D.underlying.edgeFinset.erase e := by
    intro x hx
    rw [List.mem_toFinset] at hx
    refine Finset.mem_erase.mpr ⟨fun h => hne (h ▸ hx), ?_⟩
    exact SimpleGraph.mem_edgeFinset.mpr (c.edges_subset_edgeSet hx)
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (SimpleGraph.mem_edgeFinset.mpr he),
    cycle_card_edgeFinset D hcyc] at this
  have h3 := hcyc.2
  omega

lemma sum_pm_one {α : Type*} (l : List α) (f : α → ℤ) (hf : ∀ a, f a = 1 ∨ f a = -1) :
    ∃ k : ℕ, k ≤ l.length ∧ (l.map f).sum = l.length - 2 * k := by
  induction l with
  | nil => exact ⟨0, le_refl _, by simp⟩
  | cons a l ih =>
    obtain ⟨k, hk, hs⟩ := ih
    rcases hf a with h | h
    · exact ⟨k, by simp; omega, by simp [h, hs]; ring⟩
    · exact ⟨k + 1, by simp; omega, by simp [h, hs]; ring⟩

lemma trig_cycle (N k : ℕ) (hN : 3 ≤ N)
    (h : ∀ θ ∈ Ico 0 (2 * Real.pi), Real.cos ((((N : ℤ) - 2 * k : ℤ) : ℝ) * θ) ≤ Real.cos θ ^ N) :
    N = 4 ∧ (((N : ℤ) - 2 * k) = 2 ∨ ((N : ℤ) - 2 * k) = -2) := by
  set ω : ℤ := (N : ℤ) - 2 * k with hω
  set a := ω.natAbs with ha
  have hωa : ω = a ∨ ω = -a := Int.natAbs_eq ω
  have h' : ∀ θ ∈ Ico 0 (2 * Real.pi), Real.cos ((a : ℝ) * θ) ≤ Real.cos θ ^ N := by
    intro θ hθ
    have := h θ hθ
    rcases hωa with e | e
    · rw [e] at this; simpa using this
    · rw [e] at this; simpa [neg_mul, Real.cos_neg] using this
  have hpi := Real.pi_pos
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with h0 | h1 | h2 | h3
  · exfalso
    have := h' (Real.pi / 2) ⟨by positivity, by linarith⟩
    rw [h0, Real.cos_pi_div_two, zero_pow (by omega)] at this
    norm_num at this
  · exfalso
    have := h' (Real.pi / 3) ⟨by positivity, by linarith⟩
    rw [h1, Real.cos_pi_div_three] at this
    simp only [Nat.cast_one, one_mul] at this
    have h2 : (1 / 2 : ℝ) ^ N ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
    norm_num at h2 this
    linarith
  · have hNeven : Even N := by
      rcases hωa with e | e <;> exact ⟨N / 2, by omega⟩
    by_cases h4 : N = 4
    · refine ⟨h4, ?_⟩
      rcases hωa with e | e
      · left; rw [e, h2]; rfl
      · right; rw [e, h2]; rfl
    · exfalso
      obtain ⟨j, hj⟩ := hNeven
      have hj3 : 3 ≤ j := by omega
      have := h' (Real.pi / 6) ⟨by positivity, by linarith⟩
      rw [h2, show ((2 : ℕ) : ℝ) * (Real.pi / 6) = Real.pi / 3 by push_cast; ring,
        Real.cos_pi_div_three, Real.cos_pi_div_six, hj, ← two_mul, pow_mul] at this
      have hsq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      rw [hsq] at this
      have h5 : (3 / 4 : ℝ) ^ j ≤ (3 / 4) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj3
      norm_num at h5 this
      linarith
  · exfalso
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    set θ := 2 * Real.pi / a with hθ
    have hθ0 : 0 < θ := by positivity
    have hθπ : θ < Real.pi := by
      rw [hθ, div_lt_iff₀ ha0]
      have : (3 : ℝ) ≤ a := by exact_mod_cast h3
      nlinarith
    have := h' θ ⟨hθ0.le, by linarith⟩
    rw [show (a : ℝ) * θ = 2 * Real.pi by rw [hθ]; field_simp, Real.cos_two_pi] at this
    have c1 : Real.cos θ < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0
      simpa using this
    have c2 : -1 < Real.cos θ := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
      simpa using this
    have hab : |Real.cos θ| < 1 := abs_lt.mpr ⟨c2, c1⟩
    have : Real.cos θ ^ N < 1 :=
      lt_of_le_of_lt (le_trans (le_abs_self _) (by rw [abs_pow]))
        (pow_lt_one₀ (abs_nonneg _) hab (by omega))
    linarith


/-- An OAS oriented cycle: every cycle walk of `\bar D` has imbalance `±2` and `|V| = 4`
(Lemma 6.1 and the trigonometric argument of the proof of Theorem 1.11). -/
lemma oask_cycle_walk (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) (hD : D.IsOASK)
    {a : V} (c : D.underlying.Walk a a) (hc : c.IsCycle) :
    Fintype.card V = 4 ∧ (walkImbalance D c = 2 ∨ walkImbalance D c = -2) := by
  classical
  set N := Fintype.card V with hN
  have hN3 : 3 ≤ N := hcyc.2
  have hacyc := cycle_not_acyclic D hcyc
  have hlen := cycle_walk_length D hcyc hc
  have hg : D.underlying.girth = N := by
    obtain ⟨b, w, hw, hl⟩ := SimpleGraph.exists_girth_eq_length.mpr hacyc
    rw [hl, cycle_walk_length D hcyc hw]
  have hC : D.cyclesOfLength D.underlying.girth = {c.edges.toFinset} := by
    ext C
    rw [Finset.mem_singleton]
    constructor
    · intro hmem
      obtain ⟨v, w, hw, -, hE⟩ := Section6Aux.cosImbalance_dif_cond_of_mem D hmem
      rw [← hE]
      ext e
      simp only [List.mem_toFinset]
      rw [cycle_walk_edges D hcyc hw, cycle_walk_edges D hcyc hc]
    · rintro rfl
      simp only [cyclesOfLength, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, c, hc, by rw [hg, hlen], by convert rfl⟩
  obtain ⟨k, hk, hsum⟩ := sum_pm_one c.darts
    (fun d => if D.Adj d.fst d.snd then (1 : ℤ) else -1) (fun d => by split_ifs <;> simp)
  have hω : walkImbalance D c = (N : ℤ) - 2 * k := by
    unfold walkImbalance
    rw [SimpleGraph.Walk.length_darts, hlen] at hsum
    convert hsum
  have htrig : ∀ θ ∈ Ico 0 (2 * Real.pi),
      Real.cos ((((N : ℤ) - 2 * k : ℤ) : ℝ) * θ) ≤ Real.cos θ ^ N := by
    intro θ hθ
    have h := lemma_6_1 D hacyc hD θ hθ
    rw [hC, Finset.sum_singleton, Finset.card_singleton, hg,
      Section6Aux.cosImbalance_eq_of_isCycle D θ hc rfl, hω] at h
    simpa using h
  rw [SimpleGraph.Walk.length_darts, hlen] at hk
  obtain ⟨h4, h2⟩ := trig_cycle N k hN3 htrig
  exact ⟨h4, by rw [hω]; exact h2⟩

/-- The orientation of `C₄` on `Fin 4` in which `o i` says the edge `{i, i+1}` points
`i → i+1`. -/
def cyc4 (o : Fin 4 → Bool) : OrientedGraph (Fin 4) where
  Adj a b := (b = a + 1 ∧ o a = true) ∨ (a = b + 1 ∧ o b = false)
  irrefl a := by fin_cases a <;> simp
  asymm a b := by fin_cases a <;> fin_cases b <;> simp_all

instance (o : Fin 4 → Bool) : DecidableRel (cyc4 o).Adj := fun a b =>
  inferInstanceAs (Decidable ((b = a + 1 ∧ o a = true) ∨ (a = b + 1 ∧ o b = false)))

instance : DecidableRel O₁.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ ({(1, 0), (1, 2), (2, 3), (3, 0)} : Finset (Fin 4 × Fin 4))))

def imb4 (o : Fin 4 → Bool) : ℤ := ∑ i, if o i then 1 else -1

def dihedral4 : List (Fin 4 → Fin 4) :=
  [fun i => i, fun i => i + 1, fun i => i + 2, fun i => i + 3, fun i => -i, fun i => 1 - i,
    fun i => 2 - i, fun i => 3 - i]

lemma dihedral4_inj : ∀ f ∈ dihedral4, Function.Injective f := by decide +kernel

lemma cyc4_iso_O₁ : ∀ o : Fin 4 → Bool, (imb4 o = 2 ∨ imb4 o = -2) →
    ∃ f ∈ dihedral4, ∀ a b, O₁.Adj (f a) (f b) ↔ (cyc4 o).Adj a b := by decide +kernel

lemma cycleGraph4_adj : ∀ a b : Fin 4,
    (SimpleGraph.cycleGraph 4).Adj a b ↔ b = a + 1 ∨ a = b + 1 := by decide

lemma cycle_oask_mp (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) (hD : D.IsOASK) :
    Nonempty (D.Iso O₁) := by
  classical
  obtain ⟨⟨φ0⟩, h3⟩ := hcyc
  -- a first cycle walk gives `|V| = 4`
  have hacyc := cycle_not_acyclic D ⟨⟨φ0⟩, h3⟩
  obtain ⟨b0, w0, hw0, -⟩ := SimpleGraph.exists_girth_eq_length.mpr hacyc
  have h4 := (oask_cycle_walk D ⟨⟨φ0⟩, h3⟩ hD w0 hw0).1
  have φ : D.underlying ≃g SimpleGraph.cycleGraph 4 := h4 ▸ φ0
  set D' := transp D φ.toEquiv with hD'
  have hU : D'.underlying = SimpleGraph.cycleGraph 4 := transp_underlying_eq D φ
  have hcyc' : D'.IsOrientedCycle := ⟨⟨by rw [Fintype.card_fin, hU]⟩, by simp⟩
  have hD'O : D'.IsOASK := (isOASK_iso (transpIso D φ.toEquiv)).mp hD
  have hadjU : ∀ a b : Fin 4, D'.underlying.Adj a b ↔ b = a + 1 ∨ a = b + 1 := by
    intro a b; rw [hU]; exact cycleGraph4_adj a b
  have e01 : D'.underlying.Adj 0 1 := (hadjU 0 1).mpr (by decide)
  have e12 : D'.underlying.Adj 1 2 := (hadjU 1 2).mpr (by decide)
  have e23 : D'.underlying.Adj 2 3 := (hadjU 2 3).mpr (by decide)
  have e30 : D'.underlying.Adj 3 0 := (hadjU 3 0).mpr (by decide)
  set w4 : D'.underlying.Walk 0 0 :=
    SimpleGraph.Walk.cons e01 (SimpleGraph.Walk.cons e12 (SimpleGraph.Walk.cons e23
      (SimpleGraph.Walk.cons e30 SimpleGraph.Walk.nil))) with hw4
  have hw4c : w4.IsCycle := by
    rw [hw4, SimpleGraph.Walk.cons_isCycle_iff]
    simp [SimpleGraph.Walk.isPath_def]
  have himb := (oask_cycle_walk D' hcyc' hD'O w4 hw4c).2
  set o : Fin 4 → Bool := fun i => decide (D'.Adj i (i + 1)) with ho
  have himb' : imb4 o = 2 ∨ imb4 o = -2 := by
    have : walkImbalance D' w4 = imb4 o := by
      simp only [walkImbalance, hw4, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, imb4, Fin.sum_univ_four, ho]
      simp only [decide_eq_true_eq]
      norm_num
      ring
    rw [← this]; exact himb
  obtain ⟨f, hfL, hf⟩ := cyc4_iso_O₁ o himb'
  have hfb : Function.Bijective f := Finite.injective_iff_bijective.mp (dihedral4_inj f hfL)
  -- `D' ≅ cyc4 o`
  have hasymm : ∀ a b, D'.underlying.Adj a b → (D'.Adj b a ↔ ¬ D'.Adj a b) := by
    intro a b hab
    constructor
    · exact fun h h' => D'.asymm _ _ h h'
    · intro h
      rcases (Section1Aux.underlying_adj_iff' D' a b).mp hab with h' | h'
      · exact absurd h' h
      · exact h'
  let g1 : D'.Iso (cyc4 o) :=
    { toEquiv := Equiv.refl _
      map_adj_iff := fun a b => by
        simp only [Equiv.refl_apply]
        show (b = a + 1 ∧ o a = true) ∨ (a = b + 1 ∧ o b = false) ↔ D'.Adj a b
        simp only [ho, decide_eq_true_eq, decide_eq_false_iff_not]
        constructor
        · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
          · exact h
          · exact (hasymm _ _ ((hadjU _ _).mpr (Or.inl rfl))).mpr h
        · intro h
          rcases (hadjU a b).mp ((Section1Aux.underlying_adj_iff' D' a b).mpr (Or.inl h))
            with e | e
          · exact Or.inl ⟨e, e ▸ h⟩
          · refine Or.inr ⟨e, ?_⟩
            subst e
            exact fun h' => D'.asymm _ _ h h' }
  let g2 : (cyc4 o).Iso O₁ :=
    { toEquiv := Equiv.ofBijective f hfb
      map_adj_iff := fun a b => hf a b }
  exact ⟨isoTrans (isoTrans (transpIso D φ.toEquiv) g1) g2⟩

end CycleOAS

/-! ## Theorem 1.1: Griffiths' identity for `O₁` -/

section O1

/-- The measure on `Fin 4 → [0,1]`. -/
noncomputable abbrev μ4 : Measure (Fin 4 → I) := Measure.pi fun _ => volume

lemma O₁_arcs : O₁.arcs = {(1, 0), (1, 2), (2, 3), (3, 0)} := by
  ext p; rw [Section6Aux.mem_arcs_iff]; rfl

/-- The `O₁` integrand. -/
def TO (U : I → I → ℝ) (x : Fin 4 → I) : ℝ :=
  U (x 1) (x 0) * (U (x 1) (x 2) * (U (x 2) (x 3) * U (x 3) (x 0)))

lemma t_O₁ (U : I → I → ℝ) : t O₁ U = ∫ x, TO U x ∂μ4 := by
  unfold t tDir
  congr 1
  funext x
  rw [O₁_arcs, TO]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

lemma integral_perm4 (e : Fin 4 ≃ Fin 4) (F : (Fin 4 → I) → ℝ) :
    ∫ x, F (fun i => x (e i)) ∂μ4 = ∫ x, F x ∂μ4 := by
  have hmp : MeasurePreserving (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl I))
      μ4 μ4 :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ => MeasurePreserving.id _)
  rw [← hmp.integral_comp' F]
  congr 1

lemma mul_le_one_of {a b : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1) (_hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 := by nlinarith

lemma integrable4 {K L M N : I → I → ℝ} (hK : Measurable (Function.uncurry K))
    (hL : Measurable (Function.uncurry L)) (hM : Measurable (Function.uncurry M))
    (hN : Measurable (Function.uncurry N)) (bK : ∀ x y, |K x y| ≤ 1) (bL : ∀ x y, |L x y| ≤ 1)
    (bM : ∀ x y, |M x y| ≤ 1) (bN : ∀ x y, |N x y| ≤ 1) (a b c d e f g h : Fin 4) :
    Integrable (fun x : Fin 4 → I => K (x a) (x b) * (L (x c) (x d) * (M (x e) (x f) *
      N (x g) (x h)))) μ4 := by
  refine Integrable.of_bound (((Section1Aux.measurable_pair hK a b).mul
    ((Section1Aux.measurable_pair hL c d).mul ((Section1Aux.measurable_pair hM e f).mul
    (Section1Aux.measurable_pair hN g h))))).aestronglyMeasurable 1
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  have := bK (x a) (x b); have := bL (x c) (x d); have := bM (x e) (x f); have := bN (x g) (x h)
  have h1 : |M (x e) (x f)| * |N (x g) (x h)| ≤ 1 :=
    mul_le_one_of (abs_nonneg _) (by assumption) (abs_nonneg _) (by assumption)
  have h2 : |L (x c) (x d)| * (|M (x e) (x f)| * |N (x g) (x h)|) ≤ 1 :=
    mul_le_one_of (abs_nonneg _) (by assumption) (by positivity) h1
  exact mul_le_one_of (abs_nonneg _) (by assumption) (by positivity) h2

/-- The antisymmetric part. -/
noncomputable def antiP (U : I → I → ℝ) : I → I → ℝ := fun x y => (U x y - U y x) / 2

/-- The `C₄`-integrand of the antisymmetric part. -/
noncomputable def GA (U : I → I → ℝ) (x : Fin 4 → I) : ℝ :=
  antiP U (x 0) (x 1) * (antiP U (x 2) (x 1) * (antiP U (x 2) (x 3) * antiP U (x 0) (x 3)))

/-- The dihedral relabellings carrying `O₁` onto the eight orientations of `C₄` with
imbalance `±2`. -/
def tau8 : Fin 8 → (Fin 4 ≃ Fin 4)
  | 0 => Equiv.refl _
  | 1 => Equiv.addRight 1
  | 2 => Equiv.addRight 2
  | 3 => Equiv.addRight 3
  | 4 => Equiv.subLeft 0
  | 5 => Equiv.subLeft 1
  | 6 => Equiv.subLeft 2
  | 7 => Equiv.subLeft 3

lemma TO_identity (U : I → I → ℝ) (x : Fin 4 → I) :
    TO (symmetrize U) x - GA U x = (1 / 8) * ∑ k : Fin 8, TO U (fun i => x (tau8 k i)) := by
  simp only [Fin.sum_univ_eight, tau8, Equiv.refl_apply, Equiv.coe_addRight, Equiv.subLeft_apply]
  simp only [TO, GA, antiP, symmetrize, Fin.reduceAdd, Fin.reduceSub]
  ring

lemma isDig_bound {U : I → I → ℝ} (hU : IsDigraphon U) (x y : I) : |U x y| ≤ 1 :=
  abs_le.mpr ⟨by linarith [(hU.2 x y).1], (hU.2 x y).2⟩

lemma antiP_meas {U : I → I → ℝ} (hU : IsDigraphon U) : Measurable (Function.uncurry (antiP U)) :=
  show Measurable fun p : I × I => (U p.1 p.2 - U p.2 p.1) / 2 from
    (hU.1.sub (hU.1.comp measurable_swap)).div_const 2

lemma antiP_bound {U : I → I → ℝ} (hU : IsDigraphon U) (x y : I) : |antiP U x y| ≤ 1 := by
  have h1 := hU.2 x y; have h2 := hU.2 y x
  simp only [antiP]
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma integrable_TO {U : I → I → ℝ} (hU : IsDigraphon U) (e : Fin 4 ≃ Fin 4) :
    Integrable (fun x => TO U (fun i => x (e i))) μ4 :=
  integrable4 hU.1 hU.1 hU.1 hU.1 (isDig_bound hU) (isDig_bound hU) (isDig_bound hU)
    (isDig_bound hU) _ _ _ _ _ _ _ _

lemma integrable_GA {U : I → I → ℝ} (hU : IsDigraphon U) : Integrable (GA U) μ4 :=
  integrable4 (antiP_meas hU) (antiP_meas hU) (antiP_meas hU) (antiP_meas hU) (antiP_bound hU)
    (antiP_bound hU) (antiP_bound hU) (antiP_bound hU) _ _ _ _ _ _ _ _

/-- Griffiths' identity (KEY A10): `t(O₁, W) = t(O₁, S) - ∫ A A A A` over the `C₄` pattern. -/
lemma t_O₁_eq {U : I → I → ℝ} (hU : IsDigraphon U) :
    t O₁ U = t O₁ (symmetrize U) - ∫ x, GA U x ∂μ4 := by
  have hS := Section1Aux.isDigraphon_symmetrize hU
  have iS : Integrable (TO (symmetrize U)) μ4 := integrable_TO hS (Equiv.refl _)
  rw [t_O₁, t_O₁, ← integral_sub iS (integrable_GA hU)]
  simp_rw [TO_identity]
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => integrable_TO hU (tau8 k))]
  simp_rw [integral_perm4 (tau8 _) (TO U)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


/-- `C₄` as the bipartite oriented graph `{0,1} → {2,3}` on `Fin 4`. -/
def bipC4 : OrientedGraph (Fin 4) :=
  ofArcs {(0, 2), (0, 3), (1, 2), (1, 3)} (by decide) (by decide)

lemma bipC4_arcs : bipC4.arcs = {(0, 2), (0, 3), (1, 2), (1, 3)} := by
  ext p; rw [Section6Aux.mem_arcs_iff]; rfl

/-- `bipOG univ ≅ bipC4`. -/
def bipC4Iso : (Section1Aux.bipOG (Finset.univ : Finset (Fin 2 × Fin 2))).Iso bipC4 where
  toEquiv := finSumFinEquiv
  map_adj_iff u v := by
    rcases u with i | i <;> rcases v with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Section1Aux.bipOG, bipC4, ofArcs] <;> decide

/-- The bipartite `C₄` integrand of a kernel. -/
def GB (K : I → I → ℝ) (x : Fin 4 → I) : ℝ :=
  K (x 0) (x 2) * (K (x 0) (x 3) * (K (x 1) (x 2) * K (x 1) (x 3)))

lemma tb_univ_eq (K : I → I → ℝ) :
    tb (Finset.univ : Finset (Fin 2 × Fin 2)) K = ∫ x, GB K x ∂μ4 := by
  rw [Section1Aux.tb_eq_t_bipOG, t_iso bipC4Iso]
  unfold t tDir
  congr 1
  funext x
  rw [bipC4_arcs, GB]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

lemma GA_eq_GB (U : I → I → ℝ) : ∫ x, GA U x ∂μ4 = ∫ x, GB (antiP U) x ∂μ4 := by
  rw [← integral_perm4 (Equiv.swap 1 2) (GA U)]
  congr 1; funext x
  simp only [GA, GB, Equiv.swap_apply_def]
  simp only [Fin.reduceEq, ite_false, ite_true, Fin.isValue]
  ring

/-- The Gram kernel `K(a, b) = ∫ A(a, y) A(b, y) dy`. -/
noncomputable def gram (K : I → I → ℝ) (xs : Fin 2 → I) : ℝ := ∫ y, K (xs 0) y * K (xs 1) y

lemma tb_univ_gram {K : I → I → ℝ} (hK : Measurable (Function.uncurry K))
    (hb : ∀ x y, |K x y| ≤ 1) :
    tb (Finset.univ : Finset (Fin 2 × Fin 2)) K =
      ∫ xs, gram K xs ^ 2 ∂(Measure.pi fun _ => (volume : Measure I)) := by
  unfold tb tBi
  have hmeas : ∀ p : Fin 2 × Fin 2, Measurable fun z : (Fin 2 → I) × (Fin 2 → I) =>
      K (z.1 p.1) (z.2 p.2) := fun p =>
    show Measurable (Function.uncurry K ∘ fun z : (Fin 2 → I) × (Fin 2 → I) => (z.1 p.1, z.2 p.2))
    from hK.comp (((measurable_pi_apply p.1).comp measurable_fst).prodMk
      ((measurable_pi_apply p.2).comp measurable_snd))
  have hint : Integrable (fun z : (Fin 2 → I) × (Fin 2 → I) =>
      ∏ p ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), K (z.1 p.1) (z.2 p.2))
      ((Measure.pi fun _ => (volume : Measure I)).prod (Measure.pi fun _ => volume)) := by
    refine Integrable.of_bound (Finset.measurable_prod _ fun p _ => hmeas p).aestronglyMeasurable
      1 (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p _ => hb _ _
  rw [integral_prod _ hint]
  congr 1; funext xs
  have : ∀ ys : Fin 2 → I, ∏ p ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), K (xs p.1) (ys p.2) =
      ∏ j, (K (xs 0) (ys j) * K (xs 1) (ys j)) := by
    intro ys
    rw [← Finset.univ_product_univ, Finset.prod_product, Finset.prod_comm]
    simp [Fin.prod_univ_two]
  simp_rw [this]
  rw [integral_fintype_prod_eq_pow (fun y => K (xs 0) y * K (xs 1) y), Fintype.card_fin]
  rfl


lemma lint_ofReal_ne_top {K : I × I → ℝ} (hb : ∀ p, |K p| ≤ 1) (S : Set (I × I)) :
    ∫⁻ p in S, ENNReal.ofReal (K p) ∂((volume : Measure I).prod volume) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => (1 : ENNReal)) fun p => ?_) ?_)
  · exact ENNReal.ofReal_le_one.mpr (le_trans (le_abs_self _) (hb p))
  · rw [lintegral_const, one_mul]; exact measure_lt_top _ _

lemma ae_zero_of_rect {K : I × I → ℝ} (hK : Measurable K) (hb : ∀ p, |K p| ≤ 1)
    (h : ∀ s, MeasurableSet s → ∀ t, MeasurableSet t →
      ∫ p in s ×ˢ t, K p ∂((volume : Measure I).prod volume) = 0) :
    ∀ᵐ p ∂((volume : Measure I).prod volume), K p = 0 := by
  have hbn : ∀ p, |(-K) p| ≤ 1 := fun p => by simpa using hb p
  have hint : Integrable K ((volume : Measure I).prod volume) :=
    Integrable.of_bound hK.aestronglyMeasurable 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hb p)
  have hae := ae_eq_of_setLIntegral_prod_eq (μ := (volume : Measure I).prod volume)
    (f := fun p => ENNReal.ofReal (K p)) (g := fun p => ENNReal.ofReal (-K p))
    hK.ennreal_ofReal.aemeasurable hK.neg.ennreal_ofReal.aemeasurable
    (by rw [← setLIntegral_univ]; exact lint_ofReal_ne_top hb _) (fun s hs t ht => ?_)
  · filter_upwards [hae] with p hp
    rcases lt_trichotomy (K p) 0 with h1 | h1 | h1
    · rw [ENNReal.ofReal_of_nonpos h1.le] at hp
      exact absurd hp.symm (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
    · exact h1
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -K p ≤ 0)] at hp
      exact absurd hp (ne_of_gt (ENNReal.ofReal_pos.mpr h1))
  · have h0 := h s hs t ht
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint.integrableOn] at h0
    have := lint_ofReal_ne_top hbn (s ×ˢ t)
    simp only [Pi.neg_apply] at this
    exact (ENNReal.toReal_eq_toReal_iff' (lint_ofReal_ne_top hb _) this).mp (by linarith)


lemma abs_integral_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (h : ∀ x, |f x| ≤ 1) : |∫ x, f x ∂μ| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := 1)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)
  simpa using this

lemma integral_sq_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) (h0 : ∫ x, f x ^ 2 ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0 := by
  have hint : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hb x))
  have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hint).mp h0
  filter_upwards [this] with x hx
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx

lemma mul_abs_le_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]

lemma abs_indicator_le_one (B : Set I) (a : I) : |B.indicator (fun _ => (1 : ℝ)) a| ≤ 1 := by
  by_cases h : a ∈ B <;> simp [h]

/-- From the vanishing Gram integral, `K = 0` almost everywhere. -/
lemma ae_zero_of_gram {K : I → I → ℝ} (hK : Measurable (Function.uncurry K))
    (hb : ∀ x y, |K x y| ≤ 1)
    (h0 : ∫ xs, gram K xs ^ 2 ∂(Measure.pi fun _ => (volume : Measure I)) = 0) :
    ∀ᵐ p ∂((volume : Measure I).prod volume), K p.1 p.2 = 0 := by
  set μ2 : Measure (Fin 2 → I) := Measure.pi fun _ => (volume : Measure I) with hμ2
  have hKp : ∀ (f : (Fin 2 → I) × I → I) (g : (Fin 2 → I) × I → I), Measurable f → Measurable g →
      Measurable fun q => K (f q) (g q) := fun f g hf hg =>
    show Measurable (Function.uncurry K ∘ fun q => (f q, g q)) from hK.comp (hf.prodMk hg)
  have hc0 : Measurable fun q : (Fin 2 → I) × I => q.1 0 := (measurable_pi_apply 0).comp measurable_fst
  have hc1 : Measurable fun q : (Fin 2 → I) × I => q.1 1 := (measurable_pi_apply 1).comp measurable_fst
  -- (1) the Gram kernel vanishes a.e.
  have hgm : Measurable (gram K) :=
    (((hKp _ _ hc0 measurable_snd).mul (hKp _ _ hc1 measurable_snd)).stronglyMeasurable
      |>.integral_prod_right').measurable
  have hgb : ∀ xs, |gram K xs| ≤ 1 := fun xs =>
    abs_integral_le_one fun y => mul_abs_le_one (hb _ _) (hb _ _)
  have hg0 := integral_sq_zero (μ := μ2) hgm hgb h0
  -- (2) for every measurable `B`, `∫_B K(·, y) = 0` for a.e. `y`
  have hrow : ∀ B : Set I, MeasurableSet B →
      ∀ᵐ y ∂(volume : Measure I), ∫ a, B.indicator (fun _ => (1 : ℝ)) a * K a y = 0 := by
    intro B hB
    have hind : ∀ (f : (Fin 2 → I) × I → I), Measurable f →
        Measurable fun q => B.indicator (fun _ => (1 : ℝ)) (f q) := fun f hf =>
      (measurable_const.indicator hB).comp hf
    set F : (Fin 2 → I) × I → ℝ := fun q =>
      ∏ i, (B.indicator (fun _ => (1 : ℝ)) (q.1 i) * K (q.1 i) q.2) with hF
    have hFm : Measurable F := Finset.measurable_prod _ fun i _ =>
      (hind _ ((measurable_pi_apply i).comp measurable_fst)).mul
        (hKp _ _ ((measurable_pi_apply i).comp measurable_fst) measurable_snd)
    have hFi : Integrable F (μ2.prod volume) :=
      Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs, hF, Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ =>
          mul_abs_le_one (abs_indicator_le_one _ _) (hb _ _))
    have hJ1 : ∫ q, F q ∂(μ2.prod volume) = 0 := by
      rw [integral_prod _ hFi]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hg0] with xs hxs
      simp only [hF, Fin.prod_univ_two]
      have : ∀ y, B.indicator (fun _ => (1 : ℝ)) (xs 0) * K (xs 0) y *
          (B.indicator (fun _ => (1 : ℝ)) (xs 1) * K (xs 1) y) =
          (B.indicator (fun _ => (1 : ℝ)) (xs 0) * B.indicator (fun _ => (1 : ℝ)) (xs 1)) *
            (K (xs 0) y * K (xs 1) y) := fun y => by ring
      simp_rw [this]
      rw [integral_const_mul]
      simp only [gram] at hxs
      rw [hxs, mul_zero]
      rfl
    rw [integral_prod_symm _ hFi] at hJ1
    have hJ2 : ∀ y, ∫ xs, F (xs, y) ∂μ2 = (∫ a, B.indicator (fun _ => (1 : ℝ)) a * K a y) ^ 2 := by
      intro y
      simp only [hF]
      rw [integral_fintype_prod_eq_pow (fun a => B.indicator (fun _ => (1 : ℝ)) a * K a y),
        Fintype.card_fin]
    simp_rw [hJ2] at hJ1
    have hhm : Measurable fun y => ∫ a, B.indicator (fun _ => (1 : ℝ)) a * K a y :=
      (((measurable_const.indicator hB).comp measurable_fst).mul hK).stronglyMeasurable
        |>.integral_prod_left'.measurable
    exact integral_sq_zero hhm (fun y => abs_integral_le_one fun a =>
      mul_abs_le_one (abs_indicator_le_one _ _) (hb _ _)) hJ1
  -- (3) rectangles
  refine ae_zero_of_rect (K := fun p => K p.1 p.2) hK (fun p => hb _ _) fun s hs t ht => ?_
  have hG : Measurable fun p : I × I => t.indicator (fun _ => (1 : ℝ)) p.2 *
      (s.indicator (fun _ => (1 : ℝ)) p.1 * K p.1 p.2) :=
    ((measurable_const.indicator ht).comp measurable_snd).mul
      (((measurable_const.indicator hs).comp measurable_fst).mul hK)
  have hGi : Integrable (fun p : I × I => t.indicator (fun _ => (1 : ℝ)) p.2 *
      (s.indicator (fun _ => (1 : ℝ)) p.1 * K p.1 p.2)) ((volume : Measure I).prod volume) :=
    Integrable.of_bound hG.aestronglyMeasurable 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact mul_abs_le_one (abs_indicator_le_one _ _)
        (mul_abs_le_one (abs_indicator_le_one _ _) (hb _ _)))
  rw [← integral_indicator (hs.prod ht)]
  have : (s ×ˢ t).indicator (fun p : I × I => K p.1 p.2) = fun p =>
      t.indicator (fun _ => (1 : ℝ)) p.2 * (s.indicator (fun _ => (1 : ℝ)) p.1 * K p.1 p.2) := by
    funext p
    by_cases h1 : p.1 ∈ s <;> by_cases h2 : p.2 ∈ t <;>
      simp [Set.indicator, h1, h2, Set.mem_prod]
  rw [this, integral_prod_symm _ hGi]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hrow s hs] with y hy
  rw [integral_const_mul, hy, mul_zero]
  rfl

lemma o1_oask_sfk' : O₁.IsOASK ∧ O₁.IsSymmetryForcingK := by
  have hnn : ∀ U, IsDigraphon U → 0 ≤ ∫ x, GA U x ∂μ4 := by
    intro U hU
    rw [GA_eq_GB, ← tb_univ_eq, tb_univ_gram (antiP_meas hU) (antiP_bound hU)]
    exact integral_nonneg fun xs => sq_nonneg _
  refine ⟨fun U hU => ?_, fun U hU heq => ?_⟩
  · rw [t_O₁_eq hU]; linarith [hnn U hU]
  · have h0 : ∫ x, GA U x ∂μ4 = 0 := by rw [t_O₁_eq hU] at heq; linarith
    rw [GA_eq_GB, ← tb_univ_eq, tb_univ_gram (antiP_meas hU) (antiP_bound hU)] at h0
    have := ae_zero_of_gram (antiP_meas hU) (antiP_bound hU) h0
    unfold AEEq
    filter_upwards [this] with p hp
    simp only [antiP, kTranspose] at hp ⊢
    linarith

end O1

/-! ## Pieces -/

lemma o1_oask_sfk : O₁.IsOASK ∧ O₁.IsSymmetryForcingK := o1_oask_sfk'

lemma cycle_osk {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u})
    (hA4 : LeeSidorenkoThm13Hyp.{u}) (hA9 : LovaszProp142aHyp) (D : OrientedGraph V)
    (hcyc : D.IsOrientedCycle) :
    D.IsOSK ↔ Even (Fintype.card V) ∧ D.IsAlternating := by
  have hconn := cycle_connected D hcyc
  obtain ⟨a, b, hab⟩ := cycle_exists_adj D hcyc
  have he := one_le_numArcs_of_adj D hab
  rw [Section1Aux.osk_char hA1 D hconn he]
  constructor
  · rintro ⟨hone, -, -⟩
    exact ⟨cycle_even_of_oneDirection D hcyc hone, alternating_of_oneDirection D hone⟩
  · rintro ⟨heven, halt⟩
    have hone := oneDirection_of_alternating D halt
    refine ⟨hone, cycle_selfConverse D hcyc halt, ?_⟩
    obtain ⟨A, hA⟩ := hone
    refine hA4 V D.underlying hconn
      ⟨s(a, b), (Section1Aux.underlying_adj_iff' D a b).mpr (Or.inl hab)⟩
      ⟨fun v => v ∈ A, fun u v huv => ?_⟩ (wnSymmFn_of_even_cycle hA9 D hcyc heven)
    rcases (Section1Aux.underlying_adj_iff' D _ _).mp huv with h | h
    · exact ⟨fun _ => (hA _ _ h).2, fun _ => (hA _ _ h).1⟩
    · exact ⟨fun hu => absurd hu (hA _ _ h).2, fun hv => by_contra fun h' => hv (hA _ _ h).1⟩

lemma cycle_oask {V : Type u} [Fintype V] (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) :
    D.IsOASK ↔ Nonempty (D.Iso O₁) := by
  refine ⟨cycle_oask_mp D hcyc, fun ⟨g⟩ => (isOASK_iso g).mpr o1_oask_sfk.1⟩

lemma o2_isOrientedCycle : O₂.IsOrientedCycle := by
  refine ⟨⟨⟨Equiv.refl _, fun {a b} => ?_⟩⟩, by simp⟩
  rw [Section1Aux.underlying_adj_iff']
  simp only [O₂, ofArcs]
  fin_cases a <;> fin_cases b <;> decide

lemma o2_alternating : O₂.IsAlternating := by
  intro v
  simp only [O₂, ofArcs]
  fin_cases v <;> decide

lemma o2_connected : O₂.IsConnected := cycle_connected O₂ o2_isOrientedCycle

lemma o2_not_acyclic : ¬ O₂.underlying.IsAcyclic := cycle_not_acyclic O₂ o2_isOrientedCycle

/-! ## The results -/

theorem thm_1_1_kernel_proof (hA1 : LovaszProp544cHyp.{0}) (hA4 : LeeSidorenkoThm13Hyp.{0})
    (hA9 : LovaszProp142aHyp) :
    (O₁.IsOASK ∧ O₁.IsSymmetryForcingK) ∧ (O₂.IsOSK ∧ O₂.IsSymmetryForcingK) := by
  have h2 : O₂.IsOSK :=
    (cycle_osk hA1 hA4 hA9 O₂ o2_isOrientedCycle).mpr ⟨⟨2, by simp⟩, o2_alternating⟩
  exact ⟨o1_oask_sfk, h2, (Section1Aux.thm13k hA1 O₂ o2_connected h2).mpr o2_not_acyclic⟩

theorem thm_1_1_proof (hA1 : LovaszProp544cHyp.{0}) (hA4 : LeeSidorenkoThm13Hyp.{0})
    (hA9 : LovaszProp142aHyp) (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0})
    (hcpt : FHMZCompactHyp) :
    (O₁.IsOAS ∧ O₁.IsSymmetryForcing) ∧ (O₂.IsOS ∧ O₂.IsSymmetryForcing) := by
  obtain ⟨⟨a, b⟩, c, d⟩ := thm_1_1_kernel_proof hA1 hA4 hA9
  exact ⟨⟨(isOAS_iff_isOASK O₁).mpr a,
      (isSymmetryForcing_iff_isSymmetryForcingK h13 h18 hcpt O₁).mpr b⟩,
    (isOS_iff_isOSK O₂).mpr c, (isSymmetryForcing_iff_isSymmetryForcingK h13 h18 hcpt O₂).mpr d⟩

theorem thm_1_10_kernel_proof {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u})
    (D : OrientedGraph V) (hpath : D.IsOrientedPath) :
    (D.numArcs = 1 → D.IsOSK ∧ D.IsOASK) ∧
    (2 ≤ D.numArcs → ¬ D.IsOSK ∧ (D.IsOASK ↔ Nonempty (D.Iso dirPath3))) :=
  path_kernel hA1 D hpath

theorem thm_1_10_proof {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u})
    (D : OrientedGraph V) (hpath : D.IsOrientedPath) :
    (D.numArcs = 1 → D.IsOS ∧ D.IsOAS) ∧
    (2 ≤ D.numArcs → ¬ D.IsOS ∧ (D.IsOAS ↔ Nonempty (D.Iso dirPath3))) := by
  obtain ⟨k1, k2⟩ := path_kernel hA1 D hpath
  exact ⟨fun h => ⟨(isOS_iff_isOSK D).mpr (k1 h).1, (isOAS_iff_isOASK D).mpr (k1 h).2⟩,
    fun h => ⟨fun hD => (k2 h).1 ((isOS_iff_isOSK D).mp hD), (isOAS_iff_isOASK D).trans (k2 h).2⟩⟩

theorem thm_1_11_kernel_proof {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u})
    (hA4 : LeeSidorenkoThm13Hyp.{u}) (hA9 : LovaszProp142aHyp) (D : OrientedGraph V)
    (hcyc : D.IsOrientedCycle) :
    (D.IsOSK ↔ Even (Fintype.card V) ∧ D.IsAlternating) ∧ (D.IsOASK ↔ Nonempty (D.Iso O₁)) :=
  ⟨cycle_osk hA1 hA4 hA9 D hcyc, cycle_oask D hcyc⟩

theorem thm_1_11_proof {V : Type u} [Fintype V] (hA1 : LovaszProp544cHyp.{u})
    (hA4 : LeeSidorenkoThm13Hyp.{u}) (hA9 : LovaszProp142aHyp) (D : OrientedGraph V)
    (hcyc : D.IsOrientedCycle) :
    (D.IsOS ↔ Even (Fintype.card V) ∧ D.IsAlternating) ∧ (D.IsOAS ↔ Nonempty (D.Iso O₁)) :=
  ⟨(isOS_iff_isOSK D).trans (cycle_osk hA1 hA4 hA9 D hcyc),
    (isOAS_iff_isOASK D).trans (cycle_oask D hcyc)⟩

end S1Families

end NieWeiOrientedSidorenko
