import NieWeiOrientedSidorenko.Mixing

/-!
# Unconditional OS witnesses (K(ii) pass)

Auxiliary non-vacuity witnesses, none of which takes a literature hypothesis:

* `isWeaklyNorming_of_isNorming`, `isWeaklyNormingGraph_of_isNormingGraph`: norming implies
  weakly norming;
* `isWeaklyNorming_of_card_eq_one`, `isWeaklyNorming_K2`: a single edge is weakly norming
  (`t_bi(K₂, |W|) = ∫ |W|`); `isWeaklyNorming_K22`: so is `K_{2,2}`;
* `isWeaklyNormingGraph_cycle4`: the 4-cycle is weakly norming;
* `dirEdge_isOSK`, `dirEdge_isOS`: the directed edge is oriented Sidorenko;
* `O₂_isAlternating`, `O₂_isOSK`, `O₂_isOS`: the alternating orientation `O₂` of `C₄` is
  oriented Sidorenko, all via the proved Theorem 4.1 (`OrientedGraph.thm_4_1`);
* `isStepSidorenko_cycle4`: the 4-cycle is step Sidorenko (`t(C₄, W^𝒫) = Q(W, W^𝒫, W^𝒫, W^𝒫)`
  by self-adjointness of step averaging, then Hölder for `K_{2,2}`); by-product
  `isStepForcing_cycle4`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace KWitness

section General

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A bipartite graph that is norming has at least one edge (for the empty edge set
`‖·‖_H ≡ 1`, which is not homogeneous). -/
lemma card_pos_of_isNorming {E : Finset (X × Y)} (hE : IsNorming E) : 0 < E.card := by
  rcases Nat.eq_zero_or_pos E.card with h0 | h0
  · exfalso
    have hk : IsKernel (fun _ _ : I => (0 : ℝ)) := Section2Aux.isKernel_const 0
    have h := hE.1 _ hk 0
    rw [Finset.card_eq_zero] at h0
    subst h0
    simp [hNorm, Section4Aux.tb_empty] at h
  · exact h0

/-- Monotonicity of `t_bi(H, ·)` on nonnegative kernels. -/
lemma tb_mono (E : Finset (X × Y)) {U V : I → I → ℝ} (hU : IsKernel U) (hV : IsKernel V)
    (h0 : ∀ x y, 0 ≤ U x y) (h1 : ∀ x y, U x y ≤ V x y) : tb E U ≤ tb E V :=
  Section2Aux.tBiDec_mono E (fun _ => U) (fun _ => V) (fun _ _ => hU) (fun _ _ => hV)
    (fun _ _ => h0) (fun _ _ => h1)

/-- For a kernel `U`, `‖U‖_{r(H)} = ‖|U|‖_H`. -/
lemma rNorm_eq_hNorm_abs (E : Finset (X × Y)) (U : I → I → ℝ) :
    rNorm E U = hNorm E (fun x y => |U x y|) := by
  unfold rNorm hNorm
  rw [abs_of_nonneg (Section2Aux.tb_nonneg E _ fun _ _ => abs_nonneg _)]

/-- **Norming implies weakly norming.** If `‖·‖_H` is a norm on kernels, so is `‖·‖_{r(H)}`:
`‖U + V‖_{r(H)} = ‖|U + V|‖_H ≤ ‖|U| + |V|‖_H ≤ ‖|U|‖_H + ‖|V|‖_H`, the first step by
monotonicity of `t_bi(H, ·)` on nonnegative kernels. -/
theorem isWeaklyNorming_of_isNorming {E : Finset (X × Y)} (hE : IsNorming E) :
    IsWeaklyNorming E := by
  have hne := card_pos_of_isNorming hE
  refine ⟨fun U _ c => Section2Aux.rNorm_smul E hne U c, fun U V hU hV => ?_,
    fun U hU h => Section2Aux.rNorm_posdef E hne U hU h⟩
  have hUa := Section2Aux.isKernel_abs hU
  have hVa := Section2Aux.isKernel_abs hV
  have hS := Section2Aux.isKernel_add hUa hVa
  have hsum0 : ∀ x y, 0 ≤ |U x y| + |V x y| := fun x y => by positivity
  have htri := hE.2.1 _ _ hUa hVa
  rw [← rNorm_eq_hNorm_abs, ← rNorm_eq_hNorm_abs] at htri
  refine Section2Aux.rNorm_le_of E hne _
    (add_nonneg (Section2Aux.rNorm_nonneg E U) (Section2Aux.rNorm_nonneg E V)) ?_
  calc tb E (fun x y => |U x y + V x y|)
      ≤ tb E (fun x y => |U x y| + |V x y|) :=
        tb_mono E (Section2Aux.isKernel_abs (Section2Aux.isKernel_add hU hV)) hS
          (fun _ _ => abs_nonneg _) (fun _ _ => abs_add_le _ _)
    _ = hNorm E (fun x y => |U x y| + |V x y|) ^ E.card := by
        rw [← Section2Aux.abs_tb_eq_hNorm_pow E hne,
          abs_of_nonneg (Section2Aux.tb_nonneg E _ hsum0)]
    _ ≤ (rNorm E U + rNorm E V) ^ E.card :=
        pow_le_pow_left₀ (Section2Aux.hNorm_nonneg E _) htri _

/-- A single edge `K₂` (any bipartite edge set with exactly one edge) is weakly norming:
`‖W‖_{r(K₂)} = t_bi(K₂, |W|) = ∫ |W|` is the `L¹` norm. -/
theorem isWeaklyNorming_of_card_eq_one {E : Finset (X × Y)} (hE : E.card = 1) :
    IsWeaklyNorming E := by
  have hne : 0 < E.card := by rw [hE]; norm_num
  refine ⟨fun U _ c => Section2Aux.rNorm_smul E hne U c, fun U V hU hV => ?_,
    fun U hU h => Section2Aux.rNorm_posdef E hne U hU h⟩
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 hE
  have hUa := Section2Aux.isKernel_abs hU
  have hVa := Section2Aux.isKernel_abs hV
  have hS := Section2Aux.isKernel_add hUa hVa
  have hr : ∀ W : I → I → ℝ, rNorm {p} W = tb {p} (fun x y => |W x y|) := fun W => by
    rw [Section2Aux.tb_abs_eq _ hne, hE, pow_one]
  rw [hr, hr, hr]
  have hadd : tb {p} (fun x y => |U x y| + |V x y|) =
      tb {p} (fun x y => |U x y|) + tb {p} (fun x y => |V x y|) := by
    have iU := Section2Aux.integrable_prod {p} (fun _ => fun x y => |U x y|) (fun _ _ => hUa)
    have iV := Section2Aux.integrable_prod {p} (fun _ => fun x y => |V x y|) (fun _ _ => hVa)
    simp only [Finset.prod_singleton] at iU iV
    simp only [tb, tBi, Finset.prod_singleton]
    exact integral_add iU iV
  rw [← hadd]
  exact tb_mono _ (Section2Aux.isKernel_abs (Section2Aux.isKernel_add hU hV)) hS
    (fun _ _ => abs_nonneg _) (fun _ _ => abs_add_le _ _)

/-- The single edge `K₂` (bipartition `{0} ∪ {0}`, `Fin 1 × Fin 1`) is weakly norming. -/
theorem isWeaklyNorming_K2 : IsWeaklyNorming (Finset.univ : Finset (Fin 1 × Fin 1)) :=
  isWeaklyNorming_of_card_eq_one (by simp)

/-- `C₄ = K_{2,2}` with its bipartition into two sides of size two is weakly norming (from the
proved norming witness `Witnesses.isNorming_K22`). -/
theorem isWeaklyNorming_K22 : IsWeaklyNorming (Finset.univ : Finset (Fin 2 × Fin 2)) :=
  isWeaklyNorming_of_isNorming Witnesses.isNorming_K22

end General

section GraphLevel

variable {V : Type*} [Fintype V]

/-- **Norming graphs are weakly norming** (full-kernel convention): the bipartition witnessing
`IsNormingGraph H` also witnesses `IsWeaklyNormingGraph H`. -/
theorem isWeaklyNormingGraph_of_isNormingGraph {H : SimpleGraph V} (hH : IsNormingGraph H) :
    IsWeaklyNormingGraph H := by
  obtain ⟨s, hs, hN⟩ := hH
  let _ := Classical.decPred s
  exact ⟨s, hs, isWeaklyNorming_of_isNorming hN⟩

end GraphLevel

/-- **Target 2.** The 4-cycle `cycleGraph 4` is weakly norming, unconditionally (from the proved
norming witness `Witnesses.isNormingGraph_cycle4`). -/
theorem isWeaklyNormingGraph_cycle4 : IsWeaklyNormingGraph (SimpleGraph.cycleGraph 4) :=
  isWeaklyNormingGraph_of_isNormingGraph Witnesses.isNormingGraph_cycle4

/-! ## Target 1: the directed edge -/

open OrientedGraph

/-- The source side `{0}` of the directed edge `0 → 1`. -/
def edgeSide : Fin 2 → Prop := fun v => v = 0

/-- The only arc of the directed edge is `0 → 1`. -/
lemma dirEdge_adj (u v : Fin 2) : dirEdge.Adj u v ↔ u = 0 ∧ v = 1 := by
  simp [dirEdge, ofArcs]

/-- Every arc of the directed edge goes from the side `{0}` to its complement. -/
lemma dirEdge_arcs_side : ∀ u v, dirEdge.Adj u v → edgeSide u ∧ ¬ edgeSide v := by
  intro u v h
  rw [dirEdge_adj] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, by simp [edgeSide]⟩

/-- For the bipartition `{0} ∪ {1}`, the underlying graph of the directed edge has exactly one
bipartite edge. -/
lemma card_sideEdges_dirEdge :
    (letI := Classical.decPred edgeSide; (sideEdges dirEdge.underlying edgeSide).card) = 1 := by
  let _ := Classical.decPred edgeSide
  show (sideEdges dirEdge.underlying edgeSide).card = 1
  rw [Finset.card_eq_one]
  refine ⟨(⟨0, rfl⟩, ⟨1, by simp [edgeSide]⟩), ?_⟩
  ext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [Section1Aux.mem_sideEdges, Finset.mem_singleton]
  simp only [edgeSide] at ha hb
  subst ha
  have hb1 : b = 1 := by revert b; decide
  subst hb1
  simp only [underlying, SimpleGraph.fromRel_adj, dirEdge_adj, iff_true]
  decide

/-- Hypothesis (c) of Theorem 4.1 for the directed edge: all arcs go from `{0}` to `{1}`, and
the underlying single edge `K₂` is weakly norming for this bipartition. -/
lemma dirEdge_hc : ∃ s : Fin 2 → Prop, (∀ u v, dirEdge.Adj u v → s u ∧ ¬ s v) ∧
    letI := Classical.decPred s
    IsWeaklyNorming (sideEdges dirEdge.underlying s) := by
  let _ := Classical.decPred edgeSide
  exact ⟨edgeSide, dirEdge_arcs_side, KWitness.isWeaklyNorming_of_card_eq_one card_sideEdges_dirEdge⟩

/-- The directed edge is homomorphic to a directed edge (by the identity). -/
lemma dirEdge_homToDirEdge : dirEdge.HomToDirEdge :=
  ⟨id, fun u v h => (dirEdge_adj u v).1 h⟩

/-- The directed edge is self-converse: the swap `0 ↔ 1` is an isomorphism `D ≅ D^T`. -/
lemma dirEdge_isSelfConverse : dirEdge.IsSelfConverse :=
  ⟨⟨Equiv.swap 0 1, fun u v => by
    simp only [transpose, dirEdge_adj]
    revert u v; decide⟩⟩

/-- **Target 1.** The directed edge `0 → 1` is oriented Sidorenko in digraphon form,
unconditionally: Theorem 4.1 (`thm_4_1`) with (a) the identity homomorphism, (b) the swap
`0 ↔ 1`, (c) the single edge `K₂`, weakly norming as `‖W‖_{r(K₂)} = ∫ |W|`. -/
theorem dirEdge_isOSK : dirEdge.IsOSK :=
  thm_4_1 dirEdge dirEdge_homToDirEdge dirEdge_isSelfConverse dirEdge_hc

/-- **Target 1, finite form.** The directed edge is oriented Sidorenko for all finite hosts
(Definition 1), via the proved bridge `isOS_iff_isOSK`. -/
theorem dirEdge_isOS : dirEdge.IsOS :=
  (isOS_iff_isOSK dirEdge).2 dirEdge_isOSK

/-! ## Target 3: the alternating orientation `O₂` of `C₄` -/

/-- The arcs of `O₂` are `1→0, 1→2, 3→2, 3→0`. -/
lemma O₂_adj (u v : Fin 4) : O₂.Adj u v ↔ (u, v) ∈
    ({(1, 0), (1, 2), (3, 2), (3, 0)} : Finset (Fin 4 × Fin 4)) := Iff.rfl

/-- `O₂` is an alternating orientation: every vertex is a source or a sink. -/
theorem O₂_isAlternating : O₂.IsAlternating := by
  intro v
  simp only [O₂_adj]
  revert v; decide

/-- The underlying graph of `O₂` is the 4-cycle `0 - 1 - 2 - 3 - 0`. -/
lemma O₂_underlying : O₂.underlying = SimpleGraph.cycleGraph 4 := by
  ext u v
  simp only [underlying, SimpleGraph.fromRel_adj, O₂_adj, SimpleGraph.cycleGraph_adj]
  revert u v; decide

/-- The odd side `{1, 3}` of `C₄`: the sources of `O₂`. -/
def oddSide : Fin 4 → Prop := fun v => v.val % 2 = 1

/-- Every arc of `O₂` goes from `{1, 3}` to `{0, 2}`. -/
lemma O₂_arcs_side : ∀ u v, O₂.Adj u v → oddSide u ∧ ¬ oddSide v := by
  intro u v h
  rw [O₂_adj] at h
  unfold oddSide
  revert u v; decide

/-- The odd side `{1, 3}` has two vertices. -/
lemma card_oddSide4 :
    (letI := Classical.decPred oddSide; Fintype.card {v // oddSide v}) = 2 := by
  have : Fintype.card {v : Fin 4 // v.val % 2 = 1} = 2 := by decide
  convert this; rfl

/-- The complement `{0, 2}` of the odd side has two vertices. -/
lemma card_evenSide4 :
    (letI := Classical.decPred oddSide; Fintype.card {v // ¬ oddSide v}) = 2 := by
  have : Fintype.card {v : Fin 4 // ¬ v.val % 2 = 1} = 2 := by decide
  convert this; rfl

/-- For the bipartition `{1, 3} ∪ {0, 2}`, every pair (odd, even) is an edge of `C₄`. -/
lemma sideEdges_cycle4_odd :
    (letI := Classical.decPred oddSide;
      sideEdges (SimpleGraph.cycleGraph 4) oddSide = Finset.univ) := by
  let _ := Classical.decPred oddSide
  ext p
  rw [Section1Aux.mem_sideEdges]
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  simp only [oddSide] at ha hb ⊢
  rw [SimpleGraph.cycleGraph_adj]
  revert a b; decide

/-- `C₄` with the bipartition `{1, 3} ∪ {0, 2}` is norming (it is `K_{2,2}`, `isNorming_K22`). -/
lemma isNorming_cycle4_odd :
    letI := Classical.decPred oddSide
    IsNorming (sideEdges (SimpleGraph.cycleGraph 4) oddSide) := by
  let _ := Classical.decPred oddSide
  show IsNorming (sideEdges (SimpleGraph.cycleGraph 4) oddSide)
  rw [sideEdges_cycle4_odd]
  set e1 : Fin 2 ≃ {v // oddSide v} := (Fintype.equivFinOfCardEq card_oddSide4).symm
  set e2 : Fin 2 ≃ {v // ¬ oddSide v} := (Fintype.equivFinOfCardEq card_evenSide4).symm
  rw [← Finset.map_univ_equiv (e1.prodCongr e2), Witnesses.isNorming_map_equiv]
  exact Witnesses.isNorming_K22

/-- Hypothesis (c) of Theorem 4.1 for `O₂`: all arcs go from `{1, 3}` to `{0, 2}`, and
`\bar O₂ = C₄` is weakly norming for this bipartition. -/
lemma O₂_hc : ∃ s : Fin 4 → Prop, (∀ u v, O₂.Adj u v → s u ∧ ¬ s v) ∧
    letI := Classical.decPred s
    IsWeaklyNorming (sideEdges O₂.underlying s) := by
  refine ⟨oddSide, O₂_arcs_side, ?_⟩
  let _ := Classical.decPred oddSide
  rw [O₂_underlying]
  exact KWitness.isWeaklyNorming_of_isNorming isNorming_cycle4_odd

/-- `O₂` is homomorphic to a directed edge (`{1, 3} ↦ 0`, `{0, 2} ↦ 1`). -/
lemma O₂_homToDirEdge : O₂.HomToDirEdge := by
  refine ⟨fun v => if v.val % 2 = 1 then 0 else 1, fun u v h => ?_⟩
  rw [O₂_adj] at h
  revert u v; decide

/-- `O₂` is self-converse: `v ↦ v + 1` is an isomorphism `O₂ ≅ O₂^T`. -/
lemma O₂_isSelfConverse : O₂.IsSelfConverse :=
  ⟨⟨Equiv.addRight 1, fun u v => by
    simp only [transpose, O₂_adj, Equiv.coe_addRight]
    revert u v; decide⟩⟩

/-- **Target 3.** The alternating orientation `O₂` of `C₄` is oriented Sidorenko in digraphon
form, unconditionally: Theorem 4.1 (`thm_4_1`) with (a) `{1, 3} ↦ 0`, `{0, 2} ↦ 1`,
(b) `v ↦ v + 1`, (c) `C₄ = K_{2,2}` weakly norming for the bipartition `{1, 3} ∪ {0, 2}`
(norming, `Witnesses.isNorming_K22`, hence weakly norming). -/
theorem O₂_isOSK : O₂.IsOSK :=
  thm_4_1 O₂ O₂_homToDirEdge O₂_isSelfConverse O₂_hc

/-- **Target 3, finite form.** `O₂` is oriented Sidorenko for all finite hosts (Definition 1),
via the proved bridge `isOS_iff_isOSK`; this is the OS half of Theorem 1.1 without its
literature hypotheses. -/
theorem O₂_isOS : O₂.IsOS :=
  (isOS_iff_isOSK O₂).2 O₂_isOSK

/-! ## Target 4: `C₄` is step Sidorenko -/

section StepC4

open Witnesses

/-- `f` is constant on every cell `P_i × P_j` of the partition. -/
def IsCellConst (P : PosPartition (volume : Measure I)) (f : I → I → ℝ) : Prop :=
  ∀ i j x x' y y', x ∈ P.part i → x' ∈ P.part i → y ∈ P.part j → y' ∈ P.part j →
    f x y = f x' y'

/-- A step average is constant on every cell. -/
lemma isCellConst_stepAvg (P : PosPartition (volume : Measure I)) (U : I → I → ℝ) :
    IsCellConst P (stepAvg P U) := by
  intro i j x x' y y' hx hx' hy hy'
  rw [S1CutDist.stepAvg_eq_of_mem P U hx hy, S1CutDist.stepAvg_eq_of_mem P U hx' hy']

/-- `G_{b,c,d}(x, y) = ∫ b(x, y') c(x', y) d(x', y') dx' dy'`. -/
noncomputable def Gk (b c d : I → I → ℝ) (x y : I) : ℝ :=
  ∫ t, b x t.2 * c t.1 y * d t.1 t.2 ∂ν

/-- `G_{b,c,d}` is a (bounded measurable) kernel. -/
lemma isKernel_Gk {b c d : I → I → ℝ} (hb : IsKernel b) (hc : IsKernel c) (hd : IsKernel d) :
    IsKernel (Gk b c d) := by
  obtain ⟨hmb, B, hB⟩ := hb
  obtain ⟨hmc, C, hC⟩ := hc
  obtain ⟨hmd, D, hD⟩ := hd
  refine ⟨?_, B * C * D, fun x y => ?_⟩
  · have hm : Measurable (fun r : (I × I) × (I × I) => b r.1.1 r.2.2 * c r.2.1 r.1.2 *
        d r.2.1 r.2.2) :=
      ((S1CutDist.meas_app hmb measurable_fst.fst measurable_snd.snd).mul
        (S1CutDist.meas_app hmc measurable_snd.fst measurable_fst.snd)).mul
        (S1CutDist.meas_app hmd measurable_snd.fst measurable_snd.snd)
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  · have := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun t : I × I => b x t.2 * c t.1 y * d t.1 t.2) (C := B * C * D)
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]
        exact abs_mul_le_of (abs_mul_le_of (hB _ _) (hC _ _)) (hD _ _))
    simpa [Gk] using this

/-- `G_{b,c,d}` is cell-constant when `b` and `c` are. -/
lemma isCellConst_Gk {P : PosPartition (volume : Measure I)} {b c : I → I → ℝ}
    (hb : IsCellConst P b) (hc : IsCellConst P c) (d : I → I → ℝ) :
    IsCellConst P (Gk b c d) := by
  intro i j x x' y y' hx hx' hy hy'
  unfold Gk
  congr 1; funext t
  obtain ⟨k, hk⟩ := S1CutDist.exists_part P t.2
  obtain ⟨l, hl⟩ := S1CutDist.exists_part P t.1
  rw [hb i k x x' t.2 t.2 hx hx' hk hk, hc l j t.1 t.1 y y' hl hl hy hy']

/-- Fubini: `Q(a, b, c, d) = ∫ a · G_{b,c,d}`. -/
lemma Q_eq_integral_Gk {a b c d : I → I → ℝ} (ha : IsKernel a) (hb : IsKernel b)
    (hc : IsKernel c) (hd : IsKernel d) :
    Q a b c d = ∫ q, a q.1 q.2 * Gk b c d q.1 q.2 ∂ν := by
  obtain ⟨hma, A, hA⟩ := ha
  obtain ⟨hmb, B, hB⟩ := hb
  obtain ⟨hmc, C, hC⟩ := hc
  obtain ⟨hmd, D, hD⟩ := hd
  set H : I × I → I × I → ℝ := fun r s => a s.1 r.1 * b s.1 r.2 * (c s.2 r.1 * d s.2 r.2)
    with hH
  set K : I × I → I × I → ℝ := fun q t => a q.1 q.2 * (b q.1 t.2 * c t.1 q.2 * d t.1 t.2)
    with hK
  have h1 : ∀ r : I × I, kk2 a b r.1 r.2 * kk2 c d r.1 r.2 = ∫ s, H r s ∂ν := fun r => by
    simp only [hH, kk2]
    rw [← integral_prod_mul (fun x => a x r.1 * b x r.2) (fun x => c x r.1 * d x r.2)]
  have h2 : ∀ q : I × I, a q.1 q.2 * Gk b c d q.1 q.2 = ∫ t, K q t ∂ν := fun q => by
    simp only [hK, Gk]; exact (integral_const_mul _ _).symm
  have hHm : Measurable (fun w : (I × I) × (I × I) => H w.1 w.2) :=
    ((S1CutDist.meas_app hma measurable_snd.fst measurable_fst.fst).mul
      (S1CutDist.meas_app hmb measurable_snd.fst measurable_fst.snd)).mul
      ((S1CutDist.meas_app hmc measurable_snd.snd measurable_fst.fst).mul
      (S1CutDist.meas_app hmd measurable_snd.snd measurable_fst.snd))
  have hKm : Measurable (fun w : (I × I) × (I × I) => K w.1 w.2) :=
    (S1CutDist.meas_app hma measurable_fst.fst measurable_fst.snd).mul
      (((S1CutDist.meas_app hmb measurable_fst.fst measurable_snd.snd).mul
      (S1CutDist.meas_app hmc measurable_snd.fst measurable_fst.snd)).mul
      (S1CutDist.meas_app hmd measurable_snd.fst measurable_snd.snd))
  have hHi : Integrable (fun w : (I × I) × (I × I) => H w.1 w.2) (ν.prod ν) :=
    S1CutDist.integrable_bdd hHm (A * B * (C * D)) fun w =>
      abs_mul_le_of (abs_mul_le_of (hA _ _) (hB _ _)) (abs_mul_le_of (hC _ _) (hD _ _))
  have hKi : Integrable (fun w : (I × I) × (I × I) => K w.1 w.2) (ν.prod ν) :=
    S1CutDist.integrable_bdd hKm (A * (B * C * D)) fun w =>
      abs_mul_le_of (hA _ _) (abs_mul_le_of (abs_mul_le_of (hB _ _) (hC _ _)) (hD _ _))
  have e1 : ∫ r, ∫ s, H r s ∂ν ∂ν = ∫ w, H w.1 w.2 ∂(ν.prod ν) :=
    (integral_prod (fun w : (I × I) × (I × I) => H w.1 w.2) hHi).symm
  have e2 : ∫ q, ∫ t, K q t ∂ν ∂ν = ∫ w, K w.1 w.2 ∂(ν.prod ν) :=
    (integral_prod (fun w : (I × I) × (I × I) => K w.1 w.2) hKi).symm
  have hφ : MeasurePreserving (fun w : (I × I) × (I × I) => ((w.2.1, w.1.1), (w.2.2, w.1.2)))
      (ν.prod ν) (ν.prod ν) := by
    have := (Section2Aux.mp_prodProdProdComm (volume : Measure I) (volume : Measure I)
      (volume : Measure I) (volume : Measure I)).comp (Measure.measurePreserving_swap
        (μ := ν) (ν := ν))
    exact this
  have e3 : ∫ w, K w.1 w.2 ∂(ν.prod ν) = ∫ w, H w.1 w.2 ∂(ν.prod ν) := by
    conv_lhs => rw [← hφ.map_eq]
    rw [integral_map hφ.measurable.aemeasurable hKm.aestronglyMeasurable]
    congr 1; funext w; simp only [hH, hK]; ring
  unfold Q
  simp_rw [h1, h2]
  rw [e1, e2, e3]

/-- Step averaging is self-adjoint against a cell-constant kernel:
`∫ W^𝒫 · G = ∫ W · G`. -/
lemma integral_stepAvg_mul (P : PosPartition (volume : Measure I)) {a G : I → I → ℝ}
    (ha : IsKernel a) (hG : IsKernel G) (hGc : IsCellConst P G) :
    ∫ q, stepAvg P a q.1 q.2 * G q.1 q.2 ∂ν = ∫ q, a q.1 q.2 * G q.1 q.2 ∂ν := by
  have e : ∀ x y, stepAvg P a x y * G x y = stepAvg P (fun x y => a x y * G x y) x y := by
    intro x y
    obtain ⟨i, hi⟩ := S1CutDist.exists_part P x
    obtain ⟨j, hj⟩ := S1CutDist.exists_part P y
    rw [S1CutDist.stepAvg_eq_of_mem P _ hi hj, S1CutDist.stepAvg_eq_of_mem P _ hi hj]
    unfold S1CutDist.avgV
    have : ∫ p in P.part i ×ˢ P.part j, a p.1 p.2 * G p.1 p.2 ∂((volume : Measure I).prod volume)
        = ∫ p in P.part i ×ˢ P.part j, a p.1 p.2 * G x y ∂((volume : Measure I).prod volume) :=
      setIntegral_congr_fun ((P.measurableSet_part i).prod (P.measurableSet_part j))
        fun p hp => by rw [hGc i j p.1 x p.2 y hp.1 hi hp.2 hj]
    rw [this, integral_mul_const]; ring
  have hbk : S1CutDist.BK (fun x y => a x y * G x y) := by
    obtain ⟨hma, A, hA⟩ := ha
    obtain ⟨hmG, B, hB⟩ := hG
    exact ⟨hma.mul hmG, A * B, fun x y => abs_mul_le_of (hA x y) (hB x y)⟩
  simp_rw [e]
  exact S1CutDist.integral_stepAvg P hbk

/-- The step average of a kernel is a kernel. -/
lemma isKernel_stepAvg (P : PosPartition (volume : Measure I)) {U : I → I → ℝ}
    (hU : IsKernel U) : IsKernel (stepAvg P U) :=
  S1CutDist.bk_stepAvg P hU

/-- The step average does not increase `t_bi(K_{2,2}, ·)`: with `Q = W^𝒫`,
`t(Q) = Q(Q,Q,Q,Q) = Q(W,Q,Q,Q) ≤ ‖W‖ ‖Q‖³` (Hölder for `K_{2,2}`), so `‖Q‖ ≤ ‖W‖`. -/
lemma tb_stepAvg_le (P : PosPartition (volume : Measure I)) {U : I → I → ℝ} (hU : IsKernel U) :
    tb E4 (stepAvg P U) ≤ tb E4 U := by
  set W := stepAvg P U with hWdef
  have hW := isKernel_stepAvg P hU
  have hWc := isCellConst_stepAvg P U
  have hkey : tb E4 W = Q U W W W := by
    rw [tb_eq_Q hW, Q_eq_integral_Gk hW hW hW hW, Q_eq_integral_Gk hU hW hW hW,
      integral_stepAvg_mul P hU (isKernel_Gk hW hW hW) (isCellConst_Gk hWc hWc W)]
  have hH := abs_Q_le hU hW hW hW
  rw [← hkey] at hH
  have h0 : 0 ≤ tb E4 W := tb_nonneg hW
  rw [abs_of_nonneg h0, tb_eq_pow hW] at hH
  set n := hNorm E4 W
  set m := hNorm E4 U
  have hn0 : 0 ≤ n := Section2Aux.hNorm_nonneg E4 W
  have hm0 : 0 ≤ m := Section2Aux.hNorm_nonneg E4 U
  have hnm : n ≤ m := by
    rcases hn0.lt_or_eq with hpos | hzero
    · by_contra hlt'
      have hlt := not_le.1 hlt'
      have : m * n * n * n < n ^ 4 := by
        have h3 : 0 < n * n * n := by positivity
        nlinarith
      linarith
    · rw [← hzero]; exact hm0
  rw [tb_eq_pow hW, tb_eq_pow hU]
  exact pow_le_pow_left₀ hn0 hnm 4

/-- For a symmetric kernel, `t(C₄, K) = t_bi(K_{2,2}, K)`. -/
lemma tU_cycle4_eq_tb {K : I → I → ℝ} (hK : ∀ x y, K x y = K y x) :
    tU (SimpleGraph.cycleGraph 4) K = tb E4 K := by
  let _ := Classical.decPred evenSide
  rw [S1CutDist.tU_eq_tb _ evenSide isBipartition_evenSide hK, sideEdges_cycle4]
  set e1 : Fin 2 ≃ {v // evenSide v} := (Fintype.equivFinOfCardEq card_evenSide).symm
  set e2 : Fin 2 ≃ {v // ¬ evenSide v} := (Fintype.equivFinOfCardEq card_oddSide).symm
  rw [← Finset.map_univ_equiv (e1.prodCongr e2), Section1Aux.tb_map_equiv]

/-- **Target 4.** The 4-cycle is step Sidorenko, unconditionally: `t(C₄, W^𝒫) ≤ t(C₄, W)` for
every graphon `W` and every finite partition `𝒫` of `[0,1]` into parts of positive measure. -/
theorem isStepSidorenko_cycle4 : IsStepSidorenko (SimpleGraph.cycleGraph 4) := by
  intro U hU P
  obtain ⟨hS, hae⟩ := Section1Aux.symmVersion_spec hU
  rw [Section1Aux.stepAvg_congr_ae P hae, Section1Aux.tU_congr_ae _ hae,
    tU_cycle4_eq_tb (S1CutDist.stepAvg_symm P hS.2), tU_cycle4_eq_tb hS.2]
  exact tb_stepAvg_le P (Section1Aux.isKernel_of_isDigraphon hS.1)

/-- `C₄` with the parity bipartition `{0, 2} ∪ {1, 3}` is weakly norming. -/
lemma isWeaklyNorming_cycle4_even :
    letI := Classical.decPred evenSide
    IsWeaklyNorming (sideEdges (SimpleGraph.cycleGraph 4) evenSide) := by
  let _ := Classical.decPred evenSide
  refine isWeaklyNorming_of_isNorming ?_
  show IsNorming (sideEdges (SimpleGraph.cycleGraph 4) evenSide)
  rw [sideEdges_cycle4]
  set e1 : Fin 2 ≃ {v // evenSide v} := (Fintype.equivFinOfCardEq card_evenSide).symm
  set e2 : Fin 2 ≃ {v // ¬ evenSide v} := (Fintype.equivFinOfCardEq card_oddSide).symm
  rw [← Finset.map_univ_equiv (e1.prodCongr e2), isNorming_map_equiv]
  exact isNorming_K22

/-- **By-product of target 4.** The 4-cycle is step forcing, unconditionally: from step
Sidorenko (`isStepSidorenko_cycle4`), weak norming and the cycle, by the proved
`S1CutDist.stepForcing_of_wn`. -/
theorem isStepForcing_cycle4 : IsStepForcing (SimpleGraph.cycleGraph 4) := by
  let _ := Classical.decPred evenSide
  have hcyc : ¬ (SimpleGraph.cycleGraph 4).IsAcyclic := by
    rw [← O₂_underlying]; exact S1Families.o2_not_acyclic
  exact S1CutDist.stepForcing_of_wn _ evenSide isBipartition_evenSide isWeaklyNorming_cycle4_even
    hcyc isStepSidorenko_cycle4

end StepC4

end KWitness

end NieWeiOrientedSidorenko
