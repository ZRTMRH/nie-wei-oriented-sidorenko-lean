import NieWeiOrientedSidorenko.Section1Aux
import NieWeiOrientedSidorenko.S1Bridges

/-!
# Proposition 1.12: symmetry-forcing implies OS or OAS

Kernel form first. If `D` is neither OS nor OAS, there are digraphons `W₋`, `W₊` with
`Δ(W₋) < 0 < Δ(W₊)`, `Δ(W) = t(D, W) - t(D, (W + Wᵀ)/2)`. Using a measure-preserving
`φ : [0,1] → [0,1]²` (`Section2Aux.exists_split`) we form block kernels
`blk K K'(x, y) = K'(φ₁ x, φ₁ y)` if `φ₂ x, φ₂ y ≤ 1/2`, and `K(φ₁ x, φ₁ y)` otherwise.
`blk K K` is a measure-preserving pull-back of `K` (same `Δ`), `blk K K'` is non-symmetric as
soon as `K` or `K'` is, and `blk` is affine in each slot. Two straight segments
`blk W₋ W₋ → blk W₊ W₋ → blk W₊ W₊` consist of non-symmetric digraphons; `Δ` is continuous
along them (the `L¹` bound `Section2Aux.abs_t_sub_le`), so the intermediate value theorem gives a
non-symmetric digraphon with `Δ = 0`, contradicting symmetry-forcing.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace S1P112

open OrientedGraph

section Kernel

variable {V : Type u} [Fintype V]

/-- The defect `Δ(W) = t(D, W) - t(D, (W + Wᵀ)/2)`. -/
noncomputable def gap (D : OrientedGraph V) (U : I → I → ℝ) : ℝ := t D U - t D (symmetrize U)

/-- `t(D, ·)` respects almost-everywhere equality of kernels. -/
lemma t_congr_ae (D : OrientedGraph V) {U U' : I → I → ℝ} (h : AEEq volume U U') :
    t D U = t D U' := by
  classical
  unfold t tDir
  apply integral_congr_ae
  have : ∀ p ∈ D.arcs, ∀ᵐ x ∂(Measure.pi fun _ : V => (volume : Measure I)),
      U (x p.1) (x p.2) = U' (x p.1) (x p.2) := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      intro he
      have hadj : D.Adj p.1 p.2 := by
        simpa [OrientedGraph.arcs] using hp
      rw [he] at hadj
      exact D.irrefl _ hadj
    exact (Section1Aux.measurePreserving_pair hne).quasiMeasurePreserving.ae h
  filter_upwards [(Filter.eventually_all_finset _).mpr this] with x hx
  exact Finset.prod_congr rfl hx

/-- A kernel symmetric a.e. has `Δ = 0`. -/
lemma gap_eq_zero_of_symm (D : OrientedGraph V) {U : I → I → ℝ}
    (h : AEEq volume U (kTranspose U)) : gap D U = 0 := by
  have : AEEq volume U (symmetrize U) := by
    unfold AEEq at *
    filter_upwards [h] with p hp
    simp only [symmetrize, kTranspose] at *
    linarith
  rw [gap, t_congr_ae D this, sub_self]

/-- `t(D, ·)` is invariant under pulling back along a measure-preserving `ψ`. -/
lemma t_comp (D : OrientedGraph V) {ψ : I → I} (hψ : MeasurePreserving ψ volume volume)
    {K : I → I → ℝ} (hK : Measurable (Function.uncurry K)) :
    t D (fun x y => K (ψ x) (ψ y)) = t D K := by
  classical
  unfold t tDir
  have hmp : MeasurePreserving (fun (a : V → I) (i : V) => ψ (a i))
      (Measure.pi fun _ : V => (volume : Measure I)) (Measure.pi fun _ : V => (volume : Measure I)) :=
    measurePreserving_pi _ _ (fun _ => hψ)
  have hmeas : Measurable fun y : V → I => ∏ p ∈ D.arcs, K (y p.1) (y p.2) :=
    Finset.measurable_prod _ fun p _ => hK.comp (Section2Aux.measurable_pair p)
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hmeas.aestronglyMeasurable]

/-- The segment `(1 - s) A + s B`. -/
noncomputable def seg (A B : I → I → ℝ) (s : ℝ) : I → I → ℝ := fun x y => (1 - s) * A x y + s * B x y

lemma isDigraphon_seg {A B : I → I → ℝ} (hA : IsDigraphon A) (hB : IsDigraphon B) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : IsDigraphon (seg A B s) := by
  refine ⟨?_, fun x y => ?_⟩
  · exact (hA.1.const_mul _).add (hB.1.const_mul _)
  · have h1 := hA.2 x y
    have h2 := hB.2 x y
    simp only [seg, Set.mem_Icc] at *
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, hs.1, hs.2]

lemma symmetrize_seg (A B : I → I → ℝ) (s : ℝ) :
    symmetrize (seg A B s) = seg (symmetrize A) (symmetrize B) s := by
  funext x y
  simp only [symmetrize, seg]
  ring

lemma seg_zero (A B : I → I → ℝ) : seg A B 0 = A := by
  funext x y; simp [seg]

lemma seg_one (A B : I → I → ℝ) : seg A B 1 = B := by
  funext x y; simp [seg]

/-- `|t(D, seg s) - t(D, seg s')| ≤ e(D) |s - s'|`. -/
lemma abs_t_seg_le (D : OrientedGraph V) {A B : I → I → ℝ} (hA : IsDigraphon A)
    (hB : IsDigraphon B) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hs' : s' ∈ Icc (0 : ℝ) 1) :
    |t D (seg A B s) - t D (seg A B s')| ≤ D.numArcs * |s - s'| := by
  refine (Section2Aux.abs_t_sub_le D _ _ (isDigraphon_seg hA hB hs)
    (isDigraphon_seg hA hB hs')).trans ?_
  gcongr
  have hb : ∀ q : I × I, ‖|seg A B s q.1 q.2 - seg A B s' q.1 q.2|‖ ≤ |s - s'| := by
    intro q
    rw [Real.norm_eq_abs, abs_abs]
    have : seg A B s q.1 q.2 - seg A B s' q.1 q.2 = (s - s') * (B q.1 q.2 - A q.1 q.2) := by
      simp only [seg]; ring
    rw [this, abs_mul]
    have h1 := hA.2 q.1 q.2
    have h2 := hB.2 q.1 q.2
    have : |B q.1 q.2 - A q.1 q.2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    calc |s - s'| * |B q.1 q.2 - A q.1 q.2| ≤ |s - s'| * 1 := by gcongr
      _ = |s - s'| := mul_one _
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure I).prod volume)
    (Eventually.of_forall hb)
  rw [probReal_univ, mul_one] at this
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ this)

lemma continuousOn_gap_seg (D : OrientedGraph V) {A B : I → I → ℝ} (hA : IsDigraphon A)
    (hB : IsDigraphon B) : ContinuousOn (fun s => gap D (seg A B s)) (Icc 0 1) := by
  have hA' := Section1Aux.isDigraphon_symmetrize hA
  have hB' := Section1Aux.isDigraphon_symmetrize hB
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      |gap D (seg A B s) - gap D (seg A B s')| ≤ (2 * D.numArcs) * |s - s'| := by
    intro s hs s' hs'
    have h1 := abs_t_seg_le D hA hB hs hs'
    have h2 := abs_t_seg_le D hA' hB' hs hs'
    simp only [gap, symmetrize_seg]
    calc _ = |(t D (seg A B s) - t D (seg A B s')) -
          (t D (seg (symmetrize A) (symmetrize B) s) -
            t D (seg (symmetrize A) (symmetrize B) s'))| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := by linarith
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨ε / (2 * D.numArcs + 1), by positivity, fun a ha hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  have hk := key a ha b hb
  have hC : (0 : ℝ) ≤ 2 * D.numArcs := by positivity
  calc _ ≤ (2 * D.numArcs) * |a - b| := hk
    _ ≤ (2 * D.numArcs + 1) * |a - b| := by nlinarith [abs_nonneg (a - b)]
    _ < (2 * D.numArcs + 1) * (ε / (2 * D.numArcs + 1)) := by gcongr
    _ = ε := by field_simp

/-- A segment of non-symmetric digraphons along which `Δ` changes sign contradicts
symmetry-forcing.
True only vacuously by design: the closing step of the proof by contradiction of Proposition
1.12 (tex l.649, l.676-678). -/
lemma seg_contra (D : OrientedGraph V) (hD : D.IsSymmetryForcingK) {A B : I → I → ℝ}
    (hA : IsDigraphon A) (hB : IsDigraphon B) (h0 : gap D A ≤ 0) (h1 : 0 ≤ gap D B)
    (hns : ∀ s ∈ Icc (0 : ℝ) 1, ¬ AEEq volume (seg A B s) (kTranspose (seg A B s))) : False := by
  have hivt := intermediate_value_Icc (zero_le_one' ℝ) (continuousOn_gap_seg D hA hB)
  have hmem : (0 : ℝ) ∈ Icc (gap D (seg A B 0)) (gap D (seg A B 1)) := by
    rw [seg_zero, seg_one]; exact ⟨h0, h1⟩
  obtain ⟨s, hs, hs0⟩ := hivt hmem
  apply hns s hs
  apply hD _ (isDigraphon_seg hA hB hs)
  simp only [gap] at hs0
  linarith

/-! ### The block kernels -/

/-- The lower half of `[0, 1]`. -/
def lo : Set I := {z | (z : ℝ) ≤ 1 / 2}

lemma measurableSet_lo : MeasurableSet lo :=
  measurableSet_le measurable_subtype_coe measurable_const

lemma volume_lo_ne_zero : (volume : Measure I) lo ≠ 0 := by
  have h : Section1Aux.ivl 0 (1 / 2) ⊆ lo := fun z hz => hz.2
  have hv := Section1Aux.volume_ivl (a := 0) (b := 1 / 2) le_rfl (by norm_num)
  intro h0
  have := measure_mono_null h h0
  rw [hv] at this
  norm_num at this

lemma volume_lo_compl_ne_zero : (volume : Measure I) loᶜ ≠ 0 := by
  have h : Section1Aux.ivl (3 / 4) 1 ⊆ loᶜ := fun z hz => by
    simp only [lo, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    have := hz.1; linarith
  have hv := Section1Aux.volume_ivl (a := 3 / 4) (b := 1) (by norm_num) le_rfl
  intro h0
  have := measure_mono_null h h0
  rw [hv] at this
  norm_num at this

open scoped Classical in
/-- `blk φ K K'`: `K'` on the block where both second coordinates of `φ` are in `lo`, `K`
elsewhere, read at the first coordinates. -/
noncomputable def blk (φ : I → I × I) (K K' : I → I → ℝ) : I → I → ℝ := fun x y =>
  if (φ x).2 ∈ lo ∧ (φ y).2 ∈ lo then K' (φ x).1 (φ y).1 else K (φ x).1 (φ y).1

lemma isDigraphon_blk {φ : I → I × I} (hφ : Measurable φ) {K K' : I → I → ℝ}
    (hK : IsDigraphon K) (hK' : IsDigraphon K') : IsDigraphon (blk φ K K') := by
  classical
  refine ⟨?_, fun x y => ?_⟩
  · have hS : MeasurableSet {p : I × I | (φ p.1).2 ∈ lo ∧ (φ p.2).2 ∈ lo} :=
      (measurableSet_lo.preimage (measurable_snd.comp (hφ.comp measurable_fst))).inter
        (measurableSet_lo.preimage (measurable_snd.comp (hφ.comp measurable_snd)))
    have hm : Measurable fun p : I × I => ((φ p.1).1, (φ p.2).1) :=
      (measurable_fst.comp (hφ.comp measurable_fst)).prodMk
        (measurable_fst.comp (hφ.comp measurable_snd))
    exact Measurable.ite hS (hK'.1.comp hm) (hK.1.comp hm)
  · simp only [blk]
    split_ifs
    · exact hK'.2 _ _
    · exact hK.2 _ _

lemma blk_self (φ : I → I × I) (K : I → I → ℝ) :
    blk φ K K = fun x y => K (φ x).1 (φ y).1 := by
  funext x y; simp [blk]

lemma seg_blk_left (φ : I → I × I) (A B K' : I → I → ℝ) (s : ℝ) :
    seg (blk φ A K') (blk φ B K') s = blk φ (seg A B s) K' := by
  funext x y
  simp only [seg, blk]
  split_ifs <;> ring

lemma seg_blk_right (φ : I → I × I) (K A B : I → I → ℝ) (s : ℝ) :
    seg (blk φ K A) (blk φ K B) s = blk φ K (seg A B s) := by
  funext x y
  simp only [seg, blk]
  split_ifs <;> ring

/-- If `F` reads `K` at the first coordinates of `φ` on a block of positive measure and `F` is
symmetric a.e., then `K` is symmetric a.e. -/
lemma symm_of_block {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    {S : Set I} (hS : MeasurableSet S) (hS0 : (volume : Measure I) S ≠ 0)
    {F K : I → I → ℝ} (hK : Measurable (Function.uncurry K))
    (hF : ∀ x y, (φ x).2 ∈ S → (φ y).2 ∈ S → F x y = K (φ x).1 (φ y).1)
    (hsym : AEEq volume F (kTranspose F)) : AEEq volume K (kTranspose K) := by
  unfold AEEq at *
  simp only [kTranspose] at *
  set E : Set (I × I) := {q | K q.1 q.2 ≠ K q.2 q.1} with hEdef
  have hKs : Measurable fun q : I × I => K q.2 q.1 := hK.comp measurable_swap
  have hE : MeasurableSet E := (measurableSet_eq_fun hK hKs).compl
  rw [ae_iff] at hsym ⊢
  change ((volume : Measure I).prod volume) E = 0
  -- the rearranged set
  set T' : Set ((I × I) × (I × I)) := {w | w.1.2 ∈ S ∧ w.2.2 ∈ S ∧ (w.1.1, w.2.1) ∈ E}
  have hR := Section2Aux.mp_prodProdProdComm (volume : Measure I) (volume : Measure I)
    (volume : Measure I) (volume : Measure I)
  have hpre : (fun w : (I × I) × (I × I) => ((w.1.1, w.2.1), (w.1.2, w.2.2))) ⁻¹'
      (E ×ˢ (S ×ˢ S)) = T' := by
    ext w; simp only [Set.mem_preimage, Set.mem_prod, T', Set.mem_ofPred_eq]; tauto
  have hmeasT : MeasurableSet (E ×ˢ (S ×ˢ S)) := hE.prod (hS.prod hS)
  have hT'eq : (((volume : Measure I).prod volume).prod ((volume : Measure I).prod volume)) T' =
      ((volume : Measure I).prod volume) E * ((volume : Measure I) S * (volume : Measure I) S) := by
    rw [← hpre, hR.measure_preimage hmeasT.nullMeasurableSet, Measure.prod_prod,
      Measure.prod_prod]
  have hφ2 : MeasurePreserving (Prod.map φ φ) ((volume : Measure I).prod volume)
      (((volume : Measure I).prod volume).prod ((volume : Measure I).prod volume)) := hφ.prod hφ
  have hT'meas : MeasurableSet T' := by
    rw [← hpre]; exact hR.measurable hmeasT
  have hsub : Prod.map φ φ ⁻¹' T' ⊆ {p : I × I | ¬ F p.1 p.2 = F p.2 p.1} := by
    rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
    simp only [Set.mem_ofPred_eq]
    rw [hF x y h1 h2, hF y x h2 h1]
    exact h3
  have hT0 : (((volume : Measure I).prod volume).prod ((volume : Measure I).prod volume)) T' = 0 := by
    rw [← hφ2.measure_preimage hT'meas.nullMeasurableSet]
    exact measure_mono_null hsub hsym
  rw [hT'eq] at hT0
  rcases mul_eq_zero.mp hT0 with h | h
  · exact h
  · exact absurd (mul_eq_zero.mp h) (by simp [hS0])

lemma not_symm_blk_right {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    {K K' : I → I → ℝ} (hK' : Measurable (Function.uncurry K'))
    (hns : ¬ AEEq volume K' (kTranspose K')) : ¬ AEEq volume (blk φ K K') (kTranspose (blk φ K K')) :=
  fun h => hns (symm_of_block hφ measurableSet_lo volume_lo_ne_zero hK'
    (fun x y hx hy => by simp [blk, hx, hy]) h)

lemma not_symm_blk_left {φ : I → I × I} (hφ : MeasurePreserving φ volume (volume.prod volume))
    {K K' : I → I → ℝ} (hK : Measurable (Function.uncurry K))
    (hns : ¬ AEEq volume K (kTranspose K)) : ¬ AEEq volume (blk φ K K') (kTranspose (blk φ K K')) :=
  fun h => hns (symm_of_block hφ measurableSet_lo.compl volume_lo_compl_ne_zero hK
    (fun x y hx hy => by simp only [Set.mem_compl_iff] at hx; simp [blk, hx]) h)

lemma gap_blk_self (D : OrientedGraph V) {φ : I → I × I}
    (hφ : MeasurePreserving φ volume (volume.prod volume)) {K : I → I → ℝ} (hK : IsDigraphon K) :
    gap D (blk φ K K) = gap D K := by
  have hψ : MeasurePreserving (fun x => (φ x).1) volume volume :=
    (measurePreserving_fst (μ := (volume : Measure I)) (ν := (volume : Measure I))).comp hφ
  rw [blk_self, gap, gap]
  have hs : symmetrize (fun x y => K (φ x).1 (φ y).1) =
      fun x y => symmetrize K (φ x).1 (φ y).1 := rfl
  rw [hs, t_comp D hψ hK.1, t_comp D hψ (Section1Aux.isDigraphon_symmetrize hK).1]

lemma not_symm_of_gap_ne (D : OrientedGraph V) {U : I → I → ℝ} (h : gap D U ≠ 0) :
    ¬ AEEq volume U (kTranspose U) := fun hs => h (gap_eq_zero_of_symm D hs)

/-- **Proposition 1.12**, kernel form. -/
theorem kernel_main (D : OrientedGraph V) (hD : D.IsSymmetryForcingK) :
    D.IsOSK ∨ D.IsOASK := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnOS, hnOAS⟩ := hcon
  simp only [IsOSK, IsOASK, not_forall, not_le] at hnOS hnOAS
  obtain ⟨Wm, hWm, hm⟩ := hnOS
  obtain ⟨Wp, hWp, hp⟩ := hnOAS
  have gm : gap D Wm < 0 := by simp only [gap]; linarith
  have gp : 0 < gap D Wp := by simp only [gap]; linarith
  have nsm := not_symm_of_gap_ne D gm.ne
  have nsp := not_symm_of_gap_ne D gp.ne'
  obtain ⟨φ, hφ⟩ := Section2Aux.exists_split
  have hφm := hφ.measurable
  rcases le_total 0 (gap D (blk φ Wp Wm)) with hM | hM
  · -- segment `blk Wm Wm → blk Wp Wm`
    refine seg_contra D hD (isDigraphon_blk hφm hWm hWm) (isDigraphon_blk hφm hWp hWm) ?_ hM ?_
    · rw [gap_blk_self D hφ hWm]; exact gm.le
    · intro s _
      rw [seg_blk_left]
      exact not_symm_blk_right hφ hWm.1 nsm
  · -- segment `blk Wp Wm → blk Wp Wp`
    refine seg_contra D hD (isDigraphon_blk hφm hWp hWm) (isDigraphon_blk hφm hWp hWp) hM ?_ ?_
    · rw [gap_blk_self D hφ hWp]; exact gp.le
    · intro s _
      rw [seg_blk_right]
      exact not_symm_blk_left hφ hWp.1 nsp

end Kernel

/-! ## The two results -/

section Main

variable {V : Type u} [Fintype V]

/-- **Proposition 1.12.** If a directed graph `D` is symmetry-forcing, then `D` is OS or OAS. -/
theorem prop_1_12_proof (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp)
    (D : OrientedGraph V) (hD : D.IsSymmetryForcing) : D.IsOS ∨ D.IsOAS := by
  classical
  have hK := (S1Bridges.isSymmetryForcing_iff_isSymmetryForcingK_proof h13 h18 hcpt D).mp hD
  rcases kernel_main D hK with h | h
  · exact Or.inl ((S1Bridges.isOS_iff_isOSK_proof D).mpr h)
  · exact Or.inr ((S1Bridges.isOAS_iff_isOASK_proof D).mpr h)

/-- **Proposition 1.12**, digraphon form. -/
theorem prop_1_12_kernel_proof (D : OrientedGraph V) (hD : D.IsSymmetryForcingK) :
    D.IsOSK ∨ D.IsOASK :=
  kernel_main D hD

end Main

end S1P112

end NieWeiOrientedSidorenko
