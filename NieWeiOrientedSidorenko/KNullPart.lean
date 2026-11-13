import NieWeiOrientedSidorenko.Mixing

/-!
# Step Sidorenko with DGHRR's partitions (null parts allowed)

Auxiliary encodings of the wording of Doležal–Grebík–Hladký–Rocha–Rozhoň (DGHRR), Definition 2.7
and (3.17): a finite partition may have null parts, and the step graphon `Γ^{⋈P}` is left
undefined on null rectangles. We encode an undefined value by an **arbitrary** filler function, and
prove that step Sidorenko in this form is equivalent to the positive-measure form
`IsStepSidorenkoSymm` used by the literature hypothesis `DGHRRThm325Hyp` (answer key A3,
SOURCES.md A3, "What must be PROVED instead", second bullet). None of this is a result of the
paper.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace KNullPart

section Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Auxiliary encoding of DGHRR's "finite partition"** (Definition 2.7, p.9): finitely many
measurable, pairwise disjoint parts covering `Ω`. Unlike `PosPartition`, parts of measure zero
(in particular empty parts) are allowed. -/
structure DGHRRFinPartition (μ : Measure Ω) where
  /-- The number of parts. -/
  k : ℕ
  /-- The parts. -/
  part : Fin k → Set Ω
  measurableSet_part : ∀ i, MeasurableSet (part i)
  disjoint : Pairwise fun i j => Disjoint (part i) (part j)
  cover : (⋃ i, part i) = univ

/-- **Auxiliary encoding of DGHRR's step graphon `Γ^{⋈P}`** (Definition 2.7) for a partition with
null parts allowed: on `Ω_i × Ω_j` with `μ(Ω_i) > 0` and `μ(Ω_j) > 0` it is the average of `U`
over `Ω_i × Ω_j`; on a rectangle with a null side (where DGHRR leave the value undefined) it takes
the value `F x y` of an arbitrary filler `F`. No condition at all is put on `F`. -/
noncomputable def dghrrStepAvg {μ : Measure Ω} (P : DGHRRFinPartition μ) (F U : Ω → Ω → ℝ) :
    Ω → Ω → ℝ := by
  classical
  exact fun x y => ∑ i, ∑ j, (P.part i).indicator (fun _ => (1 : ℝ)) x *
    (P.part j).indicator (fun _ => (1 : ℝ)) y *
    (if 0 < μ (P.part i) ∧ 0 < μ (P.part j) then
      (∫ p in P.part i ×ˢ P.part j, U p.1 p.2 ∂(μ.prod μ)) /
        ((μ (P.part i)).toReal * (μ (P.part j)).toReal)
    else F x y)

end Defs

/-- **Auxiliary encoding of DGHRR's step Sidorenko property (3.17)** with DGHRR's partitions:
`t(H, W^{⋈P}) ≤ t(H, W)` for every everywhere-symmetric graphon `W`, every finite measurable
partition `P` of `[0,1]` (null parts allowed) and every filler `F` on the null rectangles (no
boundedness, measurability or symmetry is asked of `F`). -/
def IsStepSidorenkoSymmNull {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  ∀ U : I → I → ℝ, IsSymmGraphon U → ∀ P : DGHRRFinPartition (volume : Measure I),
    ∀ F : I → I → ℝ, tU H (dghrrStepAvg P F U) ≤ tU H U

/-- **Auxiliary encoding of DGHRR Theorem 3.25 (with Theorem 2.14) with DGHRR's own premise**:
`DGHRRThm325Hyp` with the premise `IsStepSidorenkoSymm H` replaced by the null-part form
`IsStepSidorenkoSymmNull H`. -/
def DGHRRThm325HypNull.{v} : Prop :=
  ∀ (V : Type v) [Fintype V] (H : SimpleGraph V), H.Connected → H.edgeSet.Nonempty →
    IsStepSidorenkoSymmNull H → IsWeaklySeminormingSymm H

/-! ## Evaluation lemmas -/

section Eval

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- A double sum of indicator products over a family of pairwise disjoint sets picks out the single
term of the parts containing `x` and `y`. -/
lemma sum_indicator_eq {k : ℕ} (part : Fin k → Set Ω)
    (hdisj : Pairwise fun i j => Disjoint (part i) (part j)) (g : Fin k → Fin k → ℝ)
    {a b : Fin k} {x y : Ω} (hx : x ∈ part a) (hy : y ∈ part b) :
    ∑ i, ∑ j, (part i).indicator (fun _ => (1 : ℝ)) x * (part j).indicator (fun _ => (1 : ℝ)) y *
      g i j = g a b := by
  have hx' : ∀ i, i ≠ a → x ∉ part i := fun i hi hxi =>
    Set.disjoint_left.mp (hdisj hi) hxi hx
  have hy' : ∀ j, j ≠ b → y ∉ part j := fun j hj hyj =>
    Set.disjoint_left.mp (hdisj hj) hyj hy
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · intro j _ hj; simp [Set.indicator_of_notMem (hy' j hj)]
  · intro h; exact absurd (Finset.mem_univ b) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Set.indicator_of_notMem (hx' i hi)]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Value of `stepAvg` on `Q_a × Q_b`: the average of `U` over that rectangle. -/
lemma stepAvg_apply (Q : PosPartition μ) (U : Ω → Ω → ℝ) {a b : Fin Q.k} {x y : Ω}
    (hx : x ∈ Q.part a) (hy : y ∈ Q.part b) :
    stepAvg Q U x y = (∫ p in Q.part a ×ˢ Q.part b, U p.1 p.2 ∂(μ.prod μ)) /
      ((μ (Q.part a)).toReal * (μ (Q.part b)).toReal) :=
  sum_indicator_eq Q.part Q.disjoint
    (fun i j => (∫ p in Q.part i ×ˢ Q.part j, U p.1 p.2 ∂(μ.prod μ)) /
      ((μ (Q.part i)).toReal * (μ (Q.part j)).toReal)) hx hy

/-- Value of `dghrrStepAvg` on `Ω_a × Ω_b` with both parts of positive measure: the average. -/
lemma dghrrStepAvg_apply_pos (P : DGHRRFinPartition μ) (F U : Ω → Ω → ℝ) {a b : Fin P.k}
    {x y : Ω} (hx : x ∈ P.part a) (hy : y ∈ P.part b) (ha : 0 < μ (P.part a))
    (hb : 0 < μ (P.part b)) :
    dghrrStepAvg P F U x y = (∫ p in P.part a ×ˢ P.part b, U p.1 p.2 ∂(μ.prod μ)) /
      ((μ (P.part a)).toReal * (μ (P.part b)).toReal) := by
  classical
  unfold dghrrStepAvg
  rw [sum_indicator_eq P.part P.disjoint _ hx hy]
  simp [ha, hb]

end Eval

/-! ## Positive-measure partitions are DGHRR partitions -/

section ToFin

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A `PosPartition` viewed as a DGHRR partition (with no null part). -/
def posToDGHRR (Q : PosPartition μ) : DGHRRFinPartition μ where
  k := Q.k
  part := Q.part
  measurableSet_part := Q.measurableSet_part
  disjoint := Q.disjoint
  cover := Q.cover

/-- On a partition with no null part the filler is never used: `dghrrStepAvg` is `stepAvg`,
pointwise, for every filler `F`. -/
lemma dghrrStepAvg_posToDGHRR (Q : PosPartition μ) (F U : Ω → Ω → ℝ) :
    dghrrStepAvg (posToDGHRR Q) F U = stepAvg Q U := by
  classical
  funext x y
  unfold dghrrStepAvg stepAvg
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [posToDGHRR, Q.pos i, Q.pos j]

end ToFin

/-! ## Merging the null parts into a positive part -/

section Merge

variable (P : DGHRRFinPartition (volume : Measure I))

/-- The union of the null parts of `P`. -/
def nullUnion : Set I := ⋃ (i) (_ : volume (P.part i) = 0), P.part i

lemma nullUnion_measure : volume (nullUnion P) = 0 := by
  unfold nullUnion
  rw [measure_iUnion_null_iff]
  intro i
  rw [measure_iUnion_null_iff]
  exact fun h => h

lemma measurableSet_nullUnion : MeasurableSet (nullUnion P) :=
  MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => P.measurableSet_part i

/-- Some part of a DGHRR partition of `[0,1]` has positive measure. -/
lemma exists_pos_part : ∃ i, 0 < volume (P.part i) := by
  by_contra h
  push Not at h
  have h0 : ∀ i, volume (P.part i) = 0 := fun i => nonpos_iff_eq_zero.mp (h i)
  have : volume (⋃ i, P.part i) = 0 := measure_iUnion_null_iff.mpr h0
  rw [P.cover, measure_univ] at this
  exact one_ne_zero this

/-- The index type of the positive parts. -/
abbrev PosIdx : Type := {i : Fin P.k // 0 < volume (P.part i)}

/-- A chosen positive part, into which the null parts are merged. -/
noncomputable def i0 : PosIdx P := ⟨(exists_pos_part P).choose, (exists_pos_part P).choose_spec⟩

/-- The merged part attached to a positive index `s`: `Ω_s`, with the null parts added to it when
`s` is the chosen index `i0`. -/
noncomputable def mergedPart (s : PosIdx P) : Set I := by
  classical exact P.part s.1 ∪ (if s = i0 P then nullUnion P else ∅)

lemma part_subset_mergedPart (s : PosIdx P) : P.part s.1 ⊆ mergedPart P s := by
  classical
  unfold mergedPart; exact Set.subset_union_left

lemma mergedPart_ae_eq (s : PosIdx P) : mergedPart P s =ᵐ[volume] P.part s.1 := by
  classical
  unfold mergedPart
  refine union_ae_eq_left_of_ae_eq_empty ?_
  split_ifs
  · exact ae_eq_empty.mpr (nullUnion_measure P)
  · exact ae_eq_refl _

lemma mergedPart_measure (s : PosIdx P) : volume (mergedPart P s) = volume (P.part s.1) :=
  measure_congr (mergedPart_ae_eq P s)

/-- The positive-measure partition obtained from `P` by dropping the null parts and merging them
into the chosen positive part `i0`. -/
noncomputable def toPos : PosPartition (volume : Measure I) where
  k := Fintype.card (PosIdx P)
  part := fun t => mergedPart P ((Fintype.equivFin (PosIdx P)).symm t)
  measurableSet_part := by
    classical
    intro t
    unfold mergedPart
    refine (P.measurableSet_part _).union ?_
    split_ifs
    · exact measurableSet_nullUnion P
    · exact MeasurableSet.empty
  pos := fun t => by
    rw [mergedPart_measure]; exact ((Fintype.equivFin (PosIdx P)).symm t).2
  disjoint := by
    classical
    intro t t' htt'
    set s := (Fintype.equivFin (PosIdx P)).symm t
    set s' := (Fintype.equivFin (PosIdx P)).symm t'
    have hss' : s ≠ s' := fun h => htt' ((Fintype.equivFin (PosIdx P)).symm.injective h)
    have hss'1 : s.1 ≠ s'.1 := fun h => hss' (Subtype.ext h)
    -- each part `Ω_s` is disjoint from the null union, since `s` is a positive index
    have hN : ∀ r : PosIdx P, Disjoint (P.part r.1) (nullUnion P) := by
      intro r
      rw [Set.disjoint_left]
      intro x hx hxN
      simp only [nullUnion, Set.mem_iUnion] at hxN
      obtain ⟨i, hi, hxi⟩ := hxN
      have hir : i ≠ r.1 := fun h => by rw [h] at hi; exact (ne_of_gt r.2) hi
      exact Set.disjoint_left.mp (P.disjoint hir) hxi hx
    show Disjoint (mergedPart P s) (mergedPart P s')
    unfold mergedPart
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    refine ⟨⟨P.disjoint hss'1, ?_⟩, ?_, ?_⟩
    · split_ifs
      · exact hN s
      · exact Set.disjoint_empty _
    · split_ifs
      · exact (hN s').symm
      · exact Set.empty_disjoint _
    · split_ifs with h1 h2
      · exact absurd (h1.trans h2.symm) hss'
      · exact Set.disjoint_empty _
      · exact Set.empty_disjoint _
      · exact Set.empty_disjoint _
  cover := by
    classical
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (P.cover ▸ Set.mem_univ x)
    rcases eq_or_ne (volume (P.part a)) 0 with ha | ha
    · -- `x` lies in a null part: it is in the merged part `i0`
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin (PosIdx P) (i0 P), ?_⟩
      simp only [Equiv.symm_apply_apply, mergedPart]
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨a, ha, hxa⟩)
    · refine Set.mem_iUnion.mpr ⟨Fintype.equivFin (PosIdx P) ⟨a, pos_iff_ne_zero.mpr ha⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      exact part_subset_mergedPart P ⟨a, pos_iff_ne_zero.mpr ha⟩ hxa

/-- Off the null set `{x ∈ N} ∪ {y ∈ N}` (`N` the union of the null parts), the DGHRR step graphon
with any filler agrees with the step average over the merged positive partition. Hence the two
agree almost everywhere. -/
lemma dghrrStepAvg_aeEq_toPos (F U : I → I → ℝ) :
    AEEq volume (dghrrStepAvg P F U) (stepAvg (toPos P) U) := by
  have hN : ∀ᵐ x ∂(volume : Measure I), x ∉ nullUnion P :=
    measure_eq_zero_iff_ae_notMem.mp (nullUnion_measure P)
  have h1 : ∀ᵐ p : I × I ∂((volume : Measure I).prod volume), p.1 ∉ nullUnion P :=
    (Measure.quasiMeasurePreserving_fst).ae hN
  have h2 : ∀ᵐ p : I × I ∂((volume : Measure I).prod volume), p.2 ∉ nullUnion P :=
    (Measure.quasiMeasurePreserving_snd).ae hN
  unfold AEEq
  filter_upwards [h1, h2] with p hp1 hp2
  -- the part of each coordinate is a positive part
  have pos_of : ∀ z : I, z ∉ nullUnion P → ∃ s : PosIdx P, z ∈ P.part s.1 := by
    intro z hz
    obtain ⟨a, hza⟩ := Set.mem_iUnion.mp (P.cover ▸ Set.mem_univ z)
    rcases eq_or_ne (volume (P.part a)) 0 with ha | ha
    · exact absurd (Set.mem_iUnion₂.mpr ⟨a, ha, hza⟩) hz
    · exact ⟨⟨a, pos_iff_ne_zero.mpr ha⟩, hza⟩
  obtain ⟨s, hs⟩ := pos_of p.1 hp1
  obtain ⟨s', hs'⟩ := pos_of p.2 hp2
  set e := Fintype.equivFin (PosIdx P)
  have hxQ : p.1 ∈ (toPos P).part (e s) := by
    show p.1 ∈ mergedPart P (e.symm (e s))
    rw [Equiv.symm_apply_apply]; exact part_subset_mergedPart P s hs
  have hyQ : p.2 ∈ (toPos P).part (e s') := by
    show p.2 ∈ mergedPart P (e.symm (e s'))
    rw [Equiv.symm_apply_apply]; exact part_subset_mergedPart P s' hs'
  rw [dghrrStepAvg_apply_pos P F U hs hs' s.2 s'.2, stepAvg_apply _ U hxQ hyQ]
  have hpart : ∀ r : PosIdx P, (toPos P).part (e r) = mergedPart P r := fun r => by
    show mergedPart P (e.symm (e r)) = _
    rw [Equiv.symm_apply_apply]
  rw [hpart s, hpart s', mergedPart_measure, mergedPart_measure,
    setIntegral_congr_set (Measure.set_prod_ae_eq (mergedPart_ae_eq P s) (mergedPart_ae_eq P s'))]

end Merge

/-! ## The equivalences -/

/-- **Step Sidorenko with or without null parts.** For a finite simple graph `H`, the
positive-measure form `IsStepSidorenkoSymm H` (the premise of `DGHRRThm325Hyp`) is equivalent to
DGHRR's form (3.17) with partitions allowed to have null parts and arbitrary values on null
rectangles (`IsStepSidorenkoSymmNull H`). Discharges answer key / SOURCES.md A3, "prove the passage
to the positive-measure step-Sidorenko form".

Proof: `t(H, ·)` only sees kernels up to null sets; a DGHRR step graphon agrees a.e. with the step
average over the positive partition obtained by merging the null parts into a positive part, and a
`PosPartition` is a DGHRR partition on which the filler is never used. -/
theorem isStepSidorenkoSymm_iff_null {V : Type*} [Fintype V] (H : SimpleGraph V) :
    IsStepSidorenkoSymm H ↔ IsStepSidorenkoSymmNull H := by
  constructor
  · intro h U hU P F
    rw [Section1Aux.tU_congr_ae H (dghrrStepAvg_aeEq_toPos P F U)]
    exact h U hU (toPos P)
  · intro h U hU Q
    have := h U hU (posToDGHRR Q) (fun _ _ => 0)
    rwa [dghrrStepAvg_posToDGHRR] at this

/-- **The literature hypothesis A3 with DGHRR's own premise.** `DGHRRThm325Hyp` (premise: step
Sidorenko over positive-measure partitions) is equivalent to `DGHRRThm325HypNull` (premise: DGHRR's
(3.17), null parts allowed). Discharges answer key / SOURCES.md A3: stating the hypothesis in the
positive-measure form loses nothing against the source's wording. -/
theorem dghrrThm325Hyp_iff_null : DGHRRThm325Hyp.{u} ↔ DGHRRThm325HypNull.{u} := by
  constructor
  · intro h V _ H hc he hs
    exact h V H hc he ((isStepSidorenkoSymm_iff_null H).mpr hs)
  · intro h V _ H hc he hs
    exact h V H hc he ((isStepSidorenkoSymm_iff_null H).mp hs)

end KNullPart

end NieWeiOrientedSidorenko
