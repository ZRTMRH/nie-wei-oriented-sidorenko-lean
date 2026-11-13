import NieWeiOrientedSidorenko.Mixing

/-!
# Conjecture 1: the hypotheses of the forcing half can all hold

`SidorenkoForcingConjecture` (Section1.lean) is a stated, unproved `Prop`; nothing here proves or
refutes it. This file gives a witness that the *antecedent* of its forcing half is satisfiable:
`H = C₄` (bipartite, contains a cycle), `p = 1/2`, `N k = 2^k`, and `G_k` the inner-product graph
on `F₂^k` (`x ~ y ↔ x ≠ y ∧ x·y = 1`), relabelled to `Fin (2^k)`. We prove
`|t(K₂, G_k) - 1/2| ≤ 2/2^k` and `|t(C₄, G_k) - 1/16| ≤ 7/2^k` by character sums over `F₂^k`:
`∑_y (-1)^{w·y} = 2^k [w = 0]`, so `#{y : x·y = 1} = 2^{k-1}` for `x ≠ 0` and
`#{y : x·y = 1 = z·y} = 2^{k-2}` for `x, z` nonzero and distinct; the diagonal costs `O(1)` per
codegree. The densities are those of `Basic.lean` (over all maps, degenerate ones included).
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace KConj1

open SimpleGraph

/-! ## Characters of `F₂^k` -/

/-- The sign character `χ(t) = (-1)^t` of `ZMod 2`, valued in `ℝ`. -/
def chi (t : ZMod 2) : ℝ := if t = 0 then 1 else -1

/-- The sign character is additive-to-multiplicative: `χ(s + t) = χ(s) χ(t)` on `ZMod 2`. -/
theorem chi_add (s t : ZMod 2) : chi (s + t) = chi s * chi t := by
  have key : ∀ s t : ZMod 2, s + t = 0 ↔ (s = 0 ↔ t = 0) := by decide
  unfold chi; simp only [key]; by_cases hs : s = 0 <;> by_cases ht : t = 0 <;> simp [hs, ht]

/-- `χ` of a finite sum is the product of the `χ`'s. -/
theorem chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, chi_add, ih]

/-- The indicator `[t = 1]` on `ZMod 2` equals `(1 - χ(t))/2`. -/
theorem ind_eq (t : ZMod 2) : (if t = 1 then (1 : ℝ) else 0) = (1 - chi t) / 2 := by
  have key : ∀ t : ZMod 2, t = 1 ↔ ¬ t = 0 := by decide
  unfold chi; simp only [key]; by_cases ht : t = 0 <;> simp [ht]

/-- The character sum `S(w) = ∑_{y ∈ F₂^k} χ(w·y)`. -/
noncomputable def charSum {k : ℕ} (w : Fin k → ZMod 2) : ℝ := ∑ y : Fin k → ZMod 2, chi (w ⬝ᵥ y)

/-- `S(0) = 2^k`: the character sum at `w = 0` counts all vectors. -/
theorem charSum_zero (k : ℕ) : charSum (0 : Fin k → ZMod 2) = Fintype.card (Fin k → ZMod 2) := by
  simp [charSum, chi]

/-- For `w ≠ 0` in `F₂^k`, `S(w) = ∑_y (-1)^{w·y} = 0` (orthogonality of characters; a nonzero
linear functional takes each value equally often). -/
theorem charSum_ne_zero {k : ℕ} {w : Fin k → ZMod 2} (hw : w ≠ 0) : charSum w = 0 := by
  classical
  have h1 : charSum w = ∏ i, ∑ t : ZMod 2, chi (w i * t) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [charSum, dotProduct, chi_sum]
  rw [h1]
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := Function.ne_iff.mp hw
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have : w i = 1 := by
    have key : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact key _ hi
  rw [this]
  simp only [one_mul]
  have h2 : ∑ t : ZMod 2, chi t = chi 0 + chi 1 := Fin.sum_univ_two chi
  rw [h2]
  simp [chi]

/-! ## The inner-product graph on `F₂^k` -/

/-- The inner-product graph on `F₂^k`: `x ~ y` iff `x ≠ y` and `x·y = 1` in `F₂`. -/
def ipGraph (k : ℕ) : SimpleGraph (Fin k → ZMod 2) where
  Adj x y := x ≠ y ∧ x ⬝ᵥ y = 1
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [dotProduct_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- Adjacency in the inner-product graph: `x ~ y ↔ x ≠ y ∧ x·y = 1`. -/
@[simp] theorem ipGraph_adj {k : ℕ} {x y : Fin k → ZMod 2} :
    (ipGraph k).Adj x y ↔ x ≠ y ∧ x ⬝ᵥ y = 1 := Iff.rfl

instance (k : ℕ) : DecidableRel (ipGraph k).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ x ⬝ᵥ y = 1))

/-- The real indicator `[x·y = 1]` (loops allowed). -/
noncomputable def dotInd {k : ℕ} (x y : Fin k → ZMod 2) : ℝ := if x ⬝ᵥ y = 1 then 1 else 0

/-- The real adjacency indicator `[x ~ y]` of the inner-product graph. -/
noncomputable def adjInd {k : ℕ} (x y : Fin k → ZMod 2) : ℝ := if (ipGraph k).Adj x y then 1 else 0

/-- `[x·y = 1] = (1 - χ(x·y))/2`. -/
theorem dotInd_eq {k : ℕ} (x y : Fin k → ZMod 2) : dotInd x y = (1 - chi (x ⬝ᵥ y)) / 2 := ind_eq _

/-- `#{y : x·y = 1} = (2^k - S(x))/2`, written with the real indicator. -/
theorem sum_dotInd {k : ℕ} (x : Fin k → ZMod 2) :
    ∑ y, dotInd x y = ((Fintype.card (Fin k → ZMod 2) : ℝ) - charSum x) / 2 := by
  simp only [dotInd_eq, ← Finset.sum_div, Finset.sum_sub_distrib, charSum]
  simp

/-- `∑_x S(x) = 2^k` (only `x = 0` contributes). -/
theorem sum_charSum (k : ℕ) : ∑ x : Fin k → ZMod 2, charSum x = Fintype.card (Fin k → ZMod 2) := by
  classical
  rw [Finset.sum_eq_single (0 : Fin k → ZMod 2)]
  · exact charSum_zero k
  · intro b _ hb; exact charSum_ne_zero hb
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `#{(x, y) : x·y = 1} = (n² - n)/2` where `n = 2^k`. -/
theorem sum_sum_dotInd (k : ℕ) : ∑ x : Fin k → ZMod 2, ∑ y, dotInd x y =
    ((Fintype.card (Fin k → ZMod 2) : ℝ) ^ 2 - Fintype.card (Fin k → ZMod 2)) / 2 := by
  simp only [sum_dotInd, ← Finset.sum_div, Finset.sum_sub_distrib, sum_charSum]
  simp [sq]

/-- The adjacency indicator of the inner-product graph is at most `[x·y = 1]`. -/
theorem adjInd_le_dotInd {k : ℕ} (x y : Fin k → ZMod 2) : adjInd x y ≤ dotInd x y := by
  simp only [adjInd, dotInd, ipGraph_adj]
  by_cases h1 : x = y
  · subst h1; split_ifs <;> simp_all
  · by_cases h2 : x ⬝ᵥ y = 1 <;> simp [h1, h2]

/-- `[x·y = 1] - [x ~ y]` is supported on the diagonal: it is at most `[x = y]`. -/
theorem dotInd_sub_adjInd_le {k : ℕ} (x y : Fin k → ZMod 2) :
    dotInd x y - adjInd x y ≤ if x = y then 1 else 0 := by
  simp only [adjInd, dotInd, ipGraph_adj]
  by_cases h1 : x = y
  · subst h1; split_ifs <;> simp_all
  · by_cases h2 : x ⬝ᵥ y = 1 <;> simp [h1, h2]

/-- The adjacency indicator is nonnegative. -/
theorem adjInd_nonneg {k : ℕ} (x y : Fin k → ZMod 2) : 0 ≤ adjInd x y := by
  unfold adjInd; split_ifs <;> norm_num
/-- The adjacency indicator is at most `1`. -/
theorem adjInd_le_one {k : ℕ} (x y : Fin k → ZMod 2) : adjInd x y ≤ 1 := by
  unfold adjInd; split_ifs <;> norm_num
/-- The indicator `[x·y = 1]` is nonnegative. -/
theorem dotInd_nonneg {k : ℕ} (x y : Fin k → ZMod 2) : 0 ≤ dotInd x y := by
  unfold dotInd; split_ifs <;> norm_num
/-- The indicator `[x·y = 1]` is at most `1`. -/
theorem dotInd_le_one {k : ℕ} (x y : Fin k → ZMod 2) : dotInd x y ≤ 1 := by
  unfold dotInd; split_ifs <;> norm_num

/-- Edge count of the inner-product graph: `|∑_{x,y} [x ~ y] - n²/2| ≤ 2n`, `n = 2^k`. -/
theorem sum_g_bound (k : ℕ) :
    |∑ x : Fin k → ZMod 2, ∑ y, adjInd x y - (Fintype.card (Fin k → ZMod 2) : ℝ) ^ 2 / 2| ≤
      2 * (Fintype.card (Fin k → ZMod 2) : ℝ) := by
  generalize hn' : (Fintype.card (Fin k → ZMod 2) : ℝ) = n
  have h1 : ∑ x : Fin k → ZMod 2, ∑ y, adjInd x y ≤ ∑ x : Fin k → ZMod 2, ∑ y, dotInd x y :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => adjInd_le_dotInd x y
  have h2 : ∑ x : Fin k → ZMod 2, ∑ y, dotInd x y - ∑ x : Fin k → ZMod 2, ∑ y, adjInd x y ≤ n := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ x : Fin k → ZMod 2, (∑ y, dotInd x y - ∑ y, adjInd x y)
        ≤ ∑ x : Fin k → ZMod 2, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [← Finset.sum_sub_distrib]
          calc ∑ y, (dotInd x y - adjInd x y) ≤ ∑ y, (if x = y then (1 : ℝ) else 0) :=
                Finset.sum_le_sum fun y _ => dotInd_sub_adjInd_le x y
            _ = 1 := by simp
      _ = n := by simp [← hn']
  have h3 := sum_sum_dotInd k
  rw [hn'] at h3
  have hn : 0 ≤ n := hn' ▸ Nat.cast_nonneg _
  rw [abs_le]; constructor <;> nlinarith

/-- The codegree `#{y : x ~ y ∧ y ~ z}` in the inner-product graph (as a real). -/
noncomputable def codeg {k : ℕ} (x z : Fin k → ZMod 2) : ℝ := ∑ y, adjInd x y * adjInd y z

/-- The codegree with the diagonal included (no x ≠ y restriction) `#{y : x·y = 1 ∧ y·z = 1}` (as a real). -/
noncomputable def dotCodeg {k : ℕ} (x z : Fin k → ZMod 2) : ℝ := ∑ y, dotInd x y * dotInd y z

/-- In `F₂^k`, `x + z = 0 ↔ x = z`. -/
theorem add_eq_zero_iff_eq {k : ℕ} {x z : Fin k → ZMod 2} : x + z = 0 ↔ x = z := by
  constructor
  · intro h; funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    have key : ∀ s t : ZMod 2, s + t = 0 → s = t := by decide
    exact key _ _ this
  · rintro rfl; funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    have key : ∀ s : ZMod 2, s + s = 0 := by decide
    exact key _

/-- For `x, z` nonzero and distinct in `F₂^k` (i.e. linearly independent over `F₂`), `#{y : x·y = 1
∧ z·y = 1} = 2^k/4`. -/
theorem dotCodeg_good {k : ℕ} {x z : Fin k → ZMod 2} (hx : x ≠ 0) (hz : z ≠ 0) (hxz : x ≠ z) :
    dotCodeg x z = (Fintype.card (Fin k → ZMod 2) : ℝ) / 4 := by
  have hpt : ∀ y, dotInd x y * dotInd y z =
      (1 - chi (x ⬝ᵥ y) - chi (z ⬝ᵥ y) + chi ((x + z) ⬝ᵥ y)) / 4 := by
    intro y
    rw [dotInd_eq, dotInd_eq, add_dotProduct, chi_add, dotProduct_comm y z]
    ring
  have hxz' : x + z ≠ 0 := fun h => hxz (add_eq_zero_iff_eq.mp h)
  have h1 : ∑ y : Fin k → ZMod 2, chi (x ⬝ᵥ y) = 0 := charSum_ne_zero hx
  have h2 : ∑ y : Fin k → ZMod 2, chi (z ⬝ᵥ y) = 0 := charSum_ne_zero hz
  have h3 : ∑ y : Fin k → ZMod 2, chi ((x + z) ⬝ᵥ y) = 0 := charSum_ne_zero hxz'
  simp only [dotCodeg, hpt, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1,
    h2, h3]
  simp

/-- `#{y : x·y = 1 ∧ y·z = 1} ≥ 0`. -/
theorem dotCodeg_nonneg {k : ℕ} (x z : Fin k → ZMod 2) : 0 ≤ dotCodeg x z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (dotInd_nonneg _ _) (dotInd_nonneg _ _)

/-- `#{y : x·y = 1 ∧ y·z = 1} ≤ 2^k`. -/
theorem dotCodeg_le {k : ℕ} (x z : Fin k → ZMod 2) :
    dotCodeg x z ≤ Fintype.card (Fin k → ZMod 2) := by
  calc dotCodeg x z ≤ ∑ _y : Fin k → ZMod 2, (1 : ℝ) := Finset.sum_le_sum fun y _ => by
        nlinarith [dotInd_le_one x y, dotInd_nonneg y z, dotInd_le_one y z, dotInd_nonneg x y]
    _ = _ := by simp

/-- Codegrees in the inner-product graph are nonnegative. -/
theorem codeg_nonneg {k : ℕ} (x z : Fin k → ZMod 2) : 0 ≤ codeg x z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (adjInd_nonneg _ _) (adjInd_nonneg _ _)

/-- The codegree of `x, z` in the inner-product graph is at most `#{y : x·y = 1 ∧ y·z = 1}`. -/
theorem codeg_le_dotCodeg {k : ℕ} (x z : Fin k → ZMod 2) : codeg x z ≤ dotCodeg x z :=
  Finset.sum_le_sum fun _ _ =>
    mul_le_mul (adjInd_le_dotInd _ _) (adjInd_le_dotInd _ _) (adjInd_nonneg _ _) (dotInd_nonneg _ _)

/-- Removing the diagonal (`y = x` or `y = z`) changes a codegree by at most `2`. -/
theorem dotCodeg_sub_codeg_le {k : ℕ} (x z : Fin k → ZMod 2) : dotCodeg x z - codeg x z ≤ 2 := by
  unfold dotCodeg codeg
  rw [← Finset.sum_sub_distrib]
  calc ∑ y, (dotInd x y * dotInd y z - adjInd x y * adjInd y z)
      ≤ ∑ y, ((if x = y then (1 : ℝ) else 0) + (if y = z then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        have e1 := dotInd_sub_adjInd_le x y
        have e2 := dotInd_sub_adjInd_le y z
        have := adjInd_nonneg x y; have := adjInd_le_one x y; have := dotInd_nonneg y z
        have := dotInd_le_one y z; have := adjInd_le_dotInd y z; have := adjInd_le_dotInd x y
        nlinarith
    _ = 2 := by rw [Finset.sum_add_distrib]; simp; norm_num

/-- `C₄` count of the inner-product graph: `|∑_{x,z} codeg(x,z)² - n⁴/16| ≤ 7n³`, `n = 2^k`. -/
theorem sum_codeg_sq_bound (k : ℕ) :
    |∑ x : Fin k → ZMod 2, ∑ z, codeg x z ^ 2 - (Fintype.card (Fin k → ZMod 2) : ℝ) ^ 4 / 16| ≤
      7 * (Fintype.card (Fin k → ZMod 2) : ℝ) ^ 3 := by
  generalize hn' : (Fintype.card (Fin k → ZMod 2) : ℝ) = n
  have hW : (2 : ℝ) ^ k = n := by rw [← hn']; simp
  have hn : 0 ≤ n := hn' ▸ Nat.cast_nonneg _
  -- step A
  have hA : ∀ x z : Fin k → ZMod 2, |codeg x z ^ 2 - dotCodeg x z ^ 2| ≤ 4 * n := by
    intro x z
    have := dotCodeg_nonneg x z; have h2 := dotCodeg_le x z; have := codeg_nonneg x z
    have := codeg_le_dotCodeg x z; have := dotCodeg_sub_codeg_le x z
    rw [hn'] at h2
    rw [abs_le]; constructor <;> nlinarith
  -- step B
  have hB : ∀ x z : Fin k → ZMod 2, |dotCodeg x z ^ 2 - (n / 4) ^ 2| ≤
      n ^ 2 * ((if x = 0 then (1 : ℝ) else 0) + (if z = 0 then (1 : ℝ) else 0) +
        (if x = z then (1 : ℝ) else 0)) := by
    intro x z
    by_cases hgood : x ≠ 0 ∧ z ≠ 0 ∧ x ≠ z
    · rw [dotCodeg_good hgood.1 hgood.2.1 hgood.2.2, hn']
      simp only [sub_self, abs_zero]
      positivity
    · have h1 : (1 : ℝ) ≤ (if x = 0 then (1 : ℝ) else 0) + (if z = 0 then (1 : ℝ) else 0) +
          (if x = z then (1 : ℝ) else 0) := by
        simp only [not_and_or, not_not] at hgood
        rcases hgood with h | h | h <;> simp only [h, ite_true] <;> split_ifs <;> norm_num
      have := dotCodeg_nonneg x z; have h2 := dotCodeg_le x z
      rw [hn'] at h2
      have hsq : n ^ 2 ≤ n ^ 2 * ((if x = 0 then (1 : ℝ) else 0) +
          (if z = 0 then (1 : ℝ) else 0) + (if x = z then (1 : ℝ) else 0)) :=
        le_mul_of_one_le_right (sq_nonneg n) h1
      refine le_trans ?_ hsq
      rw [abs_le]; constructor <;> nlinarith
  have hsumB : ∑ x : Fin k → ZMod 2, ∑ z : Fin k → ZMod 2,
      n ^ 2 * ((if x = 0 then (1 : ℝ) else 0) + (if z = 0 then (1 : ℝ) else 0) +
        (if x = z then (1 : ℝ) else 0)) = 3 * n ^ 3 := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    simp [hW]
    ring
  have hconst : ∑ _x : Fin k → ZMod 2, ∑ _z : Fin k → ZMod 2, (n / 4) ^ 2 = n ^ 4 / 16 := by
    simp [hW]; ring
  have hsumA : ∑ _x : Fin k → ZMod 2, ∑ _z : Fin k → ZMod 2, 4 * n = 4 * n ^ 3 := by
    simp [hW]; ring
  calc |∑ x : Fin k → ZMod 2, ∑ z, codeg x z ^ 2 - n ^ 4 / 16|
      = |∑ x : Fin k → ZMod 2, ∑ z : Fin k → ZMod 2,
          ((codeg x z ^ 2 - dotCodeg x z ^ 2) + (dotCodeg x z ^ 2 - (n / 4) ^ 2))| := by
        rw [← hconst, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
    _ ≤ ∑ x : Fin k → ZMod 2, ∑ z : Fin k → ZMod 2,
          (4 * n + n ^ 2 * ((if x = 0 then (1 : ℝ) else 0) +
          (if z = 0 then (1 : ℝ) else 0) + (if x = z then (1 : ℝ) else 0))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
        exact (abs_add_le _ _).trans (add_le_add (hA x z) (hB x z))
    _ = 7 * n ^ 3 := by
        simp only [Finset.sum_add_distrib] at hsumB ⊢
        rw [hsumA, hsumB]; ring

/-! ## `C₄` and homomorphism counts -/

/-- `C₄` is bipartite (`2`-colourable). -/
theorem c4_colorable : (cycleGraph 4).Colorable 2 :=
  IsBipartite.cycleGraph_of_even (by decide)

/-- `C₄` contains a cycle: it is not acyclic. -/
theorem c4_not_acyclic : ¬ (cycleGraph 4).IsAcyclic := by
  rw [isAcyclic_iff_free_cycleGraph]
  intro h
  exact h 4 (by norm_num) IsContained.rfl

/-- `C₄` has `4` edges, with `edgeFinset` taken for the decidability instance `Classical.decRel`
used in `SidorenkoForcingConjecture`. -/
theorem c4_card :
    (letI := Classical.decRel (cycleGraph 4).Adj; (cycleGraph 4).edgeFinset.card) = 4 := by
  have : (cycleGraph 4).edgeFinset.card = 4 := by decide
  convert this

/-- Homomorphism counts are invariant under relabelling the host graph by an equivalence: `hom(H, G
∘ e) = hom(H, G)`. -/
theorem simpleHomCount_comap {V W W' : Type*} [Fintype V] [Fintype W] [Fintype W']
    (H : SimpleGraph V) (G : SimpleGraph W) (e : W' ≃ W) :
    simpleHomCount H (G.comap e) = simpleHomCount H G := by
  classical
  unfold simpleHomCount
  apply Finset.card_equiv (Equiv.arrowCongr (Equiv.refl V) e)
  intro f
  simp [Equiv.arrowCongr_apply]

/-- `hom(K₂, G) = ∑_{x,y} [x ~ y]` (twice the number of edges). -/
theorem homCount_top_two {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (simpleHomCount (⊤ : SimpleGraph (Fin 2)) G : ℝ) =
      ∑ x : W, ∑ y : W, (if G.Adj x y then (1 : ℝ) else 0) := by
  classical
  unfold simpleHomCount
  rw [Finset.card_equiv (piFinTwoEquiv fun _ => W)
    (t := Finset.univ.filter fun p : W × W => G.Adj p.1 p.2)]
  · rw [Finset.card_filter, Nat.cast_sum, ← Finset.univ_product_univ, Finset.sum_product]
    simp
  · intro f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, piFinTwoEquiv_apply, top_adj]
    constructor
    · intro h; exact h 0 1 (by decide)
    · intro h u v huv
      fin_cases u <;> fin_cases v
      · exact absurd rfl huv
      · exact h
      · exact h.symm
      · exact absurd rfl huv

/-- Maps `Fin 4 → W` as quadruples. -/
def fin4Equiv (W : Type*) : (Fin 4 → W) ≃ W × W × W × W where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun t := ![t.1, t.2.1, t.2.2.1, t.2.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

/-- `hom(C₄, G) = ∑_{a,b,c,d} [a~b][b~c][c~d][d~a]` (the four edge conditions of the cycle
`0-1-2-3-0`). -/
theorem homCount_c4 {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (simpleHomCount (cycleGraph 4) G : ℝ) =
      ∑ a : W, ∑ b : W, ∑ c : W, ∑ d : W,
        (if G.Adj a b then (1 : ℝ) else 0) * (if G.Adj b c then (1 : ℝ) else 0) *
        (if G.Adj c d then (1 : ℝ) else 0) * (if G.Adj d a then (1 : ℝ) else 0) := by
  classical
  unfold simpleHomCount
  rw [Finset.card_equiv (fin4Equiv W) (t := Finset.univ.filter fun p : W × W × W × W =>
    G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2.1 ∧ G.Adj p.2.2.1 p.2.2.2 ∧ G.Adj p.2.2.2 p.1)]
  · rw [Finset.card_filter, Nat.cast_sum, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h1 : G.Adj a b <;> by_cases h2 : G.Adj b c <;> by_cases h3 : G.Adj c d <;>
      by_cases h4 : G.Adj d a <;> simp [h1, h2, h3, h4]
  · intro f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, fin4Equiv]
    constructor
    · intro h
      exact ⟨h 0 1 (by decide), h 1 2 (by decide), h 2 3 (by decide), h 3 0 (by decide)⟩
    · rintro ⟨h1, h2, h3, h4⟩ u v huv
      fin_cases u <;> fin_cases v <;> first
        | exact absurd huv (by decide)
        | assumption
        | exact h1.symm | exact h2.symm | exact h3.symm | exact h4.symm

/-- For a symmetric weight `f`, `∑_{a,b,c,d} f(a,b) f(b,c) f(c,d) f(d,a) = ∑_{a,c} (∑_b f(a,b)
f(b,c))²`: the `C₄` count is the sum of squared codegrees. -/
theorem sum4_eq {W : Type*} [Fintype W] (f : W → W → ℝ) (hf : ∀ x y, f x y = f y x) :
    ∑ a : W, ∑ b : W, ∑ c : W, ∑ d : W, f a b * f b c * f c d * f d a =
      ∑ a : W, ∑ c : W, (∑ b : W, f a b * f b c) ^ 2 := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  rw [hf c d, hf d a]; ring

/-- `|F₂^k| = 2^k`. -/
theorem card_W (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by simp

/-- The edge density of the inner-product graph on `F₂^k`: `|t(K₂, G_k) - 1/2| ≤ 2/2^k`. -/
theorem density_top_bound (k : ℕ) :
    |simpleHomDensity (⊤ : SimpleGraph (Fin 2)) (ipGraph k) - 1 / 2| ≤ 2 / (2 : ℝ) ^ k := by
  have hcount : (simpleHomCount (⊤ : SimpleGraph (Fin 2)) (ipGraph k) : ℝ) =
      ∑ x : Fin k → ZMod 2, ∑ y, adjInd x y := homCount_top_two (ipGraph k)
  have hb := sum_g_bound k
  have hc : (Fintype.card (Fin k → ZMod 2) : ℝ) = 2 ^ k := by rw [card_W]; push_cast; ring
  rw [hc] at hb
  unfold simpleHomDensity
  rw [hcount, hc, Fintype.card_fin]
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [show (∑ x : Fin k → ZMod 2, ∑ y, adjInd x y) / ((2 : ℝ) ^ k) ^ 2 - 1 / 2 =
      ((∑ x : Fin k → ZMod 2, ∑ y, adjInd x y) - ((2 : ℝ) ^ k) ^ 2 / 2) / ((2 : ℝ) ^ k) ^ 2 by
    field_simp]
  rw [abs_div, abs_of_pos (show (0 : ℝ) < ((2 : ℝ) ^ k) ^ 2 by positivity),
    div_le_div_iff₀ (by positivity) hpos]
  nlinarith [mul_le_mul_of_nonneg_right hb hpos.le]

/-- The `C₄` density of the inner-product graph on `F₂^k`: `|t(C₄, G_k) - 1/16| ≤ 7/2^k`. -/
theorem density_c4_bound (k : ℕ) :
    |simpleHomDensity (cycleGraph 4) (ipGraph k) - 1 / 16| ≤ 7 / (2 : ℝ) ^ k := by
  have hcount : (simpleHomCount (cycleGraph 4) (ipGraph k) : ℝ) =
      ∑ x : Fin k → ZMod 2, ∑ z, codeg x z ^ 2 := by
    rw [homCount_c4 (ipGraph k)]
    exact sum4_eq adjInd fun x y => by simp only [adjInd, (ipGraph k).adj_comm]
  have hb := sum_codeg_sq_bound k
  have hc : (Fintype.card (Fin k → ZMod 2) : ℝ) = 2 ^ k := by rw [card_W]; push_cast; ring
  rw [hc] at hb
  unfold simpleHomDensity
  rw [hcount, hc, Fintype.card_fin]
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [show (∑ x : Fin k → ZMod 2, ∑ z, codeg x z ^ 2) / ((2 : ℝ) ^ k) ^ 4 - 1 / 16 =
      ((∑ x : Fin k → ZMod 2, ∑ z, codeg x z ^ 2) - ((2 : ℝ) ^ k) ^ 4 / 16) / ((2 : ℝ) ^ k) ^ 4 by
    field_simp]
  rw [abs_div, abs_of_pos (show (0 : ℝ) < ((2 : ℝ) ^ k) ^ 4 by positivity),
    div_le_div_iff₀ (by positivity) hpos]
  nlinarith [mul_le_mul_of_nonneg_right hb hpos.le]

/-- Homomorphism densities are invariant under relabelling the host graph by an equivalence. -/
theorem simpleHomDensity_comap {V W W' : Type*} [Fintype V] [Fintype W] [Fintype W']
    (H : SimpleGraph V) (G : SimpleGraph W) (e : W' ≃ W) :
    simpleHomDensity H (G.comap e) = simpleHomDensity H G := by
  unfold simpleHomDensity
  rw [simpleHomCount_comap, Fintype.card_congr e]

/-- The relabelling of `F₂^k` by `Fin (2^k)`. -/
noncomputable def relabel (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → ZMod 2) :=
  (Fintype.equivFinOfCardEq (card_W k)).symm

/-- The witness sequence: the inner-product graph on `F₂^k`, relabelled to `Fin (2^k)`. -/
noncomputable def ipSeq (k : ℕ) : SimpleGraph (Fin (2 ^ k)) := (ipGraph k).comap (relabel k)

/-- A real sequence with `|u_k - L| ≤ C/2^k` tends to `L`. -/
theorem tendsto_of_abs_le {u : ℕ → ℝ} {L C : ℝ} (h : ∀ k, |u k - L| ≤ C / (2 : ℝ) ^ k) :
    Tendsto u atTop (𝓝 L) := by
  have h0 : Tendsto (fun k : ℕ => C / (2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact h k) h0

/-! ## The witness -/

/-- The witness sequence has `t(K₂, G_k) → 1/2`. -/
theorem ipSeq_density_top :
    Tendsto (fun k => simpleHomDensity (⊤ : SimpleGraph (Fin 2)) (ipSeq k)) atTop (𝓝 (1 / 2)) :=
  tendsto_of_abs_le (C := 2) fun k => by
    rw [ipSeq, simpleHomDensity_comap]; exact density_top_bound k

/-- The witness sequence has `t(C₄, G_k) → (1/2)^{e(C₄)} = 1/16`, with `e(C₄)` computed by the
`Classical.decRel` instance of `SidorenkoForcingConjecture`. -/
theorem ipSeq_density_c4 :
    letI := Classical.decRel (cycleGraph 4).Adj
    Tendsto (fun k => simpleHomDensity (cycleGraph 4) (ipSeq k)) atTop
      (𝓝 ((1 / 2 : ℝ) ^ (cycleGraph 4).edgeFinset.card)) := by
  show Tendsto _ atTop (𝓝 ((1 / 2 : ℝ) ^
    (letI := Classical.decRel (cycleGraph 4).Adj; (cycleGraph 4).edgeFinset.card)))
  rw [c4_card]
  refine tendsto_of_abs_le (C := 7) fun k => ?_
  rw [ipSeq, simpleHomDensity_comap]; norm_num; exact density_c4_bound k

/-- **The antecedent of the forcing half of Conjecture 1 is satisfiable.** There are a bipartite
graph `H` on `Fin 4` containing a cycle (`H = C₄`), `p ∈ (0, 1)` (`p = 1/2`), `N k → ∞`
(`N k = 2^k`) and graphs `G k` on `Fin (N k)` (the inner-product graphs on `F₂^k`) with
`t(K₂, G k) → p` and `t(H, G k) → p^{e(H)}`. This is exactly the list of hypotheses that the
forcing half of `SidorenkoForcingConjecture` consumes (see `forcing_half_applies_to_witness`);
it discharges the author's obligation to show that those hypotheses can all hold. -/
theorem conj1_forcing_antecedent : ∃ (H : SimpleGraph (Fin 4)) (p : ℝ) (N : ℕ → ℕ)
    (G : ∀ n, SimpleGraph (Fin (N n))), H.Colorable 2 ∧ ¬ H.IsAcyclic ∧ p ∈ Ioo 0 1 ∧
      Tendsto N atTop atTop ∧
      Tendsto (fun n => simpleHomDensity (⊤ : SimpleGraph (Fin 2)) (G n)) atTop (𝓝 p) ∧
      (letI := Classical.decRel H.Adj;
        Tendsto (fun n => simpleHomDensity H (G n)) atTop (𝓝 (p ^ H.edgeFinset.card))) :=
  ⟨cycleGraph 4, 1 / 2, fun k => 2 ^ k, ipSeq, c4_colorable, c4_not_acyclic,
    ⟨by norm_num, by norm_num⟩, tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2),
    ipSeq_density_top, ipSeq_density_c4⟩

/-- **The antecedent matches the conjecture.** Any data satisfying the conjunction of
`conj1_forcing_antecedent` is accepted, hypothesis by hypothesis, by the forcing half of
`SidorenkoForcingConjecture`: under that conjecture (taken as an explicit hypothesis, not
assumed) the sequence is quasi-random, `e_{G_n}(A, B) = p|A||B| + o(N_n²)` uniformly. The proof is
a direct application of the definition, so the two hypothesis lists are syntactically the same. -/
theorem forcing_antecedent_unfold (hconj : SidorenkoForcingConjecture)
    (H : SimpleGraph (Fin 4)) (p : ℝ) (N : ℕ → ℕ) (G : ∀ n, SimpleGraph (Fin (N n)))
    (hant : H.Colorable 2 ∧ ¬ H.IsAcyclic ∧ p ∈ Ioo 0 1 ∧ Tendsto N atTop atTop ∧
      Tendsto (fun n => simpleHomDensity (⊤ : SimpleGraph (Fin 2)) (G n)) atTop (𝓝 p) ∧
      (letI := Classical.decRel H.Adj;
        Tendsto (fun n => simpleHomDensity H (G n)) atTop (𝓝 (p ^ H.edgeFinset.card)))) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ A B : Finset (Fin (N n)),
      |(simpleEdgesBetween (G n) A B : ℝ) - p * A.card * B.card| ≤ ε * (N n : ℝ) ^ 2 :=
  (hconj (Fin 4) H hant.1).2 hant.2.1 p hant.2.2.1 N G hant.2.2.2.1 hant.2.2.2.2.1
    hant.2.2.2.2.2

/-- **The forcing half applied to the witness.** Under `SidorenkoForcingConjecture` (an explicit
hypothesis, not assumed), the forcing half applied to `H = C₄`, `p = 1/2` and the inner-product
graphs `G_k` on `Fin (2^k)` gives `e_{G_k}(A, B) = |A||B|/2 + o(4^k)` uniformly over `A, B`.
The conclusion also holds without the conjecture (`ipSeq_quasirandom`); the content of this
theorem is only that the witness's data are accepted by the conjecture's hypothesis list. -/
theorem forcing_half_applies_to_witness (hconj : SidorenkoForcingConjecture) :
    ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ A B : Finset (Fin (2 ^ k)),
      |(simpleEdgesBetween (ipSeq k) A B : ℝ) - 1 / 2 * A.card * B.card| ≤
        ε * ((2 ^ k : ℕ) : ℝ) ^ 2 :=
  forcing_antecedent_unfold hconj (cycleGraph 4) (1 / 2) (fun k => 2 ^ k) ipSeq
    ⟨c4_colorable, c4_not_acyclic, ⟨by norm_num, by norm_num⟩,
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2), ipSeq_density_top,
      ipSeq_density_c4⟩

/-! ## Optional: the witness is quasi-random -/

/-- `∑_x χ(x·w) = 2^k [w = 0]`, in the orientation `x·w`. -/
theorem charSum_left {k : ℕ} (w : Fin k → ZMod 2) :
    ∑ x : Fin k → ZMod 2, chi (x ⬝ᵥ w) =
      if w = 0 then (Fintype.card (Fin k → ZMod 2) : ℝ) else 0 := by
  have : ∑ x : Fin k → ZMod 2, chi (x ⬝ᵥ w) = charSum w := by
    simp only [charSum, dotProduct_comm]
  rw [this]
  split_ifs with hw
  · rw [hw, charSum_zero]
  · exact charSum_ne_zero hw

/-- **Lindsey's lemma** for `F₂^k`: `(∑_{x ∈ A} ∑_{y ∈ B} (-1)^{x·y})² ≤ |A| |B| 2^k`. -/
theorem lindsey {k : ℕ} (A B : Finset (Fin k → ZMod 2)) :
    (∑ x ∈ A, ∑ y ∈ B, chi (x ⬝ᵥ y)) ^ 2 ≤
      A.card * B.card * (Fintype.card (Fin k → ZMod 2) : ℝ) := by
  classical
  set u : (Fin k → ZMod 2) → ℝ := fun x => ∑ y ∈ B, chi (x ⬝ᵥ y)
  have h1 : (∑ x ∈ A, u x) ^ 2 ≤ A.card * ∑ x ∈ A, u x ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : ∑ x ∈ A, u x ^ 2 ≤ ∑ x, u x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have h3 : ∑ x, u x ^ 2 = B.card * (Fintype.card (Fin k → ZMod 2) : ℝ) := by
    calc ∑ x, u x ^ 2 = ∑ x : Fin k → ZMod 2, ∑ y ∈ B, ∑ y' ∈ B, chi (x ⬝ᵥ (y + y')) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [u, sq, Finset.sum_mul_sum, dotProduct_add, chi_add]
      _ = ∑ y ∈ B, ∑ y' ∈ B, ∑ x : Fin k → ZMod 2, chi (x ⬝ᵥ (y + y')) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ y ∈ B, ∑ y' ∈ B,
            (if y = y' then (Fintype.card (Fin k → ZMod 2) : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
          rw [charSum_left]
          simp only [add_eq_zero_iff_eq]
      _ = B.card * (Fintype.card (Fin k → ZMod 2) : ℝ) := by
          rw [Finset.sum_congr rfl (g := fun _ => (Fintype.card (Fin k → ZMod 2) : ℝ))
            fun y hy => by simp [hy]]
          simp
  have hA : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  calc (∑ x ∈ A, u x) ^ 2 ≤ A.card * ∑ x ∈ A, u x ^ 2 := h1
    _ ≤ A.card * ∑ x, u x ^ 2 := mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by rw [h3]; ring

/-- The edge count `e_G(A, B)` as a double sum of the adjacency indicator. -/
theorem edgesBetween_eq_sum {k : ℕ} (A B : Finset (Fin k → ZMod 2)) :
    (simpleEdgesBetween (ipGraph k) A B : ℝ) = ∑ x ∈ A, ∑ y ∈ B, adjInd x y := by
  classical
  unfold simpleEdgesBetween
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  simp [adjInd]

/-- Edge counts are invariant under relabelling: `e_{G ∘ e}(A, B) = e_G(e(A), e(B))`. -/
theorem simpleEdgesBetween_comap {W W' : Type*} [Fintype W] [Fintype W'] (G : SimpleGraph W)
    (e : W' ≃ W) (A B : Finset W') :
    simpleEdgesBetween (G.comap e) A B =
      simpleEdgesBetween G (A.map e.toEmbedding) (B.map e.toEmbedding) := by
  classical
  unfold simpleEdgesBetween
  apply Finset.card_equiv (e.prodCongr e)
  intro p
  simp

/-- Discrepancy of the inner-product graph: for all `A, B ⊆ F₂^k`,
`|e(A, B) - |A||B|/2| ≤ n + |T|/2` with `T² ≤ n³`, `n = 2^k`; we record the consequence that
`|e(A, B) - |A||B|/2| ≤ ε n²` once `n ≥ 2/ε` and `n ≥ 4/ε²`. -/
theorem ipGraph_discrepancy {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn1 : 2 / ε ≤ (Fintype.card (Fin k → ZMod 2) : ℝ))
    (hn2 : 4 / ε ^ 2 ≤ (Fintype.card (Fin k → ZMod 2) : ℝ))
    (A B : Finset (Fin k → ZMod 2)) :
    |(simpleEdgesBetween (ipGraph k) A B : ℝ) - 1 / 2 * A.card * B.card| ≤
      ε * (Fintype.card (Fin k → ZMod 2) : ℝ) ^ 2 := by
  classical
  generalize hn' : (Fintype.card (Fin k → ZMod 2) : ℝ) = n at hn1 hn2
  have hAn : (A.card : ℝ) ≤ n := by
    rw [← hn']; exact_mod_cast Finset.card_le_univ A
  have hBn : (B.card : ℝ) ≤ n := by
    rw [← hn']; exact_mod_cast Finset.card_le_univ B
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  set T := ∑ x ∈ A, ∑ y ∈ B, chi (x ⬝ᵥ y) with hT
  have hL := lindsey A B
  rw [← hT, hn'] at hL
  -- the dot-product count
  have hdot : ∑ x ∈ A, ∑ y ∈ B, dotInd x y = A.card * B.card / 2 - T / 2 := by
    simp only [dotInd_eq, hT, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one]
    ring
  -- the diagonal correction
  have hdiag0 : 0 ≤ ∑ x ∈ A, ∑ y ∈ B, (dotInd x y - adjInd x y) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      sub_nonneg.mpr (adjInd_le_dotInd x y)
  have hdiag1 : ∑ x ∈ A, ∑ y ∈ B, (dotInd x y - adjInd x y) ≤ n := by
    calc ∑ x ∈ A, ∑ y ∈ B, (dotInd x y - adjInd x y)
        ≤ ∑ x ∈ A, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          calc ∑ y ∈ B, (dotInd x y - adjInd x y)
              ≤ ∑ y ∈ B, (if x = y then (1 : ℝ) else 0) :=
                Finset.sum_le_sum fun y _ => dotInd_sub_adjInd_le x y
            _ ≤ 1 := by rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
      _ ≤ n := by simpa using hAn
  have he : (simpleEdgesBetween (ipGraph k) A B : ℝ) =
      ∑ x ∈ A, ∑ y ∈ B, dotInd x y - ∑ x ∈ A, ∑ y ∈ B, (dotInd x y - adjInd x y) := by
    rw [edgesBetween_eq_sum]
    simp only [Finset.sum_sub_distrib]
    ring
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn1
  -- `|T| ≤ ε n² / 2`
  have hT2 : T ^ 2 ≤ (ε * n ^ 2 / 2) ^ 2 := by
    have h4 : 4 ≤ ε ^ 2 * n := by
      rw [div_le_iff₀ (by positivity)] at hn2; linarith
    calc T ^ 2 ≤ A.card * B.card * n := hL
      _ ≤ n * n * n := by
          apply mul_le_mul_of_nonneg_right _ hn0.le
          exact mul_le_mul hAn hBn hB0 hn0.le
      _ ≤ (ε * n ^ 2 / 2) ^ 2 := by nlinarith
  have hTabs := abs_le_of_sq_le_sq hT2 (by positivity)
  have hnε : n ≤ ε * n ^ 2 / 2 := by
    rw [div_le_iff₀ hε] at hn1
    nlinarith
  rw [he, hdot, abs_le]
  rw [abs_le] at hTabs
  constructor <;> nlinarith

/-- **The witness is quasi-random** (optional; not needed for the antecedent): for every
`ε > 0`, eventually `|e_{G_k}(A, B) - |A||B|/2| ≤ ε (2^k)²` for all `A, B ⊆ Fin (2^k)`. So the
witness also satisfies the conclusion of the forcing half at `p = 1/2`, unconditionally. -/
theorem ipSeq_quasirandom :
    ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ A B : Finset (Fin (2 ^ k)),
      |(simpleEdgesBetween (ipSeq k) A B : ℝ) - 1 / 2 * A.card * B.card| ≤
        ε * ((2 ^ k : ℕ) : ℝ) ^ 2 := by
  intro ε hε
  have hlim : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  filter_upwards [hlim.eventually_ge_atTop (2 / ε), hlim.eventually_ge_atTop (4 / ε ^ 2)]
    with k h1 h2 A B
  have hc : (Fintype.card (Fin k → ZMod 2) : ℝ) = 2 ^ k := by rw [card_W]; push_cast; ring
  rw [ipSeq, simpleEdgesBetween_comap]
  have := ipGraph_discrepancy (k := k) hε (hc ▸ h1) (hc ▸ h2)
    (A.map (relabel k).toEmbedding) (B.map (relabel k).toEmbedding)
  simpa [hc] using this

end KConj1

end NieWeiOrientedSidorenko
