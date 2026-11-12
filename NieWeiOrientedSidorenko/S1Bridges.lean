import NieWeiOrientedSidorenko.Section1Aux

/-!
# Section 1: the Question 1(c) bridges

Proofs of `OrientedGraph.isOS_iff_isOSK`, `OrientedGraph.isOAS_iff_isOASK` and
`OrientedGraph.isSymmetryForcing_iff_isSymmetryForcingK` (as `*_proof`), in the namespace
`NieWeiOrientedSidorenko.S1Bridges`.

* Finite hosts to digraphons (OS/OAS): the answer key's sampling argument. For `x ∈ [0,1]^n`
  and `q = W/2`, every unordered pair `{i, j}` is independently oriented `i → j` with probability
  `q(x_i, x_j)`, `j → i` with probability `q(x_j, x_i)`, or left empty; the average over these
  orientations is a finite weighted sum. Injective maps give the kernel integrands exactly,
  noninjective maps contribute at most `1 - (n)_v / n^v → 0`.
* Digraphons to finite hosts: substitution of the step digraphon of the host.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace S1Bridges

open OrientedGraph

set_option linter.unusedSectionVars false

/-! ## Finite densities as sums -/

section FiniteSums

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma mem_arcs (D : OrientedGraph V) (p : V × V) : p ∈ D.arcs ↔ D.Adj p.1 p.2 := by
  classical
  unfold OrientedGraph.arcs
  simp

lemma underlying_adj {W' : Type*} (G : OrientedGraph W') (a b : W') :
    G.underlying.Adj a b ↔ a ≠ b ∧ (G.Adj a b ∨ G.Adj b a) := by
  simp [OrientedGraph.underlying, SimpleGraph.fromRel_adj]

lemma homDensity_eq_sum {W' : Type*} [Fintype W'] (D : OrientedGraph V) (G : OrientedGraph W')
    [DecidableRel G.Adj] :
    homDensity D G = ((Fintype.card W' : ℝ)⁻¹) ^ Fintype.card V *
      ∑ f : V → W', ∏ a ∈ D.arcs, (if G.Adj (f a.1) (f a.2) then (1 : ℝ) else 0) := by
  classical
  have h : ∀ f : V → W', (∏ a ∈ D.arcs, (if G.Adj (f a.1) (f a.2) then (1 : ℝ) else 0)) =
      if (∀ u v, D.Adj u v → G.Adj (f u) (f v)) then 1 else 0 := by
    intro f
    rw [Finset.prod_boole]
    congr 1
    apply propext
    constructor
    · intro h u v huv; exact h (u, v) ((mem_arcs D _).2 huv)
    · intro h a ha; exact h a.1 a.2 ((mem_arcs D a).1 ha)
  simp_rw [h]
  rw [Finset.sum_boole]
  unfold homDensity homCount
  rw [inv_pow, ← div_eq_inv_mul]
  congr 2
  congr 1
  ext f; simp

lemma symmDensity_eq_sum {W' : Type*} [Fintype W'] (D : OrientedGraph V) (G : OrientedGraph W')
    [DecidableRel G.underlying.Adj] :
    symmDensity D G = (2 : ℝ)⁻¹ ^ D.numArcs * (((Fintype.card W' : ℝ)⁻¹) ^ Fintype.card V *
      ∑ f : V → W', ∏ a ∈ D.arcs,
        (if G.underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0)) := by
  classical
  have h : ∀ f : V → W', (∏ a ∈ D.arcs,
      (if G.underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0)) =
      if (∀ u v, D.underlying.Adj u v → G.underlying.Adj (f u) (f v)) then 1 else 0 := by
    intro f
    rw [Finset.prod_boole]
    congr 1
    apply propext
    constructor
    · intro h u v huv
      rw [underlying_adj] at huv
      rcases huv.2 with h1 | h1
      · exact h (u, v) ((mem_arcs D _).2 h1)
      · exact (h (v, u) ((mem_arcs D _).2 h1)).symm
    · intro h a ha
      have ha' := (mem_arcs D a).1 ha
      exact h a.1 a.2 ((underlying_adj D _ _).2 ⟨fun he => D.irrefl a.1 (by
        rw [he] at ha' ⊢; exact ha'), Or.inl ha'⟩)
  simp_rw [h]
  rw [Finset.sum_boole]
  unfold symmDensity simpleHomDensity simpleHomCount
  rw [div_eq_inv_mul, inv_pow, inv_pow]
  congr 2
  congr 1
  congr 1
  ext f; simp

end FiniteSums

/-! ## Step kernels of finite hosts -/

section Host

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Integrals of functions of the equipartition indices are finite averages. -/
lemma integral_comp_equipart {Z : Type*} [Fintype Z] [DecidableEq Z] (n : ℕ) (hn : 0 < n)
    (F : (Z → Fin n) → ℝ) :
    ∫ x : Z → I, F (fun v => equipartIdx n hn (x v))
        ∂(Measure.pi fun _ => (volume : Measure I)) =
      ((n : ℝ)⁻¹) ^ Fintype.card Z * ∑ g, F g := by
  let P : (Z → I) → (Z → Fin n) := fun x v => equipartIdx n hn (x v)
  have hP : Measurable P := measurable_pi_iff.2 fun v =>
    (Section4Aux.measurable_equipartIdx n hn).comp (measurable_pi_apply v)
  have : (∫ x : Z → I, F (fun v => equipartIdx n hn (x v))
      ∂(Measure.pi fun _ => (volume : Measure I))) =
      ∫ x, F (P x) ∂(Measure.pi fun _ : Z => (volume : Measure I)) := rfl
  rw [this, ← integral_map hP.aemeasurable (measurable_of_countable F).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite), Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [measureReal_def, Measure.map_apply hP (measurableSet_singleton _)]
  have : P ⁻¹' {φ} = Set.pi univ fun v => equipartIdx n hn ⁻¹' {φ v} := by
    ext x; simp [P, funext_iff]
  rw [this, Measure.pi_pi]
  simp only [Section4Aux.volume_equipartIdx, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity), one_div]

lemma card_eq_of_equiv {W' : Type*} [Fintype W'] {n : ℕ} (e : Fin n ≃ W') :
    Fintype.card W' = n := by
  rw [← Fintype.card_fin n]; exact (Fintype.card_congr e).symm

lemma t_hostKer {W' : Type*} [Fintype W'] (D : OrientedGraph V) (G : OrientedGraph W')
    (n : ℕ) (hn : 0 < n) (e : Fin n ≃ W') :
    t D (Section4Aux.hostKer G n hn e) = homDensity D G := by
  classical
  rw [homDensity_eq_sum, card_eq_of_equiv e]
  have : t D (Section4Aux.hostKer G n hn e) = ((n : ℝ)⁻¹) ^ Fintype.card V *
      ∑ g : V → Fin n, ∏ a ∈ D.arcs,
        if G.Adj (e (g a.1)) (e (g a.2)) then (1 : ℝ) else 0 := by
    rw [← integral_comp_equipart]
    unfold t tDir Section4Aux.hostKer
    rfl
  rw [this]
  congr 1
  exact Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl V) e) _ _ (fun g => rfl)

lemma half_ind {W' : Type*} (G : OrientedGraph W') [DecidableRel G.Adj]
    [DecidableRel G.underlying.Adj] (a b : W') :
    ((if G.Adj a b then (1 : ℝ) else 0) + (if G.Adj b a then (1 : ℝ) else 0)) / 2 =
      (2 : ℝ)⁻¹ * (if G.underlying.Adj a b then 1 else 0) := by
  by_cases h1 : G.Adj a b
  · have h2 : ¬ G.Adj b a := G.asymm a b h1
    have h3 : G.underlying.Adj a b := (underlying_adj G a b).2
      ⟨fun h => G.irrefl a (by rw [h] at h1 ⊢; exact h1), Or.inl h1⟩
    simp [h1, h2, h3]
  · by_cases h2 : G.Adj b a
    · have h3 : G.underlying.Adj a b := (underlying_adj G a b).2
        ⟨fun h => G.irrefl a (by rw [h] at h2 ⊢; exact h2), Or.inr h2⟩
      simp [h1, h2, h3]
    · have h3 : ¬ G.underlying.Adj a b := fun h => by
        rcases ((underlying_adj G a b).1 h).2 with h' | h' <;> contradiction
      simp [h1, h2, h3]

lemma t_symm_hostKer {W' : Type*} [Fintype W'] (D : OrientedGraph V) (G : OrientedGraph W')
    (n : ℕ) (hn : 0 < n) (e : Fin n ≃ W') :
    t D (symmetrize (Section4Aux.hostKer G n hn e)) = symmDensity D G := by
  classical
  rw [symmDensity_eq_sum, card_eq_of_equiv e]
  have : t D (symmetrize (Section4Aux.hostKer G n hn e)) = ((n : ℝ)⁻¹) ^ Fintype.card V *
      ∑ g : V → Fin n, ∏ a ∈ D.arcs,
        ((if G.Adj (e (g a.1)) (e (g a.2)) then (1 : ℝ) else 0) +
          (if G.Adj (e (g a.2)) (e (g a.1)) then (1 : ℝ) else 0)) / 2 := by
    rw [← integral_comp_equipart]
    unfold t tDir symmetrize Section4Aux.hostKer
    rfl
  rw [this]
  simp_rw [half_ind, Finset.prod_mul_distrib, Finset.prod_const]
  rw [← Finset.mul_sum]
  have h2 : D.arcs.card = D.numArcs := rfl
  rw [h2]
  have := Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl V) e)
    (fun g : V → Fin n => ∏ a ∈ D.arcs,
      if G.underlying.Adj (e (g a.1)) (e (g a.2)) then (1 : ℝ) else 0)
    (fun f : V → W' => ∏ a ∈ D.arcs, if G.underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0)
    (fun g => rfl)
  rw [this]
  ring

lemma osk_to_os (D : OrientedGraph V) (h : D.IsOSK) : D.IsOS := by
  intro W' _ _ G
  set n := Fintype.card W'
  have hn : 0 < n := Fintype.card_pos
  let e : Fin n ≃ W' := (Fintype.equivFin W').symm
  have := h _ (Section4Aux.isDigraphon_hostKer G n hn e)
  rwa [t_hostKer, t_symm_hostKer] at this

lemma oask_to_oas (D : OrientedGraph V) (h : D.IsOASK) : D.IsOAS := by
  intro W' _ _ G
  set n := Fintype.card W'
  have hn : 0 < n := Fintype.card_pos
  let e : Fin n ≃ W' := (Fintype.equivFin W').symm
  have := h _ (Section4Aux.isDigraphon_hostKer G n hn e)
  rwa [t_hostKer, t_symm_hostKer] at this

end Host

/-! ## Random orientations as finite weighted averages -/

section Orient

variable {n : ℕ}

/-- The oriented graph on `Fin n` coded by `c`: for `i < j`, `c (i, j) = 1` means `i → j`,
`c (i, j) = 2` means `j → i`, and `c (i, j) = 0` means no arc. -/
def orientOf (c : Fin n × Fin n → Fin 3) : OrientedGraph (Fin n) where
  Adj i j := (i < j ∧ c (i, j) = 1) ∨ (j < i ∧ c (j, i) = 2)
  irrefl i h := by rcases h with h | h <;> exact lt_irrefl _ h.1
  asymm i j h h' := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact lt_asymm h1 h3
    · rw [h2] at h4; exact absurd h4 (by decide)
    · rw [h2] at h4; exact absurd h4 (by decide)
    · exact lt_asymm h1 h3

/-- The sorted pair. -/
def key (i j : Fin n) : Fin n × Fin n := if i < j then (i, j) else (j, i)

/-- The code of the direction `i → j`. -/
def dir (i j : Fin n) : Fin 3 := if i < j then 1 else 2

lemma orientOf_adj_iff (c : Fin n × Fin n → Fin 3) {i j : Fin n} (h : i ≠ j) :
    (orientOf c).Adj i j ↔ c (key i j) = dir i j := by
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [orientOf, key, dir, h', not_lt.2 h'.le]
  · simp [orientOf, key, dir, h', not_lt.2 h'.le]

lemma orientOf_und_iff (c : Fin n × Fin n → Fin 3) {i j : Fin n} (h : i ≠ j) :
    (orientOf c).underlying.Adj i j ↔ c (key i j) ≠ 0 := by
  rw [underlying_adj, orientOf_adj_iff c h, orientOf_adj_iff c h.symm]
  have hk : ∀ k : Fin 3, (k = 1 ∨ k = 2) ↔ k ≠ 0 := by decide
  have hk' : ∀ k : Fin 3, (k = 2 ∨ k = 1) ↔ k ≠ 0 := by decide
  rcases lt_or_gt_of_ne h with h' | h'
  · simp only [key, dir, h', not_lt.2 h'.le, if_true, if_false, ne_eq, h, not_false_eq_true,
      true_and]
    exact hk _
  · simp only [key, dir, h', not_lt.2 h'.le, if_true, if_false, ne_eq, h, not_false_eq_true,
      true_and]
    exact hk' _

lemma key_eq {i j i' j' : Fin n} (he : key i j = key i' j') :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  unfold key at he
  split_ifs at he <;> simp only [Prod.mk.injEq] at he <;> tauto

/-- The orientation probabilities of the pair `p`. -/
noncomputable def ω (Q : Fin n → Fin n → ℝ) (p : Fin n × Fin n) (k : Fin 3) : ℝ :=
  if p.1 < p.2 then
    (if k = 0 then 1 - Q p.1 p.2 - Q p.2 p.1 else if k = 1 then Q p.1 p.2 else Q p.2 p.1)
  else (if k = 0 then 1 else 0)

lemma sum_ω (Q : Fin n → Fin n → ℝ) (p : Fin n × Fin n) : ∑ k, ω Q p k = 1 := by
  unfold ω
  split_ifs
  · simp [Fin.sum_univ_three]; ring
  · simp [Fin.sum_univ_three]

lemma ω_nonneg {Q : Fin n → Fin n → ℝ} (hQ0 : ∀ i j, 0 ≤ Q i j)
    (hQ1 : ∀ i j, Q i j + Q j i ≤ 1) (p : Fin n × Fin n) (k : Fin 3) : 0 ≤ ω Q p k := by
  unfold ω
  have := hQ1 p.1 p.2
  split_ifs <;> linarith [hQ0 p.1 p.2, hQ0 p.2 p.1]

lemma sum_ω_dir (Q : Fin n → Fin n → ℝ) {i j : Fin n} (h : i ≠ j) :
    ∑ k, ω Q (key i j) k * (if k = dir i j then 1 else 0) = Q i j := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [ω, key, dir, h']
  · simp [ω, key, dir, h', not_lt.2 h'.le]

lemma sum_ω_ne (Q : Fin n → Fin n → ℝ) {i j : Fin n} (h : i ≠ j) :
    ∑ k, ω Q (key i j) k * (if k = 0 then 0 else 1) = Q i j + Q j i := by
  rw [Fin.sum_univ_three]
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [ω, key, h']
  · simp [ω, key, h', not_lt.2 h'.le]; ring

/-- Independence: averaging a product of functions of distinct pairs. -/
lemma sum_wt_prod {α : Type*} (w : Fin n × Fin n → Fin 3 → ℝ) (hw : ∀ p, ∑ k, w p k = 1)
    (s : Finset α) (g : α → Fin n × Fin n) (hg : Set.InjOn g s) (e : α → Fin 3 → ℝ) :
    ∑ c : Fin n × Fin n → Fin 3, (∏ p, w p (c p)) * ∏ a ∈ s, e a (c (g a)) =
      ∏ a ∈ s, ∑ k, w (g a) k * e a k := by
  classical
  have h1 : ∀ c : Fin n × Fin n → Fin 3, (∏ p, w p (c p)) * ∏ a ∈ s, e a (c (g a)) =
      ∏ p, (w p (c p) * ∏ a ∈ s with g a = p, e a (c p)) := by
    intro c
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_fiberwise s g (fun a => e a (c (g a)))]
    refine Finset.prod_congr rfl fun p _ => Finset.prod_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun p k => w p k * ∏ a ∈ s with g a = p, e a k)]
  rw [← Finset.prod_fiberwise s g (fun a => ∑ k, w (g a) k * e a k)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hcard : (s.filter (fun a => g a = p)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact hg (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1
      ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
  · rw [Finset.card_eq_zero.1 h0]; simp [hw p]
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    have hmem : a ∈ s.filter (fun a => g a = p) := by rw [ha]; exact Finset.mem_singleton_self a
    have hga : g a = p := (Finset.mem_filter.1 hmem).2
    rw [ha]; simp [hga]

end Orient

section Sampling

variable {V : Type u} [Fintype V] [DecidableEq V] {n : ℕ}

omit [DecidableEq V] in
lemma injOn_key (D : OrientedGraph V) {f : V → Fin n} (hf : Function.Injective f) :
    Set.InjOn (fun a : V × V => key (f a.1) (f a.2)) D.arcs := by
  intro a ha b hb he
  have ha' := (mem_arcs D a).1 ha
  have hb' := (mem_arcs D b).1 hb
  rcases key_eq he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext (hf h1) (hf h2)
  · rw [hf h1, hf h2] at ha'
    exact absurd ha' (D.asymm _ _ hb')

omit [DecidableEq V] in
lemma ne_of_arc (D : OrientedGraph V) {f : V → Fin n} (hf : Function.Injective f) {a : V × V}
    (ha : a ∈ D.arcs) : f a.1 ≠ f a.2 := fun h => by
  have := (mem_arcs D a).1 ha
  rw [hf h] at this
  exact D.irrefl _ this

omit [DecidableEq V] in
open scoped Classical in
/-- Expected arc indicator product for an injective map. -/
lemma avg_ind_inj (D : OrientedGraph V) (Q : Fin n → Fin n → ℝ) {f : V → Fin n}
    (hf : Function.Injective f) :
    ∑ c : Fin n × Fin n → Fin 3, (∏ p, ω Q p (c p)) *
      ∏ a ∈ D.arcs, (if (orientOf c).Adj (f a.1) (f a.2) then (1 : ℝ) else 0) =
      ∏ a ∈ D.arcs, Q (f a.1) (f a.2) := by
  classical
  have h : ∀ c : Fin n × Fin n → Fin 3, ∏ a ∈ D.arcs,
      (if (orientOf c).Adj (f a.1) (f a.2) then (1 : ℝ) else 0) =
      ∏ a ∈ D.arcs, (fun (a : V × V) (k : Fin 3) => if k = dir (f a.1) (f a.2) then (1 : ℝ) else 0)
        a (c (key (f a.1) (f a.2))) := by
    intro c
    refine Finset.prod_congr rfl fun a ha => ?_
    simp only [orientOf_adj_iff c (ne_of_arc D hf ha)]
  simp_rw [h]
  refine (sum_wt_prod _ (sum_ω Q) D.arcs (fun a => key (f a.1) (f a.2)) (injOn_key D hf)
    (fun a k => if k = dir (f a.1) (f a.2) then (1 : ℝ) else 0)).trans ?_
  exact Finset.prod_congr rfl fun a ha => sum_ω_dir Q (ne_of_arc D hf ha)

omit [DecidableEq V] in
open scoped Classical in
lemma avg_sind_inj (D : OrientedGraph V) (Q : Fin n → Fin n → ℝ) {f : V → Fin n}
    (hf : Function.Injective f) :
    ∑ c : Fin n × Fin n → Fin 3, (∏ p, ω Q p (c p)) *
      ∏ a ∈ D.arcs, (if (orientOf c).underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0) =
      ∏ a ∈ D.arcs, (Q (f a.1) (f a.2) + Q (f a.2) (f a.1)) := by
  classical
  have h : ∀ c : Fin n × Fin n → Fin 3, ∏ a ∈ D.arcs,
      (if (orientOf c).underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0) =
      ∏ a ∈ D.arcs, (fun (_ : V × V) (k : Fin 3) => if k = 0 then (0 : ℝ) else 1)
        a (c (key (f a.1) (f a.2))) := by
    intro c
    refine Finset.prod_congr rfl fun a ha => ?_
    simp only [orientOf_und_iff c (ne_of_arc D hf ha), ne_eq, ite_not]
  simp_rw [h]
  refine (sum_wt_prod _ (sum_ω Q) D.arcs (fun a => key (f a.1) (f a.2)) (injOn_key D hf)
    (fun _ k => if k = 0 then (0 : ℝ) else 1)).trans ?_
  exact Finset.prod_congr rfl fun a ha => sum_ω_ne Q (ne_of_arc D hf ha)

/-- Averages of `[0,1]`-valued map statistics: injective maps are exact, the others cost at
most `1` each. -/
lemma avg_bounds {C Fm : Type*} [Fintype C] [Fintype Fm] (P : Fm → Prop) [DecidablePred P]
    (wt : C → ℝ) (hwt0 : ∀ c, 0 ≤ wt c) (hwt1 : ∑ c, wt c = 1) (Y : C → Fm → ℝ)
    (hY0 : ∀ c f, 0 ≤ Y c f) (hY1 : ∀ c f, Y c f ≤ 1) (y : Fm → ℝ)
    (hy : ∀ f, P f → ∑ c, wt c * Y c f = y f) :
    ∑ f ∈ Finset.univ.filter P, y f ≤ ∑ c, wt c * ∑ f, Y c f ∧
      ∑ c, wt c * ∑ f, Y c f ≤
        ∑ f ∈ Finset.univ.filter P, y f + ((Finset.univ.filter fun f => ¬ P f).card : ℝ) := by
  have e : ∑ c, wt c * ∑ f, Y c f = ∑ f, ∑ c, wt c * Y c f := by
    simp_rw [Finset.mul_sum]; exact Finset.sum_comm
  rw [e, ← Finset.sum_filter_add_sum_filter_not Finset.univ P]
  have h1 : ∑ f ∈ Finset.univ.filter P, ∑ c, wt c * Y c f = ∑ f ∈ Finset.univ.filter P, y f :=
    Finset.sum_congr rfl fun f hf => hy f (Finset.mem_filter.1 hf).2
  rw [h1]
  have h2 : 0 ≤ ∑ f ∈ Finset.univ.filter (fun f => ¬ P f), ∑ c, wt c * Y c f :=
    Finset.sum_nonneg fun f _ => Finset.sum_nonneg fun c _ => mul_nonneg (hwt0 c) (hY0 c f)
  have h3 : ∑ f ∈ Finset.univ.filter (fun f => ¬ P f), ∑ c, wt c * Y c f ≤
      ((Finset.univ.filter fun f => ¬ P f).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_le_sum fun f _ => ?_
    calc ∑ c, wt c * Y c f ≤ ∑ c, wt c * 1 :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hY1 c f) (hwt0 c)
      _ = 1 := by simp [hwt1]
  constructor <;> linarith

lemma ind_mem {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    0 ≤ ∏ a ∈ s, (if P a then (1 : ℝ) else 0) ∧ ∏ a ∈ s, (if P a then (1 : ℝ) else 0) ≤ 1 := by
  refine ⟨Finset.prod_nonneg fun a _ => by split_ifs <;> norm_num,
    Finset.prod_le_one₀ (fun a _ => by split_ifs <;> norm_num) fun a _ => by
      split_ifs <;> norm_num⟩

end Sampling

section Integration

variable {V : Type u} [Fintype V] [DecidableEq V] {n : ℕ}

omit [DecidableEq V] in
lemma mp_comp_inj {f : V → Fin n} (hf : Function.Injective f) :
    MeasurePreserving (fun (x : Fin n → I) (v : V) => x (f v))
      (Measure.pi fun _ : Fin n => (volume : Measure I))
      (Measure.pi fun _ : V => (volume : Measure I)) := by
  classical
  have hm : Measurable (fun (x : Fin n → I) (v : V) => x (f v)) :=
    measurable_pi_iff.2 fun v => measurable_pi_apply _
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hch : ∀ v, Classical.choose (⟨v, rfl⟩ : ∃ w, f w = f v) = v := fun v =>
    hf (Classical.choose_spec (⟨v, rfl⟩ : ∃ w, f w = f v))
  let s' : Fin n → Set I := fun j => if h : ∃ v, f v = j then s (Classical.choose h) else univ
  have hpre : (fun (x : Fin n → I) (v : V) => x (f v)) ⁻¹' (Set.pi univ s) =
      Set.pi univ s' := by
    ext x
    simp only [mem_preimage, Set.mem_univ_pi, s']
    constructor
    · intro h j
      split_ifs with hj
      · have := Classical.choose_spec hj
        have h2 := h (Classical.choose hj)
        rw [this] at h2
        exact h2
      · trivial
    · intro h v
      have := h (f v)
      rw [dif_pos ⟨v, rfl⟩, hch v] at this
      exact this
  rw [hpre, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective f hf _ _ (fun j hj => ?_) (fun v => ?_)
  · have : ¬ ∃ v, f v = j := fun ⟨v, hv⟩ => hj ⟨v, hv⟩
    simp only [s', dif_neg this, measure_univ]
  · simp only [s', dif_pos (⟨v, rfl⟩ : ∃ w, f w = f v), hch v]

omit [DecidableEq V] in
lemma integrable_inj (D : OrientedGraph V) {K : I → I → ℝ} (hK : IsDigraphon K) (f : V → Fin n) :
    Integrable (fun x : Fin n → I => ∏ a ∈ D.arcs, K (x (f a.1)) (x (f a.2)))
      (Measure.pi fun _ => (volume : Measure I)) := by
  refine Integrable.of_bound (Finset.measurable_prod _ fun p _ =>
    Section1Aux.measurable_pair hK.1 _ _).aestronglyMeasurable 1 (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p _ => by
    rw [abs_le]; constructor <;> linarith [(hK.2 (x (f p.1)) (x (f p.2))).1,
      (hK.2 (x (f p.1)) (x (f p.2))).2]

omit [DecidableEq V] in
lemma integral_comp_inj (D : OrientedGraph V) {K : I → I → ℝ} (hK : IsDigraphon K)
    {f : V → Fin n} (hf : Function.Injective f) :
    ∫ x : Fin n → I, ∏ a ∈ D.arcs, K (x (f a.1)) (x (f a.2))
      ∂(Measure.pi fun _ => (volume : Measure I)) = t D K := by
  have hmp := mp_comp_inj (V := V) hf
  have hint := Section1Aux.integrable_arcs D hK
  unfold t tDir
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hint.aestronglyMeasurable)]

/-- The number of injective maps `V → Fin n`. -/
noncomputable abbrev nInj (V : Type u) [Fintype V] [DecidableEq V] (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : V → Fin n => Function.Injective f).card

lemma nInj_eq (n : ℕ) : nInj V n = n.descFactorial (Fintype.card V) := by
  classical
  rw [nInj, ← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding V
    (Fin n)), Fintype.card_embedding_eq, Fintype.card_fin]

lemma nNonInj_eq (n : ℕ) :
    ((Finset.univ.filter fun f : V → Fin n => ¬ Function.Injective f).card : ℝ) =
      (n : ℝ) ^ Fintype.card V - nInj V n := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (V → Fin n)))
    (fun f => Function.Injective f)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at this
  rw [eq_sub_iff_add_eq, add_comm, nInj]
  exact_mod_cast this

lemma tendsto_nInj :
    Tendsto (fun n : ℕ => (nInj V n : ℝ) / (n : ℝ) ^ Fintype.card V) atTop (𝓝 1) := by
  set v := Fintype.card V
  have hlow : Tendsto (fun n : ℕ => (1 - (v : ℝ) / n) ^ v) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (v : ℝ))).pow v
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (v + 1)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [nInj_eq, le_div_iff₀ (by positivity), ← mul_pow]
    have h1 : (1 - (v : ℝ) / n) * n = (n - v : ℕ) := by
      rw [Nat.cast_sub (by omega)]; field_simp
    rw [h1]
    calc ((n - v : ℕ) : ℝ) ^ v ≤ ((n + 1 - v : ℕ) : ℝ) ^ v := by
          gcongr; omega
      _ ≤ (n.descFactorial v : ℝ) := by exact_mod_cast Nat.pow_sub_le_descFactorial n v
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_one (by positivity), nInj_eq]
    exact_mod_cast Nat.descFactorial_le_pow n v

/-- Passing the averaged inequality to the limit. -/
lemma le_of_avg {a b C : ℝ}
    (h : ∀ n : ℕ, 0 < n → (nInj V n : ℝ) * a ≤ nInj V n * b +
      C * ((n : ℝ) ^ Fintype.card V - nInj V n)) : a ≤ b := by
  set v := Fintype.card V
  set r : ℕ → ℝ := fun n => (nInj V n : ℝ) / (n : ℝ) ^ v
  have hr := tendsto_nInj (V := V)
  have h1 : Tendsto (fun n => r n * a) atTop (𝓝 a) := by simpa using hr.mul_const a
  have h2 : Tendsto (fun n => r n * b + C * (1 - r n)) atTop (𝓝 b) := by
    have := (hr.mul_const b).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hr).const_mul C)
    simpa using this
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ v := by have : (0 : ℝ) < n := by exact_mod_cast hn
                                          positivity
  have := h n hn
  simp only [r]
  have key : (nInj V n : ℝ) / (n : ℝ) ^ v * a - ((nInj V n : ℝ) / (n : ℝ) ^ v * b +
      C * (1 - (nInj V n : ℝ) / (n : ℝ) ^ v)) =
      ((nInj V n : ℝ) * a - ((nInj V n : ℝ) * b + C * ((n : ℝ) ^ v - nInj V n))) / (n : ℝ) ^ v := by
    field_simp
  have : ((nInj V n : ℝ) * a - ((nInj V n : ℝ) * b + C * ((n : ℝ) ^ v - nInj V n))) /
      (n : ℝ) ^ v ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  linarith

end Integration

section Bridge

variable {V : Type u} [Fintype V] [DecidableEq V] {n : ℕ}

/-- The weight of the coded orientation `c` given the sample `x`. -/
noncomputable def wt (W : I → I → ℝ) (x : Fin n → I) (c : Fin n × Fin n → Fin 3) : ℝ :=
  ∏ p, ω (fun i j => W (x i) (x j) / 2) p (c p)

lemma wt_nonneg {W : I → I → ℝ} (hW : IsDigraphon W) (x : Fin n → I) (c) : 0 ≤ wt W x c :=
  Finset.prod_nonneg fun p _ => ω_nonneg (fun i j => by linarith [(hW.2 (x i) (x j)).1])
    (fun i j => by linarith [(hW.2 (x i) (x j)).2, (hW.2 (x j) (x i)).2]) p _

lemma sum_wt (W : I → I → ℝ) (x : Fin n → I) : ∑ c, wt W x c = 1 := by
  have := sum_wt_prod (ω fun i j => W (x i) (x j) / 2) (sum_ω _) (∅ : Finset Empty)
    (fun e => e.elim) (by simp) (fun e => e.elim)
  simpa [wt] using this

/-- The sums over injective maps. -/
noncomputable def injSum (D : OrientedGraph V) (n : ℕ) (K : I → I → ℝ) (x : Fin n → I) : ℝ :=
  ∑ f ∈ Finset.univ.filter (fun f : V → Fin n => Function.Injective f),
    ∏ a ∈ D.arcs, K (x (f a.1)) (x (f a.2))

open scoped Classical in
/-- The four averaged bounds: `h = 2^{-e(D)}`, `c = n^{-v(D)}`, `N` the number of noninjective
maps. -/
lemma avg_four (D : OrientedGraph V) {W : I → I → ℝ} (hW : IsDigraphon W) (x : Fin n → I) :
    let h := (2 : ℝ)⁻¹ ^ D.numArcs
    let c := ((n : ℝ)⁻¹) ^ Fintype.card V
    let N := ((Finset.univ.filter fun f : V → Fin n => ¬ Function.Injective f).card : ℝ)
    (h * (c * injSum D n (symmetrize W) x) ≤ ∑ q, wt W x q * symmDensity D (orientOf q) ∧
      ∑ q, wt W x q * symmDensity D (orientOf q) ≤ h * (c * (injSum D n (symmetrize W) x + N))) ∧
    (c * (h * injSum D n W x) ≤ ∑ q, wt W x q * homDensity D (orientOf q) ∧
      ∑ q, wt W x q * homDensity D (orientOf q) ≤ c * (h * injSum D n W x + N)) := by
  intro h c N
  have hc : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hhom : ∀ q, homDensity D (orientOf q) = c * ∑ f : V → Fin n, ∏ a ∈ D.arcs,
      (if (orientOf q).Adj (f a.1) (f a.2) then (1 : ℝ) else 0) := fun q => by
    rw [homDensity_eq_sum, hc]
  have hsym : ∀ q, symmDensity D (orientOf q) = h * (c * ∑ f : V → Fin n, ∏ a ∈ D.arcs,
      (if (orientOf q).underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0)) := fun q => by
    rw [symmDensity_eq_sum, hc]
  have B1 := avg_bounds (fun f : V → Fin n => Function.Injective f) (wt W x)
    (wt_nonneg hW x) (sum_wt W x)
    (fun q f => ∏ a ∈ D.arcs, (if (orientOf q).Adj (f a.1) (f a.2) then (1 : ℝ) else 0))
    (fun q f => (ind_mem _ _).1) (fun q f => (ind_mem _ _).2)
    (fun f => h * ∏ a ∈ D.arcs, W (x (f a.1)) (x (f a.2))) (fun f hf => by
      rw [show (∑ q, wt W x q * ∏ a ∈ D.arcs,
          (if (orientOf q).Adj (f a.1) (f a.2) then (1 : ℝ) else 0)) =
          ∏ a ∈ D.arcs, (fun i j => W (x i) (x j) / 2) (f a.1) (f a.2) from avg_ind_inj D _ hf]
      simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, h]
      rw [mul_comm]; rfl)
  have B2 := avg_bounds (fun f : V → Fin n => Function.Injective f) (wt W x)
    (wt_nonneg hW x) (sum_wt W x)
    (fun q f => ∏ a ∈ D.arcs,
      (if (orientOf q).underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0))
    (fun q f => (ind_mem _ _).1) (fun q f => (ind_mem _ _).2)
    (fun f => ∏ a ∈ D.arcs, symmetrize W (x (f a.1)) (x (f a.2))) (fun f hf => by
      rw [show (∑ q, wt W x q * ∏ a ∈ D.arcs,
          (if (orientOf q).underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0)) =
          ∏ a ∈ D.arcs, ((fun i j => W (x i) (x j) / 2) (f a.1) (f a.2) +
            (fun i j => W (x i) (x j) / 2) (f a.2) (f a.1)) from avg_sind_inj D _ hf]
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [symmetrize]; ring)
  have eh : ∑ q, wt W x q * homDensity D (orientOf q) = c * ∑ q, wt W x q *
      ∑ f : V → Fin n, ∏ a ∈ D.arcs,
        (if (orientOf q).Adj (f a.1) (f a.2) then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => ?_; rw [hhom]; ring
  have es : ∑ q, wt W x q * symmDensity D (orientOf q) = h * (c * ∑ q, wt W x q *
      ∑ f : V → Fin n, ∏ a ∈ D.arcs,
        (if (orientOf q).underlying.Adj (f a.1) (f a.2) then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => ?_; rw [hsym]; ring
  have hinj1 : ∑ f ∈ Finset.univ.filter (fun f : V → Fin n => Function.Injective f),
      h * ∏ a ∈ D.arcs, W (x (f a.1)) (x (f a.2)) = h * injSum D n W x := by
    rw [injSum, Finset.mul_sum]
  have hh0 : 0 ≤ h := by positivity
  have hc0 : 0 ≤ c := by positivity
  rw [hinj1] at B1
  have hN1 : N ≤ (Finset.univ.filter fun f : V → Fin n => ¬ Function.Injective f).card := le_rfl
  rw [eh, es]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left B2.1 hc0) hh0
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left B2.2 hc0) hh0
  · exact mul_le_mul_of_nonneg_left B1.1 hc0
  · exact mul_le_mul_of_nonneg_left B1.2 hc0

lemma integral_injSum (D : OrientedGraph V) {K : I → I → ℝ} (hK : IsDigraphon K) :
    ∫ x, injSum D n K x ∂(Measure.pi fun _ => (volume : Measure I)) = nInj V n * t D K := by
  unfold injSum
  rw [integral_finsetSum _ fun f _ => integrable_inj D hK f]
  rw [Finset.sum_congr rfl fun f hf => integral_comp_inj D hK (Finset.mem_filter.1 hf).2]
  rw [Finset.sum_const, nsmul_eq_mul]

lemma integrable_injSum (D : OrientedGraph V) {K : I → I → ℝ} (hK : IsDigraphon K) :
    Integrable (injSum D n K) (Measure.pi fun _ => (volume : Measure I)) := by
  unfold injSum
  exact integrable_finsetSum _ fun f _ => integrable_inj D hK f

/-- Integrating a pointwise inequality between injective sums. -/
lemma integrate_ineq (D : OrientedGraph V) {K L : I → I → ℝ} (hK : IsDigraphon K)
    (hL : IsDigraphon L) (C : ℝ) (h : ∀ x : Fin n → I, injSum D n K x ≤ injSum D n L x + C) :
    (nInj V n : ℝ) * t D K ≤ nInj V n * t D L + C := by
  have hi : Integrable (fun x => injSum D n L x + C) (Measure.pi fun _ => (volume : Measure I)) :=
    (integrable_injSum D hL).add (integrable_const C)
  have := integral_mono (integrable_injSum (n := n) D hK) hi h
  rw [integral_add (integrable_injSum D hL) (integrable_const C), integral_injSum D hK,
    integral_injSum D hL, integral_const] at this
  simpa using this

lemma os_to_osk (D : OrientedGraph V) (hD : D.IsOS) : D.IsOSK := by
  intro W hW
  have hS := Section1Aux.isDigraphon_symmetrize hW
  refine le_of_avg (V := V) (C := 2 ^ D.numArcs) fun n hn => ?_
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← nNonInj_eq]
  refine integrate_ineq D hS hW _ fun x => ?_
  obtain ⟨⟨h1, _⟩, ⟨_, h4⟩⟩ := avg_four (n := n) D hW x
  have hle : ∑ q, wt W x q * symmDensity D (orientOf q) ≤
      ∑ q, wt W x q * homDensity D (orientOf q) :=
    Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hD _ _) (wt_nonneg hW x q)
  have hc : (0 : ℝ) < ((n : ℝ)⁻¹) ^ Fintype.card V := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h2 : (2 : ℝ) ^ D.numArcs * (2 : ℝ)⁻¹ ^ D.numArcs = 1 := by
    rw [← mul_pow]; norm_num
  have h3 := h1.trans (hle.trans h4)
  set N := ((Finset.univ.filter fun f : V → Fin n => ¬ Function.Injective f).card : ℝ)
  set c := ((n : ℝ)⁻¹) ^ Fintype.card V
  set h := (2 : ℝ)⁻¹ ^ D.numArcs
  have h5 : h * injSum D n (symmetrize W) x ≤ h * injSum D n W x + N := by
    have : c * (h * injSum D n (symmetrize W) x) ≤ c * (h * injSum D n W x + N) := by
      linarith
    exact le_of_mul_le_mul_left this hc
  have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 ^ D.numArcs)
  rw [mul_add, ← mul_assoc, ← mul_assoc, h2, one_mul, one_mul] at this
  exact this

lemma oas_to_oask (D : OrientedGraph V) (hD : D.IsOAS) : D.IsOASK := by
  intro W hW
  have hS := Section1Aux.isDigraphon_symmetrize hW
  refine le_of_avg (V := V) (C := 2 ^ D.numArcs) fun n hn => ?_
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← nNonInj_eq]
  refine integrate_ineq D hW hS _ fun x => ?_
  obtain ⟨⟨_, h2⟩, ⟨h3, _⟩⟩ := avg_four (n := n) D hW x
  have hle : ∑ q, wt W x q * homDensity D (orientOf q) ≤
      ∑ q, wt W x q * symmDensity D (orientOf q) :=
    Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hD _ _) (wt_nonneg hW x q)
  have hc : (0 : ℝ) < ((n : ℝ)⁻¹) ^ Fintype.card V := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h6 := h3.trans (hle.trans h2)
  set N := ((Finset.univ.filter fun f : V → Fin n => ¬ Function.Injective f).card : ℝ)
  set c := ((n : ℝ)⁻¹) ^ Fintype.card V
  set h := (2 : ℝ)⁻¹ ^ D.numArcs
  have hh : 0 < h := by positivity
  have hN : 0 ≤ N := by positivity
  have h5 : injSum D n W x ≤ injSum D n (symmetrize W) x + N := by
    have : c * (h * injSum D n W x) ≤ c * (h * (injSum D n (symmetrize W) x + N)) := by
      rw [← mul_assoc, ← mul_assoc, mul_comm c h, mul_assoc, mul_assoc]; linarith
    exact le_of_mul_le_mul_left (le_of_mul_le_mul_left this hc) hh
  have h1 : (1 : ℝ) ≤ 2 ^ D.numArcs := one_le_pow₀ (by norm_num)
  nlinarith

end Bridge

/-! ## Cut norm and the map-based cut distance -/

section Cut

lemma intOn {F : I → I → ℝ} (hF : IsKernel F) (s : Set (I × I)) :
    IntegrableOn (fun p : I × I => F p.1 p.2) s (volume : Measure (I × I)) := by
  obtain ⟨M, hM⟩ := hF.2
  exact (Integrable.of_bound hF.1.aestronglyMeasurable M (Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]; exact hM _ _)).integrableOn

lemma abs_rect_le {F : I → I → ℝ} (hF : IsKernel F) :
    ∃ M, ∀ S T : Set I, |∫ p in S ×ˢ T, F p.1 p.2| ≤ M := by
  obtain ⟨M, hM⟩ := hF.2
  refine ⟨|M|, fun S T => ?_⟩
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure I).prod volume)
    (s := S ×ˢ T) (f := fun p : I × I => F p.1 p.2) (C := |M|) (measure_lt_top _ _)
    (fun p _ => by rw [Real.norm_eq_abs]; exact (hM _ _).trans (le_abs_self M))
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have : ((volume : Measure I).prod volume).real (S ×ˢ T) ≤ 1 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one (μ := (volume : Measure I).prod volume) (s := S ×ˢ T)))
  calc |M| * ((volume : Measure I).prod volume).real (S ×ˢ T) ≤ |M| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg M)
    _ = |M| := mul_one _

lemma bdd_cut {F : I → I → ℝ} (hF : IsKernel F) :
    BddAbove {r | ∃ S T : Set I, MeasurableSet S ∧ MeasurableSet T ∧
      r = |∫ p in S ×ˢ T, F p.1 p.2|} := by
  obtain ⟨M, hM⟩ := abs_rect_le hF
  exact ⟨M, by rintro _ ⟨S, T, _, _, rfl⟩; exact hM S T⟩

lemma le_cutNorm {F : I → I → ℝ} (hF : IsKernel F) {S T : Set I} (hS : MeasurableSet S)
    (hT : MeasurableSet T) : |∫ p in S ×ˢ T, F p.1 p.2| ≤ cutNorm F :=
  le_csSup (bdd_cut hF) ⟨S, T, hS, hT, rfl⟩

lemma cutNorm_le {F : I → I → ℝ} {c : ℝ}
    (h : ∀ S T : Set I, MeasurableSet S → MeasurableSet T → |∫ p in S ×ˢ T, F p.1 p.2| ≤ c) :
    cutNorm F ≤ c :=
  csSup_le ⟨_, ∅, ∅, MeasurableSet.empty, MeasurableSet.empty, rfl⟩
    (by rintro _ ⟨S, T, hS, hT, rfl⟩; exact h S T hS hT)

lemma cutNorm_nonneg (F : I → I → ℝ) : 0 ≤ cutNorm F :=
  Real.sSup_nonneg (by rintro _ ⟨S, T, _, _, rfl⟩; exact abs_nonneg _)

lemma rect_swap (F : I → I → ℝ) (S T : Set I) :
    ∫ p in S ×ˢ T, F p.2 p.1 = ∫ p in T ×ˢ S, F p.1 p.2 :=
  setIntegral_prod_swap (μ := (volume : Measure I)) (ν := (volume : Measure I)) T S
    (fun p => F p.1 p.2)

lemma isKernel_sub_pullback {U W : I → I → ℝ} (hU : IsDigraphon U) (hW : IsDigraphon W)
    {φ : I → I} (hφ : Measurable φ) : IsKernel (fun x y => U x y - pullback φ W x y) := by
  refine ⟨hU.1.sub (hW.1.comp (hφ.prodMap hφ)), 1, fun x y => ?_⟩
  simp only [pullback]
  rw [abs_le]
  constructor <;> linarith [(hU.2 x y).1, (hU.2 x y).2, (hW.2 (φ x) (φ y)).1,
    (hW.2 (φ x) (φ y)).2]

lemma cutNorm_symm_le {F : I → I → ℝ} (hF : IsKernel F) :
    cutNorm (fun x y => (F x y + F y x) / 2) ≤ cutNorm F := by
  refine cutNorm_le fun S T hS hT => ?_
  have hFT := Section4Aux.isKernel_kTranspose hF
  have e : ∫ p in S ×ˢ T, (F p.1 p.2 + F p.2 p.1) / 2 =
      ((∫ p in S ×ˢ T, F p.1 p.2) + ∫ p in T ×ˢ S, F p.1 p.2) / 2 := by
    have hFT' : IntegrableOn (fun p : I × I => F p.2 p.1) (S ×ˢ T)
        (volume : Measure (I × I)) := intOn hFT _
    rw [integral_div, integral_add (intOn hF _) hFT', rect_swap]
  rw [e, abs_div, abs_two]
  have h1 := le_cutNorm hF hS hT
  have h2 := le_cutNorm hF hT hS
  have := abs_add_le (∫ p in S ×ˢ T, F p.1 p.2) (∫ p in T ×ˢ S, F p.1 p.2)
  linarith

lemma cdm_bdd (U W : I → I → ℝ) :
    BddBelow {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = cutNorm fun x y => U x y - pullback φ W x y} :=
  ⟨0, by rintro _ ⟨φ, _, rfl⟩; exact cutNorm_nonneg _⟩

lemma cdm_nonneg (U W : I → I → ℝ) : 0 ≤ cutDistMap U W :=
  Real.sInf_nonneg (by rintro _ ⟨φ, _, rfl⟩; exact cutNorm_nonneg _)

lemma cdm_le_id (U W : I → I → ℝ) : cutDistMap U W ≤ cutNorm (fun x y => U x y - W x y) :=
  csInf_le (cdm_bdd U W) ⟨id, MeasurePreserving.id _, rfl⟩

lemma cdm_self (U : I → I → ℝ) : cutDistMap U U = 0 :=
  le_antisymm ((cdm_le_id U U).trans (cutNorm_le fun S T _ _ => by simp)) (cdm_nonneg U U)

lemma exists_map_lt {U W : I → I → ℝ} {r : ℝ} (h : cutDistMap U W < r) :
    ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      cutNorm (fun x y => U x y - pullback φ W x y) < r := by
  have hne : Set.Nonempty {r | ∃ φ : I → I, MeasurePreserving φ volume volume ∧
      r = cutNorm fun x y => U x y - pullback φ W x y} := ⟨_, id, MeasurePreserving.id _, rfl⟩
  obtain ⟨_, ⟨φ, hφ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne h
  exact ⟨φ, hφ, hlt⟩

lemma cdm_symm_le {U W : I → I → ℝ} (hU : IsDigraphon U) (hW : IsDigraphon W) :
    cutDistMap (symmetrize U) (symmetrize W) ≤ cutDistMap U W := by
  refine le_csInf ⟨_, ⟨id, MeasurePreserving.id _, rfl⟩⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  refine (csInf_le (cdm_bdd _ _) ⟨φ, hφ, rfl⟩).trans ?_
  have : (fun x y => symmetrize U x y - pullback φ (symmetrize W) x y) =
      fun x y => ((U x y - pullback φ W x y) + (U y x - pullback φ W y x)) / 2 := by
    funext x y; simp only [symmetrize, pullback]; ring
  rw [this]
  exact cutNorm_symm_le (isKernel_sub_pullback hU hW hφ.measurable)

/-- `Δ_D(W) = t(D, W) - t(D, (W + W^T)/2)`. -/
noncomputable def Δ {V : Type*} [Fintype V] (D : OrientedGraph V) (U : I → I → ℝ) : ℝ :=
  t D U - t D (symmetrize U)

lemma lip_Δ (h18 : FHMZThm18Hyp.{u}) {V : Type u} [Fintype V] (D : OrientedGraph V)
    {U W : I → I → ℝ} (hU : IsDigraphon U) (hW : IsDigraphon W) :
    |Δ D W - Δ D U| ≤ 2 * D.numArcs * cutDistMap U W := by
  have h1 := h18 V D U W hU hW
  have h2 := h18 V D _ _ (Section1Aux.isDigraphon_symmetrize hU)
    (Section1Aux.isDigraphon_symmetrize hW)
  have h3 := cdm_symm_le hU hW
  have hm : (0 : ℝ) ≤ D.numArcs := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h3 hm
  have : Δ D W - Δ D U = (t D W - t D U) - (t D (symmetrize W) - t D (symmetrize U)) := by
    unfold Δ; ring
  rw [this]
  have := abs_sub (t D W - t D U) (t D (symmetrize W) - t D (symmetrize U))
  linarith

end Cut

/-! ## Step digraphons of finite hosts and rectangle integrals -/

section StepRect

lemma stepDigraphonOf_eq {N : ℕ} (G : OrientedGraph (Fin N)) (hN : 0 < N) :
    stepDigraphonOf G = Section4Aux.hostKer G N hN (Equiv.refl _) := by
  classical
  funext x y
  simp only [stepDigraphonOf, Section4Aux.hostKer, hN, dif_pos, Equiv.refl_apply]
  exact if_congr Iff.rfl rfl rfl

lemma isDigraphon_step {N : ℕ} (G : OrientedGraph (Fin N)) : IsDigraphon (stepDigraphonOf G) := by
  by_cases hN : 0 < N
  · rw [stepDigraphonOf_eq G hN]; exact Section4Aux.isDigraphon_hostKer _ _ _ _
  · have : stepDigraphonOf G = fun _ _ => 0 := by funext x y; simp [stepDigraphonOf, hN]
    rw [this]; exact ⟨measurable_const, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩

lemma Δ_step {V : Type u} [Fintype V] (D : OrientedGraph V) {N : ℕ} (G : OrientedGraph (Fin N))
    (hN : 0 < N) : Δ D (stepDigraphonOf G) = homDensity D G - symmDensity D G := by
  classical
  rw [Δ, stepDigraphonOf_eq G hN, t_hostKer, t_symm_hostKer]

lemma lin_le {ι : Type*} [Fintype ι] (r s : ι → ℝ) {c K : ℝ} (hc : 0 ≤ c)
    (hs : ∀ a, 0 ≤ s a ∧ s a ≤ c) (hK : ∀ A : Finset ι, ∑ a ∈ A, r a ≤ K) :
    ∑ a, s a * r a ≤ c * K := by
  classical
  calc ∑ a, s a * r a ≤ ∑ a, c * max (r a) 0 := Finset.sum_le_sum fun a _ => by
          rcases le_total 0 (r a) with h | h
          · rw [max_eq_left h]; exact mul_le_mul_of_nonneg_right (hs a).2 h
          · rw [max_eq_right h, mul_zero]; exact mul_nonpos_of_nonneg_of_nonpos (hs a).1 h
    _ = c * ∑ a ∈ Finset.univ.filter (fun a => 0 ≤ r a), r a := by
          rw [← Finset.mul_sum, Finset.sum_filter]
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs with h
          · exact max_eq_left h
          · exact max_eq_right (not_le.1 h).le
    _ ≤ c * K := mul_le_mul_of_nonneg_left (hK _) hc

lemma bilin_le {ι κ : Type*} [Fintype ι] [Fintype κ] (Mx : ι → κ → ℝ) {K c d : ℝ}
    (hK : ∀ A B, ∑ a ∈ A, ∑ b ∈ B, Mx a b ≤ K) (hc : 0 ≤ c) (hd : 0 ≤ d) (s : ι → ℝ)
    (t : κ → ℝ) (hs : ∀ a, 0 ≤ s a ∧ s a ≤ c) (ht : ∀ b, 0 ≤ t b ∧ t b ≤ d) :
    ∑ a, ∑ b, s a * t b * Mx a b ≤ c * (d * K) := by
  have e : ∑ a, ∑ b, s a * t b * Mx a b = ∑ a, s a * (∑ b, t b * Mx a b) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  refine lin_le _ s hc hs fun A => ?_
  have e2 : ∑ a ∈ A, ∑ b, t b * Mx a b = ∑ b, t b * ∑ a ∈ A, Mx a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
  rw [e2]
  exact lin_le _ t hd ht fun B => by rw [Finset.sum_comm]; exact hK A B

lemma abs_bilin_le {ι κ : Type*} [Fintype ι] [Fintype κ] (Mx : ι → κ → ℝ) {K c d : ℝ}
    (hK : ∀ A B, |∑ a ∈ A, ∑ b ∈ B, Mx a b| ≤ K) (hc : 0 ≤ c) (hd : 0 ≤ d) (s : ι → ℝ)
    (t : κ → ℝ) (hs : ∀ a, 0 ≤ s a ∧ s a ≤ c) (ht : ∀ b, 0 ≤ t b ∧ t b ≤ d) :
    |∑ a, ∑ b, s a * t b * Mx a b| ≤ c * (d * K) := by
  have h1 := bilin_le Mx (fun A B => (le_abs_self _).trans (hK A B)) hc hd s t hs ht
  have h2 := bilin_le (fun a b => -Mx a b) (K := K) (fun A B => by
    simp only [Finset.sum_neg_distrib]; exact (neg_le_abs _).trans (hK A B)) hc hd s t hs ht
  simp only [mul_neg, Finset.sum_neg_distrib] at h2
  rw [abs_le]; constructor <;> linarith

lemma isKernel_rect (c : ℝ) {A B : Set I} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IsKernel (fun x y => c * (A.indicator (1 : I → ℝ) x * B.indicator (1 : I → ℝ) y)) := by
  refine ⟨?_, |c|, fun x y => ?_⟩
  · exact measurable_const.mul (((measurable_const.indicator hA).comp measurable_fst).mul
      ((measurable_const.indicator hB).comp measurable_snd))
  · rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg c) ?_
    simp only [Set.indicator, Pi.one_apply]
    split_ifs <;> simp

/-- If every block sum of `Mx` is at most `K` in absolute value, then every rectangle integral of the
pulled-back step function is at most `K/N²` in absolute value, via its bilinear form in the cell
masses. -/
lemma rect_step {N : ℕ} (hN : 0 < N) (Mx : Fin N → Fin N → ℝ) {K : ℝ}
    (hK : ∀ A B : Finset (Fin N), |∑ a ∈ A, ∑ b ∈ B, Mx a b| ≤ K) {φ : I → I}
    (hφ : MeasurePreserving φ volume volume) {S T : Set I} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    |∫ p in S ×ˢ T, Mx (equipartIdx N hN (φ p.1)) (equipartIdx N hN (φ p.2))| ≤
      (1 / N) * ((1 / N) * K) := by
  set π : I → Fin N := fun x => equipartIdx N hN (φ x) with hπdef
  have hπ : Measurable π := (Section4Aux.measurable_equipartIdx N hN).comp hφ.measurable
  let E : Fin N → Set I := fun a => π ⁻¹' {a}
  have hE : ∀ a, MeasurableSet (E a) := fun a => hπ (measurableSet_singleton a)
  have hpt : ∀ p : I × I, Mx (π p.1) (π p.2) = ∑ a, ∑ b, Mx a b *
      ((E a).indicator (1 : I → ℝ) p.1 * (E b).indicator (1 : I → ℝ) p.2) := by
    intro p
    rw [Finset.sum_eq_single (π p.1), Finset.sum_eq_single (π p.2)]
    · simp [E]
    · intro b _ hb; simp [E, Set.indicator, Ne.symm hb]
    · simp
    · intro a _ ha; refine Finset.sum_eq_zero fun b _ => ?_; simp [E, Set.indicator, Ne.symm ha]
    · simp
  have hint : ∀ a b, IntegrableOn (fun p : I × I => Mx a b *
      ((E a).indicator (1 : I → ℝ) p.1 * (E b).indicator (1 : I → ℝ) p.2)) (S ×ˢ T) volume :=
    fun a b => intOn (isKernel_rect (Mx a b) (hE a) (hE b)) _
  have hcell : ∀ a (R : Set I), MeasurableSet R →
      ∫ x in R, (E a).indicator (1 : I → ℝ) x = (volume : Measure I).real (E a ∩ R) := by
    intro a R hR
    rw [integral_indicator_one (hE a), measureReal_def, Measure.restrict_apply (hE a),
      ← measureReal_def]
  have e : ∫ p in S ×ˢ T, Mx (π p.1) (π p.2) = ∑ a, ∑ b,
      (volume : Measure I).real (E a ∩ S) * (volume : Measure I).real (E b ∩ T) * Mx a b := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
    have := setIntegral_prod_mul (μ := (volume : Measure I)) (ν := (volume : Measure I))
      ((E a).indicator (1 : I → ℝ)) ((E b).indicator (1 : I → ℝ)) S T
    rw [show (∫ p in S ×ˢ T, (E a).indicator (1 : I → ℝ) p.1 * (E b).indicator (1 : I → ℝ) p.2)
      = (∫ x in S, (E a).indicator (1 : I → ℝ) x) * ∫ y in T, (E b).indicator (1 : I → ℝ) y
      from this, hcell a S hS, hcell b T hT]
    ring
  have hmass : ∀ a (R : Set I), 0 ≤ (volume : Measure I).real (E a ∩ R) ∧
      (volume : Measure I).real (E a ∩ R) ≤ 1 / N := by
    intro a R
    refine ⟨measureReal_nonneg, ?_⟩
    have h1 : (volume : Measure I).real (E a ∩ R) ≤ (volume : Measure I).real (E a) :=
      measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    have h2 : (volume : Measure I) (E a) = ENNReal.ofReal (1 / N) := by
      have : E a = φ ⁻¹' (equipartIdx N hN ⁻¹' {a}) := rfl
      rw [this, hφ.measure_preimage
        ((Section4Aux.measurable_equipartIdx N hN (measurableSet_singleton a)).nullMeasurableSet),
        Section4Aux.volume_equipartIdx]
    have h3 : (volume : Measure I).real (E a) = 1 / N := by
      rw [measureReal_def, h2, ENNReal.toReal_ofReal (by positivity)]
    linarith
  rw [e]
  have hN0 : (0 : ℝ) ≤ 1 / N := by positivity
  exact abs_bilin_le Mx hK hN0 hN0 _ _ (fun a => hmass a S) (fun b => hmass b T)

/-- A bounded measurable kernel with all rectangle integrals zero vanishes almost everywhere. -/
lemma ae_zero_of_rect {F : I → I → ℝ} (hF : IsKernel F)
    (h : ∀ S T : Set I, MeasurableSet S → MeasurableSet T → ∫ p in S ×ˢ T, F p.1 p.2 = 0) :
    ∀ᵐ p ∂(volume : Measure (I × I)), F p.1 p.2 = 0 := by
  have hint : Integrable (fun p : I × I => F p.1 p.2) volume := by
    simpa using intOn hF univ
  have huniv : ∫ p : I × I, F p.1 p.2 = 0 := by
    have := h univ univ MeasurableSet.univ MeasurableSet.univ
    rwa [univ_prod_univ, Measure.restrict_univ] at this
  have hall : ∀ s : Set (I × I), MeasurableSet s → ∫ p in s, F p.1 p.2 = 0 := by
    intro s hs
    refine MeasurableSpace.induction_on_inter
      (C := fun (s : Set (I × I)) _ => ∫ p in s, F p.1 p.2 = 0)
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ s hs
    · simp
    · rintro _ ⟨S, hS, T, hT, rfl⟩; exact h S T hS hT
    · intro t ht h0
      have := integral_add_compl ht hint
      linarith
    · intro f hd hfm hf
      rw [integral_iUnion hfm hd hint.integrableOn]
      simp [hf]
  have := hint.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => hall s hs)
  filter_upwards [this] with p hp
  exact hp

lemma arcsFromTo_eq {M : ℕ} (G : OrientedGraph (Fin M)) (A B : Finset (Fin M)) [DecidableRel G.Adj] :
    (G.arcsFromTo A B : ℝ) = ∑ a ∈ A, ∑ b ∈ B, (if G.Adj a b then (1 : ℝ) else 0) := by
  classical
  unfold arcsFromTo arcs
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    ← Finset.univ_product_univ, Finset.sum_product]
  have hA : ∀ (C : Finset (Fin M)) (g : Fin M → ℝ), ∑ a ∈ C, g a =
      ∑ a, if a ∈ C then g a else 0 := fun C g => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hA A]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [hA B]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ B <;> by_cases hab : G.Adj a b <;> simp [ha, hb, hab]
  · exact Finset.sum_eq_zero fun b _ => by simp [ha]

end StepRect

/-! ## The `C₄` asymmetry functional -/

section C4

/-- The vertex set of `C₄ = K_{2,2}` with its two sides. -/
abbrev Z4 : Type u := ULift.{u} (Fin 2 ⊕ Fin 2)

/-- Left vertices. -/
def zL (i : Fin 2) : Z4.{u} := ULift.up (Sum.inl i)

/-- Right vertices. -/
def zR (j : Fin 2) : Z4.{u} := ULift.up (Sum.inr j)

lemma zL_ne_zR (i j : Fin 2) : zL.{u} i ≠ zR.{u} j := by simp [zL, zR]

lemma zL_inj {i j : Fin 2} (h : zL.{u} i = zL.{u} j) : i = j := by simpa [zL] using h

lemma zR_inj {i j : Fin 2} (h : zR.{u} i = zR.{u} j) : i = j := by simpa [zR] using h

/-- The arc of the orientation `o` on the edge `p`. -/
def arcOf (o : Fin 2 × Fin 2 → Bool) (p : Fin 2 × Fin 2) : Z4.{u} × Z4.{u} :=
  if o p then (zL p.1, zR p.2) else (zR p.2, zL p.1)

lemma arcOf_inj (o : Fin 2 × Fin 2 → Bool) : Function.Injective (arcOf.{u} o) := by
  intro p q h
  unfold arcOf at h
  split_ifs at h with h1 h2 h2
  · obtain ⟨e1, e2⟩ := Prod.mk.inj h; exact Prod.ext (zL_inj e1) (zR_inj e2)
  · exact absurd (Prod.mk.inj h).1 (zL_ne_zR _ _)
  · exact absurd (Prod.mk.inj h).1.symm (zL_ne_zR _ _)
  · obtain ⟨e1, e2⟩ := Prod.mk.inj h; exact Prod.ext (zL_inj e2) (zR_inj e1)

/-- The orientation `o` of `C₄`. -/
def Bo (o : Fin 2 × Fin 2 → Bool) : OrientedGraph Z4.{u} where
  Adj a b := ∃ p, arcOf o p = (a, b)
  irrefl a := by
    rintro ⟨p, hp⟩
    unfold arcOf at hp
    split_ifs at hp
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hp; exact zL_ne_zR _ _ (h1.trans h2.symm)
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hp; exact zL_ne_zR _ _ (h2.trans h1.symm)
  asymm a b := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    have key : arcOf o p = (arcOf o q).swap := by rw [hp, hq]; rfl
    unfold arcOf at key
    split_ifs at key with h1 h2 h2
    · exact zL_ne_zR _ _ (Prod.mk.inj key).1
    · obtain ⟨e1, e2⟩ := Prod.mk.inj key
      have : p = q := Prod.ext (zL_inj e1) (zR_inj e2)
      rw [this] at h1; exact h2 h1
    · obtain ⟨e1, e2⟩ := Prod.mk.inj key
      have : p = q := Prod.ext (zL_inj e2) (zR_inj e1)
      rw [this] at h1; exact h1 h2
    · exact zL_ne_zR _ _ (Prod.mk.inj key).2

lemma arcs_Bo (o : Fin 2 × Fin 2 → Bool) :
    (Bo.{u} o).arcs = Finset.univ.image (arcOf.{u} o) := by
  ext a
  rw [mem_arcs]
  simp [Bo]

lemma t_Bo (o : Fin 2 × Fin 2 → Bool) (U : I → I → ℝ) :
    t (Bo.{u} o) U = ∫ z : Z4.{u} → I, ∏ p : Fin 2 × Fin 2,
      (if o p then U (z (zL p.1)) (z (zR p.2)) else U (z (zR p.2)) (z (zL p.1)))
      ∂(Measure.pi fun _ => (volume : Measure I)) := by
  unfold t tDir
  rw [arcs_Bo]
  congr 1
  funext z
  rw [Finset.prod_image (arcOf_inj o).injOn]
  refine Finset.prod_congr rfl fun p _ => ?_
  unfold arcOf
  split_ifs <;> rfl

/-- The `C₄` density of `W - W^T` (bipartite reading). -/
noncomputable def cF (U : I → I → ℝ) : ℝ :=
  ∫ z : Z4.{u} → I, ∏ p : Fin 2 × Fin 2,
    (U (z (zL p.1)) (z (zR p.2)) - U (z (zR p.2)) (z (zL p.1)))
    ∂(Measure.pi fun _ => (volume : Measure I))

/-- The sign of an orientation. -/
def sg (o : Fin 2 × Fin 2 → Bool) : ℝ := ∏ p, (if o p then (1 : ℝ) else -1)

lemma abs_sg (o : Fin 2 × Fin 2 → Bool) : |sg o| = 1 := by
  unfold sg
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun p _ => by split_ifs <;> simp

lemma cF_eq {U : I → I → ℝ} (hU : IsDigraphon U) :
    cF.{u} U = ∑ o, sg o * t (Bo.{u} o) U := by
  have hpt : ∀ z : Z4.{u} → I, ∏ p : Fin 2 × Fin 2,
      (U (z (zL p.1)) (z (zR p.2)) - U (z (zR p.2)) (z (zL p.1))) =
      ∑ o : Fin 2 × Fin 2 → Bool, sg o * ∏ p : Fin 2 × Fin 2,
        (if o p then U (z (zL p.1)) (z (zR p.2)) else U (z (zR p.2)) (z (zL p.1))) := by
    intro z
    have e : ∀ p : Fin 2 × Fin 2,
        U (z (zL p.1)) (z (zR p.2)) - U (z (zR p.2)) (z (zL p.1)) =
        ∑ β : Bool, (if β then U (z (zL p.1)) (z (zR p.2))
          else -U (z (zR p.2)) (z (zL p.1))) := fun p => by
      simp [Fintype.sum_bool, sub_eq_add_neg, add_comm]
    simp_rw [e]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [sg, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    cases o p <;> simp
  unfold cF
  simp_rw [hpt]
  have hint : ∀ o : Fin 2 × Fin 2 → Bool, Integrable (fun z : Z4.{u} → I => sg o *
      ∏ p : Fin 2 × Fin 2,
        (if o p then U (z (zL p.1)) (z (zR p.2)) else U (z (zR p.2)) (z (zL p.1))))
      (Measure.pi fun _ => (volume : Measure I)) := by
    intro o
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (Finset.measurable_prod _ fun p _ => ?_).aestronglyMeasurable 1
      (Eventually.of_forall fun z => ?_)
    · cases o p
      · exact Section1Aux.measurable_pair hU.1 _ _
      · exact Section1Aux.measurable_pair hU.1 _ _
    · rw [Real.norm_eq_abs, Finset.abs_prod]
      refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p _ => ?_
      split_ifs
      · rw [abs_of_nonneg (hU.2 _ _).1]; exact (hU.2 _ _).2
      · rw [abs_of_nonneg (hU.2 _ _).1]; exact (hU.2 _ _).2
  rw [integral_finsetSum _ fun o _ => hint o]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [integral_const_mul, t_Bo]

/-- The Lipschitz constant of `cF`. -/
noncomputable def cC : ℝ := ∑ o : Fin 2 × Fin 2 → Bool, ((Bo.{u} o).numArcs : ℝ)

lemma lip_cF (h18 : FHMZThm18Hyp.{u}) {U W : I → I → ℝ} (hU : IsDigraphon U)
    (hW : IsDigraphon W) : |cF.{u} W - cF.{u} U| ≤ cC.{u} * cutDistMap U W := by
  rw [cF_eq hU, cF_eq hW, ← Finset.sum_sub_distrib, cC, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun o _ => ?_)
  rw [← mul_sub, abs_mul, abs_sg, one_mul]
  exact h18 Z4.{u} (Bo o) U W hU hW

lemma cF_zero_of_symm {U : I → I → ℝ} (h : AEEq volume U (kTranspose U)) : cF.{u} U = 0 := by
  unfold cF
  have hmp := Section1Aux.measurePreserving_pair (V := Z4.{u}) (zL_ne_zR 0 0)
  have hae : ∀ᵐ z ∂(Measure.pi fun _ : Z4.{u} => (volume : Measure I)),
      U (z (zL 0)) (z (zR 0)) = U (z (zR 0)) (z (zL 0)) := hmp.quasiMeasurePreserving.ae h
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with z hz
  exact Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin 2), (0 : Fin 2))) (by
    simp only; rw [hz, sub_self])

open scoped Classical in
/-- The step-kernel value of `cF`: a sum of squares of row products. -/
lemma cF_step {N : ℕ} (hN : 0 < N) (G : OrientedGraph (Fin N)) :
    cF.{u} (stepDigraphonOf G) = ((N : ℝ)⁻¹) ^ 4 * ∑ a0 : Fin N, ∑ a1 : Fin N,
      (∑ c : Fin N, ((if G.Adj a0 c then (1 : ℝ) else 0) - (if G.Adj c a0 then 1 else 0)) *
        ((if G.Adj a1 c then (1 : ℝ) else 0) - (if G.Adj c a1 then 1 else 0))) ^ 2 := by
  set Mx : Fin N → Fin N → ℝ := fun a b =>
    (if G.Adj a b then (1 : ℝ) else 0) - (if G.Adj b a then 1 else 0) with hMx
  have hcard : Fintype.card Z4.{u} = 4 := by simp
  have h1 : cF.{u} (stepDigraphonOf G) = ((N : ℝ)⁻¹) ^ Fintype.card Z4.{u} *
      ∑ g : Z4.{u} → Fin N, ∏ p : Fin 2 × Fin 2, Mx (g (zL p.1)) (g (zR p.2)) := by
    rw [← integral_comp_equipart N hN]
    unfold cF
    rw [stepDigraphonOf_eq G hN]
    rfl
  rw [h1, hcard]
  congr 1
  let e : (Fin 2 → Fin N) × (Fin 2 → Fin N) ≃ (Z4.{u} → Fin N) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
      (Equiv.arrowCongr Equiv.ulift.symm (Equiv.refl _))
  rw [← Fintype.sum_equiv e (fun ab => ∏ p : Fin 2 × Fin 2, Mx (ab.1 p.1) (ab.2 p.2)) _
    (fun ab => rfl), Fintype.sum_prod_type]
  have hrow : ∀ x : Fin 2 → Fin N, ∑ y : Fin 2 → Fin N, ∏ p : Fin 2 × Fin 2, Mx (x p.1) (y p.2) =
      (∑ c, Mx (x 0) c * Mx (x 1) c) ^ 2 := by
    intro x
    have : ∀ y : Fin 2 → Fin N, ∏ p : Fin 2 × Fin 2, Mx (x p.1) (y p.2) =
        ∏ j : Fin 2, (Mx (x 0) (y j) * Mx (x 1) (y j)) := by
      intro y; rw [Fintype.prod_prod_type, Fin.prod_univ_two, ← Finset.prod_mul_distrib]
    simp_rw [this]
    rw [← Fintype.prod_sum (fun (_ : Fin 2) c => Mx (x 0) c * Mx (x 1) c), Fin.prod_univ_two, sq]
  simp only [hrow]
  rw [← Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin N).symm
    (fun q => (∑ c, Mx q.1 c * Mx q.2 c) ^ 2) _ (fun q => by simp), Fintype.sum_prod_type]

/-- Discrete Cauchy–Schwarz: the cut discrepancy is controlled by the `C₄` sum. -/
lemma disc4 {N : ℕ} (Mx : Fin N → Fin N → ℝ) (A B : Finset (Fin N)) :
    (∑ a ∈ A, ∑ b ∈ B, Mx a b) ^ 4 ≤
      (N : ℝ) ^ 4 * ∑ a0 : Fin N, ∑ a1 : Fin N, (∑ c : Fin N, Mx a0 c * Mx a1 c) ^ 2 := by
  classical
  set col : Fin N → ℝ := fun b => ∑ a ∈ A, Mx a b
  set R : Fin N → Fin N → ℝ := fun a a' => ∑ c, Mx a c * Mx a' c
  have hd : ∑ a ∈ A, ∑ b ∈ B, Mx a b = ∑ b ∈ B, col b := Finset.sum_comm
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hcardB : ((B.card : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_univ B).trans (Fintype.card_fin N).le
  have h1 : (∑ b ∈ B, col b) ^ 2 ≤ N * ∑ b, col b ^ 2 := by
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    have hs : ∑ b ∈ B, col b ^ 2 ≤ ∑ b, col b ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun b => sq_nonneg _
    have h0 : 0 ≤ ∑ b ∈ B, col b ^ 2 := Finset.sum_nonneg fun b _ => sq_nonneg _
    nlinarith
  have h2 : ∑ b, col b ^ 2 = ∑ q ∈ A ×ˢ A, R q.1 q.2 := by
    rw [Finset.sum_product]
    simp only [col, R, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  have hcardAA : (((A ×ˢ A).card : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    rw [Finset.card_product]
    have : ((A.card : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (Finset.card_le_univ A).trans (Fintype.card_fin N).le
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
  have h3 : (∑ q ∈ A ×ˢ A, R q.1 q.2) ^ 2 ≤ (N : ℝ) ^ 2 * ∑ a0, ∑ a1, R a0 a1 ^ 2 := by
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    have hs : ∑ q ∈ A ×ˢ A, R q.1 q.2 ^ 2 ≤ ∑ a0, ∑ a1, R a0 a1 ^ 2 :=
      calc ∑ q ∈ A ×ˢ A, R q.1 q.2 ^ 2 ≤ ∑ q : Fin N × Fin N, R q.1 q.2 ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun q => sq_nonneg _
        _ = ∑ a0, ∑ a1, R a0 a1 ^ 2 := Fintype.sum_prod_type _
    have h0 : 0 ≤ ∑ q ∈ A ×ˢ A, R q.1 q.2 ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
    nlinarith
  rw [hd]
  set d := ∑ b ∈ B, col b
  set S := ∑ b, col b ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => sq_nonneg _
  have h4 : (d ^ 2) ^ 2 ≤ (N * S) ^ 2 := pow_le_pow_left₀ (sq_nonneg d) h1 2
  rw [h2] at h4
  have : (d ^ 2) ^ 2 = d ^ 4 := by ring
  rw [this] at h4
  calc d ^ 4 ≤ (N * ∑ q ∈ A ×ˢ A, R q.1 q.2) ^ 2 := h4
    _ = (N : ℝ) ^ 2 * (∑ q ∈ A ×ˢ A, R q.1 q.2) ^ 2 := by ring
    _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 * ∑ a0, ∑ a1, R a0 a1 ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (N : ℝ) ^ 4 * ∑ a0, ∑ a1, R a0 a1 ^ 2 := by ring

end C4

/-! ## Orientation discrepancy of finite hosts -/

section Disc

open scoped Classical in
lemma disc_eq {N : ℕ} (G : OrientedGraph (Fin N)) (A B : Finset (Fin N)) :
    ((G.arcsFromTo A B : ℝ) - G.arcsFromTo B A) = ∑ a ∈ A, ∑ b ∈ B,
      ((if G.Adj a b then (1 : ℝ) else 0) - (if G.Adj b a then 1 else 0)) := by
  rw [arcsFromTo_eq, arcsFromTo_eq, Finset.sum_comm (s := B) (t := A), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_sub_distrib]

lemma cF_step_ge {N : ℕ} (hN : 0 < N) (G : OrientedGraph (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (A B : Finset (Fin N))
    (h : ε * (N : ℝ) ^ 2 < |(G.arcsFromTo A B : ℝ) - G.arcsFromTo B A|) :
    ε ^ 4 ≤ cF.{u} (stepDigraphonOf G) := by
  classical
  rw [cF_step hN G]
  have hd := disc4 (fun a b => (if G.Adj a b then (1 : ℝ) else 0) - (if G.Adj b a then 1 else 0))
    A B
  rw [← disc_eq] at hd
  set d := ((G.arcsFromTo A B : ℝ) - G.arcsFromTo B A)
  set Q := ∑ a0 : Fin N, ∑ a1 : Fin N,
      (∑ c : Fin N, ((if G.Adj a0 c then (1 : ℝ) else 0) - (if G.Adj c a0 then 1 else 0)) *
        ((if G.Adj a1 c then (1 : ℝ) else 0) - (if G.Adj c a1 then 1 else 0))) ^ 2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : (ε * (N : ℝ) ^ 2) ^ 4 ≤ d ^ 4 := by
    have : (ε * (N : ℝ) ^ 2) ^ 4 ≤ |d| ^ 4 := pow_le_pow_left₀ (by positivity) h.le 4
    rwa [show |d| ^ 4 = d ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
      at this
  have h5 : ε ^ 4 * (N : ℝ) ^ 4 * (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 * Q := by
    calc ε ^ 4 * (N : ℝ) ^ 4 * (N : ℝ) ^ 4 = (ε * (N : ℝ) ^ 2) ^ 4 := by ring
      _ ≤ d ^ 4 := h4
      _ ≤ (N : ℝ) ^ 4 * Q := hd
  have h6 : ε ^ 4 * (N : ℝ) ^ 4 ≤ Q := by
    have hp : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    nlinarith
  rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  exact h6

/-- The asymmetric part of a step digraphon has cut norm at most `max |e(A,B) - e(B,A)| / 2N²`. -/
lemma cut_step_asym {N : ℕ} (hN : 0 < N) (G : OrientedGraph (Fin N)) {K : ℝ}
    (hK : ∀ A B : Finset (Fin N), |(G.arcsFromTo A B : ℝ) - G.arcsFromTo B A| ≤ K) :
    cutNorm (fun x y => stepDigraphonOf G x y - symmetrize (stepDigraphonOf G) x y) ≤
      (1 / N) * ((1 / N) * (K / 2)) := by
  classical
  set Mx : Fin N → Fin N → ℝ := fun a b =>
    ((if G.Adj a b then (1 : ℝ) else 0) - (if G.Adj b a then 1 else 0)) / 2
  have hK' : ∀ A B : Finset (Fin N), |∑ a ∈ A, ∑ b ∈ B, Mx a b| ≤ K / 2 := by
    intro A B
    have : ∑ a ∈ A, ∑ b ∈ B, Mx a b = ((G.arcsFromTo A B : ℝ) - G.arcsFromTo B A) / 2 := by
      rw [disc_eq, Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_div]
    rw [this, abs_div, abs_two]
    linarith [hK A B]
  refine cutNorm_le fun S T hS hT => ?_
  have e : ∀ x y : I, stepDigraphonOf G x y - symmetrize (stepDigraphonOf G) x y =
      Mx (equipartIdx N hN (id x)) (equipartIdx N hN (id y)) := by
    intro x y
    rw [stepDigraphonOf_eq G hN]
    simp only [symmetrize, Section4Aux.hostKer, Equiv.refl_apply, id, Mx]
    by_cases h1 : G.Adj (equipartIdx N hN x) (equipartIdx N hN y) <;>
      by_cases h2 : G.Adj (equipartIdx N hN y) (equipartIdx N hN x) <;> simp [h1, h2] <;> norm_num
  simp_rw [e]
  exact rect_step hN Mx hK' (MeasurePreserving.id volume) hS hT

lemma qr_to_Δ (h18 : FHMZThm18Hyp.{u}) {V : Type u} [Fintype V] (D : OrientedGraph V)
    (N : ℕ → ℕ) (G : ∀ n, OrientedGraph (Fin (N n))) (hN : Tendsto N atTop atTop)
    (hq : IsOrientQuasirandom N G) :
    Tendsto (fun n => homDensity D (G n) - symmDensity D (G n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set m : ℝ := (D.numArcs : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hε' : 0 < ε / (m + 1) := by positivity
  filter_upwards [hq _ hε', hN.eventually_gt_atTop 0] with n hn hpos
  rw [Real.dist_eq, sub_zero, ← Δ_step D (G n) hpos]
  have hW := isDigraphon_step (G n)
  have hS := Section1Aux.isDigraphon_symmetrize hW
  have h1 := h18 V D _ _ hW hS
  have h2 := cdm_le_id (stepDigraphonOf (G n)) (symmetrize (stepDigraphonOf (G n)))
  have h3 := cut_step_asym hpos (G n) hn
  have hN0 : (0 : ℝ) < N n := by exact_mod_cast hpos
  have h4 : (1 / (N n : ℝ)) * ((1 / N n) * (ε / (m + 1) * (N n : ℝ) ^ 2 / 2)) = ε / (m + 1) / 2 := by
    field_simp
  rw [h4] at h3
  have h5 : |Δ D (stepDigraphonOf (G n))| ≤ m * (ε / (m + 1) / 2) := by
    rw [Δ, abs_sub_comm]
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hm)
  have h6 : m * (ε / (m + 1) / 2) < ε := by
    have h7 : m / (m + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have h8 : m * (ε / (m + 1) / 2) = (m / (m + 1)) * (ε / 2) := by ring
    rw [h8]
    nlinarith
  linarith

end Disc

/-! ## Compactness: kernel symmetry-forcing gives sequence symmetry-forcing -/

section Compact

/-- A function Lipschitz for `δ_□^{map}` (centre first) is continuous for the topology generated by
the `δ_□^{map}`-balls. -/
lemma lip_continuous (f : Digraphon → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ U W : Digraphon, |f W - f U| ≤ C * cutDistMap U.toFun W.toFun) :
    @Continuous _ _ cutMapTopology _ f := by
  letI : TopologicalSpace Digraphon := cutMapTopology
  rw [continuous_def]
  intro O hO
  rw [isOpen_iff_forall_mem_open]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO (f U) hU
  refine ⟨{W | cutDistMap U.toFun W.toFun < ε / (C + 1)}, ?_, ?_, ?_⟩
  · intro W hW
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 := h U W
    have h2 : C * cutDistMap U.toFun W.toFun ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hW) hC
    have h3 : C * (ε / (C + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, ε / (C + 1), rfl⟩
  · show cutDistMap U.toFun U.toFun < ε / (C + 1)
    rw [cdm_self]; positivity

lemma lip_resp (f : Digraphon → ℝ) {C : ℝ}
    (h : ∀ U W : Digraphon, |f W - f U| ≤ C * cutDistMap U.toFun W.toFun) :
    ∀ U W : Digraphon, cutDistMap U.toFun W.toFun = 0 → f U = f W := by
  intro U W hUW
  have := h U W
  rw [hUW, mul_zero] at this
  exact (sub_eq_zero.1 (abs_nonpos_iff.1 this)).symm

lemma clusterPt_closed {X : Type*} [TopologicalSpace X] {g : X → ℝ} (hg : Continuous g)
    {F : Filter ℕ} {x : ℕ → X} {y : X} (hy : ClusterPt y (map x F)) {C : Set ℝ}
    (hC : IsClosed C) (h : ∀ᶠ n in F, g (x n) ∈ C) : g y ∈ C := by
  by_contra hn
  have h1 : ∀ᶠ z in 𝓝 y, g z ∉ C :=
    hg.continuousAt.preimage_mem_nhds (hC.isOpen_compl.mem_nhds hn)
  have h2 := hy.frequently h1
  rw [Filter.frequently_map] at h2
  obtain ⟨n, hn1, hn2⟩ := (h2.and_eventually h).exists
  exact hn1 hn2

lemma sf_compact (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp) {V : Type u} [Fintype V]
    (D : OrientedGraph V) (hD : D.IsSymmetryForcingK) (N : ℕ → ℕ)
    (G : ∀ n, OrientedGraph (Fin (N n))) (hN : Tendsto N atTop atTop)
    (hΔ : Tendsto (fun n => homDensity D (G n) - symmDensity D (G n)) atTop (𝓝 0)) :
    IsOrientQuasirandom N G := by
  letI : TopologicalSpace Digraphon := cutMapTopology
  have : CompactSpace (Quot fun U W : Digraphon => cutDistMap U.toFun W.toFun = 0) := hcpt
  by_contra hq
  unfold IsOrientQuasirandom at hq
  push_neg at hq
  obtain ⟨ε, hε, hfreq⟩ := hq
  let r : Digraphon → Digraphon → Prop := fun U W => cutDistMap U.toFun W.toFun = 0
  let x : ℕ → Quot r := fun n => Quot.mk r ⟨stepDigraphonOf (G n), isDigraphon_step (G n)⟩
  let ΔD : Digraphon → ℝ := fun U => Δ D U.toFun
  let cD : Digraphon → ℝ := fun U => cF.{u} U.toFun
  have hΔlip : ∀ U W : Digraphon, |ΔD W - ΔD U| ≤
      (2 * D.numArcs) * cutDistMap U.toFun W.toFun :=
    fun U W => lip_Δ h18 D U.isDigraphon W.isDigraphon
  have hclip : ∀ U W : Digraphon, |cD W - cD U| ≤ cC.{u} * cutDistMap U.toFun W.toFun :=
    fun U W => lip_cF h18 U.isDigraphon W.isDigraphon
  have hC0 : (0 : ℝ) ≤ cC.{u} := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  let Δq : Quot r → ℝ := Quot.lift ΔD (lip_resp ΔD hΔlip)
  let cq : Quot r → ℝ := Quot.lift cD (lip_resp cD hclip)
  have hΔc : Continuous Δq :=
    continuous_quot_lift _ (lip_continuous ΔD (by positivity) hΔlip)
  have hcc : Continuous cq := continuous_quot_lift _ (lip_continuous cD hC0 hclip)
  let P : ℕ → Prop := fun n => 0 < N n ∧ ∃ A B : Finset (Fin (N n)),
    ε * (N n : ℝ) ^ 2 < |((G n).arcsFromTo A B : ℝ) - (G n).arcsFromTo B A|
  have hPf : ∃ᶠ n in atTop, P n :=
    (hfreq.and_eventually (hN.eventually_gt_atTop 0)).mono fun n h => ⟨h.2, h.1⟩
  let F := atTop ⊓ 𝓟 {n | P n}
  have : F.NeBot := frequently_iff_neBot.1 hPf
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace (map x F)
  have hFP : ∀ᶠ n in F, P n := mem_inf_of_right (mem_principal_self _)
  have hFat : ∀ {p : ℕ → Prop}, (∀ᶠ n in atTop, p n) → ∀ᶠ n in F, p n :=
    fun h => mem_inf_of_left h
  have hΔy : Δq y = 0 := by
    have hle : ∀ δ > 0, Δq y ∈ Icc (-δ) δ := by
      intro δ hδ
      refine clusterPt_closed hΔc hy isClosed_Icc ?_
      have h1 := (Metric.tendsto_nhds.1 hΔ) δ hδ
      refine hFat ?_
      filter_upwards [h1, hN.eventually_gt_atTop 0] with n hn hpos
      rw [Real.dist_eq, sub_zero] at hn
      show Δ D (stepDigraphonOf (G n)) ∈ Icc (-δ) δ
      rw [Δ_step D (G n) hpos]
      exact ⟨by linarith [neg_abs_le (homDensity D (G n) - symmDensity D (G n))],
        (le_abs_self _).trans hn.le⟩
    by_contra hne
    have := hle (|Δq y| / 2) (by positivity)
    have h1 := this.1; have h2 := this.2
    rcases le_or_gt 0 (Δq y) with h | h
    · rw [abs_of_nonneg h] at h2; have : Δq y ≠ 0 := hne; 
      exact absurd (le_antisymm (by linarith) h) this
    · rw [abs_of_neg h] at h1; linarith
  have hcy : ε ^ 4 ≤ cq y := by
    refine clusterPt_closed hcc hy isClosed_Ici ?_
    filter_upwards [hFP] with n hn
    obtain ⟨hpos, A, B, hAB⟩ := hn
    exact cF_step_ge hpos (G n) hε A B hAB
  obtain ⟨U, rfl⟩ := Quot.exists_rep y
  have hΔU : Δ D U.toFun = 0 := hΔy
  have hsym := hD U.toFun U.isDigraphon (by unfold Δ at hΔU; linarith)
  have hc0 : cF.{u} U.toFun = 0 := cF_zero_of_symm hsym
  have : ε ^ 4 ≤ 0 := by
    have h' : cq (Quot.mk r U) = cF.{u} U.toFun := rfl
    rw [h', hc0] at hcy; exact hcy
  linarith [pow_pos hε 4]

lemma sfk_to_sf (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp) {V : Type u} [Fintype V]
    (D : OrientedGraph V) (hD : D.IsSymmetryForcingK) : D.IsSymmetryForcing := by
  intro N G hN
  exact ⟨sf_compact h18 hcpt D hD N G hN, qr_to_Δ h18 D N G hN⟩

end Compact

/-! ## Blow-ups -/

section Blow

/-- The graph on one vertex with no arc. -/
def emptyOG : OrientedGraph (Fin 1) where
  Adj _ _ := False
  irrefl _ h := h
  asymm _ _ h := h.elim

lemma exists_pos_rep {N : ℕ} (G : OrientedGraph (Fin N)) :
    ∃ (M : ℕ) (H : OrientedGraph (Fin M)), 0 < M ∧ stepDigraphonOf H = stepDigraphonOf G := by
  by_cases hN : 0 < N
  · exact ⟨N, G, hN, rfl⟩
  · refine ⟨1, emptyOG, one_pos, ?_⟩
    funext x y
    simp [stepDigraphonOf, hN, emptyOG]

/-- The `k`-fold blow-up: vertex `i` of `Fin (M * k)` is a copy of `i / k`. -/
def blow {M : ℕ} (H : OrientedGraph (Fin M)) (k : ℕ) : OrientedGraph (Fin (M * k)) where
  Adj i j := H.Adj i.divNat j.divNat
  irrefl i := H.irrefl _
  asymm i j h := H.asymm _ _ h

lemma nat_min_div {a P M k : ℕ} (hk : 0 < k) (hM : 0 < M) (hP : P = M * k) (ha : a ≤ P) :
    min a (P - 1) / k = min (a / k) (M - 1) := by
  have hPk : (M - 1) * k = P - k := by rw [Nat.sub_one_mul, hP]
  have hkP : k ≤ P := by rw [hP]; exact Nat.le_mul_of_pos_left k hM
  rcases Nat.lt_or_eq_of_le ha with h | h
  · have h1 : min a (P - 1) = a := min_eq_left (by omega)
    have h2 : a / k < M := (Nat.div_lt_iff_lt_mul hk).2 (by rw [← hP]; exact h)
    rw [h1, min_eq_left (by omega)]
  · have h1 : min a (P - 1) = P - 1 := min_eq_right (by omega)
    have h2 : a / k = M := by rw [h, hP, Nat.mul_div_cancel M hk]
    rw [h1, h2, min_eq_right (by omega)]
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [hPk]; omega
    · have : (M - 1 + 1) * k = P := by rw [Nat.sub_add_cancel hM, hP]
      rw [this]; omega

lemma divNat_equipart {M k : ℕ} (hM : 0 < M) (hk : 0 < k) (x : I) :
    (equipartIdx (M * k) (Nat.mul_pos hM hk) x).divNat = equipartIdx M hM x := by
  apply Fin.ext
  show min (⌊(x : ℝ) * ((M * k : ℕ) : ℝ)⌋₊) (M * k - 1) / k = min (⌊(x : ℝ) * M⌋₊) (M - 1)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hfl : ⌊(x : ℝ) * M⌋₊ = ⌊(x : ℝ) * ((M * k : ℕ) : ℝ)⌋₊ / k := by
    rw [← Nat.floor_div_natCast]
    congr 1
    push_cast
    field_simp
  rw [hfl]
  refine nat_min_div hk hM rfl (Nat.floor_le_of_le ?_)
  have hx := x.2.2
  have : (0 : ℝ) ≤ ((M * k : ℕ) : ℝ) := Nat.cast_nonneg _
  calc (x : ℝ) * ((M * k : ℕ) : ℝ) ≤ 1 * ((M * k : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hx this
    _ = ((M * k : ℕ) : ℝ) := one_mul _

lemma step_blow {M : ℕ} (H : OrientedGraph (Fin M)) (hM : 0 < M) {k : ℕ} (hk : 0 < k) :
    stepDigraphonOf (blow H k) = stepDigraphonOf H := by
  classical
  funext x y
  simp only [stepDigraphonOf, dif_pos hM, dif_pos (Nat.mul_pos hM hk)]
  have h1 := divNat_equipart hM hk x
  have h2 := divNat_equipart hM hk y
  by_cases h : H.Adj (equipartIdx M hM x) (equipartIdx M hM y)
  · have h' : (blow H k).Adj (equipartIdx (M * k) (Nat.mul_pos hM hk) x)
        (equipartIdx (M * k) (Nat.mul_pos hM hk) y) := by
      show H.Adj _ _; rw [h1, h2]; exact h
    simp [h, h']
  · have h' : ¬ (blow H k).Adj (equipartIdx (M * k) (Nat.mul_pos hM hk) x)
        (equipartIdx (M * k) (Nat.mul_pos hM hk) y) := by
      show ¬ H.Adj _ _; rw [h1, h2]; exact h
    simp [h, h']

lemma sum_divNat {M k : ℕ} (h : Fin M → ℝ) :
    ∑ i : Fin (M * k), h i.divNat = k * ∑ a, h a := by
  rw [← Fintype.sum_equiv finProdFinEquiv (fun q => h q.1) _ (fun q => by
    have : (finProdFinEquiv q).divNat = q.1 := by
      have := finProdFinEquiv.symm_apply_apply q
      exact congrArg Prod.fst this
    rw [this]), Fintype.sum_prod_type]
  simp [Finset.mul_sum]

/-- The lift of a vertex set to the blow-up. -/
def liftSet {M : ℕ} (k : ℕ) (A : Finset (Fin M)) : Finset (Fin (M * k)) :=
  Finset.univ.filter fun i => i.divNat ∈ A

lemma sum_liftSet {M k : ℕ} (A : Finset (Fin M)) (g : Fin M → ℝ) :
    ∑ i ∈ liftSet k A, g i.divNat = k * ∑ a ∈ A, g a := by
  classical
  unfold liftSet
  rw [Finset.sum_filter]
  rw [sum_divNat (fun a => if a ∈ A then g a else 0), Finset.sum_ite_mem, Finset.univ_inter]

lemma blow_disc {M : ℕ} (H : OrientedGraph (Fin M)) (k : ℕ) (A B : Finset (Fin M)) :
    (((blow H k).arcsFromTo (liftSet k A) (liftSet k B) : ℝ) -
      (blow H k).arcsFromTo (liftSet k B) (liftSet k A)) =
      (k : ℝ) ^ 2 * ((H.arcsFromTo A B : ℝ) - H.arcsFromTo B A) := by
  classical
  rw [disc_eq, disc_eq]
  have : ∀ i : Fin (M * k), ∑ j ∈ liftSet k B,
      ((if (blow H k).Adj i j then (1 : ℝ) else 0) - (if (blow H k).Adj j i then 1 else 0)) =
      k * ∑ b ∈ B, ((if H.Adj i.divNat b then (1 : ℝ) else 0) -
        (if H.Adj b i.divNat then 1 else 0)) := fun i =>
    sum_liftSet B (fun b => (if H.Adj i.divNat b then (1 : ℝ) else 0) -
      (if H.Adj b i.divNat then 1 else 0))
  simp_rw [this]
  rw [sum_liftSet A (fun a => (k : ℝ) * ∑ b ∈ B, ((if H.Adj a b then (1 : ℝ) else 0) -
    (if H.Adj b a then 1 else 0))), ← Finset.mul_sum]
  ring

end Blow

/-! ## Sequence symmetry-forcing gives kernel symmetry-forcing -/

section SeqToKernel

lemma sf_to_sfk (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u}) {V : Type u} [Fintype V]
    (D : OrientedGraph V) (hD : D.IsSymmetryForcing) : D.IsSymmetryForcingK := by
  classical
  intro W hW hWeq
  set q : I → I → ℝ := fun x y => (1 / 2 : ℝ) * W x y with hqdef
  have hq : IsDigraphon q := ⟨hW.1.const_mul _, fun x y => ⟨by
    have := (hW.2 x y).1; simp only [q]; positivity, by
    have := (hW.2 x y).2; simp only [q]; linarith⟩⟩
  have hq1 : ∀ x y, q x y + q y x ≤ 1 := fun x y => by
    simp only [q]; linarith [(hW.2 x y).2, (hW.2 y x).2]
  obtain ⟨N, G, hconv⟩ := h13 q hq hq1
  choose M H hMpos hHeq using fun n => exists_pos_rep (G n)
  let G'' : ∀ n, OrientedGraph (Fin (M n * (n + 1))) := fun n => blow (H n) (n + 1)
  have hstep : ∀ n, stepDigraphonOf (G'' n) = stepDigraphonOf (G n) := fun n =>
    (step_blow (H n) (hMpos n) (Nat.succ_pos n)).trans (hHeq n)
  have hN'' : Tendsto (fun n => M n * (n + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (Nat.le_mul_of_pos_left _ (hMpos n)))
      tendsto_id
  have hΔq : Δ D q = 0 := by
    have hs : symmetrize q = fun x y => (1 / 2 : ℝ) * symmetrize W x y := by
      funext x y; simp only [symmetrize, q]; ring
    unfold Δ
    rw [hs, Section4Aux.t_const_mul, Section4Aux.t_const_mul, hWeq, sub_self]
  set m : ℝ := (D.numArcs : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hΔ'' : Tendsto (fun n => homDensity D (G'' n) - symmDensity D (G'' n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h1 := (Metric.tendsto_nhds.1 hconv) (ε / (2 * m + 1)) (by positivity)
    filter_upwards [h1] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (cdm_nonneg _ _)] at hn
    rw [Real.dist_eq, sub_zero, ← Δ_step D (G'' n) (Nat.mul_pos (hMpos n) (Nat.succ_pos n)),
      hstep n]
    have h2 := lip_Δ h18 D hq (isDigraphon_step (G n))
    rw [hΔq, sub_zero] at h2
    have h3 : 2 * m * cutDistMap q (stepDigraphonOf (G n)) ≤ 2 * m * (ε / (2 * m + 1)) :=
      mul_le_mul_of_nonneg_left hn.le (by positivity)
    have h4 : 2 * m * (ε / (2 * m + 1)) < ε := by
      have h7 : 2 * m / (2 * m + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
      have h8 : 2 * m * (ε / (2 * m + 1)) = (2 * m / (2 * m + 1)) * ε := by ring
      rw [h8]; nlinarith
    linarith
  have hqr := (hD _ G'' hN'').1 hΔ''
  have hrect : ∀ S T : Set I, MeasurableSet S → MeasurableSet T →
      ∫ p in S ×ˢ T, (q p.1 p.2 - q p.2 p.1) = 0 := by
    intro S T hS hT
    refine Section4Aux.eq_zero_of_abs_le_mul zero_le_one fun η hη => ?_
    have hc := (Metric.tendsto_nhds.1 hconv) (η / 4) (by positivity)
    obtain ⟨n, hn1, hn2⟩ := ((hqr (η / 2) (by positivity)).and hc).exists
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (cdm_nonneg _ _)] at hn2
    obtain ⟨φ, hφ, hcut⟩ := exists_map_lt hn2
    rw [← hHeq n] at hcut
    have hMn : (0 : ℝ) < M n := by exact_mod_cast hMpos n
    have hdisc : ∀ A B : Finset (Fin (M n)),
        |((H n).arcsFromTo A B : ℝ) - (H n).arcsFromTo B A| ≤ η / 2 * (M n : ℝ) ^ 2 := by
      intro A B
      have h1 := hn1 (liftSet (n + 1) A) (liftSet (n + 1) B)
      rw [blow_disc, abs_mul, abs_of_nonneg (by positivity)] at h1
      have hk : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have e : η / 2 * (((M n * (n + 1) : ℕ) : ℝ)) ^ 2 =
          ((n + 1 : ℕ) : ℝ) ^ 2 * (η / 2 * (M n : ℝ) ^ 2) := by push_cast; ring
      rw [e] at h1
      exact le_of_mul_le_mul_left h1 hk
    set P : I → I → ℝ := pullback φ (stepDigraphonOf (H n))
    have hF : IsKernel (fun x y => q x y - P x y) :=
      isKernel_sub_pullback hq (isDigraphon_step (H n)) hφ.measurable
    have hPk : IsKernel (fun x y => P x y - P y x) := by
      have hP : IsKernel P := by
        refine ⟨(isDigraphon_step (H n)).1.comp (hφ.measurable.prodMap hφ.measurable), 1,
          fun x y => ?_⟩
        have := (isDigraphon_step (H n)).2 (φ x) (φ y)
        show |stepDigraphonOf (H n) (φ x) (φ y)| ≤ 1
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      exact Section2Aux.isKernel_add hP (Section2Aux.isKernel_neg
        (Section4Aux.isKernel_kTranspose hP))
    have hFT : IsKernel (fun x y => q y x - P y x) := Section4Aux.isKernel_kTranspose hF
    have e1 : ∫ p in S ×ˢ T, (q p.1 p.2 - q p.2 p.1) =
        (∫ p in S ×ˢ T, (q p.1 p.2 - P p.1 p.2)) - (∫ p in T ×ˢ S, (q p.1 p.2 - P p.1 p.2)) +
          ∫ p in S ×ˢ T, (P p.1 p.2 - P p.2 p.1) := by
      have hs := rect_swap (fun x y => q x y - P x y) S T
      rw [← hs, show (∫ p in S ×ˢ T, (q p.1 p.2 - q p.2 p.1)) =
          ∫ p in S ×ˢ T, (((q p.1 p.2 - P p.1 p.2) - (q p.2 p.1 - P p.2 p.1)) +
            (P p.1 p.2 - P p.2 p.1)) from by congr 1; funext p; ring]
      have i1 : IntegrableOn (fun p : I × I => (q p.1 p.2 - P p.1 p.2) - (q p.2 p.1 - P p.2 p.1))
          (S ×ˢ T) volume := (intOn hF _).sub (intOn hFT _)
      have i2 : IntegrableOn (fun p : I × I => q p.2 p.1 - P p.2 p.1) (S ×ˢ T) volume := intOn hFT _
      rw [integral_add i1 (intOn hPk _), integral_sub (intOn hF _) i2]
    have b1 := le_cutNorm hF hS hT
    have b2 := le_cutNorm hF hT hS
    have b3 : |∫ p in S ×ˢ T, (P p.1 p.2 - P p.2 p.1)| ≤ η / 2 := by
      set Mx : Fin (M n) → Fin (M n) → ℝ := fun a b =>
        (if (H n).Adj a b then (1 : ℝ) else 0) - (if (H n).Adj b a then 1 else 0)
      have hK : ∀ A B : Finset (Fin (M n)), |∑ a ∈ A, ∑ b ∈ B, Mx a b| ≤ η / 2 * (M n : ℝ) ^ 2 :=
        fun A B => by rw [← disc_eq]; exact hdisc A B
      have e : ∀ x y : I, P x y - P y x =
          Mx (equipartIdx (M n) (hMpos n) (φ x)) (equipartIdx (M n) (hMpos n) (φ y)) := by
        intro x y
        simp only [P, pullback, stepDigraphonOf_eq (H n) (hMpos n), Section4Aux.hostKer,
          Equiv.refl_apply, Mx]
        by_cases h1 : (H n).Adj (equipartIdx (M n) (hMpos n) (φ x))
            (equipartIdx (M n) (hMpos n) (φ y)) <;>
          by_cases h2 : (H n).Adj (equipartIdx (M n) (hMpos n) (φ y))
            (equipartIdx (M n) (hMpos n) (φ x)) <;> simp [h1, h2]
      simp_rw [e]
      have := rect_step (hMpos n) Mx hK hφ hS hT
      have e2 : (1 / (M n : ℝ)) * ((1 / M n) * (η / 2 * (M n : ℝ) ^ 2)) = η / 2 := by
        field_simp
      linarith
    rw [e1]
    have := abs_add_le ((∫ p in S ×ˢ T, (q p.1 p.2 - P p.1 p.2)) -
      (∫ p in T ×ˢ S, (q p.1 p.2 - P p.1 p.2))) (∫ p in S ×ˢ T, (P p.1 p.2 - P p.2 p.1))
    have := abs_sub (∫ p in S ×ˢ T, (q p.1 p.2 - P p.1 p.2))
      (∫ p in T ×ˢ S, (q p.1 p.2 - P p.1 p.2))
    linarith
  have hker : IsKernel (fun x y => q x y - q y x) :=
    Section2Aux.isKernel_add (Section4Aux.isKernel_of_isDigraphon hq)
      (Section2Aux.isKernel_neg (Section4Aux.isKernel_kTranspose
        (Section4Aux.isKernel_of_isDigraphon hq)))
  have hae := ae_zero_of_rect hker hrect
  unfold AEEq
  filter_upwards [hae] with p hp
  simp only [q, kTranspose] at hp ⊢
  linarith

end SeqToKernel

/-! ## The bridges -/

section Main

variable {V : Type u} [Fintype V]

/-- **Question 1(c), finite-host bridge (OS).** -/
theorem isOS_iff_isOSK_proof (D : OrientedGraph V) : D.IsOS ↔ D.IsOSK := by
  classical
  exact ⟨os_to_osk D, osk_to_os D⟩

/-- **Question 1(c), finite-host bridge (OAS).** -/
theorem isOAS_iff_isOASK_proof (D : OrientedGraph V) : D.IsOAS ↔ D.IsOASK := by
  classical
  exact ⟨oas_to_oask D, oask_to_oas D⟩

/-- **Question 1(c), sequence bridge (symmetry-forcing).** -/
theorem isSymmetryForcing_iff_isSymmetryForcingK_proof (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u})
    (hcpt : FHMZCompactHyp) (D : OrientedGraph V) :
    D.IsSymmetryForcing ↔ D.IsSymmetryForcingK :=
  ⟨sf_to_sfk h13 h18 D, sfk_to_sf h18 hcpt D⟩

end Main

end S1Bridges

end NieWeiOrientedSidorenko
