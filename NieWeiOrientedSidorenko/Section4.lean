import NieWeiOrientedSidorenko.Section2
import NieWeiOrientedSidorenko.Literature
import NieWeiOrientedSidorenko.Section4Aux

/-!
# Section 4: OS directed graphs

Theorem 4.1 and Lemmas 4.2–4.6, stated in the digraphon language of Section 2.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

universe u

namespace NieWeiOrientedSidorenko

namespace Section4Aux

variable {V : Type u} [Fintype V]

open OrientedGraph

lemma mem_arcs (D : OrientedGraph V) (p : V × V) : p ∈ D.arcs ↔ D.Adj p.1 p.2 := by
  classical
  unfold OrientedGraph.arcs
  simp

/-- One-direction bridge: `t(D, U) = t_bi(\bar D, U)` for the bipartition of the arcs. -/
lemma t_eq_tb (D : OrientedGraph V) (s : V → Prop) [DecidablePred s]
    (hs : ∀ u v, D.Adj u v → s u ∧ ¬ s v) (U : I → I → ℝ) :
    t D U = tb (sideEdges D.underlying s) U := by
  classical
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => (volume : Measure I)) s
  unfold t tb tDir tBi
  have h2 := hmp.integral_comp' (g := fun z : ({v // s v} → I) × ({v // ¬ s v} → I) =>
    ∏ p ∈ sideEdges D.underlying s, U (z.1 p.1) (z.2 p.2))
  refine Eq.trans ?_ h2
  congr 1
  funext x
  simp only [MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
    Equiv.piEquivPiSubtypeProd_apply]
  have hE : ∀ (a : {v // s v}) (b : {v // ¬ s v}),
      (a, b) ∈ sideEdges D.underlying s ↔ D.underlying.Adj a.1 b.1 := by
    intro a b
    unfold sideEdges
    simp
  symm
  refine Finset.prod_bij (fun p _ => (p.1.1, p.2.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    rw [hE] at h
    rw [mem_arcs]
    simp only [OrientedGraph.underlying, SimpleGraph.fromRel_adj] at h
    rcases h.2 with h' | h'
    · exact h'
    · exact absurd (hs _ _ h').1 b.2
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h
    ext <;> simp [h.1, h.2]
  · rintro ⟨u, v⟩ h
    rw [mem_arcs] at h
    refine ⟨(⟨u, (hs _ _ h).1⟩, ⟨v, (hs _ _ h).2⟩), ?_, rfl⟩
    rw [hE]
    exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun e => D.irrefl u (by simp only at e; rw [← e] at h; exact h), Or.inl h⟩
  · intro p _
    rfl

/-- For `D ≅ D^T`, `t(D, U^T) = t(D, U)`. -/
lemma t_transpose_of_selfConverse (D : OrientedGraph V) (hD : D.IsSelfConverse)
    (U : I → I → ℝ) : t D (kTranspose U) = t D U := by
  classical
  obtain ⟨φ⟩ := hD
  have hmp := measurePreserving_piCongrLeft (fun _ : V => (volume : Measure I)) φ.toEquiv
  unfold t tDir
  have h2 := hmp.integral_comp' (g := fun x : V → I => ∏ p ∈ D.arcs, U (x p.1) (x p.2))
  refine Eq.trans ?_ h2
  congr 1
  funext y
  simp only [kTranspose]
  have hadj : ∀ a b, D.Adj (φ.toEquiv a) (φ.toEquiv b) ↔ D.Adj b a := fun a b =>
    φ.map_adj_iff b a
  refine Finset.prod_nbij' (fun p => (φ.toEquiv p.2, φ.toEquiv p.1))
    (fun p => (φ.toEquiv.symm p.2, φ.toEquiv.symm p.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [mem_arcs] at h ⊢
    exact (hadj b a).2 h
  · rintro ⟨a, b⟩ h
    simp only [mem_arcs] at h ⊢
    have := (hadj (φ.toEquiv.symm a) (φ.toEquiv.symm b)).1
    simp only [Equiv.apply_symm_apply] at this
    exact this h
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

lemma isKernel_of_isDigraphon {U : I → I → ℝ} (hU : IsDigraphon U) : IsKernel U :=
  ⟨hU.1, 1, fun x y => by
    rw [abs_le]; exact ⟨by linarith [(hU.2 x y).1], (hU.2 x y).2⟩⟩

lemma isKernel_kTranspose {U : I → I → ℝ} (hU : IsKernel U) : IsKernel (kTranspose U) := by
  refine ⟨?_, ?_⟩
  · exact hU.1.comp measurable_swap
  · obtain ⟨M, hM⟩ := hU.2
    exact ⟨M, fun x y => hM y x⟩

lemma measurable_equipartIdx (n : ℕ) (hn : 0 < n) : Measurable (equipartIdx n hn) := by
  refine measurable_to_countable' fun i => ?_
  have hg : Measurable fun x : I => min (⌊(x : ℝ) * n⌋₊) (n - 1) :=
    ((measurable_subtype_coe.mul_const _).nat_floor).min measurable_const
  have : equipartIdx n hn ⁻¹' {i} = (fun x : I => min (⌊(x : ℝ) * n⌋₊) (n - 1)) ⁻¹' {i.val} := by
    ext x
    simp [equipartIdx, Fin.ext_iff]
  rw [this]
  exact hg (measurableSet_singleton _)

lemma volume_equipartIdx_pos (n : ℕ) (hn : 0 < n) (i : Fin n) :
    0 < volume (equipartIdx n hn ⁻¹' {i}) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.2
  have ha0 : (0 : ℝ) ≤ i / n := by positivity
  have ha1 : (i : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; linarith
  have hb0 : (0 : ℝ) ≤ (i + 1) / n := by positivity
  have hb1 : ((i : ℝ) + 1) / n ≤ 1 := by rw [div_le_one hnr]; linarith
  let a : I := ⟨i / n, ha0, ha1⟩
  let b : I := ⟨(i + 1) / n, hb0, hb1⟩
  have hsub : Ioo a b ⊆ equipartIdx n hn ⁻¹' {i} := by
    intro x hx
    have h1 : (i : ℝ) / n < x := hx.1
    have h2 : (x : ℝ) < (i + 1) / n := hx.2
    rw [div_lt_iff₀ hnr] at h1
    rw [lt_div_iff₀ hnr] at h2
    have hfl : ⌊(x : ℝ) * n⌋₊ = i := by
      rw [Nat.floor_eq_iff (mul_nonneg x.2.1 hnr.le)]
      exact ⟨h1.le, h2⟩
    simp only [mem_preimage, mem_singleton_iff, equipartIdx, Fin.ext_iff, hfl]
    omega
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [unitInterval.volume_Ioo]
  simp only [ENNReal.ofReal_pos, a, b, sub_pos]
  rw [div_lt_div_iff_of_pos_right hnr]
  linarith

/-- The host kernel of a finite oriented graph. -/
noncomputable def hostKer {W' : Type*} (H : OrientedGraph W') (n : ℕ) (hn : 0 < n)
    (e : Fin n ≃ W') : I → I → ℝ := by
  classical
  exact fun x y => if H.Adj (e (equipartIdx n hn x)) (e (equipartIdx n hn y)) then 1 else 0

lemma isDigraphon_hostKer {W' : Type*} (H : OrientedGraph W') (n : ℕ) (hn : 0 < n)
    (e : Fin n ≃ W') : IsDigraphon (hostKer H n hn e) := by
  classical
  refine ⟨?_, fun x y => ?_⟩
  · have hm : Measurable fun p : I × I => (equipartIdx n hn p.1, equipartIdx n hn p.2) :=
      ((measurable_equipartIdx n hn).comp measurable_fst).prodMk
        ((measurable_equipartIdx n hn).comp measurable_snd)
    have hg : Measurable fun q : Fin n × Fin n => if H.Adj (e q.1) (e q.2) then (1 : ℝ) else 0 :=
      measurable_of_countable _
    convert hg.comp hm using 1
    funext p
    simp only [hostKer, Function.uncurry, Function.comp]
  · simp only [hostKer]
    split_ifs <;> simp

lemma measurable_integrand (D : OrientedGraph V) {K : I → I → ℝ}
    (hK : Measurable (Function.uncurry K)) :
    Measurable fun x : V → I => ∏ p ∈ D.arcs, K (x p.1) (x p.2) := by
  refine Finset.measurable_prod _ fun p _ => ?_
  exact hK.comp (by fun_prop : Measurable fun x : V → I => (x p.1, x p.2))

/-- The host-graph contradiction: a finite oriented host receiving no homomorphism from `D`
but receiving one from `\bar D` into its underlying graph witnesses that `D` is not OS. -/
lemma not_isOSK_of_host {W' : Type*} [Fintype W'] [Nonempty W'] (D : OrientedGraph V)
    (H : OrientedGraph W')
    (h1 : ∀ f : V → W', ∃ u v, D.Adj u v ∧ ¬ H.Adj (f u) (f v))
    (h2 : ∃ f : V → W', ∀ u v, D.Adj u v → H.Adj (f u) (f v) ∨ H.Adj (f v) (f u)) :
    ¬ D.IsOSK := by
  classical
  intro hOS
  set n := Fintype.card W' with hn_def
  have hn : 0 < n := Fintype.card_pos
  let e : Fin n ≃ W' := (Fintype.equivFin W').symm
  let ι : I → W' := fun x => e (equipartIdx n hn x)
  have hK := isDigraphon_hostKer H n hn e
  have hle := hOS _ hK
  have h0 : t D (hostKer H n hn e) = 0 := by
    unfold t tDir
    have : (fun x : V → I => ∏ p ∈ D.arcs, hostKer H n hn e (x p.1) (x p.2)) = fun _ => 0 := by
      funext x
      obtain ⟨u, v, huv, hn'⟩ := h1 (fun w => ι (x w))
      refine Finset.prod_eq_zero ((mem_arcs D (u, v)).2 huv) ?_
      simp only [hostKer]
      exact if_neg hn'
    rw [this, integral_zero]
  obtain ⟨f, hf⟩ := h2
  have hpos : 0 < t D (symmetrize (hostKer H n hn e)) := by
    have hKv : ∀ x y, hostKer H n hn e x y ∈ Icc (0 : ℝ) 1 := hK.2
    have hsym_nn : ∀ x y, 0 ≤ symmetrize (hostKer H n hn e) x y := by
      intro x y
      have := (hKv x y).1; have := (hKv y x).1
      simp only [symmetrize]; positivity
    have hsym_le : ∀ x y, symmetrize (hostKer H n hn e) x y ≤ 1 := by
      intro x y
      have := (hKv x y).2; have := (hKv y x).2
      simp only [symmetrize]; linarith
    have hsm : Measurable (Function.uncurry (symmetrize (hostKer H n hn e))) := by
      have := hK.1
      have h' : Measurable fun p : I × I => hostKer H n hn e p.2 p.1 := this.comp measurable_swap
      exact (this.add h').div_const 2
    unfold t tDir
    rw [integral_pos_iff_support_of_nonneg]
    · let B : Set (V → I) := Set.pi univ fun v => ι ⁻¹' {f v}
      have hB : 0 < (Measure.pi fun _ : V => (volume : Measure I)) B := by
        rw [Measure.pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
        intro v _
        refine ne_of_gt ?_
        have : ι ⁻¹' {f v} = equipartIdx n hn ⁻¹' {e.symm (f v)} := by
          ext x; simp [ι, Equiv.apply_eq_iff_eq_symm_apply]
        rw [this]
        exact volume_equipartIdx_pos n hn _
      refine lt_of_lt_of_le hB (measure_mono fun x hx => ?_)
      simp only [B, Set.mem_pi, mem_univ, mem_preimage, mem_singleton_iff, true_implies] at hx
      rw [Function.mem_support]
      refine (Finset.prod_pos fun p hp => ?_).ne'
      rw [mem_arcs] at hp
      simp only [symmetrize, hostKer]
      change 0 < ((if H.Adj (ι (x p.1)) (ι (x p.2)) then (1 : ℝ) else 0) +
        (if H.Adj (ι (x p.2)) (ι (x p.1)) then (1 : ℝ) else 0)) / 2
      rw [hx p.1, hx p.2]
      rcases hf _ _ hp with h | h
      · rw [if_pos h]; split_ifs <;> norm_num
      · rw [if_pos h]; split_ifs <;> norm_num
    · intro x
      exact Finset.prod_nonneg fun p _ => hsym_nn _ _
    · refine Integrable.of_bound (measurable_integrand D hsm).aestronglyMeasurable 1
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun p _ => hsym_nn _ _)]
      exact Finset.prod_le_one₀ (fun p _ => hsym_nn _ _) (fun p _ => hsym_le _ _)
  linarith

omit [Fintype V] in
lemma underlying_adj (D : OrientedGraph V) (a b : V) :
    D.underlying.Adj a b ↔ a ≠ b ∧ (D.Adj a b ∨ D.Adj b a) := by
  simp [OrientedGraph.underlying, SimpleGraph.fromRel_adj]

omit [Fintype V] in
lemma underlying_adj_of_adj (D : OrientedGraph V) {a b : V} (h : D.Adj a b) :
    D.underlying.Adj a b :=
  (underlying_adj D a b).2 ⟨fun e => D.irrefl a (by rw [← e] at h; exact h), Or.inl h⟩

/-- Step 1 of Lemma 4.2: an OS directed graph admits a ranking increasing along arcs. -/
lemma exists_rank_of_isOSK (D : OrientedGraph V) (hD : D.IsOSK) :
    ∃ r : V → ℕ, ∀ u v, D.Adj u v → r u < r v := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨fun _ => 0, fun u => isEmptyElim u⟩
  by_contra hr
  let e := Fintype.equivFin V
  let H : OrientedGraph V :=
    { Adj := fun a b => D.underlying.Adj a b ∧ e a < e b
      irrefl := fun a h => lt_irrefl _ h.2
      asymm := fun a b h h' => lt_asymm h.2 h'.2 }
  refine not_isOSK_of_host D H ?_ ⟨id, fun u v h => ?_⟩ hD
  · intro f
    by_contra hf
    push_neg at hf
    exact hr ⟨fun v => (e (f v)).val, fun u v h => (hf u v h).2⟩
  · have hG := underlying_adj_of_adj D h
    have hne : e u ≠ e v := fun h' => hG.ne (e.injective h')
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact Or.inl ⟨hG, h'⟩
    · exact Or.inr ⟨hG.symm, h'⟩

/-- The bipartite case of Lemma 4.2. -/
lemma homToDirEdge_of_colorable (D : OrientedGraph V) (hD : D.IsOSK)
    (hcol : D.underlying.Colorable 2) : D.HomToDirEdge := by
  classical
  by_contra hne
  obtain ⟨C⟩ := hcol
  have hadj : ∀ a b : Fin 2, dirEdge.Adj a b ↔ a = 0 ∧ b = 1 := by
    intro a b
    simp [dirEdge, ofArcs]
  refine not_isOSK_of_host D dirEdge ?_ ⟨fun v => C v, fun u v h => ?_⟩ hD
  · intro f
    by_contra hf
    push_neg at hf
    exact hne ⟨f, fun u v h => (hadj _ _).1 (hf u v h)⟩
  · have hc := C.valid (underlying_adj_of_adj D h)
    rw [hadj, hadj]
    have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (b = 0 ∧ a = 1) := by decide
    exact key _ _ hc

/-- A walk all of whose darts are arcs of an oriented graph `H` increases a ranking of `H` by at
least its length. -/
lemma rank_walk {G : SimpleGraph V} (H : OrientedGraph V) (ρ : V → ℕ)
    (hρ : ∀ a b, H.Adj a b → ρ a < ρ b) :
    ∀ {a b : V} (p : G.Walk a b), (∀ d ∈ p.darts, H.Adj d.fst d.snd) → ρ a + p.length ≤ ρ b
  | _, _, .nil, _ => by simp
  | _, _, .cons h p, hd => by
    simp only [SimpleGraph.Walk.darts_cons, List.mem_cons, forall_eq_or_imp] at hd
    have h1 := hρ _ _ hd.1
    have h2 := rank_walk H ρ hρ p hd.2
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- The non-bipartite (core) case of Lemma 4.2.
True only vacuously: an OS directed graph has a 2-colourable underlying graph (Lemma 4.2); this
is the non-bipartite case of the proof by contradiction at tex l.726-732. -/
lemma false_of_not_colorable (D : OrientedGraph V) (hD : D.IsOSK) (r : V → ℕ)
    (hr : ∀ u v, D.Adj u v → r u < r v) (hcol : ¬ D.underlying.Colorable 2) : False := by
  classical
  set G := D.underlying with hGdef
  have hV : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hcol ⟨SimpleGraph.Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v)⟩
  -- an endomorphism of `G` with an image of least size
  let IsEndo : (V → V) → Prop := fun φ => ∀ a b, G.Adj a b → G.Adj (φ a) (φ b)
  obtain ⟨φ, hφmem, hφmin⟩ := Finset.exists_min_image (Finset.univ.filter IsEndo)
    (fun φ => (Finset.univ.image φ).card) ⟨id, by simp [IsEndo]⟩
  have hφ : IsEndo φ := (Finset.mem_filter.1 hφmem).2
  set K := Finset.univ.image φ with hKdef
  let GK : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ K ∧ b ∈ K
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ }
  have hGK : ∀ a b, GK.Adj a b ↔ G.Adj a b ∧ a ∈ K ∧ b ∈ K := fun a b => Iff.rfl
  have hφK : ∀ a b, G.Adj a b → GK.Adj (φ a) (φ b) := fun a b h =>
    ⟨hφ a b h, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hGKcol : ¬ GK.Colorable 2 := by
    rintro ⟨C⟩
    exact hcol ⟨SimpleGraph.Coloring.mk (fun v => C (φ v)) (fun {a b} h => C.valid (hφK a b h))⟩
  have hcyc : ¬ GK.IsAcyclic := fun h => hGKcol h.colorable_two
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hcyc
  obtain ⟨v0, c, hc⟩ := hcyc
  let e := Fintype.equivFin V
  have hedge : ∀ d ∈ c.darts, d.edge ∈ c.edges := fun d hd => by
    rw [SimpleGraph.Walk.edges_eq_map_darts]; exact List.mem_map_of_mem hd
  have hdedge : ∀ (d : GK.Dart) a b, d.fst = a → d.snd = b → d.edge = s(a, b) := by
    intro d a b h1 h2; rw [← h1, ← h2]; rfl
  let H : OrientedGraph V :=
    { Adj := fun a b => (∃ d ∈ c.darts, d.fst = a ∧ d.snd = b) ∨
        (GK.Adj a b ∧ s(a, b) ∉ c.edges ∧ e a < e b)
      irrefl := by
        rintro a (⟨d, _, h1, h2⟩ | ⟨h, _, _⟩)
        · have := d.adj; rw [h1, h2] at this; exact GK.irrefl this
        · exact GK.irrefl h
      asymm := by
        rintro a b (⟨d, hd, h1, h2⟩ | ⟨h, hn, hlt⟩) (⟨d', hd', h1', h2'⟩ | ⟨h', hn', hlt'⟩)
        · have hnd : (c.darts.map SimpleGraph.Dart.edge).Nodup := by
            rw [← SimpleGraph.Walk.edges_eq_map_darts]; exact hc.edges_nodup
          have heq : d.edge = d'.edge := by
            rw [hdedge d a b h1 h2, hdedge d' b a h1' h2', Sym2.eq_swap]
          have := List.inj_on_of_nodup_map hnd hd hd' heq
          have hadj := d.adj
          rw [this, h1', ← this, h2] at hadj
          exact GK.irrefl hadj
        · apply hn'
          rw [Sym2.eq_swap, ← hdedge d a b h1 h2]
          exact hedge d hd
        · apply hn
          rw [Sym2.eq_swap, ← hdedge d' b a h1' h2']
          exact hedge d' hd'
        · exact lt_asymm hlt hlt' }
  have hHGK : ∀ a b, H.Adj a b → GK.Adj a b := by
    rintro a b (⟨d, _, h1, h2⟩ | ⟨h, _, _⟩)
    · have := d.adj; rw [h1, h2] at this; exact this
    · exact h
  have hHtot : ∀ a b, GK.Adj a b → H.Adj a b ∨ H.Adj b a := by
    intro a b h
    by_cases hm : s(a, b) ∈ c.edges
    · rw [SimpleGraph.Walk.edges_eq_map_darts, List.mem_map] at hm
      obtain ⟨d, hd, hde⟩ := hm
      have hde' : s(d.fst, d.snd) = s(a, b) := hde
      rcases Sym2.eq_iff.1 hde' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; left; exact ⟨d, hd, h1, h2⟩
      · right; left; exact ⟨d, hd, h1, h2⟩
    · have hne : e a ≠ e b := fun h' => GK.ne_of_adj h (e.injective h')
      rcases lt_or_gt_of_ne hne with h' | h'
      · left; right; exact ⟨h, hm, h'⟩
      · right; right
        refine ⟨h.symm, ?_, h'⟩
        rwa [Sym2.eq_swap]
  refine not_isOSK_of_host D H ?_ ⟨φ, fun u v huv => hHtot _ _ (hφK u v
    (underlying_adj_of_adj D huv))⟩ hD
  intro ψ
  by_contra hψ
  push_neg at hψ
  -- `ψ` is an endomorphism of `G`
  have hψG : ∀ a b, G.Adj a b → GK.Adj (ψ a) (ψ b) := by
    intro a b h
    rcases ((underlying_adj D a b).1 h).2 with h' | h'
    · exact hHGK _ _ (hψ _ _ h')
    · exact (hHGK _ _ (hψ _ _ h')).symm
  have hψφ : IsEndo (ψ ∘ φ) := fun a b h => (hψG _ _ (hφ a b h)).1
  have hcard : K.card ≤ (K.image ψ).card := by
    have := hφmin (ψ ∘ φ) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hψφ⟩)
    rwa [← Finset.image_image] at this
  have hinj : Set.InjOn ψ K := by
    exact Finset.card_image_iff.1 (le_antisymm Finset.card_image_le hcard)
  -- the ordered adjacent pairs inside `K`
  let P := (K ×ˢ K).filter fun p => GK.Adj p.1 p.2
  have hmemP : ∀ p : V × V, p ∈ P ↔ GK.Adj p.1 p.2 := by
    intro p
    simp only [P, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => h.2, fun h => ⟨⟨h.2.1, h.2.2⟩, h⟩⟩
  let m : V × V → V × V := fun p => (ψ p.1, ψ p.2)
  have hmP : P.image m ⊆ P := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    rw [hmemP] at hp ⊢
    exact hψG _ _ hp.1
  have hminj : Set.InjOn m P := by
    intro p hp q hq h
    rw [Finset.mem_coe, hmemP] at hp hq
    simp only [m, Prod.mk.injEq] at h
    exact Prod.ext (hinj hp.2.1 hq.2.1 h.1) (hinj hp.2.2 hq.2.2 h.2)
  have himP : P.image m = P :=
    Finset.eq_of_subset_of_card_le hmP (Finset.card_image_of_injOn hminj).ge
  -- every arc of `H` is the image of an arc of `D` inside `K`
  have hpre : ∀ a b, H.Adj a b → ∃ a' ∈ K, ∃ b' ∈ K, ψ a' = a ∧ ψ b' = b ∧ D.Adj a' b' := by
    intro a b h
    have hab : (a, b) ∈ P.image m := by rw [himP, hmemP]; exact hHGK _ _ h
    obtain ⟨⟨a', b'⟩, hp, hm⟩ := Finset.mem_image.1 hab
    simp only [m, Prod.mk.injEq] at hm
    rw [hmemP] at hp
    refine ⟨a', hp.2.1, b', hp.2.2, hm.1, hm.2, ?_⟩
    rcases ((underlying_adj D a' b').1 hp.1).2 with h' | h'
    · exact h'
    · exfalso
      have := hψ _ _ h'
      rw [hm.1, hm.2] at this
      exact H.asymm _ _ h this
  -- a ranking of `H`
  let ρ : V → ℕ := fun a => if h : ∃ a' ∈ K, ψ a' = a then r (Classical.choose h) else 0
  have hρ_eq : ∀ a' ∈ K, ρ (ψ a') = r a' := by
    intro a' ha'
    have h : ∃ x ∈ K, ψ x = ψ a' := ⟨a', ha', rfl⟩
    simp only [ρ, dif_pos h]
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    rw [hinj h1 ha' h2]
  have hρ : ∀ a b, H.Adj a b → ρ a < ρ b := by
    intro a b h
    obtain ⟨a', ha', b', hb', rfl, rfl, hD'⟩ := hpre a b h
    rw [hρ_eq a' ha', hρ_eq b' hb']
    exact hr _ _ hD'
  have hall : ∀ d ∈ c.darts, H.Adj d.fst d.snd := fun d hd => Or.inl ⟨d, hd, rfl, rfl⟩
  have := rank_walk H ρ hρ c hall
  have h3 := hc.three_le_length
  omega

omit [Fintype V] in
/-- In a connected oriented graph with an arc, no vertex is isolated. -/
lemma exists_adj_of_connected (D : OrientedGraph V) (hconn : D.IsConnected) {u0 v0 : V}
    (h0 : D.Adj u0 v0) : ∀ v, ∃ u, D.underlying.Adj v u := by
  intro v
  have hne : u0 ≠ v0 := (underlying_adj_of_adj D h0).ne
  have key : ∀ w, w ≠ v → ∃ u, D.underlying.Adj v u := by
    intro w hw
    obtain ⟨p⟩ := hconn.preconnected v w
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, h⟩
  by_cases hv : u0 = v
  · exact key v0 (fun h => hne (hv.trans h.symm))
  · exact key u0 hv

/-- Along a walk, the two proper 2-colourings `f` and `f ∘ g` either agree or disagree
uniformly. -/
lemma flip_walk (G : SimpleGraph V) (f : V → Fin 2) (hf : ∀ a b, G.Adj a b → f a ≠ f b)
    (g : V → V) (hg : ∀ a b, G.Adj a b → G.Adj (g a) (g b)) :
    ∀ {a b : V} (_ : G.Walk a b), (f (g a) = f a ↔ f (g b) = f b)
  | _, _, .nil => Iff.rfl
  | _, _, .cons h p => by
    refine Iff.trans ?_ (flip_walk G f hf g hg p)
    have h1 := hf _ _ h
    have h2 := hf _ _ (hg _ _ h)
    revert h1 h2
    generalize f (g _) = x1
    generalize f (g _) = x2
    generalize f _ = x3
    generalize f _ = x4
    revert x1 x2 x3 x4
    decide

lemma measurable_integrandΩ {Ω : Type*} [MeasurableSpace Ω] (D : OrientedGraph V)
    {K : Ω → Ω → ℝ} (hK : Measurable (Function.uncurry K)) :
    Measurable fun x : V → Ω => ∏ p ∈ D.arcs, K (x p.1) (x p.2) := by
  refine Finset.measurable_prod _ fun p _ => ?_
  exact hK.comp (by fun_prop : Measurable fun x : V → Ω => (x p.1, x p.2))

lemma abs_integrand_le_one {Ω : Type*} (D : OrientedGraph V) {K : Ω → Ω → ℝ}
    (hK : ∀ p q, |K p q| ≤ 1) (x : V → Ω) : ‖∏ p ∈ D.arcs, K (x p.1) (x p.2)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hK _ _)

/-- Densities pulled back along the splitting map. -/
lemma t_pullback_halfSplit (D : OrientedGraph V) (K : I × Bool → I × Bool → ℝ)
    (hK : Measurable (Function.uncurry K)) :
    t D (fun x y => K (halfSplit x) (halfSplit y)) = tDir twoCopies D K := by
  have hmp := measurePreserving_pi (fun _ : V => (volume : Measure I)) (fun _ => twoCopies)
    (fun _ => measurePreserving_halfSplit)
  unfold t tDir
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (measurable_integrandΩ D hK).aestronglyMeasurable]

/-- The density over the two copies as an average over the copy labels. -/
lemma tDir_twoCopies_eq [DecidableEq V] (D : OrientedGraph V) (K : I × Bool → I × Bool → ℝ)
    (hK : Measurable (Function.uncurry K)) (hKb : ∀ p q, |K p q| ≤ 1) :
    tDir twoCopies D K = ∑ τ : V → Bool, (2⁻¹ : ℝ) ^ Fintype.card V *
      ∫ x : V → I, ∏ p ∈ D.arcs, K (x p.1, τ p.1) (x p.2, τ p.2)
        ∂(Measure.pi fun _ => (volume : Measure I)) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow I Bool V (fun _ => volume)
    (fun _ => halfCount)
  unfold tDir twoCopies
  have h1 := hmp.symm.integral_comp' (g := fun x : V → I × Bool =>
    ∏ p ∈ D.arcs, K (x p.1) (x p.2))
  rw [← h1]
  have hint : Integrable (fun z : (V → I) × (V → Bool) =>
      ∏ p ∈ D.arcs, K ((z.1 p.1, z.2 p.1)) ((z.1 p.2, z.2 p.2)))
      ((Measure.pi fun _ => (volume : Measure I)).prod (Measure.pi fun _ => halfCount)) := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun z => ?_)
    · have : Measurable fun z : (V → I) × (V → Bool) => fun v => (z.1 v, z.2 v) := by fun_prop
      exact ((measurable_integrandΩ D hK).comp this).aestronglyMeasurable
    · exact abs_integrand_le_one D hKb (fun v => (z.1 v, z.2 v))
  refine (integral_prod_symm _ hint).trans ?_
  rw [integral_fintype]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_eq_mul]
    congr 1
    have : ({τ} : Set (V → Bool)) = Set.pi univ fun v => {τ v} := by
      ext τ; simp [funext_iff]
    rw [measureReal_def, this, Measure.pi_pi]
    simp [halfCount, Measure.count_singleton, ENNReal.toReal_prod]
  · exact Integrable.of_finite

/-- Agreement of two proper 2-colourings propagates along walks. -/
lemma agree_walk (G : SimpleGraph V) (c1 c2 : V → Bool) (h1 : ∀ a b, G.Adj a b → c1 a ≠ c1 b)
    (h2 : ∀ a b, G.Adj a b → c2 a ≠ c2 b) :
    ∀ {a b : V} (_ : G.Walk a b), (c1 a = c2 a ↔ c1 b = c2 b)
  | _, _, .nil => Iff.rfl
  | _, _, .cons h p => by
    refine Iff.trans ?_ (agree_walk G c1 c2 h1 h2 p)
    have e1 := h1 _ _ h
    have e2 := h2 _ _ h
    revert e1 e2
    cases c1 _ <;> cases c1 _ <;> cases c2 _ <;> cases c2 _ <;> simp

/-- For a connected one-direction `D`, the only labellings with no monochromatic arc are the
side labelling `τA` and its complement. -/
lemma sum_two_labellings [DecidableEq V] (D : OrientedGraph V) (hconn : D.IsConnected) (f : V → Fin 2)
    (hf : ∀ u v, D.Adj u v → f u = 0 ∧ f v = 1) (g : (V → Bool) → ℝ)
    (hg : ∀ τ : V → Bool, (∃ a b, D.Adj a b ∧ τ a = τ b) → g τ = 0) :
    ∑ τ, g τ = g (fun v => decide (f v = 0)) + g (fun v => !decide (f v = 0)) := by
  classical
  obtain ⟨v0⟩ := hconn.nonempty
  set τA : V → Bool := fun v => decide (f v = 0)
  have hA : ∀ a b, D.underlying.Adj a b → τA a ≠ τA b := by
    intro a b h
    rcases ((underlying_adj D a b).1 h).2 with h' | h'
    · simp [τA, (hf _ _ h').1, (hf _ _ h').2]
    · simp [τA, (hf _ _ h').1, (hf _ _ h').2]
  refine Finset.sum_eq_add_of_mem _ _ (Finset.mem_univ _) (Finset.mem_univ _) ?_ ?_
  · intro h
    have := congrFun h v0
    simp only [τA] at this
    cases decide (f v0 = 0) <;> simp at this
  · rintro τ - ⟨hτA, hτB⟩
    apply hg
    by_contra hno
    push_neg at hno
    have hτ : ∀ a b, D.underlying.Adj a b → τ a ≠ τ b := by
      intro a b h
      rcases ((underlying_adj D a b).1 h).2 with h' | h'
      · exact hno a b h'
      · exact (hno b a h').symm
    by_cases h0 : τ v0 = τA v0
    · apply hτA
      funext v
      obtain ⟨p⟩ := hconn.preconnected v0 v
      exact (agree_walk _ τ τA hτ hA p).1 h0
    · apply hτB
      funext v
      obtain ⟨p⟩ := hconn.preconnected v0 v
      have : ¬ τ v = τA v := fun h => h0 ((agree_walk _ τ τA hτ hA p).2 h)
      cases hv : τ v <;> cases hv' : τA v <;> simp_all [τA]

/-- The two-copies density of a kernel vanishing on the diagonal blocks. -/
lemma tDir_twoCopies_offDiag (D : OrientedGraph V) (hconn : D.IsConnected) (f : V → Fin 2)
    (hf : ∀ u v, D.Adj u v → f u = 0 ∧ f v = 1) (K : I × Bool → I × Bool → ℝ)
    (hK : Measurable (Function.uncurry K)) (hKb : ∀ p q, |K p q| ≤ 1)
    (hK0 : ∀ x y b, K (x, b) (y, b) = 0) :
    tDir twoCopies D K = (2⁻¹ : ℝ) ^ Fintype.card V *
      (t D (fun x y => K (x, true) (y, false)) + t D (fun x y => K (x, false) (y, true))) := by
  classical
  rw [tDir_twoCopies_eq D K hK hKb, sum_two_labellings D hconn f hf, mul_add]
  · congr 1
    · congr 1
      unfold t tDir
      congr 1
      funext x
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [mem_arcs] at hp
      simp [(hf _ _ hp).1, (hf _ _ hp).2]
    · congr 1
      unfold t tDir
      congr 1
      funext x
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [mem_arcs] at hp
      simp [(hf _ _ hp).1, (hf _ _ hp).2]
  · rintro τ ⟨a, b, hab, hτ⟩
    have : (fun x : V → I => ∏ p ∈ D.arcs, K (x p.1, τ p.1) (x p.2, τ p.2)) = fun _ => 0 := by
      funext x
      refine Finset.prod_eq_zero ((mem_arcs D (a, b)).2 hab) ?_
      simp only
      rw [hτ, hK0]
    rw [this, integral_zero, mul_zero]

/-- The block kernel `[[0, U], [V^T, 0]]` on the two copies (copy `true` first). -/
noncomputable def blockK (U V : I → I → ℝ) : I × Bool → I × Bool → ℝ := fun p q =>
  if p.2 = true ∧ q.2 = false then U p.1 q.1 else if p.2 = false ∧ q.2 = true then V q.1 p.1
  else 0

lemma measurable_blockK {U V : I → I → ℝ} (hU : Measurable (Function.uncurry U))
    (hV : Measurable (Function.uncurry V)) : Measurable (Function.uncurry (blockK U V)) := by
  classical
  have hb1 : Measurable fun z : (I × Bool) × (I × Bool) => z.1.2 := by fun_prop
  have hb2 : Measurable fun z : (I × Bool) × (I × Bool) => z.2.2 := by fun_prop
  have hs1 : MeasurableSet {z : (I × Bool) × (I × Bool) | z.1.2 = true ∧ z.2.2 = false} :=
    (hb1 (measurableSet_singleton true)).inter (hb2 (measurableSet_singleton false))
  have hs2 : MeasurableSet {z : (I × Bool) × (I × Bool) | z.1.2 = false ∧ z.2.2 = true} :=
    (hb1 (measurableSet_singleton false)).inter (hb2 (measurableSet_singleton true))
  have hfU : Measurable fun z : (I × Bool) × (I × Bool) => U z.1.1 z.2.1 :=
    hU.comp (by fun_prop : Measurable fun z : (I × Bool) × (I × Bool) => (z.1.1, z.2.1))
  have hfV : Measurable fun z : (I × Bool) × (I × Bool) => V z.2.1 z.1.1 :=
    hV.comp (by fun_prop : Measurable fun z : (I × Bool) × (I × Bool) => (z.2.1, z.1.1))
  exact Measurable.ite hs1 hfU (Measurable.ite hs2 hfV measurable_const)

lemma blockK_mem {U V : I → I → ℝ} (hU : IsDigraphon U) (hV : IsDigraphon V) (p q : I × Bool) :
    blockK U V p q ∈ Icc (0 : ℝ) 1 := by
  unfold blockK
  split_ifs
  · exact hU.2 _ _
  · exact hV.2 _ _
  · exact ⟨le_refl _, zero_le_one⟩

lemma abs_le_one_of_mem {r : ℝ} (h : r ∈ Icc (0 : ℝ) 1) : |r| ≤ 1 := by
  rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩

/-- The midpoint inequality from OS, for digraphons. -/
lemma midpoint_digraphon (D : OrientedGraph V) (hconn : D.IsConnected)
    (hsc : D.IsSelfConverse) (hOS : D.IsOSK) (f : V → Fin 2)
    (hf : ∀ u v, D.Adj u v → f u = 0 ∧ f v = 1) (P Q : I → I → ℝ) (hU : IsDigraphon P)
    (hV : IsDigraphon Q) :
    t D (fun x y => (P x y + Q x y) / 2) ≤ (t D P + t D Q) / 2 := by
  classical
  set K := blockK P Q with hKdef
  have hKm := measurable_blockK hU.1 hV.1
  have hKmem := blockK_mem hU hV
  have hSm : Measurable (Function.uncurry (symmetrize K)) :=
    (hKm.add (hKm.comp measurable_swap)).div_const 2
  have hSmem : ∀ p q, symmetrize K p q ∈ Icc (0 : ℝ) 1 := by
    intro p q
    have := hKmem p q; have := hKmem q p
    simp only [symmetrize, mem_Icc] at *
    constructor <;> linarith
  let W : I → I → ℝ := fun x y => K (halfSplit x) (halfSplit y)
  have hW : IsDigraphon W := by
    refine ⟨?_, fun x y => hKmem _ _⟩
    exact hKm.comp (measurable_halfSplit.prodMap measurable_halfSplit)
  have h := hOS W hW
  have e1 : symmetrize W = fun x y => symmetrize K (halfSplit x) (halfSplit y) := rfl
  rw [e1, t_pullback_halfSplit D _ hSm, t_pullback_halfSplit D _ hKm,
    tDir_twoCopies_offDiag D hconn f hf _ hSm (fun p q => abs_le_one_of_mem (hSmem p q)) ?_,
    tDir_twoCopies_offDiag D hconn f hf _ hKm (fun p q => abs_le_one_of_mem (hKmem p q)) ?_] at h
  · have q1 : (fun x y => K (x, true) (y, false)) = P := by
      funext x y; simp [hKdef, blockK]
    have q2 : (fun x y => K (x, false) (y, true)) = kTranspose Q := by
      funext x y; simp [hKdef, blockK, kTranspose]
    have q3 : (fun x y => symmetrize K (x, true) (y, false)) = fun x y => (P x y + Q x y) / 2 := by
      funext x y; simp [hKdef, blockK, symmetrize]
    have q4 : (fun x y => symmetrize K (x, false) (y, true)) =
        kTranspose (fun x y => (P x y + Q x y) / 2) := by
      funext x y; simp [hKdef, blockK, symmetrize, kTranspose]; ring
    rw [q1, q2, q3, q4, t_transpose_of_selfConverse D hsc,
      t_transpose_of_selfConverse D hsc] at h
    have hc : (0 : ℝ) < (2⁻¹ : ℝ) ^ Fintype.card V := by positivity
    have := le_of_mul_le_mul_left h hc
    linarith
  · intro x y b; cases b <;> simp [hKdef, blockK]
  · intro x y b; cases b <;> simp [hKdef, blockK, symmetrize]

lemma t_const_mul (D : OrientedGraph V) (U : I → I → ℝ) (c : ℝ) :
    t D (fun x y => c * U x y) = c ^ D.numArcs * t D U := by
  unfold t tDir
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [integral_const_mul]
  rfl

/-- The midpoint inequality from OS, for nonnegative bounded kernels, for a connected self-converse
OS directed graph `D` with a homomorphism `f` to the directed edge (the setting of Theorem 4.1
after Lemmas 4.2 and 4.4). -/
lemma midpoint_kernel (D : OrientedGraph V) (hconn : D.IsConnected)
    (hsc : D.IsSelfConverse) (hOS : D.IsOSK) (f : V → Fin 2)
    (hf : ∀ u v, D.Adj u v → f u = 0 ∧ f v = 1) (P Q : I → I → ℝ) (hP : IsKernel P)
    (hQ : IsKernel Q) (hP0 : ∀ x y, 0 ≤ P x y) (hQ0 : ∀ x y, 0 ≤ Q x y) :
    t D (fun x y => (P x y + Q x y) / 2) ≤ (t D P + t D Q) / 2 := by
  obtain ⟨MP, hMP⟩ := hP.2
  obtain ⟨MQ, hMQ⟩ := hQ.2
  set c : ℝ := max MP 0 + max MQ 0 + 1 with hc
  have hcpos : 0 < c := by positivity
  have hscale : ∀ (K : I → I → ℝ) (M : ℝ), IsKernel K → (∀ x y, 0 ≤ K x y) →
      (∀ x y, |K x y| ≤ M) → M ≤ c → IsDigraphon (fun x y => c⁻¹ * K x y) := by
    intro K M hK hK0 hKM hMc
    refine ⟨measurable_const.mul hK.1, fun x y => ⟨?_, ?_⟩⟩
    · have := hK0 x y; positivity
    · rw [inv_mul_le_iff₀ hcpos, mul_one]
      have := hKM x y
      rw [abs_of_nonneg (hK0 x y)] at this
      linarith
  have hP' := hscale P MP hP hP0 hMP (by rw [hc]; linarith [le_max_left MP 0, le_max_right MQ 0])
  have hQ' := hscale Q MQ hQ hQ0 hMQ (by rw [hc]; linarith [le_max_right MP 0, le_max_left MQ 0])
  have hmid := midpoint_digraphon D hconn hsc hOS f hf _ _ hP' hQ'
  have eP : t D P = c ^ D.numArcs * t D (fun x y => c⁻¹ * P x y) := by
    rw [← t_const_mul]; congr 1; funext x y; field_simp
  have eQ : t D Q = c ^ D.numArcs * t D (fun x y => c⁻¹ * Q x y) := by
    rw [← t_const_mul]; congr 1; funext x y; field_simp
  have eM : t D (fun x y => (P x y + Q x y) / 2) =
      c ^ D.numArcs * t D (fun x y => (c⁻¹ * P x y + c⁻¹ * Q x y) / 2) := by
    rw [← t_const_mul]; congr 1; funext x y; field_simp
  rw [eM, eP, eQ]
  have hpow : 0 ≤ c ^ D.numArcs := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmid hpow]

/-- Midpoint convexity and continuity on `[0, 1]` give the convexity inequality. -/
lemma convex_of_midpoint (φ : ℝ → ℝ) (hc : ContinuousOn φ (Icc 0 1))
    (hm : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, φ ((a + b) / 2) ≤ (φ a + φ b) / 2) :
    ∀ a ∈ Icc (0 : ℝ) 1, φ a ≤ a * φ 1 + (1 - a) * φ 0 := by
  set g : ℝ → ℝ := fun a => φ a - (a * φ 1 + (1 - a) * φ 0) with hg
  have hgm : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, g ((a + b) / 2) ≤ (g a + g b) / 2 := by
    intro a ha b hb
    simp only [hg]
    have := hm a ha b hb
    linarith
  have hdy : ∀ k : ℕ, ∀ j : ℕ, j ≤ 2 ^ k → g (j / 2 ^ k) ≤ 0 := by
    intro k
    induction k with
    | zero =>
      intro j hj
      simp only [pow_zero, Nat.cast_ofNat, div_one] at hj ⊢
      interval_cases j <;> simp [hg]
    | succ k ih =>
      intro j hj
      rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have : ((i + i : ℕ) : ℝ) / 2 ^ (k + 1) = (i : ℝ) / 2 ^ k := by
          push_cast; rw [pow_succ]; field_simp; ring
        rw [this]
        exact ih i (by rw [pow_succ] at hj; omega)
      · have hi1 : i + 1 ≤ 2 ^ k := by rw [pow_succ] at hj; omega
        have : ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (k + 1) =
            ((i : ℝ) / 2 ^ k + ((i + 1 : ℕ) : ℝ) / 2 ^ k) / 2 := by
          push_cast; rw [pow_succ]; field_simp; ring
        rw [this]
        have hmem : ∀ m : ℕ, m ≤ 2 ^ k → (m : ℝ) / 2 ^ k ∈ Icc (0 : ℝ) 1 := by
          intro m hm
          refine ⟨by positivity, ?_⟩
          rw [div_le_one (by positivity)]
          exact_mod_cast hm
        refine (hgm _ (hmem i (by omega)) _ (hmem (i + 1) hi1)).trans ?_
        have := ih i (by omega)
        have := ih (i + 1) hi1
        linarith
  intro a ha
  have hgc : ContinuousOn g (Icc 0 1) := by
    simp only [hg]
    exact hc.sub (by fun_prop)
  let ak : ℕ → ℝ := fun k => (⌊a * 2 ^ k⌋₊ : ℝ) / 2 ^ k
  have hak_mem : ∀ k, ak k ∈ Icc (0 : ℝ) 1 := by
    intro k
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    calc (⌊a * 2 ^ k⌋₊ : ℝ) ≤ a * 2 ^ k := Nat.floor_le (by have := ha.1; positivity)
      _ ≤ 1 * 2 ^ k := by gcongr; exact ha.2
      _ = 2 ^ k := one_mul _
  have hak_le : ∀ k, g (ak k) ≤ 0 := by
    intro k
    apply hdy
    have : (⌊a * 2 ^ k⌋₊ : ℝ) ≤ 2 ^ k := by
      calc (⌊a * 2 ^ k⌋₊ : ℝ) ≤ a * 2 ^ k := Nat.floor_le (by have := ha.1; positivity)
        _ ≤ 1 * 2 ^ k := by gcongr; exact ha.2
        _ = 2 ^ k := one_mul _
    exact_mod_cast this
  have hlim : Tendsto ak atTop (𝓝 a) := by
    have h2 : Tendsto (fun k : ℕ => a - (2 ^ k : ℝ)⁻¹) atTop (𝓝 a) := by
      have : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
      simpa using (tendsto_const_nhds (x := a)).sub this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h2 tendsto_const_nhds (fun k => ?_)
      (fun k => ?_)
    · have hp : (0 : ℝ) < 2 ^ k := by positivity
      simp only [ak]
      rw [le_div_iff₀ hp, sub_mul, inv_mul_cancel₀ hp.ne']
      have := Nat.lt_floor_add_one (a * 2 ^ k)
      linarith
    · have hp : (0 : ℝ) < 2 ^ k := by positivity
      simp only [ak]
      rw [div_le_iff₀ hp]
      exact Nat.floor_le (by have := ha.1; positivity)
  have hcont := (hgc a ha).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall
    hak_mem⟩)
  have := le_of_tendsto' hcont hak_le
  simp only [hg] at this
  linarith

lemma isKernel_add {P Q : I → I → ℝ} (hP : IsKernel P) (hQ : IsKernel Q) :
    IsKernel (fun x y => P x y + Q x y) := by
  refine ⟨hP.1.add hQ.1, ?_⟩
  obtain ⟨MP, hMP⟩ := hP.2
  obtain ⟨MQ, hMQ⟩ := hQ.2
  exact ⟨MP + MQ, fun x y => (abs_add_le _ _).trans (add_le_add (hMP x y) (hMQ x y))⟩

/-- Convexity of `t(D, ·)` on nonnegative bounded kernels, for a connected self-converse OS directed
graph `D` with a homomorphism `f` to the directed edge (the setting of Theorem 4.1 after Lemmas
4.2 and 4.4). -/
lemma convex_t_of_isOSK (D : OrientedGraph V) (hconn : D.IsConnected)
    (hsc : D.IsSelfConverse) (hOS : D.IsOSK) (f : V → Fin 2)
    (hf : ∀ u v, D.Adj u v → f u = 0 ∧ f v = 1) (P Q : I → I → ℝ) (hP : IsKernel P)
    (hQ : IsKernel Q) (hP0 : ∀ x y, 0 ≤ P x y) (hQ0 : ∀ x y, 0 ≤ Q x y) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    t D (fun x y => a * P x y + (1 - a) * Q x y) ≤ a * t D P + (1 - a) * t D Q := by
  let φ : ℝ → ℝ := fun a => t D (fun x y => a * P x y + (1 - a) * Q x y)
  have h1 : φ 1 = t D P := by simp [φ]
  have h0 : φ 0 = t D Q := by simp [φ]
  have hker : ∀ a, IsKernel (fun x y => a * P x y + (1 - a) * Q x y) := fun a =>
    isKernel_add (isKernel_const_mul hP a) (isKernel_const_mul hQ _)
  have hnn : ∀ a ∈ Icc (0 : ℝ) 1, ∀ x y, 0 ≤ a * P x y + (1 - a) * Q x y := by
    intro a ha x y
    have := hP0 x y; have := hQ0 x y; have := ha.1; have : 0 ≤ 1 - a := by linarith [ha.2]
    positivity
  have hm : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, φ ((a + b) / 2) ≤ (φ a + φ b) / 2 := by
    intro a ha b hb
    have := midpoint_kernel D hconn hsc hOS f hf _ _ (hker a) (hker b) (hnn a ha) (hnn b hb)
    convert this using 2
    funext x y; ring
  obtain ⟨MP, hMP⟩ := hP.2
  obtain ⟨MQ, hMQ⟩ := hQ.2
  have hc : ContinuousOn φ (Icc 0 1) := by
    refine continuousOn_of_dominated (bound := fun _ => (max MP 0 + max MQ 0) ^ D.arcs.card)
      (fun a _ => (measurable_integrand D (hker a).1).aestronglyMeasurable) ?_
      (integrable_const _) (ae_of_all _ fun z => ?_)
    · intro a ha
      refine ae_of_all _ fun z => ?_
      rw [Real.norm_eq_abs, Finset.abs_prod, ← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p _ => ?_
      have h1 := hMP (z p.1) (z p.2)
      have h2 := hMQ (z p.1) (z p.2)
      have ha1 := ha.1
      have ha2 : 0 ≤ 1 - a := by linarith [ha.2]
      calc |a * P (z p.1) (z p.2) + (1 - a) * Q (z p.1) (z p.2)|
          ≤ a * |P (z p.1) (z p.2)| + (1 - a) * |Q (z p.1) (z p.2)| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ha1, abs_of_nonneg ha2]
        _ ≤ a * max MP 0 + (1 - a) * max MQ 0 := by
            gcongr
            · exact h1.trans (le_max_left _ _)
            · exact h2.trans (le_max_left _ _)
        _ ≤ max MP 0 + max MQ 0 := by
            nlinarith [le_max_right MP 0, le_max_right MQ 0, ha.2]
    · exact (continuous_finsetProd _ fun p _ => by fun_prop).continuousOn
  have := convex_of_midpoint φ hc hm a ha
  rw [h1, h0] at this
  exact this

lemma mem_sideEdges (H : SimpleGraph V) (s : V → Prop) (a : {v // s v})
    (b : {v // ¬ s v}) : (a, b) ∈ sideEdges H s ↔ H.Adj a.1 b.1 := by
  unfold sideEdges
  simp

lemma volume_equipartIdx (n : ℕ) (hn : 0 < n) (i : Fin n) :
    volume (equipartIdx n hn ⁻¹' {i}) = ENNReal.ofReal (1 / n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.2
  have ha0 : (0 : ℝ) ≤ i / n := by positivity
  have ha1 : (i : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; linarith
  have hb0 : (0 : ℝ) ≤ (i + 1) / n := by positivity
  have hb1 : ((i : ℝ) + 1) / n ≤ 1 := by rw [div_le_one hnr]; linarith
  let a : I := ⟨i / n, ha0, ha1⟩
  let b : I := ⟨(i + 1) / n, hb0, hb1⟩
  have hlen : (b : ℝ) - a = 1 / n := by simp only [a, b]; field_simp; ring
  have hsub : Ioo a b ⊆ equipartIdx n hn ⁻¹' {i} := by
    intro x hx
    have h1 : (i : ℝ) / n < x := hx.1
    have h2 : (x : ℝ) < (i + 1) / n := hx.2
    rw [div_lt_iff₀ hnr] at h1
    rw [lt_div_iff₀ hnr] at h2
    have hfl : ⌊(x : ℝ) * n⌋₊ = i := by
      rw [Nat.floor_eq_iff (mul_nonneg x.2.1 hnr.le)]
      exact ⟨h1.le, h2⟩
    simp only [mem_preimage, mem_singleton_iff, equipartIdx, Fin.ext_iff, hfl]
    omega
  have hsup : equipartIdx n hn ⁻¹' {i} ⊆ Icc a b := by
    intro x hx
    simp only [mem_preimage, mem_singleton_iff, equipartIdx, Fin.ext_iff] at hx
    have hx0 := x.2.1
    have hx1 := x.2.2
    have hxn : 0 ≤ (x : ℝ) * n := mul_nonneg hx0 hnr.le
    show (i : ℝ) / n ≤ x ∧ (x : ℝ) ≤ (i + 1) / n
    rw [div_le_iff₀ hnr, le_div_iff₀ hnr]
    by_cases hfl : ⌊(x : ℝ) * n⌋₊ ≤ n - 1
    · rw [min_eq_left hfl] at hx
      rw [← hx]
      exact ⟨Nat.floor_le hxn, (Nat.lt_floor_add_one _).le⟩
    · rw [min_eq_right (by omega)] at hx
      have hin : ((i : ℕ) : ℝ) = n - 1 := by rw [← hx]; push_cast [Nat.cast_sub hn]; ring
      rw [hin]
      have h1 : ((n - 1 : ℕ) : ℝ) < ⌊(x : ℝ) * n⌋₊ := by exact_mod_cast (not_le.1 hfl)
      push_cast [Nat.cast_sub hn] at h1
      have h2 := Nat.floor_le hxn
      constructor
      · linarith
      · nlinarith
  apply le_antisymm
  · refine (measure_mono hsup).trans ?_
    rw [unitInterval.volume_Icc, hlen]
  · refine le_trans ?_ (measure_mono hsub)
    rw [unitInterval.volume_Ioo, hlen]

/-- The step kernel of a matrix on the equipartition into `n` intervals. -/
noncomputable def stepK (n : ℕ) (hn : 0 < n) (M : Fin n → Fin n → ℝ) : I → I → ℝ :=
  fun x y => M (equipartIdx n hn x) (equipartIdx n hn y)

lemma measurable_stepK (n : ℕ) (hn : 0 < n) (M : Fin n → Fin n → ℝ) :
    Measurable (Function.uncurry (stepK n hn M)) := by
  have hm : Measurable fun p : I × I => (equipartIdx n hn p.1, equipartIdx n hn p.2) :=
    ((measurable_equipartIdx n hn).comp measurable_fst).prodMk
      ((measurable_equipartIdx n hn).comp measurable_snd)
  have hg : Measurable fun q : Fin n × Fin n => M q.1 q.2 := measurable_of_countable _
  exact hg.comp hm

/-- The density of a step kernel is a finite average. -/
lemma t_stepK [DecidableEq V] (D : OrientedGraph V) (n : ℕ) (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) :
    t D (stepK n hn M) = ((n : ℝ)⁻¹) ^ Fintype.card V *
      ∑ φ : V → Fin n, ∏ p ∈ D.arcs, M (φ p.1) (φ p.2) := by
  let F : (V → I) → (V → Fin n) := fun x v => equipartIdx n hn (x v)
  have hF : Measurable F := measurable_pi_iff.2 fun v =>
    (measurable_equipartIdx n hn).comp (measurable_pi_apply v)
  let g : (V → Fin n) → ℝ := fun φ => ∏ p ∈ D.arcs, M (φ p.1) (φ p.2)
  have : t D (stepK n hn M) = ∫ x, g (F x) ∂(Measure.pi fun _ : V => (volume : Measure I)) := rfl
  rw [this, ← integral_map hF.aemeasurable (measurable_of_countable g).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite), Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [measureReal_def, Measure.map_apply hF (measurableSet_singleton _)]
  have : F ⁻¹' {φ} = Set.pi univ fun v => equipartIdx n hn ⁻¹' {φ v} := by
    ext x; simp [F, funext_iff]
  rw [this, Measure.pi_pi]
  simp only [volume_equipartIdx, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity), one_div]

/-- The first-order condition at the symmetric point: for `A` symmetric with values in `[0,1]` and
`B` antisymmetric with `|B| ≤ A`, OS (or OAS) forces the derivative of `ε ↦ t(D, (A + εB)/2)` at
`0` to vanish. -/
lemma sum_deriv_zero [DecidableEq V] (D : OrientedGraph V) (hD : D.IsOSK ∨ D.IsOASK) (n : ℕ)
    (hn : 0 < n) (A B : Fin n → Fin n → ℝ) (hA01 : ∀ x y, A x y ∈ Icc (0 : ℝ) 1)
    (hAs : ∀ x y, A x y = A y x) (hBs : ∀ x y, B x y = - B y x)
    (hAB : ∀ x y, |B x y| ≤ A x y) :
    ∑ φ : V → Fin n, ∑ e ∈ D.arcs,
      (∏ e' ∈ D.arcs.erase e, A (φ e'.1) (φ e'.2)) * B (φ e.1) (φ e.2) = 0 := by
  let M : ℝ → Fin n → Fin n → ℝ := fun ε x y => A x y / 2 + ε * (B x y / 2)
  let Q : ℝ → ℝ := fun ε => ∑ φ : V → Fin n, ∏ p ∈ D.arcs, M ε (φ p.1) (φ p.2)
  have hdig : ∀ ε : ℝ, |ε| ≤ 1 → IsDigraphon (stepK n hn (M ε)) := by
    intro ε hε
    refine ⟨measurable_stepK n hn _, fun x y => ?_⟩
    simp only [stepK, M]
    set i := equipartIdx n hn x
    set j := equipartIdx n hn y
    have h1 : |ε * B i j| ≤ A i j := by
      rw [abs_mul]
      calc |ε| * |B i j| ≤ 1 * |B i j| := by gcongr
        _ ≤ A i j := by rw [one_mul]; exact hAB i j
    have h2 := (hA01 i j).2
    rw [abs_le] at h1
    constructor <;> nlinarith [h1.1, h1.2]
  have hsym : ∀ ε, symmetrize (stepK n hn (M ε)) = stepK n hn (M 0) := by
    intro ε
    funext x y
    simp only [symmetrize, stepK, M]
    rw [hAs (equipartIdx n hn y), hBs (equipartIdx n hn y)]
    ring
  have hc : (0 : ℝ) < ((n : ℝ)⁻¹) ^ Fintype.card V := by positivity
  have hloc : ∀ ε : ℝ, |ε| ≤ 1 → (Q 0 ≤ Q ε ∨ ∀ ε : ℝ, |ε| ≤ 1 → Q ε ≤ Q 0) := by
    intro ε hε
    rcases hD with hOS | hOAS
    · left
      have := hOS _ (hdig ε hε)
      rw [hsym, t_stepK, t_stepK] at this
      exact le_of_mul_le_mul_left this hc
    · right
      intro ε' hε'
      have := hOAS _ (hdig ε' hε')
      rw [hsym, t_stepK, t_stepK] at this
      exact le_of_mul_le_mul_left this hc
  have hderiv : HasDerivAt Q (∑ φ : V → Fin n, ∑ e ∈ D.arcs,
      (∏ e' ∈ D.arcs.erase e, M 0 (φ e'.1) (φ e'.2)) • (B (φ e.1) (φ e.2) / 2)) 0 := by
    refine HasDerivAt.fun_sum fun φ _ => ?_
    refine HasDerivAt.fun_finsetProd fun p _ => ?_
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (B (φ p.1) (φ p.2) / 2)).const_add
      (A (φ p.1) (φ p.2) / 2)
    simpa [M] using this
  have hzero : (∑ φ : V → Fin n, ∑ e ∈ D.arcs,
      (∏ e' ∈ D.arcs.erase e, M 0 (φ e'.1) (φ e'.2)) • (B (φ e.1) (φ e.2) / 2)) = 0 := by
    have hnhds : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    by_cases hmin : ∀ ε : ℝ, |ε| ≤ 1 → Q 0 ≤ Q ε
    · refine IsLocalMin.hasDerivAt_eq_zero ?_ hderiv
      filter_upwards [hnhds] with ε hε
      exact hmin ε (abs_le.2 ⟨hε.1.le, hε.2.le⟩)
    · push_neg at hmin
      obtain ⟨ε0, hε0, hlt⟩ := hmin
      rcases hloc ε0 hε0 with h | hmax
      · exact absurd h (not_le.2 hlt)
      · refine IsLocalMax.hasDerivAt_eq_zero ?_ hderiv
        filter_upwards [hnhds] with ε hε
        exact hmax ε (abs_le.2 ⟨hε.1.le, hε.2.le⟩)
  have hterm : ∀ (φ : V → Fin n) (e : V × V), e ∈ D.arcs →
      (∏ e' ∈ D.arcs.erase e, M 0 (φ e'.1) (φ e'.2)) • (B (φ e.1) (φ e.2) / 2) =
        ((2⁻¹ : ℝ) ^ D.arcs.card) *
          ((∏ e' ∈ D.arcs.erase e, A (φ e'.1) (φ e'.2)) * B (φ e.1) (φ e.2)) := by
    intro φ e he
    simp only [M, zero_mul, add_zero, smul_eq_mul]
    simp_rw [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem he]
    have hpos : 0 < D.arcs.card := Finset.card_pos.2 ⟨e, he⟩
    obtain ⟨m, hm⟩ : ∃ m, D.arcs.card = m + 1 := ⟨D.arcs.card - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    ring
  have : ((2⁻¹ : ℝ) ^ D.arcs.card) * (∑ φ : V → Fin n, ∑ e ∈ D.arcs,
      (∏ e' ∈ D.arcs.erase e, A (φ e'.1) (φ e'.2)) * B (φ e.1) (φ e.2)) = 0 := by
    rw [← hzero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he => (hterm φ e he).symm
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (by positivity)
  · exact h

/-- Adjacency of the glued graph: `H` on `V`, a clique gadget `Fin k1` joined to `r1`, a clique
gadget `Fin k2` joined to `r2`. -/
def glueAdj (H : SimpleGraph V) (k1 k2 : ℕ) (r1 r2 : V) :
    V ⊕ (Fin k1 ⊕ Fin k2) → V ⊕ (Fin k1 ⊕ Fin k2) → Prop
  | .inl x, .inl y => H.Adj x y
  | .inl x, .inr (.inl _) => x = r1
  | .inr (.inl _), .inl x => x = r1
  | .inl x, .inr (.inr _) => x = r2
  | .inr (.inr _), .inl x => x = r2
  | .inr (.inl i), .inr (.inl j) => i ≠ j
  | .inr (.inr i), .inr (.inr j) => i ≠ j
  | .inr (.inl _), .inr (.inr _) => False
  | .inr (.inr _), .inr (.inl _) => False

/-- The glued graph `\bar D` with clique gadgets of sizes `k1`, `k2` at `r1`, `r2`. -/
def glue (H : SimpleGraph V) (k1 k2 : ℕ) (r1 r2 : V) : SimpleGraph (V ⊕ (Fin k1 ⊕ Fin k2)) where
  Adj := glueAdj H k1 k2 r1 r2
  symm := ⟨by
    rintro (x | x | x) (y | y | y) h <;> simp only [glueAdj] at h ⊢ <;>
      first | exact h.symm | exact h | exact Ne.symm h⟩
  loopless := ⟨by
    rintro (x | x | x) h <;> simp only [glueAdj] at h
    · exact H.irrefl h
    · exact h rfl
    · exact h rfl⟩

/-- A gadget map: all gadget vertices adjacent to the root image and pairwise adjacent. -/
def gadgetOK {W' : Type*} (G : SimpleGraph W') {k : ℕ} (z : W') (ψ : Fin k → W') : Prop :=
  (∀ i, G.Adj z (ψ i)) ∧ ∀ i j, i ≠ j → G.Adj (ψ i) (ψ j)

/-- The rooted count of clique gadgets. -/
noncomputable def rho {W' : Type*} [Fintype W'] (G : SimpleGraph W') (k : ℕ) (z : W') : ℕ := by
  classical exact (Finset.univ.filter fun ψ : Fin k → W' => gadgetOK G z ψ).card

lemma rho_le {W' : Type*} [Fintype W'] (G : SimpleGraph W') (k : ℕ) (z : W') :
    rho G k z ≤ Fintype.card W' ^ k := by
  classical
  unfold rho
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- `f` is a homomorphism `H → G`. -/
def IsHomOf {W' : Type*} (H : SimpleGraph V) (G : SimpleGraph W') (f : V → W') : Prop :=
  ∀ x y, H.Adj x y → G.Adj (f x) (f y)

omit [Fintype V] in
lemma isHom_glue_iff {W' : Type*} (H : SimpleGraph V) (G : SimpleGraph W') (k1 k2 : ℕ)
    (r1 r2 : V) (f : V ⊕ (Fin k1 ⊕ Fin k2) → W') :
    (∀ a b, (glue H k1 k2 r1 r2).Adj a b → G.Adj (f a) (f b)) ↔
      IsHomOf H G (fun x => f (.inl x)) ∧ gadgetOK G (f (.inl r1)) (fun i => f (.inr (.inl i))) ∧
        gadgetOK G (f (.inl r2)) (fun i => f (.inr (.inr i))) := by
  constructor
  · intro h
    refine ⟨fun x y hxy => h (.inl x) (.inl y) hxy, ⟨fun i => h (.inl r1) (.inr (.inl i)) rfl,
      fun i j hij => h (.inr (.inl i)) (.inr (.inl j)) hij⟩,
      ⟨fun i => h (.inl r2) (.inr (.inr i)) rfl,
      fun i j hij => h (.inr (.inr i)) (.inr (.inr j)) hij⟩⟩
  · rintro ⟨hφ, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ a b hab
    rcases a with x | x | x <;> rcases b with y | y | y <;>
      simp only [glue, glueAdj] at hab
    · exact hφ x y hab
    · subst hab; exact h1 y
    · subst hab; exact h2 y
    · subst hab; exact (h1 x).symm
    · exact h1' x y hab
    · subst hab; exact (h2 x).symm
    · exact h2' x y hab

open Classical in
/-- Hom counts of the glued graph as a weighted sum over homomorphisms of `H`. -/
lemma homCount_glue {W' : Type*} [Fintype W'] (H : SimpleGraph V) (G : SimpleGraph W')
    (k1 k2 : ℕ) (r1 r2 : V) :
    (simpleHomCount (glue H k1 k2 r1 r2) G : ℝ) = ∑ φ : V → W',
      (if IsHomOf H G φ then (1 : ℝ) else 0) * (rho G k1 (φ r1) : ℝ) * (rho G k2 (φ r2) : ℝ) := by
  unfold rho
  let e : (V ⊕ (Fin k1 ⊕ Fin k2) → W') ≃ (V → W') × ((Fin k1 → W') × (Fin k2 → W')) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ _))
  let Q : (V → W') × ((Fin k1 → W') × (Fin k2 → W')) → Prop := fun t =>
    IsHomOf H G t.1 ∧ gadgetOK G (t.1 r1) t.2.1 ∧ gadgetOK G (t.1 r2) t.2.2
  have hcard : (Finset.univ.filter fun f : V ⊕ (Fin k1 ⊕ Fin k2) → W' =>
      ∀ a b, (glue H k1 k2 r1 r2).Adj a b → G.Adj (f a) (f b)).card =
      (Finset.univ.filter Q).card := by
    refine Finset.card_equiv e fun f => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [isHom_glue_iff]
    rfl
  have hc2 : simpleHomCount (glue H k1 k2 r1 r2) G = (Finset.univ.filter Q).card := by
    unfold simpleHomCount
    convert hcard
  rw [hc2, Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Fintype.sum_prod_type]
  by_cases h0 : IsHomOf H G φ
  · simp only [Q, h0, true_and, if_true, one_mul, Finset.card_filter, Nat.cast_sum,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ψ1 _ => Finset.sum_congr rfl fun ψ2 _ => ?_
    by_cases h1 : gadgetOK G (φ r1) ψ1 <;> by_cases h2 : gadgetOK G (φ r2) ψ2 <;> simp [h1, h2]
  · simp [Q, h0]

open Classical in
lemma prod_adj_eq_ite {W' : Type*} (D : OrientedGraph V) (G : SimpleGraph W') {n : ℕ}
    (eq : Fin n ≃ W') [DecidableRel G.Adj] (φ : V → Fin n) :
    ∏ p ∈ D.arcs, (if G.Adj (eq (φ p.1)) (eq (φ p.2)) then (1 : ℝ) else 0) =
      (if IsHomOf D.underlying G (fun x => eq (φ x)) then 1 else 0) := by
  classical
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h x y hxy
    rcases ((underlying_adj D x y).1 hxy).2 with h' | h'
    · exact h (x, y) ((mem_arcs D _).2 h')
    · exact (h (y, x) ((mem_arcs D _).2 h')).symm
  · intro h p hp
    exact h _ _ (underlying_adj_of_adj D ((mem_arcs D _).1 hp))

/-- For `D` OS or OAS in digraphon form (`hD`), the identity `∑_e t(D_e, G) = ∑_e t(D_{e^T}, G)`
(as hom counts) for every finite nonempty host `G`. -/
lemma glue_identity (D : OrientedGraph V) (hD : D.IsOSK ∨ D.IsOASK) {W' : Type*} [Fintype W']
    [Nonempty W'] (G : SimpleGraph W') (k1 k2 : ℕ) :
    ∑ e ∈ D.arcs, (simpleHomCount (glue D.underlying k1 k2 e.1 e.2) G : ℝ) =
      ∑ e ∈ D.arcs, (simpleHomCount (glue D.underlying k1 k2 e.2 e.1) G : ℝ) := by
  classical
  set n := Fintype.card W' with hn_def
  have hn : 0 < n := Fintype.card_pos
  let eq : Fin n ≃ W' := (Fintype.equivFin W').symm
  let A : Fin n → Fin n → ℝ := fun i j => if G.Adj (eq i) (eq j) then 1 else 0
  let r1 : Fin n → ℝ := fun i => (rho G k1 (eq i) : ℝ)
  let r2 : Fin n → ℝ := fun i => (rho G k2 (eq i) : ℝ)
  set N : ℝ := (n : ℝ) ^ k1 * (n : ℝ) ^ k2 with hN
  have hNpos : 0 < N := by positivity
  let B : Fin n → Fin n → ℝ := fun i j => A i j * ((r1 i * r2 j - r1 j * r2 i) / N)
  have hr1 : ∀ i, 0 ≤ r1 i ∧ r1 i ≤ (n : ℝ) ^ k1 := fun i =>
    ⟨Nat.cast_nonneg _, by
      have := rho_le G k1 (eq i); rw [← hn_def] at this
      show (rho G k1 (eq i) : ℝ) ≤ (n : ℝ) ^ k1; exact_mod_cast this⟩
  have hr2 : ∀ i, 0 ≤ r2 i ∧ r2 i ≤ (n : ℝ) ^ k2 := fun i =>
    ⟨Nat.cast_nonneg _, by
      have := rho_le G k2 (eq i); rw [← hn_def] at this
      show (rho G k2 (eq i) : ℝ) ≤ (n : ℝ) ^ k2; exact_mod_cast this⟩
  have hA01 : ∀ x y, A x y ∈ Icc (0 : ℝ) 1 := by
    intro x y; simp only [A]; split_ifs <;> simp
  have hAs : ∀ x y, A x y = A y x := by
    intro x y; simp only [A]
    by_cases h : G.Adj (eq x) (eq y)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hBs : ∀ x y, B x y = - B y x := by
    intro x y; simp only [B]; rw [hAs y x]; ring
  have hAB : ∀ x y, |B x y| ≤ A x y := by
    intro x y
    simp only [B]
    rw [abs_mul, abs_of_nonneg (hA01 x y).1]
    have hA1 := (hA01 x y).2
    have hA0 := (hA01 x y).1
    have : |(r1 x * r2 y - r1 y * r2 x) / N| ≤ 1 := by
      rw [abs_div, abs_of_pos hNpos, div_le_one hNpos, abs_le]
      have h1 : 0 ≤ r1 x * r2 y := mul_nonneg (hr1 x).1 (hr2 y).1
      have h2 : 0 ≤ r1 y * r2 x := mul_nonneg (hr1 y).1 (hr2 x).1
      have h3 : r1 x * r2 y ≤ N := mul_le_mul (hr1 x).2 (hr2 y).2 (hr2 y).1 (by positivity)
      have h4 : r1 y * r2 x ≤ N := mul_le_mul (hr1 y).2 (hr2 x).2 (hr2 x).1 (by positivity)
      constructor <;> linarith
    calc A x y * |(r1 x * r2 y - r1 y * r2 x) / N| ≤ A x y * 1 := by gcongr
      _ = A x y := mul_one _
  have h := sum_deriv_zero D hD n hn A B hA01 hAs hBs hAB
  have key : ∀ a b : V, (simpleHomCount (glue D.underlying k1 k2 a b) G : ℝ) =
      ∑ φ : V → Fin n, (if IsHomOf D.underlying G (fun x => eq (φ x)) then (1 : ℝ) else 0) *
        r1 (φ a) * r2 (φ b) := by
    intro a b
    rw [homCount_glue]
    exact (Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl V) eq) _ _ (fun φ => rfl)).symm
  have h' : ∑ φ : V → Fin n, ∑ e ∈ D.arcs,
      (if IsHomOf D.underlying G (fun x => eq (φ x)) then (1 : ℝ) else 0) *
        ((r1 (φ e.1) * r2 (φ e.2) - r1 (φ e.2) * r2 (φ e.1)) / N) = 0 := by
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun φ _ => Finset.sum_congr rfl fun e he => ?_
    rw [← prod_adj_eq_ite D G eq φ, ← Finset.mul_prod_erase _ _ he]
    simp only [B, A]
    ring
  simp_rw [key]
  rw [Finset.sum_comm] at h'
  have h'' : ∑ e ∈ D.arcs, ∑ φ : V → Fin n,
      ((if IsHomOf D.underlying G (fun x => eq (φ x)) then (1 : ℝ) else 0) * r1 (φ e.1) *
        r2 (φ e.2) - (if IsHomOf D.underlying G (fun x => eq (φ x)) then (1 : ℝ) else 0) *
        r1 (φ e.2) * r2 (φ e.1)) = 0 := by
    refine Eq.trans ?_ ((congrArg (N * ·) h').trans (mul_zero N))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    field_simp
  simp_rw [Finset.sum_sub_distrib] at h''
  linarith

lemma simpleHomCount_iso {Vg W' : Type*} [Fintype Vg] [Fintype W'] {F F' : SimpleGraph Vg}
    (g : F ≃g F') (G : SimpleGraph W') : simpleHomCount F G = simpleHomCount F' G := by
  classical
  have h : (Finset.univ.filter fun f : Vg → W' => ∀ u v, F.Adj u v → G.Adj (f u) (f v)).card =
      (Finset.univ.filter fun f : Vg → W' => ∀ u v, F'.Adj u v → G.Adj (f u) (f v)).card := by
    refine Finset.card_equiv (Equiv.arrowCongr g.toEquiv (Equiv.refl W')) fun f => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.arrowCongr_apply,
      Equiv.refl_apply, Function.comp_apply]
    constructor
    · intro hf u v huv
      exact hf _ _ (g.symm.map_adj_iff.2 huv)
    · intro hf u v huv
      have := hf (g u) (g v) (g.map_adj_iff.2 huv)
      rwa [show g.toEquiv.symm (g u) = u from g.toEquiv.symm_apply_apply u,
        show g.toEquiv.symm (g v) = v from g.toEquiv.symm_apply_apply v] at this
  unfold simpleHomCount
  convert h

lemma simpleHomDensity_iso {Vg W' : Type*} [Fintype Vg] [Fintype W'] {F F' : SimpleGraph Vg}
    (g : F ≃g F') (G : SimpleGraph W') : simpleHomDensity F G = simpleHomDensity F' G := by
  unfold simpleHomDensity
  rw [simpleHomCount_iso g]

/-- Lovász's linear independence (A1) turned into a bijection between two families of graphs
with equal summed densities in every finite host. -/
lemma lovasz_bijection (hA1 : LovaszProp544cHyp.{u}) {Vg : Type u} [Fintype Vg] [Nonempty Vg]
    {X : Type*} [Fintype X] (Γ1 Γ2 : X → SimpleGraph Vg)
    (hiso1 : ∀ x v, ∃ w, (Γ1 x).Adj v w) (hiso2 : ∀ x v, ∃ w, (Γ2 x).Adj v w)
    (hsum : ∀ (W' : Type u) [Fintype W'] (G : SimpleGraph W'),
      ∑ x, simpleHomDensity (Γ1 x) G = ∑ x, simpleHomDensity (Γ2 x) G) :
    ∃ f : X ≃ X, ∀ x, Nonempty (Γ1 x ≃g Γ2 (f x)) := by
  classical
  let Γ : X ⊕ X → SimpleGraph Vg := Sum.elim Γ1 Γ2
  let st : Setoid (X ⊕ X) :=
    { r := fun a b => Nonempty (Γ a ≃g Γ b)
      iseqv := ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨g⟩ => ⟨g.symm⟩,
        fun ⟨g⟩ ⟨h⟩ => ⟨g.trans h⟩⟩ }
  let Y := Quotient st
  let k := Fintype.card Y
  let eY : Fin k ≃ Y := (Fintype.equivFin Y).symm
  let F : Fin k → SimpleGraph Vg := fun i => Γ (eY i).out
  let cls : X ⊕ X → Fin k := fun a => eY.symm (Quotient.mk st a)
  have hcls : ∀ a, Nonempty (Γ a ≃g F (cls a)) := by
    intro a
    have : Quotient.mk st (eY (cls a)).out = Quotient.mk st a := by
      simp only [cls, Equiv.apply_symm_apply, Quotient.out_eq]
    obtain ⟨g⟩ := Quotient.exact this
    exact ⟨g.symm⟩
  have hni : ∀ i j, i ≠ j → IsEmpty (F i ≃g F j) := by
    intro i j hij
    refine ⟨fun g => hij (eY.injective ?_)⟩
    rw [← Quotient.out_eq (eY i), ← Quotient.out_eq (eY j)]
    exact Quotient.sound ⟨g⟩
  have hiF : ∀ i v, ∃ w, (F i).Adj v w := by
    intro i v
    rcases h : (eY i).out with x | x
    · simp only [F, h, Γ, Sum.elim_inl]; exact hiso1 x v
    · simp only [F, h, Γ, Sum.elim_inr]; exact hiso2 x v
  obtain ⟨W, hW, G, hdet⟩ := hA1 k (fun _ => Vg) F hni hiF
  set M := Matrix.of fun i j => @simpleHomDensity Vg (W j) _ (hW j) (F i) (G j) with hM
  have hden : ∀ a j, @simpleHomDensity Vg (W j) _ (hW j) (Γ a) (G j) = M (cls a) j := by
    intro a j
    obtain ⟨g⟩ := hcls a
    exact @simpleHomDensity_iso Vg (W j) _ (hW j) _ _ g (G j)
  let m1 : Fin k → ℝ := fun i => ((Finset.univ.filter fun x => cls (.inl x) = i).card : ℝ)
  let m2 : Fin k → ℝ := fun i => ((Finset.univ.filter fun x => cls (.inr x) = i).card : ℝ)
  have hgroup : ∀ (c : X → Fin k) (j : Fin k), ∑ x, M (c x) j =
      ∑ i, ((Finset.univ.filter fun x => c x = i).card : ℝ) * M i j := by
    intro c j
    rw [← Finset.sum_fiberwise Finset.univ c (fun x => M (c x) j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
      Finset.sum_const, nsmul_eq_mul]
  have hvec : Matrix.vecMul (m1 - m2) M = 0 := by
    funext j
    have h1 : ∑ x, M (cls (.inl x)) j = ∑ x, M (cls (.inr x)) j := by
      simp only [← hden]
      exact @hsum (W j) (hW j) (G j)
    have e1 := hgroup (fun x => cls (.inl x)) j
    have e2 := hgroup (fun x => cls (.inr x)) j
    simp only [Matrix.vecMul, dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    have : ∑ i, m1 i * M i j = ∑ i, m2 i * M i j := by
      simp only [m1, m2]
      rw [← e1, ← e2]
      convert h1 using 1
    linarith
  have hm := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  have hcard : ∀ y : Y, Fintype.card {x // Quotient.mk st (.inl x) = y} =
      Fintype.card {x // Quotient.mk st (.inr x) = y} := by
    intro y
    have := congrFun hm (eY.symm y)
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero, m1, m2, Nat.cast_inj] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert this using 3 <;> simp [cls, Equiv.symm_apply_eq]
  let f := Equiv.ofFiberEquiv fun y => Fintype.equivOfCardEq (hcard y)
  refine ⟨f, fun x => ?_⟩
  have := Equiv.ofFiberEquiv_map (fun y => Fintype.equivOfCardEq (hcard y)) x
  obtain ⟨g⟩ := Quotient.exact this
  exact ⟨g.symm⟩

open Classical in
/-- Degree in a finite simple graph. -/
noncomputable def degOf {α : Type*} [Fintype α] (X : SimpleGraph α) (a : α) : ℕ :=
  (Finset.univ.filter (X.Adj a)).card

lemma degOf_iso {α β : Type*} [Fintype α] [Fintype β] {X : SimpleGraph α} {Y : SimpleGraph β}
    (g : X ≃g Y) (a : α) : degOf Y (g a) = degOf X a := by
  classical
  unfold degOf
  symm
  convert Finset.card_equiv g.toEquiv (t := Finset.univ.filter (Y.Adj (g a))) fun b => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact g.map_adj_iff.symm

lemma degOf_le (H : SimpleGraph V) (x : V) : degOf H x ≤ Fintype.card V - 1 := by
  classical
  unfold degOf
  have : Finset.univ.filter (H.Adj x) ⊆ Finset.univ.erase x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact Finset.mem_erase.2 ⟨hy.ne.symm, Finset.mem_univ _⟩
  refine (Finset.card_le_card this).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

lemma degOf_pos (H : SimpleGraph V) (x : V) (h : ∃ y, H.Adj x y) : 1 ≤ degOf H x := by
  classical
  obtain ⟨y, hy⟩ := h
  unfold degOf
  exact Finset.card_pos.2 ⟨y, by simpa using hy⟩

open Classical in
lemma degOf_eq_sum {α : Type*} [Fintype α] (X : SimpleGraph α) (a : α) :
    degOf X a = ∑ b, (if X.Adj a b then 1 else 0 : ℕ) := by
  unfold degOf
  rw [Finset.card_filter]

lemma sum_ite_ne_fin (k : ℕ) (i : Fin k) [∀ x : Fin k, Decidable (i = x)] :
    ∑ x : Fin k, (if i = x then 0 else 1 : ℕ) = k - 1 := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
  have : (Finset.univ.filter fun x => ¬ i = x) = Finset.univ.erase i := by
    ext x; simp [eq_comm]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

open Classical in
lemma degOf_glue_inl (H : SimpleGraph V) (k1 k2 : ℕ) {r1 r2 : V} (h12 : r1 ≠ r2) (x : V) :
    degOf (glue H k1 k2 r1 r2) (.inl x) =
      degOf H x + (if x = r1 then k1 else 0) + (if x = r2 then k2 else 0) := by
  rw [degOf_eq_sum, degOf_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  congr 1
  by_cases h1 : x = r1
  · subst h1
    simp [glue, glueAdj, h12]
  · by_cases h2 : x = r2
    · subst h2
      simp [glue, glueAdj, h1]
    · simp [glue, glueAdj, h1, h2]

lemma degOf_glue_inr_inl (H : SimpleGraph V) (k1 k2 : ℕ) (r1 r2 : V) (i : Fin k1) :
    degOf (glue H k1 k2 r1 r2) (.inr (.inl i)) = k1 := by
  classical
  unfold degOf
  have : Finset.univ.filter ((glue H k1 k2 r1 r2).Adj (.inr (.inl i))) =
      insert (.inl r1) ((Finset.univ.erase i).image fun j => (.inr (.inl j) :
        V ⊕ (Fin k1 ⊕ Fin k2))) := by
    ext b
    rw [Finset.mem_filter]
    rcases b with y | j | j <;> simp [glue, glueAdj, eq_comm]
  rw [this, Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _
    (by intro a b h; simpa using h), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  have := i.2
  omega

lemma degOf_glue_inr_inr (H : SimpleGraph V) (k1 k2 : ℕ) (r1 r2 : V) (i : Fin k2) :
    degOf (glue H k1 k2 r1 r2) (.inr (.inr i)) = k2 := by
  classical
  unfold degOf
  have : Finset.univ.filter ((glue H k1 k2 r1 r2).Adj (.inr (.inr i))) =
      insert (.inl r2) ((Finset.univ.erase i).image fun j => (.inr (.inr j) :
        V ⊕ (Fin k1 ⊕ Fin k2))) := by
    ext b
    rw [Finset.mem_filter]
    rcases b with y | j | j <;> simp [glue, glueAdj, eq_comm]
  rw [this, Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _
    (by intro a b h; simpa using h), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  have := i.2
  omega

/-- An isomorphism of glued graphs restricts to an automorphism of the base graph, exchanging the
roots as prescribed by the gadget sizes. -/
lemma auto_of_glue_iso (H : SimpleGraph V) (hH : ∀ x, ∃ y, H.Adj x y)
    (hv : 2 ≤ Fintype.card V) {u w u' w' : V} (huw : u ≠ w) (hu'w' : u' ≠ w')
    (g : glue H (Fintype.card V) (2 * Fintype.card V) u w ≃g
      glue H (Fintype.card V) (2 * Fintype.card V) w' u') :
    ∃ τ : H ≃g H, τ u = w' ∧ τ w = u' := by
  classical
  set v := Fintype.card V with hvdef
  have hdle := degOf_le H
  have hdpos : ∀ x, 1 ≤ degOf H x := fun x => degOf_pos H x (hH x)
  -- degrees of the source and the target
  have hsrc : ∀ x, degOf (glue H v (2 * v) u w) (.inl x) =
      degOf H x + (if x = u then v else 0) + (if x = w then 2 * v else 0) :=
    degOf_glue_inl H _ _ huw
  have htgt : ∀ x, degOf (glue H v (2 * v) w' u') (.inl x) =
      degOf H x + (if x = w' then v else 0) + (if x = u' then 2 * v else 0) :=
    degOf_glue_inl H _ _ (Ne.symm hu'w')
  have hdeg : ∀ a, degOf (glue H v (2 * v) w' u') (g a) = degOf (glue H v (2 * v) u w) a :=
    degOf_iso g
  -- every vertex of `V` is sent into `V`
  have hinl : ∀ x, ∃ y, g (.inl x) = .inl y := by
    intro x
    have hd := hdeg (.inl x)
    rw [hsrc] at hd
    have h1 := hdle x
    have h2 := hdpos x
    rcases hgx : g (.inl x) with y | i | i
    · exact ⟨y, rfl⟩
    · rw [hgx, degOf_glue_inr_inl] at hd
      exfalso
      split_ifs at hd <;> omega
    · rw [hgx, degOf_glue_inr_inr] at hd
      exfalso
      split_ifs at hd <;> omega
  choose τf hτf using hinl
  have hroot_u : ∀ y, g (.inl u) = .inl y → y = w' := by
    intro y hy
    have hd := hdeg (.inl u)
    rw [hy, hsrc, htgt, if_pos rfl, if_neg huw] at hd
    have h1 := hdle u
    have h3 := hdle y
    have h4 := hdpos y
    by_contra hne
    rw [if_neg hne] at hd
    by_cases hy2 : y = u'
    · rw [if_pos hy2] at hd; omega
    · rw [if_neg hy2] at hd; omega
  have hroot_w : ∀ y, g (.inl w) = .inl y → y = u' := by
    intro y hy
    have hd := hdeg (.inl w)
    rw [hy, hsrc, htgt, if_neg (Ne.symm huw), if_pos rfl] at hd
    have h1 := hdle w
    have h2 := hdpos w
    have h3 := hdle y
    by_contra hne
    rw [if_neg hne] at hd
    by_cases hy2 : y = w'
    · rw [if_pos hy2] at hd; omega
    · rw [if_neg hy2] at hd; omega
  have hinj : Function.Injective τf := by
    intro x x' h
    have := (hτf x).trans ((congrArg Sum.inl h).trans (hτf x').symm)
    exact Sum.inl_injective (g.injective this)
  have hbij : Function.Bijective τf := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  refine ⟨⟨Equiv.ofBijective τf hbij, fun {a b} => ?_⟩, ?_, ?_⟩
  · simp only [Equiv.ofBijective_apply]
    have := g.map_adj_iff (v := .inl a) (w := .inl b)
    rw [hτf a, hτf b] at this
    exact this
  · simp only [RelIso.coe_fn_mk, Equiv.ofBijective_apply]
    exact hroot_u _ (hτf u)
  · simp only [RelIso.coe_fn_mk, Equiv.ofBijective_apply]
    exact hroot_w _ (hτf w)

end Section4Aux

namespace OrientedGraph

variable {V : Type u} [Fintype V]

/-- **Theorem 4.1.** Let `D` be a directed graph such that (a) `D` is homomorphic to a directed
edge; (b) `D ≅ D^T`; (c) `\bar D` is weakly norming with respect to a bipartition under which all
arcs of `D` go from the first part to the second. Then `D` is oriented Sidorenko.
Hypothesis (a) is the paper's; it follows from (c), and the proof does not use it. -/
theorem thm_4_1 (D : OrientedGraph V) (ha : D.HomToDirEdge) (hb : D.IsSelfConverse)
    (hc : ∃ s : V → Prop, (∀ u v, D.Adj u v → s u ∧ ¬ s v) ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges D.underlying s)) :
    D.IsOSK := by
  open Section4Aux in
  obtain ⟨s, hs, hW⟩ := hc
  let _ := Classical.decPred s
  intro U hU
  have key : ∀ K, t D K = tb (sideEdges D.underlying s) K := fun K => t_eq_tb D s hs K
  set E := sideEdges D.underlying s with hEdef
  have hUk := isKernel_of_isDigraphon hU
  have hT : rNorm E (kTranspose U) = rNorm E U := by
    unfold rNorm
    congr 1
    rw [← key, ← key]
    exact t_transpose_of_selfConverse D hb (fun x y => |U x y|)
  have h1 := hW.2.1 (fun x y => (1 / 2 : ℝ) * U x y) (fun x y => (1 / 2 : ℝ) * kTranspose U x y)
    (isKernel_const_mul hUk _) (isKernel_const_mul (isKernel_kTranspose hUk) _)
  rw [hW.1 U hUk, hW.1 _ (isKernel_kTranspose hUk), hT] at h1
  have hsym : symmetrize U = fun x y => (1 / 2 : ℝ) * U x y + (1 / 2 : ℝ) * kTranspose U x y := by
    funext x y; simp only [symmetrize, kTranspose]; ring
  rw [key, key, hsym]
  apply tb_le_of_rNorm_le
  · intro x y
    simp only [kTranspose]
    have := (hU.2 x y).1; have := (hU.2 y x).1
    positivity
  · exact fun x y => (hU.2 x y).1
  · refine h1.trans (le_of_eq ?_)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring

/-- **Lemma 4.2.** If `D` is an OS directed graph, then `D` is homomorphic to a directed edge. -/
theorem lemma_4_2 (D : OrientedGraph V) (hD : D.IsOSK) : D.HomToDirEdge := by
  open Section4Aux in
  by_cases hcol : D.underlying.Colorable 2
  · exact homToDirEdge_of_colorable D hD hcol
  · obtain ⟨r, hr⟩ := exists_rank_of_isOSK D hD
    exact (false_of_not_colorable D hD r hr hcol).elim

/-- **Lemma 4.3.** Let `D` be an OS or OAS directed graph with no isolated vertices. There is a
bijection `f : E(D) → E(D)` such that for all arcs `(u, w)` and `(u', w') = f((u, w))` there is an
automorphism `g` of `\bar D` with `g(u) = w'` and `g(w) = u'`. -/
theorem lemma_4_3 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hD : D.IsOSK ∨ D.IsOASK)
    (hiso : ∀ v, ∃ u, D.underlying.Adj v u) :
    ∃ f : {p // p ∈ D.arcs} ≃ {p // p ∈ D.arcs}, ∀ e : {p // p ∈ D.arcs},
      ∃ g : D.underlying ≃g D.underlying, g e.1.1 = (f e).1.2 ∧ g e.1.2 = (f e).1.1 := by
  open Section4Aux in
  classical
  by_cases hne : D.arcs.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨Equiv.refl _, fun e => absurd e.2 ?_⟩
    have := e.2
    simp [hne] at this
  obtain ⟨⟨a0, b0⟩, h0⟩ := hne
  have hab : a0 ≠ b0 := ((underlying_adj_of_adj D ((mem_arcs D _).1 h0))).ne
  have hv : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.2 ⟨a0, b0, hab⟩
  set v := Fintype.card V with hvdef
  have : Nonempty (V ⊕ (Fin v ⊕ Fin (2 * v))) := ⟨.inl a0⟩
  let Γ1 : {p // p ∈ D.arcs} → SimpleGraph (V ⊕ (Fin v ⊕ Fin (2 * v))) := fun x =>
    glue D.underlying v (2 * v) x.1.1 x.1.2
  let Γ2 : {p // p ∈ D.arcs} → SimpleGraph (V ⊕ (Fin v ⊕ Fin (2 * v))) := fun x =>
    glue D.underlying v (2 * v) x.1.2 x.1.1
  have hisoG : ∀ (r1 r2 : V) (a : V ⊕ (Fin v ⊕ Fin (2 * v))),
      ∃ b, (glue D.underlying v (2 * v) r1 r2).Adj a b := by
    intro r1 r2 a
    rcases a with y | i | i
    · obtain ⟨z, hz⟩ := hiso y
      exact ⟨.inl z, hz⟩
    · exact ⟨.inl r1, rfl⟩
    · exact ⟨.inl r2, rfl⟩
  have hsum : ∀ (W' : Type u) [Fintype W'] (G : SimpleGraph W'),
      ∑ x, simpleHomDensity (Γ1 x) G = ∑ x, simpleHomDensity (Γ2 x) G := by
    intro W' _ G
    unfold simpleHomDensity
    rw [← Finset.sum_div, ← Finset.sum_div]
    rcases isEmpty_or_nonempty W' with hW | hW
    · have : (Fintype.card W' : ℝ) ^ Fintype.card (V ⊕ (Fin v ⊕ Fin (2 * v))) = 0 := by
        rw [Fintype.card_eq_zero, Nat.cast_zero, zero_pow Fintype.card_ne_zero]
      rw [this, div_zero, div_zero]
    · congr 1
      have := glue_identity D hD G v (2 * v)
      rw [← Finset.sum_coe_sort D.arcs, ← Finset.sum_coe_sort D.arcs] at this
      exact this
  obtain ⟨f, hf⟩ := lovasz_bijection hA1 Γ1 Γ2 (fun x => hisoG _ _) (fun x => hisoG _ _) hsum
  refine ⟨f, fun x => ?_⟩
  obtain ⟨g⟩ := hf x
  have h1 : x.1.1 ≠ x.1.2 := (underlying_adj_of_adj D ((mem_arcs D _).1 x.2)).ne
  have h2 : (f x).1.1 ≠ (f x).1.2 := (underlying_adj_of_adj D ((mem_arcs D _).1 (f x).2)).ne
  exact auto_of_glue_iso D.underlying hiso hv h1 h2 g

/-- **Lemma 4.4.** If `D` is a connected OS directed graph, then `D ≅ D^T`. -/
theorem lemma_4_4 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V) (hconn : D.IsConnected)
    (hD : D.IsOSK) :
    D.IsSelfConverse := by
  open Section4Aux in
  by_cases harc : ∃ u v, D.Adj u v
  swap
  · push_neg at harc
    exact ⟨{ toEquiv := Equiv.refl V
             map_adj_iff := fun u v => by
               simp only [OrientedGraph.transpose, Equiv.refl_apply]
               exact ⟨fun h => absurd h (harc v u), fun h => absurd h (harc u v)⟩ }⟩
  obtain ⟨u0, v0, h0⟩ := harc
  have hiso := exists_adj_of_connected D hconn h0
  obtain ⟨f, hf⟩ := lemma_4_2 D hD
  obtain ⟨F, hF⟩ := lemma_4_3 hA1 D (Or.inl hD) hiso
  have hmem : (u0, v0) ∈ D.arcs := (mem_arcs D _).2 h0
  obtain ⟨g, hgu, -⟩ := hF ⟨(u0, v0), hmem⟩
  have hFarc := (mem_arcs D _).1 (F ⟨(u0, v0), hmem⟩).2
  have hcol : ∀ a b, D.underlying.Adj a b → f a ≠ f b := by
    intro a b h
    rcases ((underlying_adj D a b).1 h).2 with h' | h'
    · rw [(hf _ _ h').1, (hf _ _ h').2]; decide
    · rw [(hf _ _ h').1, (hf _ _ h').2]; decide
  have hgadj : ∀ a b, D.underlying.Adj a b → D.underlying.Adj (g a) (g b) :=
    fun a b h => g.map_adj_iff.2 h
  have hflip : ∀ x, f (g x) ≠ f x := by
    intro x hx
    obtain ⟨p⟩ := hconn.preconnected u0 x
    have := (flip_walk D.underlying f hcol g hgadj p).2 hx
    simp only at hgu
    rw [hgu, (hf _ _ hFarc).2, (hf _ _ h0).1] at this
    exact absurd this (by decide)
  refine ⟨{ toEquiv := g.toEquiv, map_adj_iff := fun a b => ?_ }⟩
  show D.Adj (g b) (g a) ↔ D.Adj a b
  have t0 : ∀ y z : Fin 2, y ≠ z → z = 0 → y = 1 := by decide
  have t1 : ∀ y z : Fin 2, y ≠ z → z = 1 → y = 0 := by decide
  have t01 : (0 : Fin 2) ≠ 1 := by decide
  constructor
  · intro h
    have hb : f b = 1 := t0 _ _ (hflip b).symm (hf _ _ h).1
    have hu := (underlying_adj D b a).1 (g.map_adj_iff.1 (underlying_adj_of_adj D h))
    rcases hu.2 with h' | h'
    · exact absurd ((hf _ _ h').1.symm.trans hb) t01
    · exact h'
  · intro h
    have hga : f (g a) = 1 := t0 _ _ (hflip a) (hf _ _ h).1
    have hu := (underlying_adj D (g a) (g b)).1 (g.map_adj_iff.2 (underlying_adj_of_adj D h))
    rcases hu.2 with h' | h'
    · exact absurd ((hf _ _ h').1.symm.trans hga) t01
    · exact h'

/-- **Lemma 4.5.** If `D` is a connected OS directed graph with at least one arc, then `\bar D` is
weakly norming. -/
theorem lemma_4_5 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V) (hconn : D.IsConnected)
    (he : 1 ≤ D.numArcs)
    (hD : D.IsOSK) : IsWeaklyNormingGraph D.underlying := by
  open Section4Aux in
  obtain ⟨⟨u0, v0⟩, hp⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one he)
  have h0 : D.Adj u0 v0 := (mem_arcs D _).1 hp
  obtain ⟨f, hf⟩ := lemma_4_2 D hD
  have hsc := lemma_4_4 hA1 D hconn hD
  have hs : ∀ u v, D.Adj u v → f u = 0 ∧ ¬ f v = 0 := fun u v h =>
    ⟨(hf u v h).1, by rw [(hf u v h).2]; decide⟩
  refine ⟨fun v => f v = 0, ?_, ?_⟩
  · intro u v h
    rcases ((underlying_adj D u v).1 h).2 with h' | h'
    · simp [(hf _ _ h').1, (hf _ _ h').2]
    · simp [(hf _ _ h').1, (hf _ _ h').2]
  · let _ := Classical.decPred (fun v => f v = 0)
    have key := fun K => t_eq_tb D (fun v => f v = 0) hs K
    have hE : 0 < (sideEdges D.underlying fun v => f v = 0).card :=
      Finset.card_pos.2 ⟨(⟨u0, (hs _ _ h0).1⟩, ⟨v0, (hs _ _ h0).2⟩),
        (mem_sideEdges _ _ _ _).2 (underlying_adj_of_adj D h0)⟩
    rw [lemma_2_3_1 _ hE]
    intro P Q hP hQ hP0 hQ0 a ha
    rw [← key, ← key, ← key]
    exact convex_t_of_isOSK D hconn hsc hD f hf P Q hP hQ hP0 hQ0 a ha

end OrientedGraph

/-- **Lemma 4.6.** Let `H = (X ∪ Y, E)` be weakly norming and contain a cycle. If `S, A` are
kernels with `S ≥ |A|` and `t_bi(H, S + A) = t_bi(H, S - A) = t_bi(H, S)`, then `A = 0` almost
everywhere. -/
theorem lemma_4_6 {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y))
    (hE : IsWeaklyNorming E) (hcyc : ¬ (bipGraph E).IsAcyclic) (S A : I → I → ℝ)
    (hS : IsKernel S) (hA : IsKernel A) (hSA : ∀ x y, |A x y| ≤ S x y)
    (hplus : tb E (fun x y => S x y + A x y) = tb E S)
    (hminus : tb E (fun x y => S x y - A x y) = tb E S) :
    AEEq volume A (fun _ _ => 0) :=
  Section4Aux.lemma_4_6_core E hE hcyc S A hS hA hSA hplus hminus

end NieWeiOrientedSidorenko
