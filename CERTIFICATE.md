# Certificate of correctness — Sidorenko Inequalities and Symmetry-Forcing for Graph Orientations (Nie, Wei)

This repository is a Lean 4 formalization of J. Nie and F. Wei, "Sidorenko inequalities and
symmetry-forcing for graph orientations", an unpublished manuscript. It follows the statements and
the numbering of the manuscript's numbered results in its **version of 11 November 2026**. Paper
references below are to that numbering (Theorem 1.2, Definition 1, …) and its sections. "tex l.N" is
line N of the manuscript's LaTeX source in that version; the manuscript itself is not in this
repository. `File.lean:N` is line N of `NieWeiOrientedSidorenko/File.lean` in this repository.

The authors also answered three sets of questions during the formalization (the pre-run answer key,
the Checkpoint B answer key and the final-delivery answers). Where a statement comes from one of
them rather than from the manuscript, this is said.

## 1. What certifies the proofs

A Lean formalization certifies a theorem through three things together:

1. **The statements.** The Lean statements of the main theorems, and the definitions they use, say
   what the paper says. This is the only part a person has to read. Sections 3 and 4 below put
   each statement and definition next to the paper's wording, and section 1a explains the Lean
   notation they use.
2. **The kernel check.** Lean's kernel accepts every proof in the repository. Nobody needs to read
   the proofs; `lake build` re-checks all of them.
3. **The axiom check.** Nothing is assumed beyond Lean's three standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`): no `sorry`, no extra `axiom`.

**Published results are hypotheses, not axioms.** The authors authorised 11 published results to
be assumed rather than re-proved (section 4b lists them with their sources and Lean wording). Each
is a Lean *definition* of a proposition, such as `LovaszProp544cHyp`, in
`NieWeiOrientedSidorenko/Literature.lean`. A theorem that needs one takes it as an explicit
argument, so its statement reads "if this published result holds, then …". Nothing is declared as
an axiom, and the axiom check above would show it if anything were. So each theorem is proved
outright *conditionally on* the published results its statement names, and section 6 lists which
those are. A statement is only as good as the wording of its hypotheses; the wording of each was
compared with its source (section 5).

The proofs themselves (about 21,000 lines in `NieWeiOrientedSidorenko/`) need not be read. Every
definition and numbered result of the manuscript has a Lean counterpart there (listed in
`NieWeiOrientedSidorenko/Main.lean` and in section 6 below): every theorem, lemma, corollary,
proposition and claim is stated and proved, every numbered definition is defined, and Conjecture 1
is stated only (it is neither assumed nor proved). The authors' requested additions are also stated
and proved: the three Question 1(c) bridges, the B1 corollary, both readings of B4(i), B4(ii), the
every-bipartition corollary of Theorem 1.4, and the finite-host forms of Lemma 6.1 and Theorem 4.1.

## 1a. Reading the Lean statements (no Lean knowledge assumed)

| Lean | Meaning |
|---|---|
| `theorem name (x : A) (h : P) : Q` | For every `x` of type `A`, if `P` holds then `Q` holds. Each `(h : P)` before the final colon is a hypothesis; the text after the final colon is the conclusion. |
| `{V : Type u}`, `[Fintype V]` | for every type `V` (a set of vertices), which is finite; the braces and brackets only mean Lean infers them itself. `u` is a universe level, a technicality (see `.{u}` below) |
| `def name … : Prop := body`, `structure name … where` | Defines `name` to be `body`; a `structure` lists the fields of the object being defined. `Prop` means "a statement". |
| `OrientedGraph V` | a directed graph on the vertex set `V`: an orientation of a finite simple graph (no loops, no antiparallel arcs) |
| `D.Adj u v` | `(u, v)` is an arc of `D`, directed from `u` to `v` |
| `D.underlying`, `D.transpose`, `D.numArcs` | the underlying graph D̄, the transpose Dᵀ, the number of arcs e(D) |
| `SimpleGraph V`, `H.Adj u v` | an undirected simple graph on `V`; `u` and `v` are adjacent |
| `H.Connected`, `¬ H.IsAcyclic`, `H.girth` | `H` is connected; `H` contains a cycle (`IsAcyclic` means "is a forest"); the girth of `H` |
| `H.edgeFinset.card` | the number of edges e(H) |
| `completeBipartiteGraph (Fin 2) (Fin 3)` | K₂,₃ |
| `Fin n` | the set {0, 1, …, n − 1}; vertices numbered from 0 |
| `Fin t → Bool` | the sign vectors ε ∈ {−1, 1}ᵗ (`true` for 1, `false` for −1) |
| `I`, `volume` | the unit interval [0,1] and Lebesgue measure on it |
| `U : I → I → ℝ` | a real function on [0,1]², which is a kernel when `IsKernel U` holds |
| `t D U`, `tU H U`, `tb E U` | the densities t(D, W), t(H, W) and t_bi(H, W) (section 4) |
| `AEEq volume U U'` | `U = U'` almost everywhere |
| `Finset (X × Y)` | a finite set of pairs: the edge set E ⊆ X × Y of a bipartite graph with fixed parts X, Y |
| `Finset.univ` | the set of all elements (here all six edges of K₂,₃) |
| `∃ s : V → Prop, IsBipartition H s` | `H` has a bipartition; `s` marks the vertices of the first part |
| `letI := Classical.decPred s` | a technical marker; it does not affect the meaning |
| `∀ x ∈ S, …` / `∃ x, …` | for every `x` in `S` / there is an `x` such that … |
| `P ∧ Q`, `P ∨ Q`, `¬ P`, `P → Q`, `P ↔ Q` | and, or, not, implies, if and only if |
| `Nonempty (D.Iso D')` | `D` and `D'` are isomorphic directed graphs |
| `Fintype.card V`, `Even n` | the number of vertices; `n` is even |
| `S.card`, `∑ C ∈ S, f C` | the number of elements of a finite set `S`; the sum of `f C` over `C ∈ S` |
| `Ico a b`, `Ioo a b`, `Icc a b` | the intervals [a, b), (a, b), [a, b] |
| `Real.pi`, `Real.cos` | π, cosine |
| `Tendsto f atTop (𝓝 a)` | f(n) → a as n → ∞ |
| `Tendsto N atTop atTop` | N(n) → ∞ |
| `∀ᶠ n in atTop, P n` | `P n` holds for all sufficiently large `n` |
| `(n : ℝ)` | the natural number `n` regarded as a real number |
| `…Hyp`, such as `LovaszProp544cHyp` | an assumed published result (section 4b): a hypothesis of the theorem, not an axiom |
| `.{u}`, `.{0}` after a `…Hyp` name | universe levels, a technicality: the published result is assumed for vertex sets of the same kind as `V`. They do not affect the mathematical meaning |
| `noncomputable`, `open … in`, `by classical` | technical markers; they do not affect the meaning |

## 2. How to check it yourself

Requirements: `elan` (the Lean installer; https://github.com/leanprover/elan), `git`, and access
to this private repository.

```
git clone -b formalize/nie-wei-oriented-sidorenko https://github.com/ZRTMRH/nie-wei-oriented-sidorenko-lean.git
cd nie-wei-oriented-sidorenko-lean
lake exe cache get        # downloads Mathlib's prebuilt files (a few GB)
lake build                # kernel-checks every proof; must end "Build completed successfully"
lake env lean Certificate.lean
```

The last command restates 26 main statements in full (each `example` must be accepted) and prints,
for each, the axioms it uses. Expected output, 26 lines of the form:

```
'NieWeiOrientedSidorenko.OrientedGraph.thm_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Versions: Lean `v4.35.0` (`lean-toolchain`); Mathlib commit
`ccbef15ebdb41c2addfac682131f83c75904c3c1`, which the project gets through Tau Ceti commit
`5a01f5fe3621126cccf9ba22e700493cbc7b7156` (`lakefile.toml`, `lake-manifest.json`).

**Results of these checks (13 November 2026).** All were run on the Lean sources of this
repository (the same file tree as commit `091c6b2` of the working project).
- `lake build`: completes, with no `sorry` (the workflow's final check before delivery).
- `lake env lean Certificate.lean`: all 26 `example`s accepted; each of the 26 theorems depends on
  `[propext, Classical.choice, Quot.sound]` only, with no errors or warnings (checked 13 November 2026;
  peak memory about 6.5 GB).
- `#print axioms` on all 133 Lean names listed in `NieWeiOrientedSidorenko/Main.lean` for the
  manuscript's definitions and results: 128 depend on `[propext, Classical.choice, Quot.sound]` or
  on part of it, and 5 definitions depend on no axiom at all. None depends on `sorryAx` or on any
  other axiom.
- **Independent kernel replay.** Lean's separate checker `leanchecker` re-checked the compiled
  library, module by module (`lake env leanchecker <module>`). All 29 modules that contain
  declarations (`NieWeiOrientedSidorenko.Basic`, `Common`, `Examples`, `Families`, `FiniteForms`,
  `KCompactId`, `KConj1`, `KCutPseudo`, `KCutSymm`, `KNullPart`, `KWitness`, `Literature`, `Main`,
  `Mixing`, `S1Bridges`, `S1CutDist`, `S1CutDistB`, `S1Dt`, `S1Families`, `S1FamiliesB`, `S1P112`,
  `Section1`, `Section1Aux`, `Section2`, `Section2Aux`, `Section4`, `Section4Aux`, `Section6`,
  `Witnesses`) were accepted (exit code 0; about 6 GB of memory per module). The root file
  `NieWeiOrientedSidorenko.lean` contains only `import` lines and no declarations. Replaying it as
  one unit re-checks the whole import closure at once and was stopped at a 16 GB memory cap, so it
  is covered by the per-module replays.

## 3. The main theorems

Conventions used throughout.
- **Directed graphs** are orientations of finite simple graphs: no loops, no antiparallel arcs,
  isolated vertices allowed. Connectivity refers to the underlying graph. Finite host graphs are
  nonempty.
- **Finite and digraphon forms.** Definitions 1 and 2 of the manuscript are stated with finite host
  graphs (and sequences of them); Section 2 (tex l.497) gives the equivalent digraphon formulation.
  In Lean these are different predicates: `IsOS`, `IsOAS`, `IsSymmetryForcing` (finite) and `IsOSK`,
  `IsOASK`, `IsSymmetryForcingK` (digraphon). The Question 1(c) bridges prove them equivalent. Each
  Section 1 result about OS, OAS or symmetry-forcing is proved in the finite form (the manuscript's statement) and, under the suffix
  `_kernel`, in the digraphon form. Theorem 4.1 and Lemma 6.1 are stated in the digraphon form, as
  the manuscript's proofs use it, and also in finite form at the authors' request.
- **The finite baseline.** t(D, (G + Gᵀ)/2) is the exact quantity 2^{−e(D)} t(D̄, Ḡ), as the
  manuscript defines it (tex l.130).
- **Kernels are functions.** A kernel is an actual measurable function on [0,1]², and a condition
  the manuscript states of a given kernel (bounded, values in [0,1], nonnegative) is required at
  every point. Equality and distinctness of kernels, and the symmetry of a graphon, are almost
  everywhere, as in the manuscript. Every kernel of the manuscript has a representative that agrees
  with it almost everywhere and meets the pointwise conditions, and the almost-everywhere passages
  the proofs need are proved.
- **"Weakly norming graph"**, for a graph given without a bipartition, means "weakly norming for
  some bipartition" (`IsWeaklyNormingGraph`), the authors' answer at Checkpoint B (Q1(a)). The
  "every bipartition" reading is a corollary (Theorem 1.4 below).
- **Assumed published results** appear as hypotheses with names such as `hA1`; section 4b gives
  their wording. The plain reading of each theorem names the ones it carries. A few statements carry
  one that the proof does not use; the authors asked to keep them, as approved (final-delivery
  answers, §1), and the Lean docstrings say so.

The theorems are in `NieWeiOrientedSidorenko/Section1.lean` (Section 1 and the answer-key
additions), `Section4.lean` (4.1), `Section6.lean` (6.1) and `FiniteForms.lean` (the finite-host
forms of 6.1 and 4.1).

### Question 1(c): finite definitions and digraphon definitions agree

> Keep both the finite/sequence definitions in the Introduction and the digraphon definitions in
> Section 2, and formalize their claimed equivalence. (Pre-run answer key, Question 1(c),
> author-confirmed; the manuscript asserts the equivalence at tex l.144–146 and l.160–161.)

```lean
theorem isOS_iff_isOSK (D : OrientedGraph V) : D.IsOS ↔ D.IsOSK
theorem isOAS_iff_isOASK (D : OrientedGraph V) : D.IsOAS ↔ D.IsOASK
theorem isSymmetryForcing_iff_isSymmetryForcingK (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u})
    (hcpt : FHMZCompactHyp) (D : OrientedGraph V) :
    D.IsSymmetryForcing ↔ D.IsSymmetryForcingK
```
(Section1.lean:65, :70, :76)

D is OS (resp. OAS) for all finite hosts if and only if it is OS (resp. OAS) for all digraphons: no
assumed result. D is symmetry-forcing for sequences of finite hosts if and only if it is
symmetry-forcing for digraphons: assuming FHMZ Theorems 13 and 18 and the FHMZ p. 6 compactness
assertion.

### Theorem 1.1 (Griffiths)

> The directed graph O₁ is OAS and symmetry-forcing, while O₂ is OS and symmetry-forcing.
> (tex l.164)

```lean
theorem thm_1_1 (hA1 : LovaszProp544cHyp.{0}) (hA4 : LeeSidorenkoThm13Hyp.{0})
    (hA9 : LovaszProp142aHyp) (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0})
    (hcpt : FHMZCompactHyp) :
    (O₁.IsOAS ∧ O₁.IsSymmetryForcing) ∧ (O₂.IsOS ∧ O₂.IsSymmetryForcing)
```
(Section1.lean:88; the digraphon form `thm_1_1_kernel`, :95, assumes only Lovász 5.44(c), 14.2(a)
and Lee–Sidorenko)

Assumes Lovász Props. 5.44(c) and 14.2(a), Lee–Sidorenko Thm 1.3, and the three FHMZ items; FHMZ
Thm 13 is carried but not needed.

### Theorem 1.2 (characterization of connected OS directed graphs)

> Let D be a connected directed graph with at least one edge. Then D is OS if and only if all of the
> following conditions hold: (a) D is a one-direction orientation, i.e., its vertex set has a
> bipartition A ∪ B such that every edge is directed from A to B; (b) D is isomorphic to Dᵀ; (c) the
> underlying graph D̄ is weakly norming. (tex l.221–223)

```lean
theorem thm_1_2 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (he : 1 ≤ D.numArcs) :
    D.IsOS ↔ D.IsOneDirection ∧ D.IsSelfConverse ∧ IsWeaklyNormingGraph D.underlying
theorem thm_1_2_kernel (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (he : 1 ≤ D.numArcs) :
    D.IsOSK ↔ D.IsOneDirection ∧ D.IsSelfConverse ∧ IsWeaklyNormingGraph D.underlying
```
(Section1.lean:105, :111)

Both forms assume Lovász Prop. 5.44(c) (`hA1`). "Weakly norming" is for some bipartition, in the
full-kernel convention (section 4).

### Theorem 1.3 (symmetry-forcing for connected OS directed graphs)

> A connected OS directed graph is symmetry-forcing if and only if its underlying graph contains a
> cycle. (tex l.233–235)

```lean
theorem thm_1_3 (hA1 : LovaszProp544cHyp.{u}) (h13 : FHMZThm13Hyp)
    (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp) (D : OrientedGraph V)
    (hconn : D.IsConnected) (hD : D.IsOS) :
    D.IsSymmetryForcing ↔ ¬ D.underlying.IsAcyclic
theorem thm_1_3_kernel (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected) (hD : D.IsOSK) :
    D.IsSymmetryForcingK ↔ ¬ D.underlying.IsAcyclic
```
(Section1.lean:118, :126)

The finite form assumes Lovász Prop. 5.44(c) and the three FHMZ items (they enter through the
sequence bridge); the digraphon form assumes only Lovász Prop. 5.44(c).

### Theorem 1.4 (cut distance identifying, step forcing)

> Let H be a weakly norming graph containing a cycle. Then t(H,·) is a cut distance identifying
> graphon parameter, and hence H is step forcing. (tex l.267–269)

```lean
theorem thm_1_4 (hA2 : DGHRRCor324Hyp.{u}) (hF217 : DGHRRFact217Hyp) (hF218 : DGHRRFact218Hyp)
    (hFR : FRHSUThm43Hyp)
    (H : SimpleGraph V) (hH : IsWeaklyNormingGraph H) (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H
```
(Section1.lean:143)

Assumes DGHRR Cor. 3.24, Facts 2.17 and 2.18, and FRHSU Thm 4.3; Fact 2.17 is unused. No
connectedness is assumed (Checkpoint B, Q1(a)).

**Reading "weakly norming for every bipartition"** (kept at Checkpoint B as a derived corollary):

```lean
theorem thm_1_4_every_bipartition (hA2 : DGHRRCor324Hyp.{u}) (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) (H : SimpleGraph V)
    (hbip : ∃ s : V → Prop, IsBipartition H s)
    (hH : ∀ s : V → Prop, IsBipartition H s →
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges H s))
    (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H
```
(Section1.lean:156; the same assumptions, Fact 2.17 forwarded only)

**B1: the connected symmetric-convention form.**

> Author-confirmed addition: also state and prove the connected symmetric-convention corollary,
> using A4 to transfer to the full-kernel setting. Preserve the connectedness and positive-edge
> conditions required for that transfer. (Pre-run answer key, B1.) The intended consequence is
> precisely: if H is connected, bipartite, has at least one edge, contains a cycle, and is weakly
> norming in the symmetric convention, then t(H,·) is cut distance identifying and H is step
> forcing. (Checkpoint B answer key, Q6.)

```lean
theorem thm_1_4_symm (hA2 : DGHRRCor324Hyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) (hbip : ∃ s : V → Prop, IsBipartition H s)
    (he : 0 < H.edgeFinset.card) (hH : IsWeaklyNormingSymm H) (hcyc : ¬ H.IsAcyclic) :
    CutDistIdentifying (tU H) ∧ IsStepForcing H
```
(Section1.lean:172)

The assumptions of Theorem 1.4, plus Lee–Sidorenko Thm 1.3 (A4); Fact 2.17 forwarded only.

### Corollary 1.5

> A connected graph is step forcing if and only if it is step Sidorenko and contains a cycle.
> (tex l.303–305)

```lean
theorem cor_1_5 (hA2 : DGHRRCor324Hyp.{u}) (hA3 : DGHRRThm325Hyp.{u})
    (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hF217 : DGHRRFact217Hyp) (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp)
    (H : SimpleGraph V) (hconn : H.Connected) :
    IsStepForcing H ↔ IsStepSidorenko H ∧ ¬ H.IsAcyclic
```
(Section1.lean:194)

Assumes DGHRR Cor. 3.24, Thm 3.25 (with Thm 2.14), Facts 2.17 (forwarded only) and 2.18,
Lee–Sidorenko Thm 1.3 and FRHSU Thm 4.3.

### Theorem 1.6 (strict convexity)

> Let H = (X ∪ Y, E) be a bipartite graph with a fixed bipartition and at least one edge. Then H is
> weakly norming and contains a cycle if and only if t_bi(H,·) is strictly convex on nonnegative
> kernels. (tex l.311–313)

```lean
theorem thm_1_6 {X Y : Type*} [Fintype X] [Fintype Y] (E : Finset (X × Y)) (hE : 0 < E.card) :
    IsWeaklyNorming E ∧ ¬ (bipGraph E).IsAcyclic ↔ StrictConvexOnNonnegKernels E
```
(Section1.lean:211)

No assumed result. The bipartite graph is given by its parts X, Y and its edge set E ⊆ X × Y.

### B4(i): K₂,₃ is weakly norming and step forcing, but not norming

> (i) explicitly prove that K₂,₃ is step forcing but not norming, giving the negative answer to
> DGHRR Problem 3.29. (Pre-run answer key, B4, author-confirmed.) Retain the full B4(i) row
> asserting that K₂,₃ is weakly norming, step forcing, and not norming on the full kernel space.
> Also retain the separate row asserting that it is not norming even on symmetric kernels.
> (Checkpoint B answer key, Q2.)

```lean
theorem k23_weaklyNorming_stepForcing_not_norming (hA2 : DGHRRCor324Hyp.{0})
    (hF217 : DGHRRFact217Hyp)
    (hF218 : DGHRRFact218Hyp) (hFR : FRHSUThm43Hyp) :
    IsWeaklyNorming (Finset.univ : Finset (Fin 2 × Fin 3)) ∧
    IsStepForcing (completeBipartiteGraph (Fin 2) (Fin 3)) ∧
    ¬ IsNormingGraph (completeBipartiteGraph (Fin 2) (Fin 3))
theorem k23_not_norming_symm :
    ¬ IsNormOn IsSymmKernel
      (fun U => |tU (completeBipartiteGraph (Fin 2) (Fin 3)) U| ^ ((1 : ℝ) / 6))
```
(Section1.lean:222, :236)

The first assumes DGHRR Cor. 3.24; it also carries Facts 2.17, 2.18 and FRHSU, unused. K₂,₃ is
weakly norming for its bipartition into parts of sizes 2 and 3, step forcing, and not norming for
any bipartition. The second assumes nothing: W ↦ |t(K₂,₃, W)|^{1/6} is not a norm on the symmetric
bounded measurable kernels, the convention of DGHRR's Problem 3.29.

### B4(ii): OS and step Sidorenko

> (ii) explicitly prove D is OS ⟺ D̄ is step Sidorenko for D connected, one-direction,
> self-converse, and e(D) > 0, using the manuscript's OS characterization and A3–A4. (Pre-run
> answer key, B4, author-confirmed.)

```lean
theorem isOS_iff_isStepSidorenko (hA1 : LovaszProp544cHyp.{u}) (hA2 : DGHRRCor324Hyp.{u})
    (hA3 : DGHRRThm325Hyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u}) (D : OrientedGraph V)
    (hconn : D.IsConnected)
    (hone : D.IsOneDirection) (hsc : D.IsSelfConverse) (he : 1 ≤ D.numArcs) :
    D.IsOS ↔ IsStepSidorenko D.underlying
```
(Section1.lean:247)

Assumes Lovász Prop. 5.44(c), DGHRR Cor. 3.24 and Thm 3.25, and Lee–Sidorenko Thm 1.3.

### Theorem 1.7

> For every t ≥ 2, the directed graph D_t is OAS and symmetry-forcing. (tex l.325–328)

```lean
theorem thm_1_7 (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{0}) (hcpt : FHMZCompactHyp)
    (t : ℕ) (ht : 2 ≤ t) :
    (Dt t).IsOAS ∧ (Dt t).IsSymmetryForcing
```
(Section1.lean:260; the digraphon form `thm_1_7_kernel`, :266, assumes nothing)

The finite form assumes the three FHMZ items (through the sequence bridge); FHMZ Thm 13 is carried
but not needed.

### Proposition 1.8

> There exists an OAS directed graph whose underlying graph contains a triangle. (tex l.332–335)

```lean
theorem prop_1_8 : ∃ (n : ℕ) (D : OrientedGraph (Fin n)), D.IsOAS ∧
    ∃ a b c : Fin n, D.underlying.Adj a b ∧ D.underlying.Adj b c ∧ D.underlying.Adj a c
```
(Section1.lean:271; digraphon form `prop_1_8_kernel`, :276)

No assumed result.

### Theorem 1.9 (oriented stars)

> Let D be an oriented star. 1. If D has one edge, then D is both OS and OAS. 2. If D has at least
> two edges, then D is not OS. Moreover, D is OAS if and only if its center has equal in-degree and
> out-degree. (tex l.351–359)

```lean
theorem thm_1_9 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V)
    (c : V) (hstar : D.IsOrientedStar c) :
    (D.numArcs = 1 → D.IsOS ∧ D.IsOAS) ∧
    (2 ≤ D.numArcs → ¬ D.IsOS ∧ (D.IsOAS ↔ D.inDeg c = D.outDeg c))
```
(Section1.lean:285; digraphon form `thm_1_9_kernel`, :294)

Assumes Lovász Prop. 5.44(c). The star is given with its center `c`.

### Theorem 1.10 (oriented paths)

> Let P be an oriented path. 1. If P has one edge, then P is both OS and OAS. 2. If P has at least
> two edges, then P is not OS. Moreover, P is OAS if and only if it is the directed two-edge path
> 1 → 2 → 3. (tex l.361–368)

```lean
theorem thm_1_10 (hA1 : LovaszProp544cHyp.{u}) (D : OrientedGraph V) (hpath : D.IsOrientedPath) :
    (D.numArcs = 1 → D.IsOS ∧ D.IsOAS) ∧
    (2 ≤ D.numArcs → ¬ D.IsOS ∧ (D.IsOAS ↔ Nonempty (D.Iso dirPath3)))
```
(Section1.lean:303; digraphon form `thm_1_10_kernel`, :309)

Assumes Lovász Prop. 5.44(c). "Is the directed two-edge path" is "is isomorphic to it".

### Theorem 1.11 (oriented cycles)

> An oriented cycle is OS if and only if it is an alternating orientation of an even cycle, and it
> is OAS if and only if it is isomorphic to O₁. (tex l.371–373)

```lean
theorem thm_1_11 (hA1 : LovaszProp544cHyp.{u}) (hA4 : LeeSidorenkoThm13Hyp.{u})
    (hA9 : LovaszProp142aHyp) (D : OrientedGraph V) (hcyc : D.IsOrientedCycle) :
    (D.IsOS ↔ Even (Fintype.card V) ∧ D.IsAlternating) ∧ (D.IsOAS ↔ Nonempty (D.Iso O₁))
```
(Section1.lean:317; digraphon form `thm_1_11_kernel`, :323)

Assumes Lovász Props. 5.44(c) and 14.2(a) and Lee–Sidorenko Thm 1.3. A cycle's length is its
number of vertices.

### Proposition 1.12

> If a directed graph D is symmetry-forcing, then D is either OS or OAS. (tex l.378)

```lean
theorem prop_1_12 (h13 : FHMZThm13Hyp) (h18 : FHMZThm18Hyp.{u}) (hcpt : FHMZCompactHyp)
    (D : OrientedGraph V) (hD : D.IsSymmetryForcing) : D.IsOS ∨ D.IsOAS
theorem prop_1_12_kernel (D : OrientedGraph V) (hD : D.IsSymmetryForcingK) :
    D.IsOSK ∨ D.IsOASK
```
(Section1.lean:334, :339)

The finite form assumes FHMZ Thms 13 and 18 (the p. 6 assertion is carried but not needed); the
digraphon form assumes nothing.

### Theorem 4.1 (a sufficient condition for OS)

> Let D be a directed graph satisfying the following properties: (a) D is homomorphic to a directed
> edge; (b) D is isomorphic to the digraph Dᵀ obtained by reversing the orientation of each edge of
> D; (c) its underlying graph D̄ is weakly norming with respect to a bipartition under which all
> edges of D go from the first part to the second. Then D is Oriented Sidorenko. (tex l.691–700)

```lean
theorem thm_4_1 (D : OrientedGraph V) (ha : D.HomToDirEdge) (hb : D.IsSelfConverse)
    (hc : ∃ s : V → Prop, (∀ u v, D.Adj u v → s u ∧ ¬ s v) ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges D.underlying s)) :
    D.IsOSK
```
(Section4.lean:1524)

**Finite hosts** (requested in the final-delivery answers, §2: "Its OS conclusion must apply to all
admissible finite oriented host graphs G as well as to all admissible digraphons W. In the finite
case this means t(D,G) ≥ 2^{−e(D)} t(D̄,Ḡ). Do not introduce a connectedness hypothesis."):

```lean
theorem thm_4_1_finite (D : OrientedGraph V) (ha : D.HomToDirEdge) (hb : D.IsSelfConverse)
    (hc : ∃ s : V → Prop, (∀ u v, D.Adj u v → s u ∧ ¬ s v) ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges D.underlying s)) :
    D.IsOS
```
(FiniteForms.lean:43)

No assumed result, in either form. Condition (a) follows from (c) and is unused; it is kept because
it is printed (final-delivery answers, §1(e)). The finite form follows from the digraphon form by
the OS bridge of Question 1(c). For D with no arcs, condition (c) is false in Lean (the exponent
1/e(D) is read as 0), so that case holds vacuously; the manuscript's (c) is undefined there.

### Lemma 6.1 (girth condition for OAS)

> Let D be a directed graph whose underlying graph contains a cycle, and let g be the girth of D̄.
> If D is OAS, then ∑_{C∈𝒞_g(D)} cos(ω_D(C)θ) ≤ |𝒞_g(D)| cos^g(θ) for every θ ∈ [0,2π).
> (tex l.1368–1378)

```lean
theorem lemma_6_1 (D : OrientedGraph V) (hcyc : ¬ D.underlying.IsAcyclic) (hD : D.IsOASK)
    (θ : ℝ) (hθ : θ ∈ Ico 0 (2 * Real.pi)) :
    ∑ C ∈ D.cyclesOfLength D.underlying.girth, D.cosImbalance θ C ≤
      (D.cyclesOfLength D.underlying.girth).card * Real.cos θ ^ D.underlying.girth
theorem lemma_6_1_finite (D : OrientedGraph V) (hcyc : ¬ D.underlying.IsAcyclic) (hD : D.IsOAS)
    (θ : ℝ) (hθ : θ ∈ Ico 0 (2 * Real.pi)) :
    ∑ C ∈ D.cyclesOfLength D.underlying.girth, D.cosImbalance θ C ≤
      (D.cyclesOfLength D.underlying.girth).card * Real.cos θ ^ D.underlying.girth
```
(Section6.lean:881; FiniteForms.lean:30)

No assumed result, in either form. The finite form (final-delivery answers, §2) takes OAS for
finite hosts and follows by the OAS bridge. The range 0 ≤ θ < 2π is unused (the inequality is
periodic) and kept as printed (§1(f)). 𝒞_g(D) is the set of cycles of length g of D̄, each given by
its edge set, and ω_D(C) is the number of its edges traversed along their orientation minus the
number traversed against it (section 4).

## 4. The definitions these statements use

Lean definitions are in `NieWeiOrientedSidorenko/Basic.lean` unless another file is named.

- **Directed graphs** (tex l.400–401): "a directed graph is an orientation of a finite simple graph;
  loops and antiparallel edges are excluded."
  ```lean
  structure OrientedGraph (V : Type*) where
    Adj : V → V → Prop
    irrefl : ∀ v, ¬ Adj v v
    asymm : ∀ u v, Adj u v → ¬ Adj v u
  def transpose (D : OrientedGraph V) : OrientedGraph V where
    Adj u v := D.Adj v u
  def underlying (D : OrientedGraph V) : SimpleGraph V := SimpleGraph.fromRel D.Adj
  noncomputable def arcs [Fintype V] (D : OrientedGraph V) : Finset (V × V) := by
    classical exact Finset.univ.filter fun p => D.Adj p.1 p.2
  noncomputable def numArcs [Fintype V] (D : OrientedGraph V) : ℕ := D.arcs.card
  structure Iso (D : OrientedGraph V) (D' : OrientedGraph W) extends V ≃ W where
    map_adj_iff : ∀ u v, D'.Adj (toEquiv u) (toEquiv v) ↔ D.Adj u v
  def IsConnected (D : OrientedGraph V) : Prop := D.underlying.Connected
  ```
  (Basic.lean:35–70; the proof fields of `transpose` are omitted here.) Finiteness of a directed
  graph is a `[Fintype V]` assumption wherever it is needed.
- **Homomorphism densities of finite graphs** (tex l.408–410): "t(H, G) = |Hom(H, G)| / |V(G)|^{v(H)}."
  ```lean
  noncomputable def homCount [Fintype V] [Fintype W] (D : OrientedGraph V) (G : OrientedGraph W) :
      ℕ := by
    classical exact (Finset.univ.filter fun f : V → W => ∀ u v, D.Adj u v → G.Adj (f u) (f v)).card
  noncomputable def homDensity [Fintype V] [Fintype W] (D : OrientedGraph V)
      (G : OrientedGraph W) : ℝ :=
    (homCount D G : ℝ) / (Fintype.card W : ℝ) ^ Fintype.card V
  ```
  `simpleHomCount`, `simpleHomDensity` (Basic.lean:96, :102) are the same for simple graphs.
- **The symmetrized finite density** (tex l.130): "t(D, (G+Gᵀ)/2) := 2^{−|E(D)|} t(D̄, Ḡ)".
  ```lean
  noncomputable def symmDensity [Fintype V] [Fintype W] (D : OrientedGraph V)
      (G : OrientedGraph W) : ℝ :=
    (2 : ℝ)⁻¹ ^ D.numArcs * simpleHomDensity D.underlying G.underlying
  ```
- **Definition 1 (OS and OAS)** (tex l.140–141): "A directed graph D has the oriented Sidorenko
  property, or is OS, if t(D,G) ≥ t(D, (G+Gᵀ)/2) for every directed graph G. A directed graph D has
  the oriented anti-Sidorenko property, or is OAS, if t(D,G) ≤ t(D, (G+Gᵀ)/2) for every directed
  graph G."
  ```lean
  def IsOS [Fintype V] (D : OrientedGraph V) : Prop :=
    ∀ (W : Type) [Fintype W] [Nonempty W] (G : OrientedGraph W), symmDensity D G ≤ homDensity D G
  def IsOAS [Fintype V] (D : OrientedGraph V) : Prop :=
    ∀ (W : Type) [Fintype W] [Nonempty W] (G : OrientedGraph W), homDensity D G ≤ symmDensity D G
  ```
  (Basic.lean:118, :123) The hosts G range over finite nonempty directed graphs.
- **Quasi-random in its orientations** (tex l.132): "max_{A,B ⊆ V(G_n)} |e_{G_n}(A,B) − e_{G_n}(B,A)|
  = o(|V(G_n)|²), where e_{G_n}(A,B) denotes the number of edges directed from A to B."
  ```lean
  noncomputable def arcsFromTo [Fintype W] (G : OrientedGraph W) (A B : Finset W) : ℕ := by
    classical exact (G.arcs.filter fun p => p.1 ∈ A ∧ p.2 ∈ B).card
  def IsOrientQuasirandom (N : ℕ → ℕ) (G : ∀ n, OrientedGraph (Fin (N n))) : Prop :=
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ A B : Finset (Fin (N n)),
      |((G n).arcsFromTo A B : ℝ) - (G n).arcsFromTo B A| ≤ ε * (N n : ℝ) ^ 2
  ```
- **Definition 2 (symmetry-forcing)** (tex l.153–158): "A directed graph D is symmetry-forcing if,
  for every sequence of directed graphs (G_n)_{n≥1} with |V(G_n)| → ∞,
  t(D, G_n) = t(D, (G_n+G_nᵀ)/2) + o(1) holds if and only if (G_n)_{n≥1} is quasi-random in its
  orientations."
  ```lean
  def IsSymmetryForcing [Fintype V] (D : OrientedGraph V) : Prop :=
    ∀ (N : ℕ → ℕ) (G : ∀ n, OrientedGraph (Fin (N n))), Tendsto N atTop atTop →
      (Tendsto (fun n => homDensity D (G n) - symmDensity D (G n)) atTop (𝓝 0) ↔
        IsOrientQuasirandom N G)
  ```
  (Basic.lean:141) The n-th host has vertex set {0, …, N(n) − 1}; densities do not depend on the
  labelling.
- **Kernels, digraphons, graphons** (tex l.415): "A (directed) kernel is a bounded measurable function
  U : [0,1]² → ℝ, not necessarily symmetric. We identify kernels that agree almost everywhere. A
  digraphon is a kernel with codomain restricted to [0,1]. Its transpose is Wᵀ(x,y) = W(y,x), and
  its symmetrization is S = (W+Wᵀ)/2. A graphon is just a symmetric digraphon, i.e. it satisfies
  W(x,y) = W(y,x) for almost all (x,y) ∈ [0,1]²."
  ```lean
  def IsKernel (U : Ω → Ω → ℝ) : Prop :=
    Measurable (Function.uncurry U) ∧ ∃ M : ℝ, ∀ x y, |U x y| ≤ M
  def IsDigraphon (U : Ω → Ω → ℝ) : Prop :=
    Measurable (Function.uncurry U) ∧ ∀ x y, U x y ∈ Icc (0 : ℝ) 1
  def kTranspose (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => U y x
  noncomputable def symmetrize (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => (U x y + U y x) / 2
  def AEEq (μ : Measure Ω) (U U' : Ω → Ω → ℝ) : Prop :=
    ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = U' p.1 p.2
  def IsGraphon (μ : Measure Ω) (U : Ω → Ω → ℝ) : Prop :=
    IsDigraphon U ∧ AEEq μ U (kTranspose U)
  ```
  (Basic.lean:156–175) In the main statements Ω = [0,1] with Lebesgue measure.
- **Homomorphism density in a kernel** (tex l.417–421): "t(H, W) = ∫_{[0,1]^{V(H)}}
  ∏_{(u,w)∈E(H)} W(x_u, x_w) ∏_{v∈V(H)} dx_v."
  ```lean
  noncomputable def tDir (μ : Measure Ω) [SigmaFinite μ] {V : Type*} [Fintype V]
      (D : OrientedGraph V) (U : Ω → Ω → ℝ) : ℝ :=
    ∫ x : V → Ω, ∏ p ∈ D.arcs, U (x p.1) (x p.2) ∂(Measure.pi fun _ => μ)
  noncomputable def tUndir (μ : Measure Ω) [SigmaFinite μ] {V : Type*} [Fintype V]
      (H : SimpleGraph V) (U : Ω → Ω → ℝ) : ℝ := by
    classical
    exact ∫ x : V → Ω, ∏ e ∈ H.edgeFinset, U (x (Quot.out e).1) (x (Quot.out e).2)
      ∂(Measure.pi fun _ => μ)
  noncomputable abbrev t {V : Type*} [Fintype V] (D : OrientedGraph V) (U : I → I → ℝ) : ℝ :=
    tDir volume D U
  noncomputable abbrev tU {V : Type*} [Fintype V] (H : SimpleGraph V) (U : I → I → ℝ) : ℝ :=
    tUndir volume H U
  ```
  For an undirected graph each edge is read in a fixed order of its endpoints; for (almost
  everywhere) symmetric kernels, the only ones it is applied to, the order does not matter, as the
  manuscript says.
- **Bipartite homomorphism density** (tex l.429–432): "t_bi(H, W) = ∫ ∏_{uv∈E, u∈A, v∈B} W(x_u, y_v)
  ∏_{u∈A} dx_u ∏_{v∈B} dy_v."
  ```lean
  noncomputable def tBi (μ : Measure Ω) [SigmaFinite μ] {X Y : Type*} [Fintype X] [Fintype Y]
      (E : Finset (X × Y)) (U : Ω → Ω → ℝ) : ℝ :=
    ∫ z : (X → Ω) × (Y → Ω), ∏ p ∈ E, U (z.1 p.1) (z.2 p.2)
      ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
  def bipGraph (E : Finset (X × Y)) : SimpleGraph (X ⊕ Y) :=
    SimpleGraph.fromRel fun a b => ∃ x y, a = Sum.inl x ∧ b = Sum.inr y ∧ (x, y) ∈ E
  ```
  `tb E U` is `tBi volume E U`.
- **Digraphon OS, OAS, symmetry-forcing** (tex l.497): "A directed graph D is OS, respectively OAS,
  if for every digraphon W, t(D,W) ≥ t(D, (W+Wᵀ)/2), respectively t(D,W) ≤ t(D, (W+Wᵀ)/2). Further,
  D is symmetry-forcing if t(D,W) = t(D, (W+Wᵀ)/2) implies W = Wᵀ."
  ```lean
  def IsOSK (D : OrientedGraph V) : Prop :=
    ∀ U : I → I → ℝ, IsDigraphon U → t D (symmetrize U) ≤ t D U
  def IsOASK (D : OrientedGraph V) : Prop :=
    ∀ U : I → I → ℝ, IsDigraphon U → t D U ≤ t D (symmetrize U)
  def IsSymmetryForcingK (D : OrientedGraph V) : Prop :=
    ∀ U : I → I → ℝ, IsDigraphon U → t D U = t D (symmetrize U) →
      AEEq volume U (kTranspose U)
  ```
  (Basic.lean:229–241) "W = Wᵀ" is almost everywhere, as the manuscript says at l.160–161.
- **Norming and weakly norming** (tex l.432–449): "Define ‖W‖_H := |t_bi(H,W)|^{1/e(H)} and
  ‖W‖_{r(H)} := t_bi(H,|W|)^{1/e(H)}. We say that H is norming if ‖·‖_H is a norm, and weakly
  norming if ‖·‖_{r(H)} is a norm on the space of all kernels. Thus the bipartition is fixed, and
  symmetry of a kernel is not assumed. … When we refer explicitly to the symmetric convention, these
  functionals are instead restricted to symmetric kernels and t(H,W) is used."
  ```lean
  noncomputable def rNorm (E : Finset (X × Y)) (U : I → I → ℝ) : ℝ :=
    tb E (fun x y => |U x y|) ^ ((1 : ℝ) / E.card)
  noncomputable def hNorm (E : Finset (X × Y)) (U : I → I → ℝ) : ℝ :=
    |tb E U| ^ ((1 : ℝ) / E.card)
  def IsKernelNorm (N : (I → I → ℝ) → ℝ) : Prop :=
    (∀ U, IsKernel U → ∀ c : ℝ, N (fun x y => c * U x y) = |c| * N U) ∧
    (∀ U V, IsKernel U → IsKernel V → N (fun x y => U x y + V x y) ≤ N U + N V) ∧
    (∀ U, IsKernel U → N U = 0 → AEEq volume U (fun _ _ => 0))
  def IsWeaklyNorming (E : Finset (X × Y)) : Prop := IsKernelNorm (rNorm E)
  def IsNorming (E : Finset (X × Y)) : Prop := IsKernelNorm (hNorm E)
  noncomputable def sideEdges (H : SimpleGraph V) (s : V → Prop) :
      Finset ({v // s v} × {v // ¬ s v}) := by
    classical exact Finset.univ.filter fun p => H.Adj p.1 p.2
  def IsBipartition (H : SimpleGraph V) (s : V → Prop) : Prop :=
    ∀ u v, H.Adj u v → (s u ↔ ¬ s v)
  def IsWeaklyNormingGraph (H : SimpleGraph V) : Prop :=
    ∃ s : V → Prop, IsBipartition H s ∧
      letI := Classical.decPred s
      IsWeaklyNorming (sideEdges H s)
  def IsNormingGraph (H : SimpleGraph V) : Prop :=
    ∃ s : V → Prop, IsBipartition H s ∧
      letI := Classical.decPred s
      IsNorming (sideEdges H s)
  def IsWeaklyNormingSymm (H : SimpleGraph V) : Prop :=
    letI := Classical.decRel H.Adj
    let N : (I → I → ℝ) → ℝ := fun U => tU H (fun x y => |U x y|) ^ ((1 : ℝ) / H.edgeFinset.card)
    let Sym : (I → I → ℝ) → Prop := fun U => IsKernel U ∧ AEEq volume U (kTranspose U)
    (∀ U, Sym U → ∀ c : ℝ, N (fun x y => c * U x y) = |c| * N U) ∧
    (∀ U V, Sym U → Sym V → N (fun x y => U x y + V x y) ≤ N U + N V) ∧
    (∀ U, Sym U → N U = 0 → AEEq volume U (fun _ _ => 0))
  ```
  (Basic.lean:252–316) A norm vanishes only at the kernel that is zero almost everywhere. A graph
  given without a bipartition is (weakly) norming if it is for some bipartition (Checkpoint B,
  Q1(a)). For the symmetric convention of B4(i), `IsSymmKernel U` is `IsKernel U ∧ ∀ x y, U x y =
  U y x`, and `IsNormOn K N` says `N` is absolutely homogeneous and subadditive on the class `K` and
  vanishes only at the almost-everywhere-zero kernel (Literature.lean:41, :63).
- **Step averages, step Sidorenko, step forcing** (tex l.476–487): "For a graphon W and a finite
  measurable partition 𝒫 of [0,1] into parts of positive measure, let W^𝒫 be the graphon whose value
  on P_i × P_j is (1/(|P_i||P_j|)) ∫_{P_i×P_j} W. … a graph H is step forcing if t(H,W^𝒫) < t(H,W)
  whenever W and W^𝒫 differ on a set of positive measure. The non-strict version of this inequality
  is the step Sidorenko property."
  ```lean
  structure PosPartition (μ : Measure Ω) where
    k : ℕ
    part : Fin k → Set Ω
    measurableSet_part : ∀ i, MeasurableSet (part i)
    pos : ∀ i, 0 < μ (part i)
    disjoint : Pairwise fun i j => Disjoint (part i) (part j)
    cover : (⋃ i, part i) = univ
  noncomputable def stepAvg {μ : Measure Ω} (P : PosPartition μ) (U : Ω → Ω → ℝ) : Ω → Ω → ℝ :=
    fun x y => ∑ i, ∑ j, (P.part i).indicator (fun _ => (1 : ℝ)) x *
      (P.part j).indicator (fun _ => (1 : ℝ)) y *
      ((∫ p in P.part i ×ˢ P.part j, U p.1 p.2 ∂(μ.prod μ)) /
        ((μ (P.part i)).toReal * (μ (P.part j)).toReal))
  def IsStepSidorenko (H : SimpleGraph V) : Prop :=
    ∀ U : I → I → ℝ, IsGraphon volume U → ∀ P : PosPartition (volume : Measure I),
      tU H (stepAvg P U) ≤ tU H U
  def IsStepForcing (H : SimpleGraph V) : Prop :=
    ∀ U : I → I → ℝ, IsGraphon volume U → ∀ P : PosPartition (volume : Measure I),
      ¬ AEEq volume U (stepAvg P U) → tU H (stepAvg P U) < tU H U
  ```
- **Envelopes and cut distance identifying parameters** (tex l.489–493): "For a measure-preserving
  bijection φ of [0,1], put W^φ(x,y) = W(φ(x),φ(y)). The envelope ⟨W⟩ is the set of weak* limits of
  sequences of versions W^{φ_n}. Write U ⪯ W when ⟨U⟩ ⊆ ⟨W⟩, and U ≺ W when the inclusion is strict.
  A graphon parameter θ is … cut distance identifying if U ≺ W implies θ(U) < θ(W)."
  ```lean
  def MPBij : Type := {φ : I ≃ᵐ I // MeasurePreserving φ volume volume}
  def pullback (φ : I → I) (U : I → I → ℝ) : I → I → ℝ := fun x y => U (φ x) (φ y)
  def WeakStarTendsto (Un : ℕ → I → I → ℝ) (U : I → I → ℝ) : Prop :=
    ∀ A B : Set I, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => ∫ p in A ×ˢ B, Un n p.1 p.2) atTop (𝓝 (∫ p in A ×ˢ B, U p.1 p.2))
  def envelope (U : I → I → ℝ) : Set (I → I → ℝ) :=
    {U' | IsGraphon volume U' ∧ ∃ φ : ℕ → MPBij, WeakStarTendsto (fun n => pullback (φ n).1 U) U'}
  def StructLT (U W : I → I → ℝ) : Prop := envelope U ⊂ envelope W
  def CutDistIdentifying (θ : (I → I → ℝ) → ℝ) : Prop :=
    ∀ U W, IsGraphon volume U → IsGraphon volume W → StructLT U W → θ U < θ W
  ```
  (Basic.lean:347–375) The cut norm and the cut distances (`cutNorm`, `cutDist`, `cutDistMap`,
  Basic.lean:378–390) are used by the assumed results and the proofs, not by the main statements.
- **Strict convexity on nonnegative kernels** (tex l.311–313, l.578–580):
  ```lean
  def StrictConvexOnNonnegKernels (E : Finset (X × Y)) : Prop :=
    ∀ U V : I → I → ℝ, IsKernel U → IsKernel V → (∀ x y, 0 ≤ U x y) → (∀ x y, 0 ≤ V x y) →
      ¬ AEEq volume U V → ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
        tb E (fun x y => a * U x y + (1 - a) * V x y) < a * tb E U + (1 - a) * tb E V
  ```
  "Distinct" kernels are kernels that are not equal almost everywhere.
- **One-direction orientation, D ≅ Dᵀ, homomorphic to a directed edge** (tex l.221–223, l.694;
  Basic.lean:74, :78, Families.lean:60):
  ```lean
  def IsOneDirection (D : OrientedGraph V) : Prop :=
    ∃ A : Set V, ∀ u v, D.Adj u v → u ∈ A ∧ v ∉ A
  def IsSelfConverse (D : OrientedGraph V) : Prop := Nonempty (D.Iso D.transpose)
  def HomToDirEdge {V : Type*} (D : OrientedGraph V) : Prop :=
    ∃ f : V → Fin 2, ∀ u v, D.Adj u v → f u = 0 ∧ f v = 1
  ```
- **O₁, O₂ and the directed two-edge path** (tex l.134: "O₁ : 1 ← 2 → 3 → 4 → 1, and
  O₂ : 1 ← 2 → 3 ← 4 → 1"; Families.lean:28–42), with vertices 1, 2, 3, 4 relabelled 0, 1, 2, 3:
  ```lean
  def O₁ : OrientedGraph (Fin 4) :=
    ofArcs {(1, 0), (1, 2), (2, 3), (3, 0)} (by decide) (by decide)
  def O₂ : OrientedGraph (Fin 4) :=
    ofArcs {(1, 0), (1, 2), (3, 2), (3, 0)} (by decide) (by decide)
  def dirPath3 : OrientedGraph (Fin 3) :=
    ofArcs {(0, 1), (1, 2)} (by decide) (by decide)
  ```
  `ofArcs A _ _` is the directed graph on `Fin n` whose arcs are the pairs in `A`.
- **Definition 3 (D_t)** (tex l.1146–1159): "For an integer t ≥ 2, let D_t be the directed graph
  whose underlying graph is K_{t,2^t}. Let X = {u_1, …, u_t} be the part of size t, and index the
  vertices in the other part by the vectors ε = (ε_1, …, ε_t) ∈ {−1,1}^t. … orient the edge between
  u_i and v_ε as u_i → v_ε if ε_i = 1 and v_ε → u_i if ε_i = −1."
  ```lean
  def Dt (t : ℕ) : OrientedGraph (Fin t ⊕ (Fin t → Bool)) where
    Adj a b := match a, b with
      | Sum.inl i, Sum.inr ε => ε i = true
      | Sum.inr ε, Sum.inl i => ε i = false
      | _, _ => False
  ```
  (Families.lean:49; the proof fields are omitted here.)
- **Oriented stars, paths and cycles** (tex l.351–375; Families.lean:66–91):
  ```lean
  noncomputable def inDeg (D : OrientedGraph V) (c : V) : ℕ := by
    classical exact (Finset.univ.filter fun u => D.Adj u c).card
  noncomputable def outDeg (D : OrientedGraph V) (c : V) : ℕ := by
    classical exact (Finset.univ.filter fun v => D.Adj c v).card
  def IsOrientedStar (D : OrientedGraph V) (c : V) : Prop :=
    (∀ u v, D.underlying.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c)) ∧ 1 ≤ D.numArcs
  def IsOrientedPath (D : OrientedGraph V) : Prop :=
    Nonempty (D.underlying ≃g SimpleGraph.pathGraph (Fintype.card V)) ∧ 2 ≤ Fintype.card V
  def IsOrientedCycle (D : OrientedGraph V) : Prop :=
    Nonempty (D.underlying ≃g SimpleGraph.cycleGraph (Fintype.card V)) ∧ 3 ≤ Fintype.card V
  def IsAlternating (D : OrientedGraph V) : Prop :=
    ∀ v, (∀ u, ¬ D.Adj u v) ∨ (∀ u, ¬ D.Adj v u)
  ```
  A star, path or cycle spans all vertices of `D`; a star or path has at least one edge.
  "Alternating" means every vertex is a source or a sink.
- **Girth cycles and orientation imbalance** (tex l.1360–1365; Families.lean:97–114): 𝒞_g(D) is the
  set of cycles of length g of D̄, and ω_D(C) = f_D(C) − b_D(C) counts the edges of C traversed
  forward minus those traversed backward.
  ```lean
  noncomputable def walkImbalance (D : OrientedGraph V) {u v : V} (w : D.underlying.Walk u v) :
      ℤ := by
    classical exact (w.darts.map fun d => if D.Adj d.fst d.snd then (1 : ℤ) else -1).sum
  noncomputable def cyclesOfLength (D : OrientedGraph V) (g : ℕ) : Finset (Finset (Sym2 V)) := by
    classical
    exact Finset.univ.filter fun C =>
      ∃ (v : V) (w : D.underlying.Walk v v), w.IsCycle ∧ w.length = g ∧ w.edges.toFinset = C
  noncomputable def cosImbalance (D : OrientedGraph V) (θ : ℝ) (C : Finset (Sym2 V)) : ℝ := by
    classical
    exact if h : ∃ (v : V) (w : D.underlying.Walk v v), w.IsCycle ∧ w.edges.toFinset = C then
      Real.cos ((walkImbalance D (Classical.choose (Classical.choose_spec h)) : ℝ) * θ)
    else 0
  ```
  The cycle's direction of traversal is chosen arbitrarily; the cosine does not depend on it, and
  this is proved (`Section6Aux.cosImbalance_eq_of_isCycle`, Section6.lean:824).
- **Conjecture 1** (tex l.121; Section1.lean:44) is recorded as a proposition `SidorenkoForcingConjecture`,
  not a result: no theorem assumes it as a hypothesis or proves it.

### 4b. The published results assumed

Each is a `def … : Prop` in `NieWeiOrientedSidorenko/Literature.lean`. Its docstring gives the exact
source, the version checked, and every modelling choice. The labels A1–A9 are the ones the
formalization's records use.

| label | Lean (Literature.lean line) | source |
|---|---|---|
| A1 | `LovaszProp544cHyp` (:191) | L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Prop. 5.44(c): finitely many pairwise nonisomorphic graphs without isolated vertices have linearly independent homomorphism-density functions (a nonsingular matrix [t(F_i, G_j)]) |
| A9 | `LovaszProp142aHyp` (:304) | Lovász (as A1), Prop. 14.2(a): even cycles are norming (on symmetric kernels) |
| A2 | `DGHRRCor324Hyp` (:214) | M. Doležal, J. Grebík, J. Hladký, I. Rocha, V. Rozhoň, *Cut distance identifying graphon parameters over weak\* limits*, J. Combin. Theory Ser. A 189 (2022) 105615, Cor. 3.24: weakly norming graphs (symmetric convention) are step Sidorenko |
| A3 | `DGHRRThm325Hyp` (:231) | DGHRR (as A2), Thm 3.25 with Thm 2.14: a connected step-Sidorenko graph with an edge is weakly norming (symmetric convention, seminorm) |
| A5 | `DGHRRFact217Hyp` (:271) | DGHRR (as A2), Fact 2.17, from the companion paper (J. Combin. Theory Ser. B 147 (2021), Lemma 4.2(b)): W^𝒫 lies in the envelope ⟨W⟩ |
| A5 | `DGHRRFact218Hyp` (:288) | DGHRR (as A2), Fact 2.18, from the companion paper's Cor. 4.24: for U ⪯ W, ⟨W⟩ ⊆ ⟨U⟩ if and only if δ_□(U, W) = 0 (the conditional form) |
| A4 | `LeeSidorenkoThm13Hyp` (:252) | J. Lee and A. Sidorenko, *On graph norms for complex-valued functions*, J. London Math. Soc. 106(2) (2022) 1501–1538, Thm 1.3 (weakly norming half): for connected bipartite graphs the symmetric and full-kernel conventions of weak norming agree |
| FRHSU | `FRHSUThm43Hyp` (:325) | V. Falgas-Ravry, R. Hancock, J. Strömberg, A. Uzzell, J. Graph Theory 104(1) (2023) 104–132, Thm 4.3: the space of [k]-graphons modulo δ_{□_k} = 0 is compact |
| FHMZ | `FHMZThm13Hyp` (:342) | J. Fox, Z. Himwich, N. Mani, Y. Zhou, *A note on directed analogues of the Sidorenko and forcing conjectures*, Electron. J. Combin. 32(3) (2025) #P3.38, Thm 13 (oriented part): finite oriented graphs approximate a digraphon W with W(x,y) + W(y,x) ≤ 1 in cut distance |
| FHMZ | `FHMZThm18Hyp` (:355) | FHMZ (as above), Thm 18 (oriented part): the counting lemma \|t(B, W) − t(B, U)\| ≤ e(B) δ_□(U, W) |
| FHMZ | `FHMZCompactHyp` (:371) | FHMZ (as above), unnumbered assertion on p. 6, stated there without proof: digraphons modulo cut distance zero form a compact space |

The Lean wording of A1, as an example of how they read:

```lean
def LovaszProp544cHyp.{u} : Prop :=
  ∀ (k : ℕ) (V : Fin k → Type u) [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (F : ∀ i, SimpleGraph (V i)),
    (∀ i j, i ≠ j → IsEmpty (F i ≃g F j)) →
    (∀ i (v : V i), ∃ w, (F i).Adj v w) →
    ∃ (W : Fin k → Type u) (hW : ∀ j, Fintype (W j)) (G : ∀ j, SimpleGraph (W j)),
      (Matrix.of fun i j => @simpleHomDensity (V i) (W j) _ (hW j) (F i) (G j)).det ≠ 0
```

The others are at the lines given. The published sources state these for kernels and graphons
symmetric at every point; the passages to the manuscript's almost-everywhere conventions, and every
other reduction around these results, are proved in Lean. Two of them (FRHSU and the FHMZ p. 6
assertion) assume compactness of a quotient with the topology generated by cut-distance balls; Lean
proves, with no hypothesis, that each is equivalent to the published compactness of the metric
space obtained by identifying distance zero (`KCompactId.frhsu_iff_published`,
`KCompactId.fhmzCompactHyp_iff_published`).

## 5. What has and has not been reviewed

- **The kernel check and the axiom check** are mechanical and reproducible by anyone with the
  commands of section 2. The independent kernel replay is reported in section 2.
- **Faithfulness of the statements** (part 1 of section 1) is a human judgement. During the
  formalization, separate Claude instances (each given a single criterion and no access to the
  others' reviews) compared the Lean statements with the paper in ten completed review rounds. Each
  statement was checked for four things: it means what its description says; it is the paper's
  result, no weaker and no stronger; its hypotheses can be satisfied; it is not trivial or
  repackaged. The wording of each of the 11 assumed published results was also compared with its
  source as quoted to the reviewers. These reviewers are instances of the same AI model that wrote
  the code, so they are not independent in the way a human referee is. No review for overlap with
  Mathlib (prior art) was run.
- **Approval of the statements by people.**
  - **Fan Wei approved the statements of the 55 rows reviewed at Checkpoint B** (every definition
    and numbered result of the manuscript, and the authors' additions except the two finite-host
    rows). The record has her approval of 12 November 2026 as relayed by Runtian Zhou, and her own
    words in the final-delivery answers of 13 November 2026: "I now approve all Checkpoint B
    statements. This approval covers the 55 indexed statement rows as presented in the Checkpoint B
    record."
  - **Runtian Zhou approved the two finite-host rows** (`lemma_6_1_finite`, `thm_4_1_finite`) on
    13 November 2026: "I approve them. And add it in the final delivery report for fan to read."
    The approval relied on Fan Wei's §2, which calls such forms "equivalent formal presentations of the same
    approved assertions, not additional mathematical claims". **Fan Wei has not yet checked these
    two rows herself.** Each follows in one line from its approved digraphon form and a proved
    bridge, with no new assumption.
  - A mechanical freeze check confirms that none of the 133 approved Lean statements has changed
    since its approval.
- **Three independent audits.** Besides the review rounds, three read-only audits by separate
  Claude sessions examined the delivered Lean at three stages (before the K pass, after it, and at
  the final commit). None found a blocking problem. The first found one condition of Checkpoint B
  (identifying the formal compactness hypotheses with the published ones) not yet proved; it was
  then proved (the equivalences named at the end of section 4b). These audits are also AI reviews.
- **Disclosed limits.** A reader should know these:
  - **Numbering of two sources.** The printed numbering of Lee–Sidorenko (J. London Math. Soc.) and
    of the printed AMS edition of Lovász's book was not verified. The checked versions are cited:
    Lee–Sidorenko, arXiv:2101.12145v2, Theorem 1.3; Lovász, the author's near-final manuscript.
  - **Cut distances.** That the Lean cut distances (`cutDistMap`, `kCutDist`) are FHMZ's
    Definition 12 and FRHSU's §4.1 rests on the reviewers' comparison, not on a proof.
  - **About the assumed results.** The FHMZ p. 6 assertion has no proof in its source. The directed
    forms of FHMZ Theorems 13 and 18 are adaptations that neither FHMZ nor Lovász proves. No Lean
    check shows the 11 hypotheses consistent as worded.
  - **No unconditional example of a cut distance identifying parameter** was built. The one example,
    t(C₄, ·), comes from Theorem 1.4 and so rests on the assumed results.
  - **Unused hypotheses are kept**, at the authors' request (final-delivery answers, §1): DGHRR
    Fact 2.17 in Theorem 1.4 (unused) and in its two other forms and Corollary 1.5 (forwarded only);
    Facts 2.17, 2.18 and FRHSU in B4(i); FHMZ Thm 13 in the finite forms of Theorems 1.1 and 1.7;
    the FHMZ p. 6 assertion in the finite form of Proposition 1.12; condition (a) of Theorem 4.1;
    the range of θ in Lemma 6.1. None is needed by its proof.
  - **Steps of proofs by contradiction.** Five auxiliary lemmas, inside the proofs of Theorem 1.10,
    Proposition 1.12, Lemma 2.3 and Lemma 4.2, have hypotheses that can never all hold, by design;
    their docstrings say so. No result of the paper is vacuous, assuming the cited results are true
    as worded.
  - **166 deferred findings** of the statement-strength review, on auxiliary helper lemmas
    (duplicate, forwarding or idle helpers), were deferred and not repaired. None touches a stated
    result, a hypothesis, a definition or a main theorem.
  - **Proof routes.** The Lean proofs were not compared with the manuscript's proofs step by step. A
    Lean proof certifies the statement, not the manuscript's written argument.
  - **A process stop (S3).** One review notice in the formalization's record lacks the two Lean names
    `OrientedGraph.lemma_6_1_finite` and `OrientedGraph.thm_4_1_finite`, after an edit that broke the
    record's ownership rule was reverted; Runtian Zhou asked that it stay as it is. It does not
    affect any Lean statement or proof.
  - **Record provenance.** The workflow's checks show that its records agree with each other and with
    the Lean; they cannot show who wrote each record.
- **Intermediate results.** `NieWeiOrientedSidorenko/Main.lean` lists every result with its Lean
  names. Some proofs take a different route from the paper's (56 recorded places, each of the same
  strength as the paper's statement). The detailed formalization report, the sign-off sheet and the
  decision record are available from the authors on request.

## 6. All numbered results

Status "proved" means: stated in Lean and proved, with no `sorry` and standard axioms only.
"Assuming X" means the statement takes the published result X as an explicit hypothesis (section
4b). "Finite" and "kernel" are the finite-host and digraphon forms (section 3). Definitions are
"defined". The 21 unnumbered definitions the manuscript introduces in its text are listed with their
Lean names in `NieWeiOrientedSidorenko/Main.lean`.

| Paper | Lean | Status |
|---|---|---|
| Conjecture 1 | `SidorenkoForcingConjecture` | stated only (a conjecture): neither assumed nor proved |
| Definition 1 | `OrientedGraph.IsOS`, `OrientedGraph.IsOAS` | defined |
| Definition 2 | `OrientedGraph.IsSymmetryForcing` | defined |
| Definition 3 | `OrientedGraph.Dt` | defined |
| Question 1(c), OS bridge | `OrientedGraph.isOS_iff_isOSK` | proved |
| Question 1(c), OAS bridge | `OrientedGraph.isOAS_iff_isOASK` | proved |
| Question 1(c), symmetry-forcing bridge | `OrientedGraph.isSymmetryForcing_iff_isSymmetryForcingK` | proved, assuming FHMZ Thms 13, 18 and the p. 6 assertion |
| Theorem 1.1 | `OrientedGraph.thm_1_1`, `OrientedGraph.thm_1_1_kernel` | proved, assuming Lovász 5.44(c), 14.2(a) and Lee–Sidorenko; the finite form also the three FHMZ items (Thm 13 not needed) |
| Theorem 1.2 | `OrientedGraph.thm_1_2`, `OrientedGraph.thm_1_2_kernel` | proved, assuming Lovász 5.44(c) |
| Theorem 1.3 | `OrientedGraph.thm_1_3`, `OrientedGraph.thm_1_3_kernel` | proved, assuming Lovász 5.44(c); the finite form also the three FHMZ items |
| Theorem 1.4 | `thm_1_4` | proved, assuming DGHRR Cor. 3.24, Facts 2.17 (unused) and 2.18, FRHSU |
| Theorem 1.4, every-bipartition reading | `thm_1_4_every_bipartition` | proved (corollary of `thm_1_4`), same assumptions |
| Theorem 1.4, B1 (connected, symmetric convention) | `thm_1_4_symm` | proved, same assumptions plus Lee–Sidorenko |
| Corollary 1.5 | `cor_1_5` | proved, assuming DGHRR Cor. 3.24, Thm 3.25, Facts 2.17 (forwarded only) and 2.18, Lee–Sidorenko, FRHSU |
| Theorem 1.6 | `thm_1_6` | proved |
| Theorem 1.7 | `OrientedGraph.thm_1_7`, `OrientedGraph.thm_1_7_kernel` | proved; the finite form assuming the three FHMZ items (Thm 13 not needed), the kernel form with no assumption |
| Proposition 1.8 | `OrientedGraph.prop_1_8`, `OrientedGraph.prop_1_8_kernel` | proved |
| Theorem 1.9 | `OrientedGraph.thm_1_9`, `OrientedGraph.thm_1_9_kernel` | proved, assuming Lovász 5.44(c) |
| Theorem 1.10 | `OrientedGraph.thm_1_10`, `OrientedGraph.thm_1_10_kernel` | proved, assuming Lovász 5.44(c) |
| Theorem 1.11 | `OrientedGraph.thm_1_11`, `OrientedGraph.thm_1_11_kernel` | proved, assuming Lovász 5.44(c), 14.2(a) and Lee–Sidorenko |
| Proposition 1.12 | `OrientedGraph.prop_1_12`, `OrientedGraph.prop_1_12_kernel` | proved; the finite form assuming FHMZ Thms 13, 18 (the p. 6 assertion carried, not needed), the kernel form with no assumption |
| B4(i), K₂,₃ weakly norming, step forcing, not norming | `k23_weaklyNorming_stepForcing_not_norming` | proved, assuming DGHRR Cor. 3.24 (Facts 2.17, 2.18 and FRHSU carried, unused) |
| B4(i), K₂,₃ not norming in the symmetric convention | `k23_not_norming_symm` | proved |
| B4(ii), OS iff step Sidorenko | `OrientedGraph.isOS_iff_isStepSidorenko` | proved, assuming Lovász 5.44(c), DGHRR Cor. 3.24 and Thm 3.25, Lee–Sidorenko |
| Claim 2.1 | `claim_2_1` | proved |
| Lemma 2.2 | `lemma_2_2` | proved |
| Lemma 2.3 | `lemma_2_3_1`, `lemma_2_3_2` (its parts 1 and 2) | proved |
| Theorem 4.1 | `OrientedGraph.thm_4_1` | proved (condition (a) unused) |
| Theorem 4.1, finite hosts | `OrientedGraph.thm_4_1_finite` | proved; approved by Runtian Zhou, not yet by Fan Wei |
| Lemma 4.2 | `OrientedGraph.lemma_4_2` | proved |
| Lemma 4.3 | `OrientedGraph.lemma_4_3` | proved, assuming Lovász 5.44(c) |
| Lemma 4.4 | `OrientedGraph.lemma_4_4` | proved, assuming Lovász 5.44(c) |
| Lemma 4.5 | `OrientedGraph.lemma_4_5` | proved, assuming Lovász 5.44(c) |
| Lemma 4.6 | `lemma_4_6` | proved |
| Lemma 6.1 | `OrientedGraph.lemma_6_1` | proved (the range of θ unused) |
| Lemma 6.1, finite hosts | `OrientedGraph.lemma_6_1_finite` | proved; approved by Runtian Zhou, not yet by Fan Wei |

All names are in the namespace `NieWeiOrientedSidorenko`. Lemmas 4.2, 4.4 and 4.5 take as a
hypothesis the manuscript's own assumption that D is OS, and Lemma 4.3 that D is OS or OAS (in
digraphon form), as printed.

## 7. How this formalization was produced

The Lean code was written by Claude (Anthropic's AI model), running in Claude Code, under the
formalize-paper autoformalization and auditing workflow (R. Zhou and X. Tang), run here under the
direction of Runtian Zhou. The
authors' answers to the workflow's questions fixed the definitions to use, the published results that
may be assumed, and the additions to the manuscript's results. Separate Claude instances, each given
one criterion and no access to the others' reviews, audited the Lean statements against the paper and
the proofs for substance; Fan Wei approved the statements (see section 5 for what this does and does
not establish). Three further read-only audits by separate Claude sessions, and the kernel replay of
section 2, re-checked the final Lean. The formalization builds on Lean's Mathlib library.
