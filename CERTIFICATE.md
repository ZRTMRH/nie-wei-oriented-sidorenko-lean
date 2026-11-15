# Lean formalization certificate — Sidorenko Inequalities and Symmetry-Forcing for Graph Orientations (Nie, Wei)

## At a glance

**What this is.** A machine-checked formalization, in the proof assistant Lean 4 with its Mathlib
library, of J. Nie and F. Wei, "Sidorenko inequalities and symmetry-forcing for graph orientations"
(arXiv:2611.15027v1, 11 November 2026; the LaTeX source formalized is byte-identical to that arXiv version's source). The Lean code was written by an AI model
(Claude, by Anthropic). Lean's kernel, a small trusted program, checked every step of every proof.

**What is certified.**
- Every numbered definition and result of the manuscript is stated in Lean. Every theorem, lemma,
  corollary, proposition and claim is proved. Conjecture 1 is stated only; no result of the paper
  depends on it. A few additions requested by the authors are also proved (section 3).
- The proofs have no gaps (no `sorry`) and use only Lean's three standard axioms (propositional
  extensionality, choice, quotient soundness).
- Results that need a published result take it as an explicit hypothesis: the Lean theorem reads
  "if these published results hold, then …". So what is certified is that **the manuscript's results
  are correct given the cited published results**, as these are worded in Lean.

**The 11 published results assumed** (authorised by the authors; section 4b gives exact sources and
the Lean wording):
- Lovász, *Large Networks and Graph Limits*: Prop. 5.44(c) and Prop. 14.2(a);
- Doležal–Grebík–Hladký–Rocha–Rozhoň (DGHRR), J. Combin. Theory Ser. A (2022): Cor. 3.24, Thm 3.25
  (with Thm 2.14), Facts 2.17 and 2.18;
- Lee–Sidorenko, J. London Math. Soc. (2022): Thm 1.3;
- Falgas-Ravry–Hancock–Strömberg–Uzzell (FRHSU), J. Graph Theory (2023): Thm 4.3;
- Fox–Himwich–Mani–Zhou (FHMZ), Electron. J. Combin. (2025): Thms 13 and 18, and a compactness
  assertion on p. 6 that **is stated there without proof**. The directed forms of FHMZ Theorems 13
  and 18 used here are adaptations that neither FHMZ nor Lovász proves.

Which result needs which is listed in section 6. For example, Theorem 1.2 and the digraphon form of
Theorem 1.3 need only Lovász Prop. 5.44(c); the FHMZ items enter only the finite-host (sequence)
forms of the results about symmetry-forcing; Theorem 1.6, Theorem 4.1, Proposition 1.8 and Lemma 6.1
need none.

**What rests on review rather than on the machine check.**
- **That the Lean statements say what the paper says.** This is a matter of judgement, not machine
  checking. Separate AI reviewers compared every Lean statement with the paper over ten review rounds,
  and Fan Wei approved every statement (section 5). Sections 3 and 4 put each Lean statement next to
  the paper's wording, so a referee can confirm it directly.
- **That the Lean wording of the 11 assumed results matches the sources.** This was compared by the
  AI reviewers, not proved. The same holds for the Lean definitions of cut distance used by the
  assumed results. The printed numbering of two sources was not verified, and no check shows the 11
  hypotheses consistent as worded (section 5).
- **Proof routes.** Lean's kernel checks each proof in full, so each result holds whatever route its
  proof takes. The formalizer recorded 56 places where a Lean proof departs from the written argument,
  all of the same strength (Appendix A); a departure nobody recorded would not appear, since nothing
  compares the Lean proofs with the written proofs.
- The AI reviewers are instances of the same model that wrote the code; their review complements,
  but does not replace, a referee's own judgement.

**How to re-check.** In the public repository, two commands re-run the kernel check and print
the axioms each main theorem uses (section 2).

**Guide to the rest.** Section 1 explains what the certificate rests on and 1a how to read the Lean
statements; section 2 gives the commands and their results; section 3 puts the main theorems next to
the paper; section 4 does the same for the definitions, and 4b for the assumed published results;
section 5 says what was reviewed, by whom, and the disclosed limits; section 6 lists every numbered
result with its status; section 7 says how the formalization was produced.

### References, names and documents used below

- **The manuscript.** This repository follows the statements and the numbering of the manuscript's
  numbered results in its version of 11 November 2026, which is arXiv:2611.15027v1. Paper references below are to that numbering
  (Theorem 1.2, Definition 1, …) and its sections. "tex l.N" is line N of the manuscript's LaTeX
  source in that version (the source of arXiv:2611.15027v1); the manuscript itself is not in this repository. `File.lean:N` is line N of
  `NieWeiOrientedSidorenko/File.lean` in this repository.
- **The authors' answers.** The authors answered three sets of questions during the formalization.
  Where a statement comes from one of them rather than from the manuscript, this is said.
  - The **pre-run answer key**, written before the formalization: it fixed the definitions to use,
    how each earlier result is used, either assumed or proved (its items A1–A11) and the additions to the
    manuscript's results (its items Question 1(c), B1 and B4).
  - The **Checkpoint B answer key**. Checkpoint B is the point at which the authors reviewed and
    approved the Lean statements; its questions are numbered Q1–Q7.
  - The **final-delivery answers**, the authors' reply to the first delivery, in sections §1–§5.
- **People.** Fan Wei is an author of the manuscript; she approved the statements. Runtian Zhou
  directed the formalization and relayed some of Fan Wei's answers.

## 1. What the certificate rests on

A Lean formalization certifies a theorem through three things together:

1. **The statements.** The Lean statements of the main theorems, and the definitions they use, say
   what the paper says. This is the only part a person has to read, and the only part no machine
   can check (section 5 says who checked it). Sections 3 and 4 below put
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
compared with its source by the AI reviewers (section 5), not proved.

The proofs themselves (about 21,000 lines in `NieWeiOrientedSidorenko/`) need not be read. Every
definition and numbered result of the manuscript has a Lean counterpart there (listed in
`NieWeiOrientedSidorenko/Main.lean` and in section 6 below): every theorem, lemma, corollary,
proposition and claim is stated and proved, every numbered definition is defined, and Conjecture 1
is stated only (it is not proved, and no result of the paper depends on it). The authors' requested additions are also stated
and proved: the three equivalences between the finite and digraphon definitions (Question 1(c) of
the pre-run answer key), the connected symmetric-convention corollary of Theorem 1.4 (item B1), both
readings of the K₂,₃ result (item B4(i)) and the OS / step-Sidorenko equivalence (item B4(ii)), the
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

Requirements: `elan` (the Lean installer; https://github.com/leanprover/elan), and `git`.

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
- `lake build`: completes, with no `sorry` (the formalization workflow's final check before
  delivery).
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

Each entry below gives the paper's statement (quoted, with its tex line), then the Lean statement,
then its source line in this repository, then in words the assumed published results its hypotheses
name and any difference of form. In a Lean statement, the arguments named `h…` before the final
colon are the hypotheses (those named `hA1`, `h13`, … are assumed published results) and the text
after the final colon is the conclusion; section 1a explains the notation.

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
  some bipartition" (`IsWeaklyNormingGraph`), the authors' answer to Q1 of the Checkpoint B answer
  key, option (a). The
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

The finite form shown assumes Lovász Props. 5.44(c) and 14.2(a), Lee–Sidorenko Thm 1.3, and the
three FHMZ items; FHMZ Thm 13 is carried but not needed.

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

**Reading "weakly norming for every bipartition"** (kept at Checkpoint B, by the authors' choice,
as a derived corollary):

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

**The connected symmetric-convention form (item B1 of the pre-run answer key).**

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

### Addition B4(i): K₂,₃ is weakly norming and step forcing, but not norming

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

### Addition B4(ii): OS and step Sidorenko

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
  not a result: it is not proved, and no result of the paper depends on it. Two auxiliary
  bookkeeping lemmas (`KConj1.forcing_antecedent_unfold`, `KConj1.forcing_half_applies_to_witness`)
  take it as an explicit hypothesis, to record that a Lean example meets the hypotheses of its forcing
  half; no result of the paper uses them.

### 4b. The published results assumed

Each is a `def … : Prop` in `NieWeiOrientedSidorenko/Literature.lean`. Its docstring gives the exact
source, the version checked, and every modelling choice. The labels A1–A9 are those of the pre-run
answer key; A5 there covers two facts, and the missing labels A6–A8 are results proved in Lean, not
assumed. FRHSU and FHMZ are labelled by their authors' initials.

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
- **Faithfulness of the statements** (part 1 of section 1) is a matter of judgement, made by AI
  reviewers and by the authors, not a machine check. During the formalization, separate Claude instances (each given a single criterion and no access to the
  others' reviews) compared the Lean statements with the paper in ten completed review rounds (in each round every reviewer examined the then-current Lean). Each
  statement was checked for four things: it means what its description says; it is the paper's
  result, no weaker and no stronger; its hypotheses can be satisfied; it is not trivial or
  repackaged. The wording of each of the 11 assumed published results was also compared with its
  source as quoted to the reviewers. These reviewers are instances of the same AI model that wrote
  the code, so they are not independent in the way a human referee is. No review for overlap with
  Mathlib (prior art) was run.
- **Approval of the statements by people.**
  - **Fan Wei approved the statements of the 55 rows (entries of the statement index) reviewed at
    Checkpoint B** (every definition
    and numbered result of the manuscript, and the authors' additions except the two finite-host
    rows). The record has her approval of 12 November 2026 as relayed by Runtian Zhou, and her own
    words in the final-delivery answers of 13 November 2026: "I now approve all Checkpoint B
    statements. This approval covers the 55 indexed statement rows as presented in the Checkpoint B
    record."
  - **Runtian Zhou approved the two finite-host rows** (`lemma_6_1_finite`, `thm_4_1_finite`) on
    13 November 2026: "I approve them. And add it in the final delivery report for fan to read."
    The approval relied on Fan Wei's §2, which calls such forms "equivalent formal presentations of the same
    approved assertions, not additional mathematical claims". Each follows in one line from its
    approved digraphon form and a proved bridge, with no new assumption.
  - **Fan Wei approved the two finite-host rows herself** on 14 November 2026 (relayed by Runtian
    Zhou, who confirms she adopted the text as her own reply): "The two finite-host statements agree
    with my intended statements, and I approve them. They are equivalent formulations of the original
    results, not additional theorems." Runtian Zhou's approval of 13 November stays recorded as his.
    Her reply "should not be used to infer any earlier approval dates or communications", and the
    record infers none.
  - **Two readings of auxiliary definitions**, settled by the formalizing agent, were agreed by Fan
    Wei on 14 November 2026 "under the stated preconditions":
    - `Section1Aux.symmVersion U` (the symmetric version of a kernel U) is an almost-everywhere-equal
      version of U only when U is symmetric almost everywhere, i.e. a graphon (`symmVersion_spec`);
    - `Section1Aux.sideOG H s` (the orientation of H from the side s) is an orientation of H, with
      underlying graph H, only when s is a bipartition of H (`sideOG_underlying`).
    The Lean uses each only under its precondition.
  - An automatic comparison of each approved Lean statement with a fingerprint recorded at its
    approval confirms that none of the 133 approved Lean statements has changed since.
- **Three independent audits.** Besides the review rounds, three read-only audits by separate
  Claude sessions examined the delivered Lean at three stages (before the final work on the authors' sign-off
  requirements, after it, and at the final commit). None found a blocking problem (one that had to be fixed before delivery). The first found one condition of Checkpoint B
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
    t(C₄, ·), comes from Theorem 1.4 and so rests on the assumed results. Fan Wei did not request one
    (14 November 2026): "please retain the existing conditional witness and accurately disclose that
    the unconditional example was not built."
  - **Review rounds.** No further review round was run after the final commit because the
    formalization workflow's limit on the number of review rounds was reached. Fan Wei clarified (14 November 2026) that her earlier
    instruction against another review round "applied only to removing or generalizing the six
    retained items. It was not a blanket instruction against further necessary review." The six
    items are the unused hypotheses of the next point.
  - **Unused hypotheses are kept**, at the authors' request (final-delivery answers, §1): DGHRR
    Fact 2.17 in Theorem 1.4 (unused) and in its two other forms and Corollary 1.5 (forwarded only);
    Facts 2.17, 2.18 and FRHSU in B4(i); FHMZ Thm 13 in the finite forms of Theorems 1.1 and 1.7;
    the FHMZ p. 6 assertion in the finite form of Proposition 1.12; condition (a) of Theorem 4.1;
    the range of θ in Lemma 6.1. None is needed by its proof.
  - **Steps of proofs by contradiction.** Five auxiliary lemmas, inside the proofs of Theorem 1.10,
    Proposition 1.12, Lemma 2.3 and Lemma 4.2, have hypotheses that can never all hold, by design;
    their docstrings say so. No result of the paper is vacuous, assuming the cited results are true
    as worded.
  - **166 deferred findings** of the AI review for statement strength, on auxiliary helper lemmas
    (duplicate, forwarding or idle helpers), were deferred and not repaired. None touches a stated
    result, a hypothesis, a definition or a main theorem.
  - **Proof routes.** The formalizer recorded 56 departures from the written argument, all of the
    same strength (Appendix A); a departure nobody recorded would not appear, since nothing compares
    the Lean proofs with the written proofs.
  - **An incomplete record entry.** One notice in the formalization's internal record lacks the two
    Lean names `OrientedGraph.lemma_6_1_finite` and `OrientedGraph.thm_4_1_finite`. An edit
    restoring them was reverted because it broke the record's rule on who may change that file;
    Runtian Zhou asked that the notice stay as it is. It does not affect any Lean statement or
    proof.
  - **Record provenance.** The formalization workflow's checks show that its records agree with each other and with
    the Lean; they cannot show who wrote each record.
- **Intermediate results.** `NieWeiOrientedSidorenko/Main.lean` lists every result with its Lean
  names. Some proofs take a different route from the paper's (56 recorded places, each of the same
  strength as the paper's statement; Appendix A lists them). The detailed formalization report, the sign-off sheet and the
  decision record are available from the authors on request.

## 6. All numbered results

Status "proved" means: stated in Lean and proved, with no `sorry` and standard axioms only.
"Assuming X" means the statement takes the published result X as an explicit hypothesis (section
4b). "Finite" and "kernel" are the finite-host and digraphon forms (section 3). Definitions are
"defined". The 21 unnumbered definitions the manuscript introduces in its text are listed with their
Lean names in `NieWeiOrientedSidorenko/Main.lean`.

| Paper | Lean | Status |
|---|---|---|
| Conjecture 1 | `SidorenkoForcingConjecture` | stated only (a conjecture): not proved; no result of the paper depends on it (two auxiliary bookkeeping lemmas take it as a hypothesis) |
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
| Theorem 4.1, finite hosts | `OrientedGraph.thm_4_1_finite` | proved; approved by Runtian Zhou (13 November 2026) and by Fan Wei (14 November 2026) |
| Lemma 4.2 | `OrientedGraph.lemma_4_2` | proved |
| Lemma 4.3 | `OrientedGraph.lemma_4_3` | proved, assuming Lovász 5.44(c) |
| Lemma 4.4 | `OrientedGraph.lemma_4_4` | proved, assuming Lovász 5.44(c) |
| Lemma 4.5 | `OrientedGraph.lemma_4_5` | proved, assuming Lovász 5.44(c) |
| Lemma 4.6 | `lemma_4_6` | proved |
| Lemma 6.1 | `OrientedGraph.lemma_6_1` | proved (the range of θ unused) |
| Lemma 6.1, finite hosts | `OrientedGraph.lemma_6_1_finite` | proved; approved by Runtian Zhou (13 November 2026) and by Fan Wei (14 November 2026) |

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

## Appendix A. Recorded proof-route changes

Lean's kernel checks every proof in full, so each result holds whatever route its proof takes. The workflow requires the formalizer to record each place where a Lean proof departs from the paper's argument, at the time it makes the change. The adjudicator (an independent reviewer) then checked that the project declarations each recorded change cites exist, and moved the changes into this table. All 56 recorded changes are of the same strength: none weakens a statement. Some supply a step that the paper states without proof or cites; others take an alternative route or a different encoding. Routes are recorded, not compared automatically: a departure nobody recorded would not appear here. "Answer key" and "KEY" (in the table) refer to the pre-run answer key of section 1, written before the formalization; its items A1–A11 fix which earlier results are assumed or proved. It is not part of the paper. The table is copied unchanged from the formalization report.

| # | result | the paper's route | the lean route | why different | kind |
|---|---|---|---|---|---|
| 1 | Lemma 6.1, kernels | Expands `W_{ε,θ}` and `S_{ε,θ}` separately, each as `½(1 + a e^{2πi(x-y)} + ā e^{-2πi(x-y)})`. | One family `testK c φ = ½ + c cos(2π(x-y)+φ)`; `W = testK ε θ`, `S = symmetrize W = testK (ε cos θ) 0` (`symmetrize_testK`); one expansion `t_testK` serves both. | Avoids duplicating the expansion. | same strength |
| 2 | Lemma 6.1, orthogonality | "By orthogonality … the integral is nonzero precisely when σ is a circulation; then it equals 1." | The product over arcs is rewritten as a product over vertices of `exp(2πi·flow_v·x_v)` (`prod_termC`, `sum_flow_mul`), then Fubini over `Measure.pi` (`integral_fintype_prod_eq_prod`) and `integral_exp_int`. | Formal proof of the orthogonality claim. | same strength |
| 3 | Lemma 6.1, "every nonzero circulation contains a cycle in its support" | Stated without proof. | A vertex with exactly one support edge has nonzero net flow (`circ_exists_cycle`); a nonempty edge set with no degree-one vertex contains a cycle (`exists_cycle_of_no_leaf`, via a longest path in the acyclic case, `exists_leaf`). | Fills in the step. | same strength |
| 4 | Lemma 6.1, "a circulation with support of size g is supported on a cycle in 𝒞_g, with exactly two possibilities" | Stated without proof. | `Phi_mem_cycles` (support = edge set of a girth cycle, by cardinality); `circ_eq_sigW`: along the cycle walk, flow conservation at each vertex (which has exactly two cycle neighbours, `ncard_neighborSet_toSubgraph_eq_two`) forces the dart values to be constant, so the circulation is `± sigW w`; `sigW_mem_Circ`, `Phi_sigW`, `sum_sigW` give that `± sigW w` are circulations with that support and imbalance `± ω(w)`. | Fills in the step. | same strength |
| 5 | Lemma 6.1, ε → 0 | `t = 2^{-m}(1 + 2ε^g Σ … + O_D(ε^{g+1}))`, divide by `ε^g` and let ε → 0. | `coeff_nonneg`: if `0 ≤ Σ_i ε^{k_i} a_i` for all small ε > 0 and all `k_i ≥ g`, then `Σ_{k_i = g} a_i ≥ 0`, with an explicit ε (no asymptotic notation). The `σ = 0` term is cancelled exactly (it equals `1 - 1`). | Explicit version of the limit. | same strength |
| 6 | Lemma 6.1, choice of cyclic direction | Remark (tex l.1360-1365) that `cos(ω_D(C)θ)` does not depend on the chosen direction. | `cosImbalance_eq_of_isCycle`: for every cycle walk with edge set `C`, `cosImbalance θ C = cos(ω(w)θ)`, proved via `circ_eq_sigW` (two traversals of `C` give circulations with the same support, equal up to sign) rather than via explicit rotation/reversal of walks. | The circulation-uniqueness lemma was already needed; it gives independence of the start vertex and direction at once. | same strength |
| 7 | Lemma 2.2 | cites Hatami (answer key A6: tensor-power argument) | tensor-power argument: for normalized nonnegative decorations, `t ≤ t(H, Σ g_e) ≤ m^m` by the triangle inequality; the tensor square is transported to `[0,1]` by a measurable measure-preserving map `φ : I → I × I` (not a bijection), giving `t^(2^k) ≤ m^m` for all `k`; normalisation by `‖U_e‖ + ε`, `ε → 0`, avoids the zero-norm case | the paper gives no proof; the answer key prescribes the tensor-power argument | same strength |
| 8 | Lemma 2.3(1), converse | triangle inequality after normalising by `p = N(U)`, `q = N(V)` for nonzero `U, V`; zero case "trivially" | normalise by `p = N(U) + ε/2`, `q = N(V) + ε/2` and let `ε → 0`, so no zero-kernel case split (and no a.e.-invariance of `t_bi`) is needed | avoids a separate a.e. argument | same strength |
| 9 | Lemma 2.3(2), norming ⇒ every vertex has even degree, `F ≥ 0` | even degrees via the product test kernel `f(x)f(y)`; then `F ≥ 0` by continuity along the segment from `W` to `1` | only `m = e(H)` even is derived (not every degree): if `m` were odd, `F(-1) = -1 < 0 < 1 = F(1)` and the intermediate value theorem along `-1 → K` or `K → 1`, `K(x,y) = x`, gives a non-zero kernel with `F = 0`; then `F ≥ 0` along `W → 1` as in the paper | the parity of `m` is all the proof uses; it avoids computing the density of a product kernel | same strength |
| 10 | Lemma 2.3(2), the norming Hölder inequality used for Hatami's inequality | cites Hatami (proof of Thm 2.16) / answer key A8: "establish the full-kernel norming Hölder inequality" | proved: polarization `Σ_ε (∏ε) t(H, Σ ε_e ψ_e) = Σ_φ c_φ t(H; ψ∘φ)` with `c_φ ≥ 0`, `c_id = 2^m`, applied to `2^{k+1}`-fold transported tensor powers (all terms then nonnegative), giving `\|t(H;f)\|^{2^{k+1}} ≤ m^m` | paper gives no proof | same strength |
| 11 | Lemma 2.3(2), Hatami's inequality | `F(U+V)+F(U−V) ≤ 2^{m−1}(F(U)+F(V))` via Hölder, weighted AM–GM and even-binomial sums | `F(U+V)+F(U−V) ≤ (u+v)^m + (u−v)^m` (`u = ‖U‖_H`, `v = ‖V‖_H`) via Hölder only; strict midpoint convexity then splits: `u ≠ v` by strict convexity of `x^m`; `u = v` from this inequality and `F(U−V) > 0` | avoids AM–GM and binomial-sum identities; the form proved is what the strict-convexity step needs | same strength |
| 12 | Claim 2.1, stepping the doubled host | "stepping the doubled host gives `S(W)/2`, up to measure-preserving relabelling" | proved pointwise: `stepAvg 𝒬_W (W ⊕ W^T)` equals `S(W)/2` read in the `[0,1]` coordinates (independent of the copy label), by computing each block integral; then the copy labels are integrated out | no relabelling needed in this encoding | same strength |
| 13 | Claim 2.1, converse, tensor power | `W^{⊗k}` on a product space identified with `[0,1]`, Jensen for `x^k`, `k`-th roots, `k → ∞` | only tensor squares, transported by a measurable measure-preserving map `φ : I → I × I` (not a bijection) to a step digraphon on `[0,1]` with `k²` positive-measure parts; Cauchy–Schwarz `(Σ_F x_F)^2 ≤ 2^m Σ_F x_F^2` in place of Jensen; iterating gives `t(D,S(W))^{2^j} ≤ C t(D,W)^{2^j}` for all `j` | squares suffice and avoid identifying `[0,1]^k` with `[0,1]` | same strength |
| 14 | Claim 2.1, converse, approximation | "approximation in `L¹` extends it to all digraphons" | a digraphon is `L¹`-approximated by a bounded continuous function (Mathlib), clamped to `[0,1]`, then sampled on the grid of `n + 1` equal intervals (uniform continuity); `\|t(D,A) − t(D,B)\| ≤ e(D) ‖A − B‖₁` for `[0,1]`-valued kernels and `‖S(A) − S(B)‖₁ ≤ ‖A − B‖₁` | the paper gives no construction | same strength |
| 15 | lemma_4_2 | host W given as "a digraph or digraphon"; counterexample hosts: directed edge, acyclic orientation of G, non-acyclic orientation of a minimal homomorphic-image subgraph C of G | each host is a finite oriented graph H turned into the 0/1 step digraphon on the equipartition (`hostKer`); `t(D,W_H)=0` pointwise and `t(D,(W_H+W_H^T)/2)>0` on a positive-measure box (`not_isOSK_of_host`). The core C is the image K of a graph endomorphism of G with fewest image vertices, G[K] is non-bipartite hence has a cycle, H orients that cycle cyclically and other edges of G[K] by a vertex order | IsOSK is stated for digraphons on [0,1], so the finite host must be realised as a digraphon; "minimal subgraph" replaced by the equivalent minimal-image endomorphism, and the acyclicity contradiction is run through a ranking pulled back along the restricted automorphism | same strength |
| 16 | lemma_4_5 | host space split into two parts of measure 1/2 carrying the block kernel [[0,U],[V^T,0]] | the block kernel lives on `twoCopies` ([0,1] x Bool), and is pulled back to [0,1] along the measure-preserving (not bijective) split map `halfSplit`; densities over `twoCopies` are computed by averaging over the 2^n copy labellings, only the two side labellings surviving by connectivity | IsOSK quantifies over kernels on [0,1] only, so the two-part host must be realised there; a measure-preserving map suffices for densities | same strength |
| 17 | lemma_4_5 | "midpoint convexity [and continuity of the polynomial s ↦ F((1-s)U+sV)] implies convexity" | continuity via dominated convergence (`continuousOn_of_dominated`), then a dyadic induction and a floor-approximation limit (`convex_of_midpoint`) | the paper leaves the standard real-analysis step implicit | same strength |
| 18 | lemma_4_4 | every automorphism g of `\bar` D from Lemma 4.3 swaps the two sides | only the automorphism attached to one arc is used; it swaps sides because it sends a tail to a head, and a proper 2-colouring of a connected graph is determined up to swap (`flip_walk`) | the paper's "any such automorphism" is more than needed | same strength |
| 19 | lemma_4_3 | for an arbitrary graphon S, perturb W_ε=(S+εU)/2 with U built from rooted densities of a double star R (pendant leaves at u and w); f_S'(0)=0 gives Σ_e t(D_e,S)=Σ_e t(D_{e^T},S) for all graphons S; Lovász 5.44(c) then gives equal multiplicities | S is taken to be the step graphon of an arbitrary finite simple graph G only (the Lovász test graphs), so W_ε is a step digraphon whose density is a finite sum (`t_stepK`), and the derivative is that of a polynomial; the gadgets are cliques K_{v+1}, K_{2v+1} glued at a root (v=\|V\|) instead of the double star's pendant leaves | Lovász's hypothesis (A1, as stated) is about finite test graphs, so finite hosts suffice; clique gadgets make all new vertices have degree v or 2v, which no old vertex has, so the isomorphism D_e ≅ D_{f(e)^T} maps V to V without the paper's "permute pendant leaves" repair step | same strength |
| 20 | lemma_4_3 | "each isomorphism class occurs with the same multiplicity ... consequently there is a bijection f" | classes are a `Quotient` of `arcs ⊕ arcs` by isomorphism; Lovász's matrix is used through `Matrix.eq_zero_of_vecMul_eq_zero`; the bijection is `Equiv.ofFiberEquiv` of fibrewise `Fintype.equivOfCardEq` | the multiset-to-bijection step is left implicit in the paper | same strength |
| 21 | lemma_4_6 | sign-lift space Ω=[0,1]×{±1}; convexity of Φ on Ω-kernels | Ω is `twoCopies` ([0,1]×Bool); every density over Ω is pulled back to [0,1] along the measure-preserving `halfSplit` (`tBi_eq_tb_pb`), and the convexity steps are run through the triangle inequality and homogeneity of the weak norm r(H) of `hE` (`rNorm_sum_le`, `tb_le_tBi_lift`) instead of convexity of Φ | the hypothesis hE is the full-kernel norm on [0,1]; the norm inequalities give exactly the convex-combination bounds needed | same strength |
| 22 | lemma_4_6 | rectangular step functions h_n → h in L¹ with ‖h_n‖∞ ≤ ‖h‖∞, then (eq kernel-L1-continuity) | only h = sgn A is needed: {A>0}, {A<0} are approximated in measure by finite unions of measurable rectangles (Mathlib `exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring` for the semiring of rectangles), whose indicators are rectangular step functions (`GridRep`), rewritten as combinations of sign products (`gridRep_comb`); the L¹ continuity is an explicit Lipschitz bound (`tBi_lift_lipschitz`) | the general-h claim (5.4) is not needed; the bound replaces the cited continuity estimate | same strength |
| 23 | lemma_4_6 | "expanding the edge product and averaging the signs leaves the even edge sets; a cycle's edge set is even" | the sign average is computed as a character sum over X ⊕ Y (`charSum_eq`, nonnegative, 1 on even sets); only the two terms F=∅ and F=edge set of a cycle are kept; evenness of a cycle's edge set from Mathlib's `IsTrail.even_countP_edges_iff` | the paper keeps all even sets but uses only these two | same strength |
| 24 | thm_1_2 (sufficiency) | Theorem 4.1 applied directly, with "the" bipartition of `\bar` D | the weakly norming bipartition `s` of `IsWeaklyNormingGraph` either agrees with the one-direction side `A` (connectivity) or is its complement; in the second case it is pulled back along the isomorphism `D ≅ D^T` to a bipartition with arcs from the first part to the second, using invariance of weak norming under relabelling (`exists_side`) | the Lean `IsWeaklyNormingGraph` is existential over bipartitions, while Theorem 4.1(c) fixes the side containing the tails | same strength |
| 25 | thm_1_3 (forests are not symmetry-forcing) | 3×3 step digraphon with row/column sums 1/2, "integrating out leaves" | test kernel `testK (1/2) (π/2) = 1/2 + ½cos(2π(x−y)+π/2)`, whose symmetrization is the constant 1/2; both densities equal 2^{-e(D)} by the Fourier formula `t_testK` of Section 6 (only the zero circulation survives on a forest); non-symmetry on a positive-measure rectangle | reuses a proved Fourier expansion instead of a leaf induction | same strength |
| 26 | thm_1_6 (strictly convex ⇒ contains a cycle) | kernels 1/2 ± ¼ f(x)f(y), leaf integration | kernels `testK (±1/2) 0`, densities 2^{-e} through `tb_eq_t_bipOG` and `t_testK` | as row 2 | same strength |
| 27 | thm_1_6 (strictly convex ⇒ convex) | "it is convex" | the a.e.-equal case `U = V` a.e. is handled by a.e. invariance of `t_bi` (`tb_congr_ae`) | the Lean strict convexity only covers non-a.e.-equal pairs | same strength |
| 28 | thm_1_3 (cycle ⇒ symmetry-forcing) | `t(D,W) = t_bi(H,W) = t_bi(H,W^T)` and Theorem 1.6 | same, with the bipartition from `exists_side`, `t_eq_tb_side`, `t_transpose_of_iso`, and the cycle transported to `bipGraph` by an injective homomorphism | — | same strength |
| 29 | thm_1_9 (stars) | "conditioning on the image of c" | Fubini split at the centre (`integral_split`, `t_center`) | formal detail | same strength |
| 30 | k23_not_norming_symm | odd-degree obstruction with a test kernel f(x)f(y) | f(x) = 2x − 1, `t(K_{2,3}, f⊗f) = (∫f³)²(∫f²)³ = 0` while f⊗f > 0 on [3/4,1]² | concrete instance of the cited argument | same strength |
| 31 | cor_1_5 (forests are not step forcing) | kernel 1/2 + ¼ f(x)f(y), one-part partition, leaf integration | `testK (1/2) 0` (an everywhere-symmetric graphon) with the one-part partition; its average is 1/2 = `testK 0 0`, and both densities are 2^{-e} via an orientation of H (`orientOut`) and `t_testK` | as row 2 | same strength |
| 32 | cor_1_5, isOS_iff_isStepSidorenko (step Sidorenko ⇒ weakly norming) | "DGHRR show that a connected step Sidorenko graph is weakly norming" | A3 gives the seminorm; definiteness (needed by A4, which asks for a norm) is proved from step Sidorenko with the one-part partition; bipartiteness (needed by A4) is proved from step Sidorenko with the half/half bipartite graphon; then A4. A.e.-symmetric ↔ everywhere-symmetric graphons via `symmVersion` | the hypotheses A3/A4 are stated in the symmetric seminorm/norm conventions | same strength |
| 33 | isOS_iff_isStepSidorenko (weakly norming ⇒ step Sidorenko) | "every weakly norming graph has the step Sidorenko property" | full-kernel weak norming of a bipartition ⇒ symmetric seminorm (`weakNormFn_eq_rNorm`, via the orientation `sideOG` and `t_eq_tb_side`), then A2 | conventions differ | same strength |
| 34 | `isOS_iff_isOSK`, `isOAS_iff_isOASK` (finite to kernel) | answer key: sample uniform `X_1..X_n`, orient each pair randomly with probabilities `q(X_i,X_j)`, `q(X_j,X_i)` (`q = W/2`), take expectations; injective maps exact, noninjective ones at most `1-(n)_v/n^v`; limit; homogeneity | the same argument, with the orientation randomness written as a finite weighted sum over codes `c : Fin n × Fin n → Fin 3` (product weights, `Fintype.prod_sum`) and the sampling as the integral over `[0,1]^n`; the limit uses `(n+1-v)^v ≤ (n)_v ≤ n^v` | an expectation over a finite product space is written as a finite sum | same strength |
| 35 | `isSymmetryForcing_iff_isSymmetryForcingK` (kernel → sequence) | answer key: compactness of the directed cut-distance quotient, with `Δ_D` and `a(W) = ‖W - W^T‖_□`, bounds `\|Δ_D(U)-Δ_D(V)\| ≤ 2m δ`, `\|a(U)-a(V)\| ≤ 2δ`, subsequence contradiction | `Δ_D` as in the key; in place of `a`, the functional `c(W) = t_bi(C₄, W - W^T)`, expanded as a signed sum of the densities of the 16 orientations of `C₄`, so `\|c(U) - c(V)\| ≤ (Σ e) δ` by FHMZ Theorem 18; for finite hosts `c(W_G) ≥ ε⁴` whenever `\|e(A,B)-e(B,A)\| > εN²` (discrete Cauchy–Schwarz), and `c(W) = 0` when `W = W^T` a.e.; a cluster point in the compact quotient (not a subsequence) gives `W` with `Δ_D(W) = 0`, `c(W) ≥ ε⁴`, contradicting kernel symmetry-forcing | `a(U) - a(V) ≤ 2δ(U,V)` holds only one way for maps (`‖F^φ‖_□ ≥ ‖F‖_□`), and without the triangle inequality for `δ_□^{map}` (not assumed) `a` is not shown constant on `δ = 0` classes, so it does not descend to the quotient; `c` is two-sided Lipschitz from Theorem 18. The quotient topology need not be first countable, hence cluster points | same strength |
| 36 | `isSymmetryForcing_iff_isSymmetryForcingK` (sequence → kernel) | answer key: approximate `W/2` by finite oriented graphs (FHMZ Theorem 13), blow up so the orders tend to infinity, recover the digraphon condition | same; graphs with no vertex are first replaced by a one-vertex arcless graph (same step digraphon), `k`-fold blow-ups have the same step digraphon pointwise and `k²` times the discrepancies; the symmetry of `W/2` is recovered from its rectangle integrals (pulled-back step asymmetry bounded through cell masses) and the π–λ rectangle lemma | details the key leaves implicit | same strength |
| 37 | `isSymmetryForcing_iff_isSymmetryForcingK` (quasirandom ⇒ `Δ → 0`) | answer key: orientation discrepancy is `a(W_G)` (extrema on unions of cells), plus counting | same: `‖W_G - sym W_G‖_□ ≤ max\|e(A,B)-e(B,A)\|/(2N²)` (bilinear extremes on cell masses), then `δ_□^{map} ≤ ‖·‖_□` (identity map) and FHMZ Theorem 18 | — | same strength |
| 38 | `thm_1_4` (step forcing half) | Cut distance identification implies step forcing: `W ≠ W^𝒫` gives `W^𝒫 ≺ W` (DGHRR §3.1), then `t(H, W^𝒫) < t(H, W)` (tex l.1100-1102) | Directly from strict convexity of `t_bi` (`Section1Aux.thm16_forward`) and step Sidorenko (A2): with `Q = W^𝒫`, `M = (W + Q)/2` one has `M^𝒫 = Q`, so `t(Q) ≤ t(M) < (t(W) + t(Q))/2` (`S1CutDist.stepForcing_of_wn`) | avoids the envelope facts and `W^𝒫 ≺ W` (whose proof needs Fact 2.17 plus transitivity of envelopes); uses only hypotheses already in the statement | same strength |
| 39 | `thm_1_4` (gap (eq:cut-convexity-gap)) | Contradiction with a sequence of pairs; simultaneous weak-regularity compactness gives a subsequence and common bijections `ψ_k` with cut-norm convergence; counting lemma; strict convexity (tex l.1035-1058; answer key A11: FRHSU multicolour compactness with the four-colour encoding) | FRHSU Theorem 4.3 (k = 4) used as stated (compact quotient): the gap functional `Φ(P) = gap(U_P, V_P)` and `M(P) = t_bi(K_{2,2}, U_P − V_P)` of the decoded pair `U_P = P₁₁+P₁₀`, `V_P = P₁₁+P₀₁` are shown continuous for `kCutTopology 4` and constant on `δ_{□,4} = 0` (counting lemma + pullback invariance), so descend to the compact quotient; `Φ` attains a positive minimum on the closed set `{M ≥ ε⁴}` (strict convexity); `‖U − V‖_□ ≥ ε ⇒ M(enc(U,V)) ≥ ε⁴` (`cutNorm_pow4_le`) (`gap_lemma`) | a sequential extraction from the FRHSU quotient would need `δ_{□,4}` to be a pseudometric (symmetry and triangle inequality for map-based distances), which is not part of the hypothesis; the open-cover/minimum argument needs only continuity of invariant functionals. `‖U−V‖_□ ≥ ε` is replaced by the invariant `t(K_{2,2}, U−V) ≥ ε⁴` inside the compactness argument | same strength |
| 40 | `thm_1_4` (weak* lsc (eq:weak-star-lsc)) | Step Sidorenko for `Z_n^𝒫`, `Z_n^𝒫 → Z^𝒫` in L¹, then successively finer dyadic partitions with `Z^𝒫 → Z` in L¹ | Same, but with grid partitions `gridPart n` chosen per ε: `‖Z^𝒫 − Z‖₁ ≤ 2‖Z − G‖₁` for the grid step approximation `G` of `Section2Aux.exists_grid_approx` (L¹ contraction of stepping); stated as "`t(Z_n) ≤ c` for all `n` ⇒ `t(Z) ≤ c`" (`tU_le_of_weakStar`) | avoids martingale convergence; the bounded form is all the proof uses | same strength |
| 41 | `thm_1_4` (`δ_□(U,W) > 0` from `U ≺ W`) | "equality of envelopes is equivalent to zero cut distance" (DGHRR) | Fact 2.18 (`hF218`) applied to everywhere-symmetric versions `symmVersion U`, `symmVersion W`; envelopes, cut distance and densities are shown invariant under a.e. modification (`envelope_congr`, `cutDist_congr`, `tU_congr_ae`) | the hypothesis is stated for everywhere-symmetric graphons, the result for a.e.-symmetric ones | same strength |
| 42 | `k23_weaklyNorming_stepForcing_not_norming` (weakly norming) | Not proved in the paper (Table 1 / Hatami: complete bipartite graphs are weakly norming) | Direct proof: `t(K_{2,3}, f) = ∫ G_f(a,b)^3` with `G_{f,g}(a,b) = ∫ f(a,y) g(b,y) dy`; triangle inequality from Minkowski in `L³` (`mink3`) and Cauchy–Schwarz `Gen(f,g)² ≤ Gen(f,f) Gen(g,g)` (`Gen_cs`, via `Gen = ∫ F_f F_g`); homogeneity and definiteness from `Section2Aux` | paper gives no proof | same strength |
| 43 | `k23_weaklyNorming_stepForcing_not_norming` (not norming) | Odd-degree obstruction (Hatami: norming graphs have even degrees) | For each bipartition `s`, a full-kernel norm `‖·‖_{H,s}` restricts on everywhere-symmetric kernels to `\|t(K_{2,3}, ·)\|^{1/6}`, contradicting `Section1Aux.k23_not_norming_symm'` (test kernel `(2x-1)(2y-1)`, where degree 3 gives `∫(2x-1)^3 = 0`) | reuses the proved symmetric-convention lemma | same strength |
| 44 | `k23_weaklyNorming_stepForcing_not_norming` (step forcing) | From Theorem 1.4 | From the step forcing half of Theorem 1.4 only (row 1); the hypotheses `hF217`, `hF218`, `hFR` are unused | the cut distance half is not needed | same strength |
| 45 | Theorem 1.11 (OS half) | Theorem 1.2: one-direction forces an alternating even cycle; "every such orientation is self-converse with a weakly norming underlying graph" | Theorem 1.2 (`osk_char`); self-converse by an explicit rotation of the cycle by one step; weak norming from A9 (Lovász Prop. 14.2(a)) by norming ⇒ weakly norming (symmetric convention) and A4 (Lee–Sidorenko Thm 1.3), as KEY A9 prescribes | the paper leaves the self-converse and weak-norming facts unproved | same strength |
| 46 | Theorem 1.11 (OAS half, necessity) | Lemma 6.1 gives cos(ωθ) ≤ cos^g θ; ω ≥ 3 excluded by θ = 2π/ω; ω² ≥ g by the θ → 0 expansion; then g = 4, ω = 2 | Lemma 6.1 with the same inequality; ω ≥ 3 by θ = 2π/ω; the cases ω = 0, 1, 2 excluded (unless g = 4, ω = 2) by the explicit values θ = π/2, π/3, π/6 instead of the θ → 0 asymptotics; the girth, the girth cycle set and "up to isomorphism this is O₁" proved combinatorially (finite check on the 16 orientations of C₄) | avoids a Taylor-expansion limit argument | same strength |
| 47 | Theorem 1.11 (OAS half, sufficiency) and Theorem 1.1 (O₁) | Griffiths' theorem cited | KEY A10: t(O₁,W) = t(O₁,S) − t_bi(C₄,A) proved as a pointwise identity over the 16 orientations of C₄ plus 8 dihedral relabellings; t_bi(C₄,A) = ∫∫(∫A(x,y)A(x',y)dy)² ≥ 0; vanishing ⇒ ∫_B A(·,y) = 0 a.e. for every measurable B ⇒ A integrates to 0 on rectangles ⇒ A = 0 a.e. (π-system uniqueness, `ae_eq_of_setLIntegral_prod_eq`) | the paper cites Griffiths (finite form only); the key prescribes a digraphon proof | same strength |
| 48 | Theorem 1.1 (O₂) | Griffiths' theorem cited | O₂ is an alternating even oriented cycle: OS by row 1, symmetry-forcing by Theorem 1.3 (`thm13k`), as KEY A10 prescribes | — | same strength |
| 49 | Theorem 1.10 (not OS, ≥ 3 edges) | Theorem 1.2 + "weakly norming bipartite graphs are biregular" (Hatami Thm 2.10(ii)) | Theorem 1.2 (`osk_char`) + KEY A7 proved from Lemma 2.2 with the decoration 1_{x ≤ 1/2} on the edges at one vertex (deg(v)·\|X\| ≤ e(H) for each v on a side, hence equality), applied on whichever side holds the vertices 0 and 2 of the path (sides swapped by `wn_swap`) | the paper cites Hatami | same strength |
| 50 | Theorem 1.10 (1 and 2 edges) | Theorem 1.9 (stars) | the same: the path is a star with centre an end vertex / the middle vertex; "in = out at the centre ⇔ ≅ 1→2→3" by a finite check | — | same strength |
| 51 | Theorem 1.10 (not OAS, ≥ 3 edges) | Lemma 4.3 + automorphisms of the path give the palindrome (4); WLOG (0,1) ∈ E; the 3-block step digraphon with entries 1, ε³, ε²; "terms of degree < 6 read from block assignments", t(P,W) = 3^{-(n+1)}(1+ε³+ε⁵) + O(ε⁶), t(P,S) = 3^{-(n+1)}(1+ε³+ε⁵/2) + O(ε⁶) | Lemma 4.3 + the values of a path automorphism at 0, 1, 2 give the arcs at the far end (only those used); WLOG by transposition; same step digraphons; W-side: lower bound by three explicit assignments (all other terms ≥ 0); S-side: S is symmetric, so the sum is 1ᵀS^N1, bounded by an exact transfer-vector induction: S^k1 = (1+δ+δη, δ, δη) + error with 0 ≤ error ≤ (2^k−1)ε⁶ (δ = ε³/2, η = ε²/2), for k ≥ 3; explicit ε = 1/(12·2^N) | makes the O(ε⁶) remainder explicit; uses only the end arcs | same strength |
| 52 | `prop_1_12_kernel` | Family `W_p` (rescaled `W₊` on `[0,p]²`, rescaled `W₋` on `(p,1]²`, 0 off-diagonal); `p ↦ Δ(W_p)` is a polynomial, hence continuous; IVT gives `p₀` with `Δ(W_{p₀}) = 0`, and `W_{p₀}` is not symmetric. | Fix a measure-preserving `φ : [0,1] → [0,1]²` and block kernels `blk K K'` (`K'` where both `φ₂`-coordinates are `≤ 1/2`, `K` elsewhere, read at the `φ₁`-coordinates). `blk K K` has the same `Δ` as `K` (measure-preserving pull-back). Path `blk W₋ W₋ → blk W₊ W₋ → blk W₊ W₊` of two straight segments, each with one diagonal block fixed at a non-symmetric `W±`, so all points are non-symmetric (positive-measure block argument); `Δ` is Lipschitz along segments (L¹ bound); IVT on whichever segment `Δ` changes sign on. | Avoids proving the polynomial (component-factorisation) formula for `t(D, W_p)` and the change of variables for the rescalings; continuity comes from the L¹ bound instead. Same conclusion, same IVT idea. | same strength |
| 53 | `prop_1_12` | (stated with Definition 2; the paper proves it in digraphon language) | kernel form plus the proved bridges `isSymmetryForcing_iff_isSymmetryForcingK_proof` (with the binders `h13 h18 hcpt`), `isOS_iff_isOSK_proof`, `isOAS_iff_isOASK_proof`. | the paper uses the equivalence of the two definitions implicitly | same strength |
| 54 | thm_1_7_kernel (symmetry-forcing half) | Test (Dt-sf2) against `f(x_1)f(x_2)` for `f` in the countable family of dyadic indicators; one null set; density of dyadic step functions in `L²` gives `A(·,y) = 0` a.e. where `∫S(·,y) > 0`; `0 ≤ \|A\| ≤ S` where `∫S(·,y) = 0`. | Test against `f = 1_S` for every measurable `S`; get `(∫_S A(·,y))·m(y)^{t-2} = 0` for a.e. `y`; integrate against `1_T` to show every rectangle integral of `F(s,y) = (W - W^T)(s,y) m(y)^{t-2}` vanishes, hence `F = 0` a.e. (π-system of rectangles, `S1Bridges.ae_zero_of_rect`); on `{m = 0}` a Fubini argument gives `W = 0` a.e. there. | Avoids building the dyadic family and the `L²` density argument; uses the available rectangle-determination lemma. | same strength |
| 55 | thm_1_7, prop_1_8 (finite forms) | Proved directly in digraphon language (the paper's definitions are identified). | Proved in the kernel form, then transferred by the Question 1(c) bridges `S1Bridges.isOAS_iff_isOASK_proof` and `S1Bridges.isSymmetryForcing_iff_isSymmetryForcingK_proof` (the latter uses the binders h13, h18, hcpt). | The formal statement uses the finite/sequence definitions of Definitions 1-2. | same strength |
| 56 | prop_1_8, prop_1_8_kernel | `D̃_2` on vertices `u_1, u_2, v_ε`. | `D̃_2` on `Fin 2 ⊕ (Fin 2 → Bool)`, relabelled to `Fin n` (`n = 6`) along `Fintype.equivFin`, with `t` invariant under relabelling (`t_relabel`). | The statement asks for a graph on `Fin n`. | same strength |
