# Sidorenko Inequalities and Symmetry-Forcing for Graph Orientations — Lean 4 formalization

A Lean 4 / Mathlib formalization of J. Nie and F. Wei, "Sidorenko inequalities and symmetry-forcing
for graph orientations", an unpublished manuscript. It follows the numbering and statements of the
manuscript's **version of 11 November 2026**.

Every definition and numbered result of the manuscript has a Lean counterpart. Definitions 1–3 and
the 21 unnumbered definitions the manuscript introduces in its text are defined. Theorems 1.1–1.4,
1.6, 1.7, 1.9–1.11 and 4.1, Lemmas 2.2, 2.3, 4.2–4.6 and 6.1, Propositions 1.8 and 1.12,
Corollary 1.5 and Claim 2.1 are stated and proved, with no `sorry` and only Lean's standard axioms.
Conjecture 1 is stated only, as a conjecture should be: it is not proved, and no result of the manuscript depends on it. Where the
manuscript states a result with finite host graphs (Definitions 1 and 2) and uses the equivalent
digraphon form of Section 2, both forms are proved. Also stated and proved, at the authors' request:
- the three Question 1(c) bridges: OS, OAS and symmetry-forcing in the finite (or sequence)
  definitions are equivalent to the digraphon definitions;
- the B1 corollary: Theorem 1.4 for connected graphs weakly norming in the symmetric convention;
- B4(i), in both readings of "not norming": K₂,₃ is weakly norming and step forcing but not norming;
- B4(ii): a connected one-direction orientation D ≅ Dᵀ with at least one arc is OS if and only if its
  underlying graph is step Sidorenko;
- Theorem 1.4 for graphs weakly norming for every bipartition, as a corollary;
- the finite-host forms of Lemma 6.1 and Theorem 4.1.

Some proofs rely on published results that the authors authorised as assumptions. Each of these 11
results enters as an explicit, named hypothesis of every statement that uses it, never as an axiom
(`NieWeiOrientedSidorenko/Literature.lean`, with the exact source in each docstring):
- Lovász, *Large Networks and Graph Limits*, Propositions 5.44(c) and 14.2(a);
- Doležal–Grebík–Hladký–Rocha–Rozhoň (DGHRR), Corollary 3.24, Theorem 3.25 (with Theorem 2.14),
  Facts 2.17 and 2.18;
- Lee–Sidorenko, Theorem 1.3;
- Falgas-Ravry–Hancock–Strömberg–Uzzell (FRHSU), Theorem 4.3;
- Fox–Himwich–Mani–Zhou (FHMZ), Theorems 13 and 18, and an unnumbered compactness assertion on p. 6.

- **Start here:** [`CERTIFICATE.md`](CERTIFICATE.md). It explains what certifies the proofs and how to
  re-check them. It shows the main statements and definitions next to the manuscript's wording, with
  a guide to the Lean notation for readers who do not know Lean. It also lists every numbered result
  with its Lean name, its status and the published results it assumes.
- `Certificate.lean`: the main results restated in full (26 statements), plus the axiom check.
- `NieWeiOrientedSidorenko/`: the formalization; `NieWeiOrientedSidorenko/Main.lean` maps each
  result of the manuscript to its Lean names.

Check:

```
lake exe cache get
lake build
lake env lean Certificate.lean
```

and, optionally, an independent kernel replay of each module with Lean's checker, for example
`lake env leanchecker NieWeiOrientedSidorenko.Section4` (one module at a time; each needs about
6 GB of memory).

Lean `v4.35.0`; Mathlib commit `ccbef15ebdb41c2addfac682131f83c75904c3c1`, pinned through Tau Ceti
commit `5a01f5fe3621126cccf9ba22e700493cbc7b7156` (`lakefile.toml`, `lake-manifest.json`).

**Status (14 November 2026).** `lake build` completes with no `sorry`. Every listed result depends
only on `propext`, `Classical.choice` and `Quot.sound`, or on a subset of them. `leanchecker`
accepted all 29 modules that contain declarations. The statements were compared with the manuscript
by AI reviewers. Fan Wei approved the statements of the 55 rows reviewed at the statement
checkpoint. Runtian Zhou approved the two finite-host rows (Lemma 6.1 and Theorem 4.1 for finite
hosts) on 13 November 2026, on the basis of Fan Wei's clarification that such forms are "equivalent
formal presentations of the same approved assertions"; Fan Wei approved them herself on 14 November
2026 ("The two finite-host statements agree with my intended statements, and I approve them"). She
also agreed to two readings of auxiliary definitions under their stated preconditions, and did not
request an unconditional example of a cut-distance-identifying parameter (none was built; the
conditional example t(C₄, ·) is kept). Conjecture 1 is not proved, and no result of the manuscript
depends on it. The Level K(ii) qualification stands: every result is proved under policy (ii), the
authorised published assumptions listed above being explicit hypotheses, and its Lean-side conditions
are met at Lean commit `091c6b2e456e81a92221d58ae554c46dd0988578`. See `CERTIFICATE.md`, section 5.

This formalization was produced with the formalize-paper workflow (Claude, Anthropic's AI model, in
Claude Code, directed by Runtian Zhou).

## Confidentiality

This is a private repository. The manuscript it formalizes is unpublished and is not included here.
All rights are reserved by the authors; no license is granted. Please do not copy or redistribute
this repository or its contents without the authors' permission.
