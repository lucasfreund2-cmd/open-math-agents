# A complete formalization of MSE 2822876

This directory accompanies the full Lean proof of the polynomial-ideal problem catalogued as [mse-2822876 on LeftToSolve](https://lefttosolve.com/p/mse-2822876).

The theorem says that if every pair of elements of an ideal in `ℂ[x₁, …, xₙ]` has a nonconstant common divisor, then one nonconstant polynomial divides every element of the ideal. The proof covers the whole statement, with arbitrary finite `n`, all ideal elements, and the zero ideal.

## Read the result

- [Academic formalization note (PDF)](paper.pdf)
- [Editable LaTeX source](paper.tex)
- [Complete Lean proof](../../proofs/mse-2822876.lean)
- [Exact proposed Lean statement](../../statements/mse-2822876.lean)
- [Verification record](verification.json)
- [Reproduction script](verify.sh)

The generic theorem also proves an equivalence for every ideal in a unique factorization domain: every pair has a nonzero nonunit common divisor if and only if a single prime element divides the whole ideal. Equivalently, the ideal is contained in a **nonzero** principal prime ideal.

## Mathematical contribution and attribution

The mathematical result is established prior work. This contribution supplies a complete Lean formalization, a precise translation of nonconstancy, an audit of zero and unit cases, and a reproducible verification package.

The polynomial statement appears in Hanspeter Kraft, *Basics from Algebraic Geometry*, Appendix A, Exercise 5.5.3, printed page 169, and in Leonardo Schultz's [2018 Mathematics Stack Exchange question](https://math.stackexchange.com/questions/2822876/is-there-a-non-constant-h-in-mathbbcx-1-dots-x-n-that-divides-ever). The general UFD argument appears in [Will Sawin's 2021 MathOverflow answer](https://mathoverflow.net/a/410694) and tj_'s accompanying prime-avoidance comment. The central library theorem is finite prime avoidance; a mathematical reference is [Stacks Project, tag 00DS](https://stacks.math.columbia.edu/tag/00DS).

The note is an AI-assisted academic draft prepared for Lucas Freund's repository. It has not been submitted to a journal or claimed as a new mathematical discovery. ChatGPT (GPT-6 Astra Pro) assisted with source review, Lean development, independent agent audits, and exposition.

## Site submission status

The problem had no Lean statement when this work began. [Upstream PR #5285](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5285) contains exactly the statement file and requests the site's required human translation review.

The complete proof is available in this branch. The unmodified exact-target local checker accepted it against the proposed statement, with only `propext`, `Classical.choice`, and `Quot.sound`. The statement also passed the upstream GitHub compilation check. Human translation review remains pending. The site's workflow requires the statement to be reviewed and merged before a separate proof PR. Verification details and the status snapshot are recorded in `verification.json`.

The statement file contains the single `sorry` required by the site's statement-submission protocol. The proof file contains no `sorry`. Its `OMA.solution` is pinned to the *type* of the proposed statement and does not use that statement's unproved body. The successful axiom report contains no `sorryAx`.

## Reproduce the checks

Use this repository branch with the pinned environment:

| Component | Version or commit |
| --- | --- |
| Lean | `4.33.1` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| formal-conjectures | `9097e2f90e66d2f6244209cb1c07f7120d17ec53` |

After installing the repository prerequisites, run its documented setup from the repository root:

```bash
tools/oma.sh setup
bash papers/mse-2822876/verify.sh
```

The script runs the unmodified site checker serially for the statement and proof, then asks Lean for the axiom dependencies of all four helper theorems and `OMA.solution`. It writes fresh logs and verdicts beneath `.oma/repro/mse-2822876/`. The allowed axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

The proof uses `type_of% @OMA.S_mse_2822876.main`, so the target is exactly the proposed statement. Translational fidelity remains a separate human-review question; the paper discusses the chosen conventions in detail.

An initial exact-target check exposed two import-sensitive `simp` conversions between normalized factors and their finite set. The restricted-import harness had passed, but the statement imports all of Mathlib, which adds simplification rules. The final proof uses `Multiset.mem_toFinset` explicitly at both transitions and passed the unmodified checker. This correction did not change the mathematical statement or argument. The verification record preserves the failed attempt as development history separately from the successful final result.

To rebuild the paper with a LaTeX installation:

```bash
cd papers/mse-2822876
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

## Proof idea

For a nonzero ideal, fix a nonzero element and list its finitely many irreducible factors up to association. The pairwise hypothesis puts each ideal element into at least one of the corresponding principal prime ideals. Finite prime avoidance then puts the entire ideal into a single one. For the zero ideal, the hypothesis at `(0,0)` already supplies a valid common divisor. The field-polynomial specialization uses the equivalence between positive total degree and being a nonzero nonunit.
