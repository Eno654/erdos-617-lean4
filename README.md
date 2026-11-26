# Erdős Problem #617 — Zero-Dependency Lean 4 Formalization (Prime `r^2` & `r = 3` on $K_{10}$)

[![CI](https://github.com/Eno654/erdos-617-lean4/actions/workflows/ci.yml/badge.svg)](https://github.com/Eno654/erdos-617-lean4/actions/workflows/ci.yml)
[![Palomar Registry](https://img.shields.io/badge/Palomar-PALOMAR--2026--11--26--000042%20v1-blue)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000042&version=1)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24553466.svg)](https://doi.org/10.5281/zenodo.24553466)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0005--7733--7079-A6CE39)](https://orcid.org/0009-0005-7733-7079)

Standalone, **zero-dependency** (no Mathlib required), **zero-`sorry`**, **zero-custom-axiom** Lean 4 (`v4.36.0`) formal proofs for two theorems of P. Erdős and A. Gyárfás (*"Split and balanced colorings of complete graphs"*, Discrete Mathematics 200, 1999, pp. 79–86) associated with [Erdős Problem #617](https://www.erdosproblems.com/617).

Author: **Cristian George Anuta** ([ORCID 0009-0005-7733-7079](https://orcid.org/0009-0005-7733-7079))  
*Developed using **Gemini 4 Neon** together with [**OXYO.si**](https://oxyo.si), an independent neuro-symbolic reasoning system developed by the author since March 22, 2026.*

This repository follows the [Palomar Registry](https://palomar-registry.org/) layout (`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`) for independent verification and submission via [https://submit.palomar-registry.org/](https://submit.palomar-registry.org/).

## Verified Theorems (`Challenge.lean` ↔ `Solution.lean`)

| Declaration | Mathematical Statement | Proof Technique | Axioms |
| :--- | :--- | :--- | :--- |
| `Erdos617.erdos_617_variants_r2_every_prime` | For **every prime** $p$, $K_{p^2}$ admits a symmetric balanced $p$-coloring (every $(p+1)$-subset hits all $p$ colors) | Pigeonhole surjectivity mod $p$ + affine-plane $AG(2,p)$ slope coloring | `[propext, Quot.sound, Classical.choice]` |
| `Erdos617.erdos_617_variants_r2` | For every $N$, there exists a prime $p \ge N$ such that $K_{p^2}$ admits a symmetric balanced $p$-coloring | Euclid's infinitude of primes + `erdos_617_variants_r2_every_prime` | `[propext, Quot.sound, Classical.choice]` |
| `Erdos617.erdos_617_variants_r_eq_3` | Every symmetric 3-coloring of $K_{10}$ has a 4-vertex subset missing at least one color | Single-color extremal Book Proof: sparsest color class $G_k$ has $2\|E(G_k)\| \le 30$, $\alpha(G_k) \le 3$, and is diamond-free; $\delta \in \{0,1,2\}$ eliminated by neighborhood bounds and $\delta = 3$ (3-regular) eliminated via $6 \nmid 20$ triangle double-counting + $K_3 \sqcup K_3$ independent 4-set | `[propext, Quot.sound, Classical.choice]` |

## Repository Map

- `Challenge.lean` — Compact, zero-custom-definition statement surface audited by human readers and `lake comparator`.
- `Solution.lean` — Exports the proved theorems matching `Challenge.lean` verbatim.
- `Erdos617/R2.lean` — Complete proof of `erdos_617_variants_r2_every_prime` and `erdos_617_variants_r2` (Euclid primes, list pigeonhole, affine-plane $AG(2,p)$ coloring).
- `Erdos617/R3.lean` — Complete single-color diamond-free extremal Book Proof of `erdos_617_variants_r_eq_3`.
- `comparator.json` — Configuration for `lake comparator` (`propext`, `Quot.sound`, `Classical.choice`).
- `formalization.yaml` — Machine-readable metadata (`v0.4` schema).
- `scripts/check-lean-sources.py` & `scripts/verify-comparator.sh` — Preflight source checks and Palomar Comparator runner.

## Quick Local Verification (< 10 seconds)

Because this development has **zero external Lean dependencies**, anyone with `elan` / Lean `v4.36.0` can build and verify the entire proof in seconds:

```bash
python3 scripts/check-lean-sources.py
lake build
```

On Linux (or in GitHub Actions CI), run Palomar's full independent kernel replay (`lake comparator` with `nanoda_bin` and `con-ron`):

```bash
./scripts/verify-comparator.sh
```

## License

Apache License 2.0 (see `LICENSE`).
