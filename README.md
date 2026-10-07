# Endpoint Coordinate

[![Lean build](https://github.com/pawelmalmyga-ai/EndpointCoordinate/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/pawelmalmyga-ai/EndpointCoordinate/actions/workflows/lean_action_ci.yml)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23221388.svg)](https://doi.org/10.5281/zenodo.23221388)

Lean 4 formalization of an exponentially weighted endpoint coordinate for time
series, its exact finite-path geometry, its log-odds transform, and selected
probabilistic scaling results.

The construction begins with the distance between the current observation and
a matched exponential mean. RSI appears only later, as a directional-mass
representation of the same bounded coordinate.

## Main idea

Let `X_t` be a time series and let `M_t` be its exponentially weighted mean
with gain `alpha`. Let `S_t` be the exponentially weighted signed increment
and `A_t` the exponentially weighted absolute increment, both using the same
gain. The formalization proves the exact matched-recursion identity

```text
X_t - M_t = ((1 - alpha) / alpha) S_t.
```

Since `|S_t| <= A_t`, the normalized directional balance

```text
F_t = S_t / A_t
```

lies in `[-1, 1]`. For the Wilder gain `alpha = 1/n`, the normalized
displacement from the mean therefore satisfies the deterministic bound

```text
-(n - 1) <= (X_t - M_t) / A_t <= n - 1.
```

After positive and negative directional masses are introduced, the same
coordinate becomes

```text
RSI / 100 = (1 + F_t) / 2,
```

and hence

```text
logit(RSI / 100)
  = log((1 + F_t) / (1 - F_t))
  = 2 * artanh(F_t).
```

These identities are finite-path and distribution-free. Probabilistic
assumptions enter only in the later variance, limit-law, and calibration
layers.

The repository also proves that the positive and negative masses obtained by
the classical Wilder recursion have, along every finite path, exactly the
signed difference and total activity used in the endpoint construction. Thus
the RSI identity is connected to the recursive `up`/`down` calculation, rather
than only to masses reconstructed algebraically from `(S, A)`.

## Verification boundary

The project uses three different sources of assurance. They are deliberately
kept separate.

| Layer | What is checked | What is not established |
| --- | --- | --- |
| Lean kernel | The declarations in `EndpointCoordinate/*.lean` follow from the assumptions visible in their types | Empirical validity of those assumptions; analytic claims absent from the theorem types |
| SymPy audit | Exact formal-series and coefficient calculations in `supplement/moment_expansion_audit.py` | Analytic remainder estimates, localization, or a theorem about the variance of the full nonlinear coordinate |
| Conventional technical note | The heavy-tail argument in `supplement/Student_t_First_Shift_Note.tex` | Verification by the Lean kernel |
| Numerical normality audit | Reproducible synthetic simulations, exported diagnostics, figures, and quality checks in `supplement/normality_audit/` | Exact finite-`n` Gaussianity, empirical validity for market data, or kernel verification |
| Price-path robustness audit | Classical price RSI under exponentiated symmetric log returns, compared with the additive log-price benchmark in `supplement/price_path_normality_audit/` | A theorem for multiplicative price models, a fitted market model, or proof of finite-sample normality |

Within the Lean layer, the project separates exact algebraic geometry from
stochastic modeling assumptions.

### 1. Deterministic core

- preservation of the endpoint identity under matched EMA recursions;
- preservation of `|S| <= A`;
- finite-path bounds `+/- (n - 1)`;
- reconstruction of positive and negative directional masses;
- finite-path equivalence with the recursively smoothed classical Wilder
  `up`/`down` masses;
- the affine correspondence between `F` and RSI;
- exact log-odds, logit, and `2 * artanh` identities;
- explicit tracking of initialization error.

### 2. Exponential-weight geometry

- Wilder weights sum to one;
- their squared energy is exactly `1 / (2n - 1)`;
- the exact Kish effective length is `2n - 1`;
- finite and infinite weighted-sum variance identities.

### 3. Asymptotic transfer

- `logOdds(x) ~ 2x` near equilibrium;
- deterministic and distributional delta transfers;
- effective-length normalization using `sqrt(2n - 1)`.

### 4. Law benchmarks and a finite-variance linear-row CLT

- exact finite-row Gaussian laws;
- Laplace characteristic-function products and their triangular-array limit;
- algebraic identities and special values for the defined Student-t scale and
  finite-`n` shift formulas;
- a finite-variance CLT for an effective-length-normalized finite weighted row,
  requiring independent, identically distributed, centered innovations with
  finite variance, but no fourth-moment assumption;
- an explicit hypothesis that the omitted geometric variance tends to zero.

The source currently contains 250 named theorem declarations and no
`sorry`, `admit`, or project-defined axioms.

### Three related but distinct stochastic objects

| Object | Location | Status |
| --- | --- | --- |
| Finite-path state `(X, M, S, A)` and classical recursive `up`/`down` masses | `Core.lean` | Kernel checked |
| `sqrt(2n-1) * sum_{k < count(n)} w_{n,k} epsilon_k` with vanishing omitted squared-weight mass | `FiniteVarianceCLT.lean` | Kernel checked |
| Infinite-past nonlinear log-odds coordinate `L_alpha = 2 * artanh(x / (1+y))` and its variance expansion | `supplement/` | Exact symbolic coefficient check plus a conventional analytic proof; not a Lean theorem |

The theorem `finiteVarianceWilderRow_clt` concerns the second object. It is not
by itself a CLT for the bounded endpoint coordinate or its log-odds transform.
The log-odds results in `CLT.lean` are conditional transfer theorems: they apply
once convergence of an appropriate bounded input coordinate has been supplied.

The truncation hypothesis in `finiteVarianceWilderRow_clt` is substantive. If
`count(n) = n`, then

```text
(1 - 1/(n+1))^(2n) -> exp(-2),
```

so the hypothesis does not hold. Longer truncations can approximate the
infinite-past smoother, but no particular choice such as `ceil(n log n)` is
instantiated as a separate theorem in the present Lean source.

Likewise, `firstVarianceShift`, `secondVarianceCoefficient`, and
`studentFirstVarianceShift` are definitions whose algebraic consequences and
special values are checked in Lean. Lean does not prove that these definitions
are coefficients in an asymptotic expansion of `Var(L_alpha)`.

For a theorem-by-theorem guide, see
[FORMALIZATION.md](FORMALIZATION.md).

## Repository structure

| Module | Role |
| --- | --- |
| `EndpointCoordinate/Core.lean` | Exact finite-path, distribution-free geometry; classical Wilder recursion; RSI and log-odds bridge |
| `EndpointCoordinate/Probability.lean` | Exponential kernel, exact weight energy, effective length, and finite variances |
| `EndpointCoordinate/Stationary.lean` | Infinite-past smoother, tail energy, Lindeberg weights, and law-dependent constants |
| `EndpointCoordinate/Asymptotics.lean` | Local calculus and deterministic log-odds transfer |
| `EndpointCoordinate/CLT.lean` | Weak-convergence transfer through log-odds |
| `EndpointCoordinate/Gaussian.lean` | Exact Gaussian finite-row benchmark and limit |
| `EndpointCoordinate/Laplace.lean` | Laplace characteristic-function benchmark and Levy bridge |
| `EndpointCoordinate/TriangularArray.lean` | Product-limit proof closing the Laplace triangular-array CLT |
| `EndpointCoordinate/Student.lean` | Student-t scale and moment-profile interfaces; algebra of the defined first-shift formula |
| `EndpointCoordinate/FiniteVarianceCLT.lean` | Finite-variance CLT for normalized linear Wilder rows and a Student-profile specialization |
| `EndpointCoordinate.lean` | Root module importing the complete formalization |

The import order is deliberately layered:

```text
Core
  -> Probability
  -> Stationary
  -> Asymptotics
  -> CLT
  -> Gaussian
  -> Laplace
  -> TriangularArray
  -> Student
  -> FiniteVarianceCLT
```

## Build and verification

The Lean toolchain and Mathlib revision are pinned by `lean-toolchain` and
`lake-manifest.json`.

### From a fresh clone

```bash
git clone https://github.com/pawelmalmyga-ai/EndpointCoordinate.git
cd EndpointCoordinate
lake exe cache get
lake build
```

A successful verification ends with:

```text
Build completed successfully
```

The GitHub Actions workflow runs the Lean build, checks the source tree for
proof placeholders, and runs the pinned SymPy audit after each push.

## Manuscript

The repository includes the current manuscript in both source and compiled
form:

- [Endpoint Coordinates and Wilder's Log-Odds RSI (PDF)](manuscript/Endpoint_Coordinate_Formalized.pdf)
- [LaTeX source](manuscript/Endpoint_Coordinate_Formalized.tex)

The manuscript distinguishes conventional mathematical arguments from the
subset represented by Lean declarations. In particular, the Lean development
checks the finite linear-row CLT and conditional log-odds transfer separately;
the full stationary nonlinear log-odds limit, Berry--Esseen argument, and
higher-order analytic remainder estimates remain conventional proofs.

For an arXiv submission or journal citation, use an immutable release tag and
commit hash rather than the moving `main` branch.

## Numerical normality audit

A separate computational supplement examines finite-lookback Gaussian
approximation after the asymptotic and law-specific variance corrections:

- [Numerical Normality Audit (PDF)](supplement/normality_audit/Numerical_Normality_Audit.pdf)
- [Reproduction guide and data inventory](supplement/normality_audit/README.md)

The audit evaluates Gaussian, Laplace, and standardized Student-t innovations
across twelve lookbacks. It includes the generating code, pinned dependencies,
aggregate diagnostics, representative draws, tables, figures, and a
machine-readable quality report. These are reproducible synthetic experiments,
not Lean theorems and not tests on financial-market data.

## Price-path robustness audit

A second computational supplement addresses the distinction between an
additive input and a classical multiplicative price path:

- [Price-Path Normality Audit (PDF)](supplement/price_path_normality_audit/Price_Path_Normality_Audit.pdf)
- [Reproduction guide and data inventory](supplement/price_path_normality_audit/README.md)

For each synthetic experiment, symmetric Gaussian, Laplace, or standardized
Student-t log returns are generated and exponentiated into a price series that
starts at 10,000. Classical RSI is then calculated from ordinary arithmetic
price changes. The same path is processed as log-price increments to provide
the additive benchmark covered directly by the manuscript.

The design uses five log-return volatility levels, twelve lookbacks, and three
million retained observations per law-volatility pair. It exports complete summary metrics, quantile and ECDF grids, histograms,
block diagnostics, and 1.8 million representative-draw rows. The log-price
rows are repeated across volatility labels by exact scale invariance and are
not independent replications. The 46 plots are stored in both PDF and PNG
formats, giving 92 figure files. The central conclusion is
limited but useful: the manuscript normalizers remain good small-return scale
benchmarks for classical price RSI, while exponentiation produces increasing
positive skewness at larger volatility and longer lookback. Variance close to
one must not be interpreted as finite-sample Gaussianity.

## Interpretation and scope

Lean verifies that the formal conclusions follow from the stated formal
assumptions. It does **not** establish that empirical market returns are
independent, identically distributed, Gaussian, Laplace, or Student-t. It also
does not validate a trading rule, forecast, or claim of profitability.

The endpoint identities, the exact effective length `2n - 1`, and the local
derivative factor `2` are kernel-checked mathematical results. The
interpretation of a defined shift formula as a coefficient in `Var(L_alpha)`,
distribution-specific finite-`n` calibration, and practical AdaptiveRSI
settings belong to separate analytic, modeling, or empirical layers.

## Reproducibility status

- Lean 4 source is included.
- Toolchain and dependency versions are pinned.
- Automated CI configuration is included.
- The project builds without proof placeholders.
- The pinned symbolic coefficient audit is run by CI.
- The synthetic finite-lookback normality audit, its aggregate outputs, and
  representative draws are included under `supplement/normality_audit/`.
- The multiplicative price-path robustness audit, its exported diagnostics,
  representative draws, figures, metadata, and validation checks are included
  under `supplement/price_path_normality_audit/`.
- Empirical financial-market datasets and backtests remain outside this
  repository.
- A publication should cite an exact tagged repository revision rather than an
  unversioned working directory.

## Authorship and AI assistance

The underlying research problem, conceptual framework, practical
interpretation, and decisions concerning the scope and assumptions of the
project were developed and directed by **Paweł Małmyga**.

AI systems contributed substantially to the detailed derivations, proof
design, Lean implementation, debugging, organization, and documentation.
Paweł Małmyga selected and reviewed the final claims and accepts responsibility
for the published work.

Every committed theorem is mechanically checked by the Lean kernel under the
assumptions stated in its type. Kernel verification establishes derivability
from those assumptions; it does not by itself establish empirical validity,
novelty, or practical usefulness.

See [PROVENANCE.md](PROVENANCE.md) for the complete disclosure.

## Citation

Citation metadata is provided in [CITATION.cff](CITATION.cff). The preferred
paper citation is included without a DOI; the arXiv or journal identifier should
be added when it becomes available. For reproducible citation, use the `v1.0.0`
release rather than the moving `main` branch.

## License

Software source code is licensed under the MIT License. Manuscripts,
documentation, figures, tables, and published data are licensed under the
Creative Commons Attribution 4.0 International License (CC BY 4.0). See
[LICENSE](LICENSE) for the exact file-level scope and attribution guidance.

## Additional documentation

- [FORMALIZATION.md](FORMALIZATION.md) — map from mathematical claims to Lean
  declarations;
- [PROVENANCE.md](PROVENANCE.md) — authorship, AI contribution, and the scope
  of machine verification;
- [RELEASE_CHECKLIST.md](RELEASE_CHECKLIST.md) — recorded checks for the
  public `v1.0.0` release and post-publication follow-ups;
- [CHANGELOG.md](CHANGELOG.md) — documented project changes;
- [supplement/README.md](supplement/README.md) — status and reproduction
  instructions for the symbolic audit, heavy-tail technical note, and
  numerical normality audit;
- [supplement/normality_audit/README.md](supplement/normality_audit/README.md) —
  design, outputs, and reproduction instructions for the finite-lookback
  numerical normality audit;
- [supplement/price_path_normality_audit/README.md](supplement/price_path_normality_audit/README.md) —
  design, outputs, and reproduction instructions for the multiplicative
  price-path robustness audit.
