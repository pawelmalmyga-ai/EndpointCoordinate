# Formalization map

This document maps the mathematical claims of the endpoint-coordinate project
to named Lean declarations. It is a guide to the formal source, not a
replacement for the theorem types themselves.

## Verification boundary

The Lean formalization has three mathematical layers:

1. **Exact finite-path identities** — no probability model is used.
2. **Exact kernel and moment algebra** — probability assumptions are explicit.
3. **Limit theorems** — independence, identical distribution, moments, and
   truncation conditions appear in theorem types.

The repository also contains four non-kernel verification layers:

4. **Symbolic audit** — `supplement/moment_expansion_audit.py` checks a formal
   moment/cumulant expansion and selected specializations with pinned SymPy.
5. **Conventional technical note** —
   `supplement/Student_t_First_Shift_Note.tex` develops the analytic
   localization and remainder argument for polynomial tails.
6. **Numerical normality audit** — `supplement/normality_audit/` contains a
   reproducible finite-lookback simulation, exported diagnostics, figures, and
   machine-readable quality checks for Gaussian, Laplace, and selected
   Student-t innovation laws.
7. **Price-path robustness audit** —
   `supplement/price_path_normality_audit/` compares the additive log-price
   benchmark with classical price RSI on synthetic multiplicative paths.

Layers 4--7 are not Lean theorems. In particular, successful execution of the
Python audits does not establish an analytic remainder bound, the TeX argument
is not checked by the Lean kernel, and numerical agreement does not establish
exact finite-sample Gaussianity or empirical validity for market returns.

This separation matters: a kernel-checked theorem can be mathematically valid
without its stochastic assumptions being empirically appropriate for a
particular time series.

## 1. Deterministic endpoint geometry

File: `EndpointCoordinate/Core.lean`

| Mathematical claim | Lean declaration | Main assumptions |
| --- | --- | --- |
| Matched EMA and signed-increment recursions preserve the endpoint identity | `matched_endpoint_identity` | `alpha != 0`; previous state satisfies the identity |
| Signed movement remains dominated by absolute activity | `signedStep_abs_le_activityStep` | `0 <= alpha <= 1`; previous domination |
| Endpoint invariant is preserved along a finite path | `endpointInvariant_run` | nonzero gain; initial invariant |
| Domination invariant is preserved along a finite path | `dominanceInvariant_run` | gain in `[0,1]`; initial domination |
| Combined finite-path identity and bound | `finite_path_geometry` | matched initialization and admissible gain |
| Normalized balance lies in `[-1,1]` | `unitCoordinate_abs_le_one` | nonzero activity and `|signed| <= activity` |
| Generic endpoint coordinate has its exact scale bound | `endpointCoordinate_abs_bound` | endpoint invariant and domination |
| Wilder gain gives scale `n - 1` | `wilder_scale` | `n != 0` |
| Current displacement equals the endpoint coordinate | `displacementCoordinate_eq_endpointCoordinate` | endpoint invariant |
| Wilder displacement is bounded by `n - 1` | `wilder_finite_path_displacement_bound` | `n > 1`; nondegenerate path |
| Explicit interval `[-(n-1), n-1]` | `wilder_finite_path_displacement_interval` | `n > 1`; positive activity |

## 2. Directional masses, RSI, and log-odds

File: `EndpointCoordinate/Core.lean`

| Mathematical claim | Lean declaration |
| --- | --- |
| Positive minus negative mass recovers signed movement | `positiveMass_sub_negativeMass` |
| Positive plus negative mass recovers activity | `positiveMass_add_negativeMass` |
| Difference and sum of recursively smoothed Wilder masses follow the matched signed/activity recursion along every finite path | `directionalRun_matches_run` |
| Zero-initialized classical Wilder masses match the endpoint state along every finite path | `directionalRun_from_initial_matches` |
| Reconstructed positive and negative masses return the corresponding fields of a directional state | `positiveMass_directionalState`, `negativeMass_directionalState` |
| RSI fraction is the affine image `(1+F)/2` | `rsiFraction_eq_affine_unitCoordinate` |
| RSI value is the affine image `50(1+F)` | `rsiValue_eq_affine_unitCoordinate` |
| The balance coordinate is reconstructed from directional masses | `balanceCoordinate_reconstructed_masses` |
| Endpoint odds equal the directional mass ratio | `oddsRatio_balanceCoordinate_eq_massRatio` |
| Endpoint log-odds equal the directional log ratio | `logOdds_balanceCoordinate_eq_directionalLogRatio` |
| `logit(RSI/100)` equals the directional log ratio | `logit_rsiFraction_eq_directionalLogRatio` |
| `logit(RSI/100)` equals endpoint log-odds | `logit_rsiFraction_eq_logOdds_balanceCoordinate` |
| Endpoint log-odds equal `2 * artanh(F)` | `logOdds_eq_twice_artanh` |
| Complete exact RSI/log-odds chain | `exact_rsi_logOdds_chain` |
| Wilder endpoint bridge on a matched state | `wilder_endpoint_logOdds_identity` |
| Finite-path chain using masses reconstructed from `(signed, activity)` | `wilder_finite_path_rsi_logOdds_chain` |
| Finite-path chain using the recursively smoothed classical Wilder `up`/`down` masses | `wilder_directionalRun_rsi_logOdds_chain` |

The open interval assumptions in the logarithmic identities correspond to
both directional masses being strictly positive. At the boundary, one mass
vanishes and log-odds diverges.

## 3. Initialization error

File: `EndpointCoordinate/Core.lean`

The exact identity is naturally preserved by matched initialization. The
formalization also records what happens away from that initialization.

| Claim | Lean declaration |
| --- | --- |
| Endpoint invariant is equivalent to zero endpoint error | `endpointInvariant_iff_endpointError_eq_zero` |
| One-step error recursion | `endpointError_stateStep` |
| Finite-path error recursion | `endpointError_run` |
| Absolute error bound | `endpointError_run_abs` |
| Wilder specialization | `wilder_endpointError_run`, `wilder_endpointError_run_abs` |

## 4. Exponential weights and exact effective length

File: `EndpointCoordinate/Probability.lean`

For the exponential kernel

```text
w_k = alpha (1-alpha)^k,
```

the project proves

```text
sum_k w_k = 1,
sum_k w_k^2 = alpha / (2-alpha),
N_eff = 1 / sum_k w_k^2 = (2-alpha)/alpha.
```

At Wilder gain `alpha = 1/n`, this gives exactly

```text
sum_k w_k^2 = 1/(2n-1),
N_eff = 2n-1.
```

| Claim | Lean declaration |
| --- | --- |
| Kernel mass equals one | `exponentialWeight_hasSum_one`, `exponentialWeight_tsum_one` |
| Exact squared energy | `exponentialWeight_sq_hasSum`, `exponentialWeight_sq_tsum` |
| Generic effective length | `effectiveLength_eq` |
| Wilder mass equals one | `wilderWeight_hasSum_one`, `wilderWeight_tsum_one` |
| Wilder squared energy | `wilderWeight_sq_tsum` |
| Wilder effective length `2n-1` | `wilder_effectiveLength` |
| Variance of a finite independent weighted sum | `variance_finiteWeightedSmoother` |
| IID simplification | `variance_finiteWeightedSmoother_iid` |
| Finite Wilder variance | `variance_finiteWilderSmoother_iid` |
| Convergence to the exact infinite-kernel scale | `finiteWilderVariance_tendsto_exactScale` |

## 5. Stationary construction and tail energy

File: `EndpointCoordinate/Stationary.lean`

| Claim | Lean declaration |
| --- | --- |
| Exact kernel tail mass | `wilderWeight_tail_hasSum`, `wilderWeight_tail_tsum` |
| Exact squared tail energy | `wilderWeight_sq_tail_hasSum`, `wilderWeight_sq_tail_tsum` |
| Finite squared mass | `wilderWeight_sq_sum_range` |
| Tail-energy fraction | `wilderWeight_sq_tail_fraction` |
| Infinite-past smoother exists | `stationaryWilderTerm_summable`, `stationaryWilderSeries_hasSum` |
| Finite smoothers converge to stationary smoother | `finiteWilderSeries_tendsto_stationary` |
| Stationary recursion | `stationaryWilderSeries_recursion` |
| `L^p` construction and convergence | `stationaryWilderLp`, `finiteWilderLp_tendsto_stationary` |
| Normalized row energies sum to one | `lindebergWeightSq_hasSum_one`, `lindebergWeightSq_tsum_one` |
| Leading normalized weight vanishes | `lindebergLeadingWeightSq_tendsto_zero` |
| Scaled Wilder energy tends to one half | `wilder_scaled_energy_tendsto_half` |

## 6. Local log-odds asymptotics

File: `EndpointCoordinate/Asymptotics.lean`

| Claim | Lean declaration |
| --- | --- |
| Derivative of log-odds on `(-1,1)` | `hasDerivAt_logOdds` |
| Derivative at equilibrium is exactly `2` | `hasDerivAt_logOdds_zero` |
| `logOdds(x) ~ 2x` | `logOdds_isEquivalent_twice_id` |
| Nonlinear remainder is `o(x)` | `logOdds_sub_twice_isLittleO` |
| `logOdds(x)/x -> 2` | `logOdds_div_tendsto_two` |
| Exact removable-slope factorization | `logOdds_eq_mul_logOddsSlope` |
| Generic deterministic delta transfer | `scaled_logOdds_tendsto` |
| Exact-effective-length specialization | `effectiveLength_scaled_logOdds_tendsto` |

## 7. Distributional transfer through log-odds

File: `EndpointCoordinate/CLT.lean`

If `F_n -> 0` in probability and `a_n F_n` converges in distribution to `Z`,
then

```text
a_n logOdds(F_n)  ->d  2Z,
(a_n/2) logOdds(F_n)  ->d  Z.
```

| Claim | Lean declaration |
| --- | --- |
| General weak-limit transfer | `logOdds_clt_transfer` |
| Derivative-normalized transfer | `half_scaled_logOdds_clt_transfer` |
| Conventional square-root form | `sqrt_logOdds_clt_transfer`, `sqrt_half_logOdds_clt_transfer` |
| Exact-effective-length form | `effectiveLength_logOdds_clt_transfer`, `effectiveLength_half_logOdds_clt_transfer` |

These are transfer theorems: they do not assume or prove a particular input
CLT.

## 8. Gaussian benchmark

File: `EndpointCoordinate/Gaussian.lean`

| Claim | Lean declaration |
| --- | --- |
| A finite independent weighted Gaussian sum is Gaussian | `finiteWeightedSmoother_hasGaussianLaw` |
| Exact Gaussian measure and variance | `finiteWeightedSmoother_hasLaw_gaussianReal` |
| Exact finite Wilder-row squared energy | `gaussianNormalizedWilderWeight_sq_sum_range` |
| Exact finite-row Gaussian law | `finiteGaussianWilderRow_hasLaw` |
| Finite-row variance | `finiteGaussianWilderRowVariance` |
| Gaussian triangular-array limit | `finiteGaussianWilderRow_clt` |

For the Gaussian benchmark, finite weighted rows are exactly Gaussian; only
the omitted tail energy separates a truncated row from the full-kernel scale.

## 9. Laplace benchmark and triangular array

Files:

- `EndpointCoordinate/Laplace.lean`
- `EndpointCoordinate/TriangularArray.lean`

The unit-variance Laplace law is represented by its characteristic function

```text
phi(t) = 1 / (1 + t^2/2).
```

| Claim | Lean declaration |
| --- | --- |
| Exact finite weighted characteristic function | `charFun_finiteWeightedSmoother_laplace` |
| Exact finite Wilder-row characteristic product | `charFun_finiteLaplaceWilderRow` |
| Exact finite variance | `variance_finiteLaplaceWilderRow` |
| Fourth-order Lyapunov mass vanishes | `laplaceFourthLyapunovMass_tendsto_zero` |
| Levy bridge from product limit to CLT | `finiteLaplaceWilderRow_clt_of_characteristicLimit` |
| Quantitative `log(1+x)` remainder | `log_one_add_remainder_bounds` |
| General finite-product limit | `tendsto_prod_one_add_inv` |
| Wilder characteristic-product limit | `laplaceWilderCharacteristicLimit_of_tail` |
| Completed Laplace-input CLT | `finiteLaplaceWilderRow_clt` |

## 10. Student-t formula audit

File: `EndpointCoordinate/Student.lean`

Mathlib does not currently provide a named Student-t probability measure. The
law is therefore exposed through `HasUnitVarianceStudentMomentProfile`, an
explicit interface containing the required moment facts. The interface does
not construct a Student-t measure from a density.

| Claim | Lean declaration |
| --- | --- |
| Unit-variance Student first absolute moment | `studentFirstAbsoluteMoment` |
| Squared first-order scale | `studentFirstOrderScaleSq` |
| Scale derived from the first absolute moment | `studentFirstOrderScaleSq_from_firstAbsoluteMoment` |
| Encoded radial third-moment formula and its ratio identity | `studentRadialThirdMoment`, `studentRadialMoment_ratio` |
| Algebraic first-shift substitution between defined formulas | `student_firstVarianceShift_from_radial_moments` |
| Closed Student second-order coefficient | `student_secondVarianceCoefficient_eq` |
| Exact values for `nu = 4,5,6,8` | `studentFirstVarianceShift_four_exact`, `studentFirstVarianceShift_five_exact`, `studentFirstVarianceShift_six_exact`, `studentFirstVarianceShift_eight_exact` |
| The shift `1` is bracketed between `nu=5` and `nu=6` | `studentFirstVarianceShift_five_lt_one`, `one_lt_studentFirstVarianceShift_six` |
| Arithmetic feasibility of the parameter inequalities `(delta, q, gamma)` | `exists_StudentLocalizationAdmissible` |
| Conditional Gaussian endpoint, assuming convergence of the scale formula | `studentFirstVarianceShift_tendsto_gaussian_of_scale` |

`firstVarianceShift`, `secondVarianceCoefficient`, and
`studentFirstVarianceShift` are definitions. Their algebraic identities and
special values are checked by Lean, but Lean does not prove that they are
coefficients in an asymptotic expansion of the variance of the nonlinear
log-odds coordinate. That analytic bridge belongs to the companion
conventional technical note and symbolic audit.

The Student shift formulas are intended as finite-`n` corrections. They do not
replace the `sqrt(2n-1)` normalization used for the linear rows in the
finite-variance CLT.

## 11. Finite-variance linear-row CLT

File: `EndpointCoordinate/FiniteVarianceCLT.lean`

The minimal innovation interface is `HasCenteredUnitVariance`:

- almost-everywhere measurability;
- mean zero;
- second moment one.

The main theorem additionally assumes rowwise independence, identical
distribution, and vanishing omitted geometric variance.

| Claim | Lean declaration |
| --- | --- |
| Exact characteristic function of a finite IID weighted sum | `charFun_finiteWeightedSmoother_iid` |
| Every centered unit-variance law has the Gaussian second-order characteristic germ | `charFun_gaussian_remainder_isLittleO` |
| Product perturbation estimate | `norm_prod_sub_prod_le` |
| Leading normalized Wilder weight tends to zero | `finiteVarianceWilder_leading_tendsto_zero` |
| Aggregate row error tends to zero | `finiteVarianceWilderRowError_tendsto_zero` |
| Gaussian comparison product converges | `finiteVarianceWilderGaussianProduct_tendsto` |
| Innovation characteristic product converges | `finiteVarianceWilderCharacteristicProduct_tendsto` |
| Finite-variance CLT for normalized linear Wilder rows | `finiteVarianceWilderRow_clt` |
| Student moment profile implies the minimal interface | `HasUnitVarianceStudentMomentProfile.toHasCenteredUnitVariance` |
| Student-input specialization | `finiteStudentWilderRow_clt_of_momentProfile` |

The proof uses only the second-order expansion of the characteristic function
at the origin. It does not require a density, a fourth moment, a Gaussian
approximation assumption, or a Student-specific characteristic function.

The random variable in `finiteVarianceWilderRow_clt` is the linear row

```text
sqrt(2n-1) * sum_{k < count(n)} w_{n,k} epsilon_k,
```

not the bounded coordinate `F = S/A` and not the nonlinear coordinate
`logOdds(F)`. The latter can be handled by the conditional transfer theorems in
`CLT.lean` only after the required convergence statements for `F` have been
supplied.

The omitted-tail hypothesis is essential:

```text
(wilderDecay (n+1))^(2 * count(n)) -> 0.
```

It is not satisfied by `count(n) = n`, because the expression then converges
to `exp(-2)`. A longer truncation can approximate the infinite-past kernel,
but the current Lean source does not instantiate a particular longer count as
a separate theorem.

## 12. Statements deliberately outside the formalized scope

The repository does not prove:

- that observed financial returns are IID;
- that a particular market follows a Gaussian, Laplace, or Student-t law;
- that an asymptotic approximation is accurate at a particular finite `n`;
- a single composed Lean theorem deriving the CLT of the nonlinear endpoint
  log-odds coordinate from the concrete finite-variance linear-row theorem;
- that `firstVarianceShift`, `secondVarianceCoefficient`, or
  `studentFirstVarianceShift` is a coefficient in an expansion of
  `Var(L_alpha)`;
- the analytic remainder estimates used by the symbolic moment expansion;
- the heavy-tail localization theorem developed in the companion TeX note;
- existence of a Student-t probability measure satisfying
  `HasUnitVarianceStudentMomentProfile`;
- the Berry--Esseen theorem for the full nonlinear log-odds coordinate;
- that the practical `2/sqrt(n-1)` AdaptiveRSI scale is an exact universal
  theorem;
- that a trading strategy is profitable;
- any empirical result based on a market dataset.

Those are modeling or empirical questions and should be documented separately
from the kernel-checked mathematical layer.

## 13. External supplements

The supplement contains four distinct verification artifacts:

1. `moment_expansion_audit.py` reconstructs formal-series coefficients using
   moment/cumulant partitions and checks law-specific substitutions. It is an
   exact symbolic audit of the implemented truncation, not an analytic proof
   that the remainder is of the claimed order.
2. `Student_t_First_Shift_Note.tex` supplies the conventional heavy-tail
   localization argument. It remains outside the kernel-checked scope.
3. `normality_audit/` contains the reproducible finite-lookback numerical audit,
   including code, pinned dependencies, aggregate results, representative
   draws, tables, figures, and a machine-readable quality report. It evaluates
   synthetic innovation laws; it is neither a Lean proof nor an empirical
   market-data study.
4. `price_path_normality_audit/` tests the same normalizers on synthetic
   multiplicative price paths and separates the exact log-price benchmark from
   the empirical behavior of classical price RSI. It is numerical evidence,
   not a theorem for multiplicative dynamics.

These artifacts should be cited according to their actual verification status,
not grouped with the Lean theorems.
