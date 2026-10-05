# Price-path normality audit

This directory contains the reproducible computational supplement that tests
the EndpointCoordinate normalizers on classical RSI calculated from a
multiplicative price path.

## What is simulated

For each law, a unit-variance symmetric innovation sequence `epsilon_t` is
generated. For each volatility `sigma`, the log return is

```text
r_t = sigma * epsilon_t
```

and the positive price path begins at 10,000:

```text
P_t = P_(t-1) * exp(r_t).
```

Two Wilder log-odds coordinates are then compared:

- `price`: classical RSI input `Delta P_t = P_t - P_(t-1)`;
- `log_price`: additive benchmark input `r_t = Delta log(P_t)`.

The deterministic RSI/endpoint identities are exact for both inputs. The audit
tests only the probabilistic calibration.

## Fixed design

- laws: Gaussian, Laplace, standardized Student-t with `nu = 4, 5, 6, 8`;
- log-return standard deviations: `0.5%, 1%, 2%, 4%, 8%`;
- lookbacks: `2, 3, 5, 8, 13, 21, 35, 55, 89, 144, 233, 377`;
- retained observations: 3,000,000 per law-volatility pair;
- burn-in: `32 * 377 = 12,064`;
- random seed: `20260925`;
- normalizers: asymptotic, finite-n corrected, centered corrected, and empirical
  variance oracle.

The Student correction uses only the first-order formula developed in the
companion conventional technical note and remains outside Lean. Gaussian and
Laplace use the audited higher-order corrections.

## Main conclusion

The formulas remain useful scale corrections for classical price RSI when log
returns are small. They apply directly to RSI of log price under the additive
model. For classical price RSI, exponentiation creates state dependence and
positive skewness that grow with volatility and lookback. Variance close to one
therefore does not establish finite-sample normality.

The experiment is synthetic. It does not fit a law to market data, validate a
trading rule, or prove a theorem for geometric price models.

## Reproduction

The pinned environment is intended for Python 3.12. From the repository
root on Windows PowerShell:

```powershell
py -m pip install -r supplement\price_path_normality_audit\requirements.txt
py supplement\price_path_normality_audit\validate_implementation.py
py supplement\price_path_normality_audit\run_price_path_audit.py
```

The run is resumable by law-volatility cell. To regenerate figures from the
published CSV files without repeating Monte Carlo:

```powershell
py supplement\price_path_normality_audit\run_price_path_audit.py --plots-only
```

The `log_price` coordinate is computed once from the standardized
innovation path and then copied across the five `sigma` labels. This is exact
because the log-price RSI coordinate is homogeneous in the innovation scale.
Those rows are repeated views of one simulated coordinate, not five
independent replications.

`results/quality_checks.json` records structural and algebraic checks on the
published aggregate files. Independent implementation checks--including the
direct Wilder recursion, price reconstruction, scale invariance, the endpoint
identity, and the small-volatility limit--are performed separately by
`validate_implementation.py`.

## Published outputs

| File or directory | Contents |
| --- | --- |
| `Price_Path_Normality_Audit.pdf` | human-readable report |
| `Price_Path_Normality_Audit.tex` | report source |
| `run_price_path_audit.py` | simulation, aggregation, checks, and plotting |
| `validate_implementation.py` | independent recursion and identity checks |
| `results/summary_metrics.csv` | all 2,880 configuration summaries |
| `results/quantile_grid.csv.gz` | reusable empirical quantile grids |
| `results/ecdf_grid.csv.gz` | reusable empirical CDF grids |
| `results/histogram_density.csv.gz` | histogram counts and densities |
| `results/block_metrics.csv.gz` | block estimates for Monte Carlo uncertainty |
| `results/representative_draws.csv.gz` | 1.8 million representative-draw rows; log-price rows repeat across `sigma` labels by exact scale invariance |
| `results/representative_draws_preview.csv` | small plain-text preview |
| `results/quality_checks.json` | machine-readable integrity checks |
| `results/run_metadata.json` | seed, versions, and full design |
| `figures/` | 46 plots, each stored as PDF and PNG (92 files) |

The combined compressed CSV files are committed directly. Temporary
transfer parts and simulation caches are not part of the repository. The
committed aggregate files are sufficient for review and `--plots-only`.
