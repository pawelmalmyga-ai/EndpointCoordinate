# Numerical normality audit

This directory contains a reproducible finite-lookback distribution audit for
the log-odds endpoint coordinate

\[
L_t=\log(U_t/D_t).
\]

It answers a narrower question than the analytical manuscript: after applying
the asymptotic or law-specific finite-\(n\) scale, how close is the *finite-\(n\)*
marginal distribution to a standard normal distribution?

## Fixed design

- laws: Gaussian, Laplace, and standardized Student \(t_\nu\) for
  \(\nu=4,5,6,8\);
- lookbacks: `2, 3, 5, 8, 13, 21, 35, 55, 89, 144, 233, 377`;
- retained observations: 3,000,000 for every law-lookback pair;
- burn-in: `32 * 377`, leaving less than about `exp(-32)` of the zero-state
  initialization at the longest lookback;
- seed: `20260923`;
- Monte Carlo uncertainty: 192 long contiguous blocks, so block summaries
  remain useful despite serial dependence of the stationary recursion.

The Student correction uses the first-order formula developed in the companion
conventional technical note. It is reported as an exploratory finite-\(n\)
calibration outside Lean and is not presented as part of the proved light-tail
expansion. For Student \(t_4\), the
first shift vanishes (\(K_4=0\)), so the `corrected` and `asymptotic`
normalizations coincide on the entire lookback grid.

## Normalizations

1. `asymptotic`: \(Z=\sqrt n\,L/C_F\);
2. `corrected`: \(Z=\sqrt{g_F(n)}\,L/C_F\), with the audited fourth-order
   Gaussian/Laplace expansion and the Student first-shift correction from the
   companion technical note;
3. `oracle`: centered and divided by the empirical standard deviation. This is
   a diagnostic only. It separates residual distributional shape from scale
   calibration and is not a proposed statistic.

## Outputs

- `results/summary_metrics.csv`: one row per law, lookback, and normalizer;
- `results/quantile_grid.csv.gz`: 1,001 probability levels per configuration;
- `results/ecdf_grid.csv.gz`: dense empirical CDF values on `[-5,5]`;
- `results/histogram_density.csv.gz`: reusable histogram counts and densities;
- `results/block_metrics.csv.gz`: block-level moments and tail frequencies;
- `results/representative_draws/*.csv.gz`: six law-level files with 20,000 raw
  observations per law-lookback pair, including `L` and all three standardized
  coordinates; the split avoids GitHub's warning for individual files above
  50 MB;
- `results/representative_draws_preview.csv`: small uncompressed sample that
  opens quickly in spreadsheet software;
- `results/simulation_config.json`: complete seed, versions, constants, and
  design metadata;
- `figures/`: PDF and PNG versions of every chart;
- `Numerical_Normality_Audit.tex` and `.pdf`: human-readable report.

The full 216 million evaluated coordinate values are not stored row by row.
The exported raw representative sample, dense distribution grids, block
results, seed, and code preserve the useful analysis surface without turning
the repository into a multi-gigabyte data archive.

## Reproduction

From the repository root:

```powershell
py -m pip install -r supplement\normality_audit\requirements.txt
py supplement\normality_audit\run_normality_audit.py
```

During a full local run, each completed law is cached separately under
`results/parts`. If execution is interrupted, running the same command resumes
from the first unfinished law. These temporary cache files are not included in
the distributed archive, so a full run started from the archive begins from the
first law. The full Monte Carlo run is intentionally not part of GitHub Actions;
CI should verify code and lightweight symbolic checks, while the committed
aggregate outputs make this expensive audit inspectable without consuming
runner time.

To recreate only the charts from the committed CSV data:

```powershell
py supplement\normality_audit\run_normality_audit.py --plots-only
```

Use `--force` only when the full simulation should be repeated deliberately.

## Interpretation

Variance near one is not evidence of exact Gaussianity. The report therefore
uses Q-Q geometry, Kolmogorov distance, truncated mean absolute error on the
normal-quantile grid, skewness, excess kurtosis, central coverage, and tail
frequencies. The exported column retains the historical name
`wasserstein_grid`, but it is not the full \(W_1\) distance on the real line.
Formal normality-test p-values are intentionally omitted: with millions of
observations they reject tiny, practically irrelevant discrepancies, while
serial dependence also invalidates the usual i.i.d. calibration.

This computation supplements but does not replace the analytical CLT and
Berry--Esseen result in the main manuscript.
