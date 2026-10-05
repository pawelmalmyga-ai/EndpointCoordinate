# Changelog

All notable changes to the formalization and its reproducibility materials are
documented in this file. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and releases use
semantic version tags.

## [Unreleased]

No changes recorded.

## [1.0.0] - 2026-09-28

### Added

- Exact finite-path endpoint-coordinate geometry and Wilder displacement
  bounds.
- Kernel-checked bridge from classical recursive Wilder `up`/`down` masses to
  the endpoint-coordinate state and RSI/log-odds chain.
- Exact RSI, logit, log-odds, and `artanh` identities.
- Exact exponential-weight energy and Wilder effective length `2n-1`.
- Stationary-series, tail-energy, local asymptotic, and conditional
  weak-convergence transfer layers.
- Gaussian and Laplace benchmark modules and a finite-variance CLT for
  normalized linear Wilder rows.
- Student-t moment-profile interfaces and algebraic checks of the defined
  first-shift formula.
- Main manuscript in TeX and PDF form, with an explicit map between paper
  claims and Lean declarations.
- Pinned SymPy audit of the finite symbolic coefficient calculation.
- Traditional Student-t heavy-tail technical note, explicitly separated from
  the Lean-checked subset.
- Reproducible numerical normality audit with code, pinned dependencies,
  aggregate diagnostics, representative draws, figures, tables, and a compiled
  report.
- Multiplicative price-path robustness audit comparing classical price RSI
  with the additive log-price benchmark across six innovation laws, five
  volatility levels, and twelve lookbacks.
- Citation metadata, theorem map, provenance and AI-assistance disclosure,
  release record, and dual software/content licensing.
- GitHub Actions checks for Lean proof placeholders, symbolic-audit
  regressions, and the complete Lean build.

### Changed

- Standardized the Student-t correction status across documentation, scripts,
  generated configuration, result tables, and reports as a conventional
  analytic result outside the Lean-verified scope.
- Added the price-path robustness audit to the formalization map, documented
  POSIX reproduction commands, and excluded local LaTeX build artifacts.
- Revised the layout of both numerical supplements for publication: reduced
  avoidable page breaks, paired related Q--Q grids on the same page, and added
  consistent PDF metadata. The simulations, exported data, figures, and
  reported numerical values are unchanged.
- Revised the Student-t heavy-tail supplement for publication clarity without
  changing its theorem, assumptions, constants, or proof calculations; renamed
  the source and PDF as a technical note and clarified that it remains outside
  the Lean-verified scope.
- Revised the main manuscript for publication clarity without changing its
  mathematical claims: explained the role of the Rademacher coefficient check,
  condensed the verification and limitations sections, and streamlined the
  research-provenance disclosure.
- Added complete PDF metadata, A4 page geometry, and explicit citations for
  Wilder and the Berry--Esseen inequality.
- Clarified throughout that the stationary nonlinear log-odds limit,
  Berry--Esseen argument, and analytic variance-remainder estimates are
  conventional proofs rather than Lean theorems.
- Clarified that `finiteVarianceWilderRow_clt` concerns normalized linear rows
  with vanishing omitted squared-weight mass.
- Clarified that the Student-t finite-shift quantities are definitions whose
  algebraic consequences are checked, not kernel-checked coefficients of the
  nonlinear variance.
- Strengthened the finite-to-infinite Berry--Esseen transfer step in the main
  manuscript.
- Documented the interpretation limits of the synthetic normality study and
  distinguished scale error from residual shape error.
- Clarified that the manuscript normalizers are exact additive-input results,
  exact controls for the log-price coordinate, and empirical approximations
  for classical price RSI under multiplicative dynamics.
