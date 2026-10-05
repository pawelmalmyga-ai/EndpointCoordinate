# Supplementary materials

This directory contains reproducibility and review materials accompanying
*Endpoint Coordinates and Wilder's Log-Odds RSI: Exact Geometry, Effective
Length, and Finite-Horizon Normalization*.

## Contents

| File | Purpose | Verification status |
| --- | --- | --- |
| `moment_expansion_audit.py` | Independently regenerates the degree-eight Taylor polynomial, reconstructs the finite-horizon variance coefficients, and checks the Laplace, Rademacher, Gaussian, and selected Student-t first-shift substitutions using exact symbolic arithmetic and set partitions. | Executable SymPy audit; no simulation or fitted constants. |
| `Student_t_First_Shift_Note.tex` | Source of the heavy-tail extension note for symmetric innovations with a finite \(3+\delta\) moment. | Conventional mathematical proof; not formalized in Lean. |
| `Student_t_First_Shift_Note.pdf` | Compiled version of the heavy-tail extension note. | Same status as the TeX source. |
| `requirements.txt` | Python dependency required by the symbolic audit. | Pins the version used for the recorded check. |
| `normality_audit/` | Reproducible finite-lookback simulation study with code, exported diagnostics, representative draws, tables, figures, and a compiled report. | Numerical evidence only; not a proof and not a test on financial-market data. |
| `price_path_normality_audit/` | Multiplicative price-path robustness study comparing classical price RSI with RSI of log price. | Numerical evidence only; not a theorem for geometric price models and not a fitted market model. |

## Run the symbolic audit

From the repository root on Windows:

```powershell
py -m pip install -r supplement\requirements.txt
py supplement\moment_expansion_audit.py
```

On Linux or macOS:

```bash
python3 -m pip install -r supplement/requirements.txt
python3 supplement/moment_expansion_audit.py
```

The successful run ends with:

```text
ALL EXACT SYMBOLIC CHECKS PASSED
```

The script checks the finite algebraic calculation, including the generation
of the polynomial used by that calculation. It does not replace the analytic
remainder estimates or the Berry--Esseen argument in the paper, and its
Student-t checks do not validate the localization proof in the separate note.

## Compile the heavy-tail technical note

With a standard LaTeX installation:

```powershell
cd supplement
pdflatex Student_t_First_Shift_Note.tex
pdflatex Student_t_First_Shift_Note.tex
```

The same `pdflatex` commands apply in a POSIX shell.

## Numerical normality audit

The directory `normality_audit/` contains the complete published analysis
surface for Gaussian, Laplace, and standardized Student-t innovations across
twelve lookbacks. Its report is available as
[`Numerical_Normality_Audit.pdf`](normality_audit/Numerical_Normality_Audit.pdf).
The committed aggregate outputs and representative draws can be inspected
without repeating the full simulation.

For the experimental design, data inventory, reproduction command, and the
precise interpretation of the reported diagnostics, see
[`normality_audit/README.md`](normality_audit/README.md).

## Price-path robustness audit

The directory `price_path_normality_audit/` starts each synthetic series at
10,000, exponentiates symmetric log returns into prices, and calculates
classical RSI from arithmetic price changes. The same innovations are also
processed as log-price changes, which supplies the additive benchmark covered
directly by the manuscript.

The report is available as
[`Price_Path_Normality_Audit.pdf`](price_path_normality_audit/Price_Path_Normality_Audit.pdf).
The directory contains the complete code, validation checks, aggregate CSVs,
representative draws, and 92 figure files. See
[`price_path_normality_audit/README.md`](price_path_normality_audit/README.md)
for the fixed design, commands, inventory, and interpretation boundary.

## Scope of verification

- The declarations in `EndpointCoordinate/*.lean` are checked by the Lean
  kernel under the assumptions visible in their types.
- `moment_expansion_audit.py` independently checks the stated symbolic moment
  and cumulant calculations.
- The heavy-tail note gives a conventional proof outside Lean; its coefficient
  algebra is independently reproduced by the pinned SymPy calculation.
- The normality audit is a reproducible synthetic experiment. It does not
  establish exact finite-sample Gaussianity or empirical validity for market
  returns.
- The price-path audit is a robustness experiment. It shows when additive-model
  normalizers remain useful for classical price RSI, but it does not extend the
  manuscript's probability theorems to multiplicative price dynamics.

For authorship and AI-assistance disclosure, see `../PROVENANCE.md`.
