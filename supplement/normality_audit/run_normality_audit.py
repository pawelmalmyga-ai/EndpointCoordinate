#!/usr/bin/env python3
"""Reproducible finite-n distribution audit for the endpoint coordinate.

The script simulates the stationary Wilder up/down recursions on one long
innovation path per law.  It evaluates the marginal distribution of

    L_t = log(U_t / D_t)

for a fixed Fibonacci-like grid of lookbacks.  Three scalings are compared:

* asymptotic: sqrt(n) L / C_F;
* corrected: sqrt(g_F(n)) L / C_F, using the audited Gaussian/Laplace
  expansion and the Student first-shift correction developed in the companion
  conventional technical note, outside Lean;
* oracle: (L - sample mean) / sample standard deviation, used only to
  separate scale error from residual non-Gaussian shape.

The full path is used for the reported metrics.  Reusable distributional
summaries and a representative raw sample are exported as CSV files.  The
simulation is resumable law by law, and ``--plots-only`` regenerates every
figure from the CSV files without repeating the Monte Carlo run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import shutil
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import scipy
from matplotlib.lines import Line2D
from matplotlib.ticker import ScalarFormatter
from scipy.signal import lfilter
from scipy.special import gammaln, ndtr, ndtri


SCRIPT_VERSION = "1.0.0"
DEFAULT_SEED = 20260923
DEFAULT_OBSERVATIONS = 3_000_000
DEFAULT_BLOCKS = 192
DEFAULT_REPRESENTATIVE = 20_000
DEFAULT_PREVIEW = 500
LOOKBACKS = (2, 3, 5, 8, 13, 21, 35, 55, 89, 144, 233, 377)
LAW_NAMES = (
    "Gaussian",
    "Laplace",
    "Student-t4",
    "Student-t5",
    "Student-t6",
    "Student-t8",
)
NORMALIZERS = ("asymptotic", "corrected", "oracle")
NORMALIZER_LABELS = {
    "asymptotic": "asymptotic scale",
    "corrected": "finite-n corrected scale",
    "oracle": "empirical variance oracle",
}
LAW_COLORS = {
    "Gaussian": "#2563eb",
    "Laplace": "#b45309",
    "Student-t4": "#7c3aed",
    "Student-t5": "#15803d",
    "Student-t6": "#be123c",
    "Student-t8": "#0f766e",
}
NORM_COLORS = {
    "asymptotic": "#9a6b16",
    "corrected": "#2563eb",
    "oracle": "#e11d48",
}


@dataclass(frozen=True)
class LawSpec:
    name: str
    family: str
    degrees_of_freedom: float | None
    C: float
    K: float
    A: float | None
    B: float | None
    correction_status: str


def student_constants(nu: float) -> tuple[float, float]:
    log_ratio = gammaln(nu / 2.0) - gammaln((nu - 1.0) / 2.0)
    c = math.sqrt(2.0 * math.pi / (nu - 2.0)) * math.exp(log_ratio)
    k = 1.25 * c * c - 7.0 / 3.0 - 8.0 / (3.0 * (nu - 3.0))
    return c, k


def law_specs() -> dict[str, LawSpec]:
    pi = math.pi
    specs: dict[str, LawSpec] = {
        "Gaussian": LawSpec(
            name="Gaussian",
            family="Gaussian",
            degrees_of_freedom=None,
            C=math.sqrt(pi),
            K=(15.0 * pi - 28.0) / 12.0,
            A=(856.0 + 240.0 * pi - 159.0 * pi**2) / 144.0,
            B=(89220.0 * pi**2 + 130784.0 - 28344.0 * pi - 29475.0 * pi**3)
            / 8640.0,
            correction_status="proved light-tail expansion",
        ),
        "Laplace": LawSpec(
            name="Laplace",
            family="Laplace",
            degrees_of_freedom=None,
            C=2.0,
            K=4.0 / 3.0,
            A=5.0 / 18.0,
            B=5.0 / 27.0,
            correction_status="proved light-tail expansion",
        ),
    }
    for nu in (4.0, 5.0, 6.0, 8.0):
        c, k = student_constants(nu)
        name = f"Student-t{int(nu)}"
        specs[name] = LawSpec(
            name=name,
            family="Student-t",
            degrees_of_freedom=nu,
            C=c,
            K=k,
            A=None,
            B=None,
            correction_status="conventional first-shift correction; outside Lean",
        )
    return specs


def slug(text: str) -> str:
    return text.lower().replace("-", "_")


def g_corrected(spec: LawSpec, n: int | np.ndarray) -> np.ndarray:
    n_arr = np.asarray(n, dtype=float)
    value = n_arr - spec.K
    if spec.A is not None:
        value = value + spec.A / n_arr + float(spec.B) / (n_arr * n_arr)
    return value


def innovation_sample(spec: LawSpec, rng: np.random.Generator, size: int) -> np.ndarray:
    if spec.family == "Gaussian":
        return rng.normal(size=size)
    if spec.family == "Laplace":
        return rng.laplace(scale=1.0 / math.sqrt(2.0), size=size)
    if spec.family == "Student-t":
        nu = float(spec.degrees_of_freedom)
        return rng.standard_t(nu, size=size) * math.sqrt((nu - 2.0) / nu)
    raise ValueError(f"Unknown family: {spec.family}")


def stable_seed(base_seed: int, *parts: object) -> int:
    payload = "|".join([str(base_seed), *(str(x) for x in parts)]).encode("utf-8")
    digest = hashlib.sha256(payload).digest()
    return int.from_bytes(digest[:8], "little")


def linear_quantiles(sorted_x: np.ndarray, probabilities: np.ndarray) -> np.ndarray:
    """NumPy-compatible linear quantiles from an already sorted array."""
    h = (len(sorted_x) - 1) * probabilities
    lo = np.floor(h).astype(np.int64)
    hi = np.ceil(h).astype(np.int64)
    frac = h - lo
    return sorted_x[lo] * (1.0 - frac) + sorted_x[hi] * frac


def exact_sample_ks(sorted_z: np.ndarray) -> float:
    n = len(sorted_z)
    cdf = ndtr(sorted_z)
    upper = np.arange(1, n + 1, dtype=float) / n
    lower = np.arange(0, n, dtype=float) / n
    return float(max(np.max(upper - cdf), np.max(cdf - lower)))


def standardized_views(
    l_values: np.ndarray,
    spec: LawSpec,
    n: int,
) -> dict[str, np.ndarray]:
    corrected_g = float(g_corrected(spec, n))
    if corrected_g <= 0:
        raise ValueError(f"Nonpositive corrected g for {spec.name}, n={n}: {corrected_g}")
    sample_mean = float(np.mean(l_values))
    sample_sd = float(np.std(l_values, ddof=1))
    return {
        "asymptotic": math.sqrt(n) * l_values / spec.C,
        "corrected": math.sqrt(corrected_g) * l_values / spec.C,
        "oracle": (l_values - sample_mean) / sample_sd,
    }


def moment_metrics(z: np.ndarray) -> dict[str, float]:
    mean = float(np.mean(z))
    centered = z - mean
    m2 = float(np.mean(centered**2))
    m3 = float(np.mean(centered**3))
    m4 = float(np.mean(centered**4))
    skewness = m3 / m2**1.5
    excess_kurtosis = m4 / (m2 * m2) - 3.0
    return {
        "mean": mean,
        "variance": float(np.var(z, ddof=1)),
        "skewness": skewness,
        "excess_kurtosis": excess_kurtosis,
    }


def block_rows(
    z: np.ndarray,
    law: str,
    n: int,
    normalizer: str,
    blocks: int,
) -> list[dict[str, float | int | str]]:
    block_size = len(z) // blocks
    usable = block_size * blocks
    x = z[:usable].reshape(blocks, block_size)
    means = np.mean(x, axis=1)
    centered = x - means[:, None]
    m2 = np.mean(centered**2, axis=1)
    m3 = np.mean(centered**3, axis=1)
    m4 = np.mean(centered**4, axis=1)
    variances = np.var(x, axis=1, ddof=1)
    skewness = m3 / np.power(m2, 1.5)
    excess_kurtosis = m4 / (m2 * m2) - 3.0
    coverage95 = np.mean(np.abs(x) <= 1.959963984540054, axis=1)
    coverage99 = np.mean(np.abs(x) <= 2.5758293035489004, axis=1)
    tail3 = np.mean(np.abs(x) > 3.0, axis=1)
    return [
        {
            "law": law,
            "n": n,
            "normalizer": normalizer,
            "block": b,
            "block_size": block_size,
            "mean": float(means[b]),
            "variance": float(variances[b]),
            "skewness": float(skewness[b]),
            "excess_kurtosis": float(excess_kurtosis[b]),
            "coverage_95": float(coverage95[b]),
            "coverage_99": float(coverage99[b]),
            "p_abs_gt_3": float(tail3[b]),
        }
        for b in range(blocks)
    ]


def summarize_view(
    z: np.ndarray,
    sorted_z: np.ndarray,
    law: str,
    n: int,
    normalizer: str,
    qq_probabilities: np.ndarray,
) -> dict[str, float | int | str]:
    metrics = moment_metrics(z)
    empirical_qq = linear_quantiles(sorted_z, qq_probabilities)
    normal_qq = ndtri(qq_probabilities)
    slope, intercept = np.polyfit(normal_qq, empirical_qq, 1)
    fit = intercept + slope * normal_qq
    ss_res = float(np.sum((empirical_qq - fit) ** 2))
    ss_tot = float(np.sum((empirical_qq - np.mean(empirical_qq)) ** 2))
    qq_r2 = 1.0 - ss_res / ss_tot
    wasserstein_grid = float(np.mean(np.abs(empirical_qq - normal_qq)))
    row: dict[str, float | int | str] = {
        "law": law,
        "n": n,
        "normalizer": normalizer,
        "observations": len(z),
        **metrics,
        "ks_to_standard_normal": exact_sample_ks(sorted_z),
        "wasserstein_quantile_grid": wasserstein_grid,
        "qq_intercept": float(intercept),
        "qq_slope": float(slope),
        "qq_r_squared": qq_r2,
        "qq_max_abs_error_0_5pct_99_5pct": float(np.max(np.abs(empirical_qq - normal_qq))),
        "coverage_95": float(np.mean(np.abs(z) <= 1.959963984540054)),
        "coverage_99": float(np.mean(np.abs(z) <= 2.5758293035489004)),
        "p_abs_gt_2": float(np.mean(np.abs(z) > 2.0)),
        "p_abs_gt_3": float(np.mean(np.abs(z) > 3.0)),
    }
    return row


def expected_part_metadata(
    spec: LawSpec,
    observations: int,
    burn_in: int,
    blocks: int,
    representative: int,
    seed: int,
) -> dict[str, object]:
    return {
        "script_version": SCRIPT_VERSION,
        "law": asdict(spec),
        "observations": observations,
        "burn_in": burn_in,
        "blocks": blocks,
        "representative": representative,
        "seed": seed,
        "lookbacks": list(LOOKBACKS),
    }


def metadata_matches(path: Path, expected: dict[str, object]) -> bool:
    if not path.exists():
        return False
    return json.loads(path.read_text(encoding="utf-8")) == expected


def simulate_law(
    spec: LawSpec,
    observations: int,
    burn_in: int,
    blocks: int,
    representative: int,
    preview: int,
    seed: int,
    part_dir: Path,
) -> None:
    print(f"\n[{spec.name}] generating {observations:,} retained observations", flush=True)
    rng = np.random.default_rng(stable_seed(seed, spec.name, "innovations"))
    eps = innovation_sample(spec, rng, observations + burn_in)
    up = np.maximum(eps, 0.0)
    down = np.maximum(-eps, 0.0)
    del eps

    quantile_probabilities = np.unique(
        np.concatenate(
            [
                np.array([0.0005]),
                np.linspace(0.001, 0.999, 999),
                np.array([0.9995]),
            ]
        )
    )
    qq_probabilities = np.linspace(0.005, 0.995, 399)
    ecdf_grid = np.linspace(-5.0, 5.0, 1001)
    histogram_edges = np.linspace(-6.0, 6.0, 481)

    summary: list[dict[str, object]] = []
    quantiles: list[dict[str, object]] = []
    ecdf_rows: list[dict[str, object]] = []
    histogram_rows: list[dict[str, object]] = []
    blocks_rows: list[dict[str, object]] = []
    representative_rows: list[pd.DataFrame] = []
    preview_rows: list[pd.DataFrame] = []

    for n in LOOKBACKS:
        alpha = 1.0 / n
        lam = 1.0 - alpha
        u = lfilter([alpha], [1.0, -lam], up)[burn_in:]
        d = lfilter([alpha], [1.0, -lam], down)[burn_in:]
        if np.any(u <= 0.0) or np.any(d <= 0.0):
            raise RuntimeError(f"Nonpositive directional mass for {spec.name}, n={n}")
        l_values = np.log(u / d)
        del u, d
        sorted_l = np.sort(l_values)
        views = standardized_views(l_values, spec, n)
        g_value = float(g_corrected(spec, n))
        l_mean = float(np.mean(l_values))
        l_var = float(np.var(l_values, ddof=1))
        g_empirical = spec.C * spec.C / l_var

        rep_rng = np.random.default_rng(stable_seed(seed, spec.name, n, "representative"))
        rep_count = min(representative, observations)
        rep_idx = np.sort(rep_rng.choice(observations, size=rep_count, replace=False))
        preview_count = min(preview, rep_count)
        preview_idx = np.linspace(0, rep_count - 1, preview_count, dtype=int)

        rep_frame = pd.DataFrame(
            {
                "law": spec.name,
                "n": n,
                "path_index": rep_idx,
                "L": l_values[rep_idx],
                "z_asymptotic": views["asymptotic"][rep_idx],
                "z_corrected": views["corrected"][rep_idx],
                "z_oracle": views["oracle"][rep_idx],
            }
        )
        representative_rows.append(rep_frame)
        preview_rows.append(rep_frame.iloc[preview_idx].copy())

        for normalizer, z in views.items():
            if normalizer == "oracle":
                sorted_z = (sorted_l - l_mean) / math.sqrt(l_var)
            else:
                scale = math.sqrt(n) / spec.C if normalizer == "asymptotic" else math.sqrt(g_value) / spec.C
                sorted_z = sorted_l * scale

            row = summarize_view(
                z,
                sorted_z,
                spec.name,
                n,
                normalizer,
                qq_probabilities,
            )
            row.update(
                {
                    "C": spec.C,
                    "K": spec.K,
                    "A": spec.A,
                    "B": spec.B,
                    "g_corrected": g_value,
                    "g_empirical": g_empirical,
                    "L_mean": l_mean,
                    "L_variance": l_var,
                    "correction_status": spec.correction_status,
                }
            )
            summary.append(row)

            q_values = linear_quantiles(sorted_z, quantile_probabilities)
            quantiles.extend(
                {
                    "law": spec.name,
                    "n": n,
                    "normalizer": normalizer,
                    "probability": float(p),
                    "empirical_quantile": float(q),
                    "normal_quantile": float(ndtri(p)),
                    "quantile_error": float(q - ndtri(p)),
                }
                for p, q in zip(quantile_probabilities, q_values, strict=True)
            )

            cdf_values = np.searchsorted(sorted_z, ecdf_grid, side="right") / len(sorted_z)
            ecdf_rows.extend(
                {
                    "law": spec.name,
                    "n": n,
                    "normalizer": normalizer,
                    "z": float(x),
                    "empirical_cdf": float(f),
                    "normal_cdf": float(ndtr(x)),
                    "cdf_error": float(f - ndtr(x)),
                }
                for x, f in zip(ecdf_grid, cdf_values, strict=True)
            )

            counts, _ = np.histogram(z, bins=histogram_edges)
            widths = np.diff(histogram_edges)
            densities = counts / (len(z) * widths)
            centers = (histogram_edges[:-1] + histogram_edges[1:]) / 2.0
            normal_density = np.exp(-0.5 * centers**2) / math.sqrt(2.0 * math.pi)
            histogram_rows.extend(
                {
                    "law": spec.name,
                    "n": n,
                    "normalizer": normalizer,
                    "bin_left": float(histogram_edges[i]),
                    "bin_right": float(histogram_edges[i + 1]),
                    "bin_center": float(centers[i]),
                    "count": int(counts[i]),
                    "density": float(densities[i]),
                    "normal_density": float(normal_density[i]),
                }
                for i in range(len(counts))
            )
            blocks_rows.extend(block_rows(z, spec.name, n, normalizer, blocks))
        del l_values, sorted_l, views
        print(f"  n={n:>3}: Var(L)={l_var:.8g}, g_emp={g_empirical:.6f}, g_corr={g_value:.6f}", flush=True)

    prefix = slug(spec.name)
    pd.DataFrame(summary).to_csv(part_dir / f"summary_{prefix}.csv", index=False)
    pd.DataFrame(quantiles).to_csv(part_dir / f"quantiles_{prefix}.csv", index=False)
    pd.DataFrame(ecdf_rows).to_csv(part_dir / f"ecdf_{prefix}.csv", index=False)
    pd.DataFrame(histogram_rows).to_csv(part_dir / f"histogram_{prefix}.csv", index=False)
    pd.DataFrame(blocks_rows).to_csv(part_dir / f"blocks_{prefix}.csv", index=False)
    pd.concat(representative_rows, ignore_index=True).to_csv(
        part_dir / f"representative_{prefix}.csv.gz", index=False, compression="gzip"
    )
    pd.concat(preview_rows, ignore_index=True).to_csv(
        part_dir / f"preview_{prefix}.csv", index=False
    )


def combine_parts(result_dir: Path, selected_laws: Iterable[str]) -> None:
    part_dir = result_dir / "parts"
    mappings = {
        "summary_metrics.csv": "summary",
        "quantile_grid.csv.gz": "quantiles",
        "ecdf_grid.csv.gz": "ecdf",
        "histogram_density.csv.gz": "histogram",
        "block_metrics.csv.gz": "blocks",
        "representative_draws_preview.csv": "preview",
    }
    for output_name, prefix in mappings.items():
        frames = []
        for law in selected_laws:
            suffix = ".csv.gz" if prefix == "representative" else ".csv"
            frames.append(pd.read_csv(part_dir / f"{prefix}_{slug(law)}{suffix}"))
        combined = pd.concat(frames, ignore_index=True)
        compression = "gzip" if output_name.endswith(".gz") else None
        combined.to_csv(result_dir / output_name, index=False, compression=compression)

    representative_dir = result_dir / "representative_draws"
    representative_dir.mkdir(parents=True, exist_ok=True)
    for law in selected_laws:
        shutil.copyfile(
            part_dir / f"representative_{slug(law)}.csv.gz",
            representative_dir / f"{slug(law)}.csv.gz",
        )

    summary_path = result_dir / "summary_metrics.csv"
    summary = pd.read_csv(summary_path)
    blocks = pd.read_csv(result_dir / "block_metrics.csv.gz")
    se = (
        blocks.groupby(["law", "n", "normalizer"])[
            ["mean", "variance", "skewness", "excess_kurtosis", "coverage_95", "coverage_99", "p_abs_gt_3"]
        ]
        .sem()
        .reset_index()
        .rename(
            columns={
                "mean": "mcse_mean",
                "variance": "mcse_variance",
                "skewness": "mcse_skewness",
                "excess_kurtosis": "mcse_excess_kurtosis",
                "coverage_95": "mcse_coverage_95",
                "coverage_99": "mcse_coverage_99",
                "p_abs_gt_3": "mcse_p_abs_gt_3",
            }
        )
    )
    summary = summary.merge(se, on=["law", "n", "normalizer"], how="left")

    q = pd.read_csv(result_dir / "quantile_grid.csv.gz")
    central = q[(q.probability >= 0.01) & (q.probability <= 0.99)].copy()
    reference = central[central.n == max(LOOKBACKS)][
        ["law", "normalizer", "probability", "empirical_quantile"]
    ].rename(columns={"empirical_quantile": "reference_quantile"})
    central = central.merge(reference, on=["law", "normalizer", "probability"], how="left")
    central["delta_sq"] = (central.empirical_quantile - central.reference_quantile) ** 2
    central["delta_abs"] = (central.empirical_quantile - central.reference_quantile).abs()
    collapse = (
        central.groupby(["law", "n", "normalizer"])
        .agg(
            quantile_rmse_vs_n377=("delta_sq", lambda x: float(np.sqrt(np.mean(x)))),
            quantile_max_abs_vs_n377=("delta_abs", "max"),
        )
        .reset_index()
    )
    summary = summary.merge(collapse, on=["law", "n", "normalizer"], how="left")
    summary.to_csv(summary_path, index=False)


def configure_matplotlib() -> None:
    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 8.5,
            "axes.titlesize": 9,
            "axes.labelsize": 8.5,
            "legend.fontsize": 7.5,
            "figure.dpi": 120,
            "savefig.dpi": 220,
            "savefig.facecolor": "white",
            "axes.spines.top": False,
            "axes.spines.right": False,
        }
    )


def save_figure(fig: plt.Figure, figure_dir: Path, stem: str) -> None:
    pdf_path = figure_dir / f"{stem}.pdf"
    png_path = figure_dir / f"{stem}.png"
    temporary_pdf = figure_dir / f"{stem}.tmp.pdf"
    temporary_png = figure_dir / f"{stem}.tmp.png"
    fig.savefig(temporary_pdf, format="pdf", bbox_inches="tight")
    fig.savefig(temporary_png, format="png", bbox_inches="tight", dpi=220)
    if temporary_pdf.stat().st_size < 100 or temporary_png.stat().st_size < 100:
        raise RuntimeError(f"Figure export failed for {stem}")
    temporary_pdf.replace(pdf_path)
    temporary_png.replace(png_path)
    plt.close(fig)


def plot_overview(summary: pd.DataFrame, figure_dir: Path) -> None:
    present_laws = [law for law in LAW_NAMES if law in set(summary.law)]
    metrics = [
        ("variance", "Empirical variance", 1.0),
        ("ks_to_standard_normal", "Kolmogorov distance", None),
        ("excess_kurtosis", "Excess kurtosis", 0.0),
        ("coverage_95", "Coverage of normal 95% interval", 0.95),
    ]
    fig, axes = plt.subplots(2, 2, figsize=(8.3, 6.5), sharex=True)
    for ax, (metric, ylabel, reference) in zip(axes.flat, metrics, strict=True):
        for law in present_laws:
            d = summary[(summary.law == law) & (summary.normalizer == "corrected")]
            ax.plot(d.n, d[metric], marker="o", ms=2.7, lw=1.0, color=LAW_COLORS[law], label=law)
        if reference is not None:
            ax.axhline(reference, color="#111827", lw=0.8, ls="--")
        ax.set_xscale("log")
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.set_ylabel(ylabel)
        ax.grid(alpha=0.18)
    axes[1, 0].set_xlabel("Lookback n")
    axes[1, 1].set_xlabel("Lookback n")
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=3, frameon=False)
    fig.suptitle("Finite-n Gaussian approximation after law-specific scaling", y=0.995, fontsize=11)
    fig.tight_layout(rect=(0, 0.075, 1, 0.97))
    save_figure(fig, figure_dir, "overview_corrected_metrics")


def plot_normalizer_comparison(summary: pd.DataFrame, figure_dir: Path) -> None:
    present_laws = [law for law in LAW_NAMES if law in set(summary.law)]
    fig, axes = plt.subplots(2, 3, figsize=(9.0, 5.9), sharex=True)
    for ax, law in zip(axes.flat, present_laws):
        d = summary[summary.law == law]
        for normalizer in NORMALIZERS:
            x = d[d.normalizer == normalizer]
            ax.plot(
                x.n,
                x.ks_to_standard_normal,
                marker="o",
                ms=2.5,
                lw=1.0,
                color=NORM_COLORS[normalizer],
                label=NORMALIZER_LABELS[normalizer],
            )
        ax.set_xscale("log")
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.set_title(law)
        ax.set_ylabel("Kolmogorov distance")
        ax.grid(alpha=0.18)
    for ax in list(axes.flat)[len(present_laws) :]:
        ax.set_visible(False)
    for ax in axes[1, :]:
        ax.set_xlabel("Lookback n")
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=3, frameon=False)
    fig.suptitle("Scale correction versus residual distributional shape", y=0.995, fontsize=11)
    fig.tight_layout(rect=(0, 0.075, 1, 0.97))
    save_figure(fig, figure_dir, "normalizer_ks_comparison")


def plot_variance_calibration(summary: pd.DataFrame, figure_dir: Path) -> None:
    present_laws = [law for law in LAW_NAMES if law in set(summary.law)]
    fig, axes = plt.subplots(2, 3, figsize=(9.0, 5.9), sharex=True, sharey=True)
    for ax, law in zip(axes.flat, present_laws):
        d = summary[summary.law == law]
        for normalizer in ("asymptotic", "corrected"):
            x = d[d.normalizer == normalizer]
            ax.errorbar(
                x.n,
                x.variance,
                yerr=1.96 * x.mcse_variance,
                marker="o",
                ms=2.5,
                lw=1.0,
                capsize=1.5,
                color=NORM_COLORS[normalizer],
                label=NORMALIZER_LABELS[normalizer],
            )
        ax.axhline(1.0, color="#111827", lw=0.8, ls="--")
        ax.set_xscale("log")
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.set_title(law)
        ax.set_ylabel("Empirical variance")
        ax.grid(alpha=0.18)
    for ax in list(axes.flat)[len(present_laws) :]:
        ax.set_visible(False)
    for ax in axes[1, :]:
        ax.set_xlabel("Lookback n")
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=2, frameon=False)
    fig.suptitle("Variance calibration across lookbacks", y=0.995, fontsize=11)
    fig.tight_layout(rect=(0, 0.075, 1, 0.97))
    save_figure(fig, figure_dir, "variance_calibration")


def plot_tail_calibration(summary: pd.DataFrame, figure_dir: Path) -> None:
    present_laws = [law for law in LAW_NAMES if law in set(summary.law)]
    fig, axes = plt.subplots(2, 3, figsize=(9.0, 5.9), sharex=True)
    normal_tail3 = 2.0 * (1.0 - ndtr(3.0))
    for ax, law in zip(axes.flat, present_laws):
        d = summary[(summary.law == law) & (summary.normalizer == "corrected")]
        ax.plot(d.n, d.p_abs_gt_3, marker="o", ms=2.8, lw=1.0, color=LAW_COLORS[law])
        ax.fill_between(
            d.n.to_numpy(float),
            (d.p_abs_gt_3 - 1.96 * d.mcse_p_abs_gt_3).clip(lower=0).to_numpy(float),
            (d.p_abs_gt_3 + 1.96 * d.mcse_p_abs_gt_3).to_numpy(float),
            color=LAW_COLORS[law],
            alpha=0.13,
        )
        ax.axhline(normal_tail3, color="#111827", lw=0.8, ls="--")
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.set_title(law)
        ax.set_ylabel(r"$P(|Z|>3)$")
        ax.grid(alpha=0.18)
    for ax in list(axes.flat)[len(present_laws) :]:
        ax.set_visible(False)
    for ax in axes[1, :]:
        ax.set_xlabel("Lookback n")
    fig.suptitle("Three-sigma tail calibration after finite-n scaling", y=0.995, fontsize=11)
    fig.tight_layout(rect=(0, 0, 1, 0.97))
    save_figure(fig, figure_dir, "three_sigma_tail_calibration")


def plot_qq_grids(quantiles: pd.DataFrame, summary: pd.DataFrame, figure_dir: Path) -> None:
    qq_probs = np.linspace(0.01, 0.99, 99)
    normal_q = ndtri(qq_probs)
    present_laws = [law for law in LAW_NAMES if law in set(summary.law)]
    for law in present_laws:
        fig, axes = plt.subplots(3, 4, figsize=(9.2, 7.1), sharex=True, sharey=True)
        for ax, n in zip(axes.flat, LOOKBACKS, strict=True):
            for normalizer, color, lw, alpha in (
                ("corrected", NORM_COLORS["corrected"], 1.15, 1.0),
                ("oracle", NORM_COLORS["oracle"], 0.9, 0.75),
            ):
                d = quantiles[
                    (quantiles.law == law)
                    & (quantiles.n == n)
                    & (quantiles.normalizer == normalizer)
                ]
                empirical = np.interp(qq_probs, d.probability, d.empirical_quantile)
                ax.plot(normal_q, empirical, color=color, lw=lw, alpha=alpha)
            ax.plot([-2.6, 2.6], [-2.6, 2.6], color="#111827", lw=0.7, ls="--")
            s = summary[(summary.law == law) & (summary.n == n) & (summary.normalizer == "corrected")].iloc[0]
            ax.text(
                0.04,
                0.96,
                f"n={n}\nKS={s.ks_to_standard_normal:.3f}\nvar={s.variance:.3f}",
                transform=ax.transAxes,
                va="top",
                ha="left",
                fontsize=6.6,
            )
            ax.grid(alpha=0.13)
            ax.set_xlim(-2.45, 2.45)
            ax.set_ylim(-2.8, 2.8)
        for ax in axes[-1, :]:
            ax.set_xlabel("Normal quantile")
        for ax in axes[:, 0]:
            ax.set_ylabel("Empirical quantile")
        legend = [
            Line2D([0], [0], color=NORM_COLORS["corrected"], lw=1.4, label="corrected"),
            Line2D([0], [0], color=NORM_COLORS["oracle"], lw=1.1, label="oracle shape"),
            Line2D([0], [0], color="#111827", lw=0.8, ls="--", label="identity"),
        ]
        fig.legend(handles=legend, loc="lower center", ncol=3, frameon=False)
        fig.suptitle(f"Normal Q-Q grid: {law}", y=0.995, fontsize=11)
        fig.tight_layout(rect=(0, 0.055, 1, 0.97))
        save_figure(fig, figure_dir, f"qq_grid_{slug(law)}")


def plot_percentile_error_heatmaps(quantiles: pd.DataFrame, figure_dir: Path) -> None:
    present_laws = [law for law in LAW_NAMES if law in set(quantiles.law)]
    probabilities = np.array([0.01, 0.025, 0.05, 0.10, 0.25, 0.75, 0.90, 0.95, 0.975, 0.99])
    fig, axes = plt.subplots(2, 3, figsize=(9.3, 5.8), sharex=True, sharey=True)
    image = None
    for ax, law in zip(axes.flat, present_laws):
        matrix = []
        for n in LOOKBACKS:
            d = quantiles[
                (quantiles.law == law)
                & (quantiles.n == n)
                & (quantiles.normalizer == "corrected")
            ]
            empirical = np.interp(probabilities, d.probability, d.empirical_quantile)
            matrix.append(empirical - ndtri(probabilities))
        matrix_arr = np.asarray(matrix).T
        image = ax.imshow(
            matrix_arr,
            origin="lower",
            aspect="auto",
            cmap="RdBu_r",
            vmin=-0.45,
            vmax=0.45,
        )
        ax.set_title(law)
        ax.set_xticks(range(len(LOOKBACKS)), labels=[str(n) for n in LOOKBACKS], rotation=45)
        ax.set_yticks(range(len(probabilities)), labels=[f"{100*p:g}%" for p in probabilities])
        ax.set_xlabel("Lookback n")
        ax.set_ylabel("Percentile")
    for ax in list(axes.flat)[len(present_laws) :]:
        ax.set_visible(False)
    if image is not None:
        colorbar_axis = fig.add_axes([0.91, 0.17, 0.018, 0.67])
        cbar = fig.colorbar(image, cax=colorbar_axis)
        cbar.set_label("Empirical minus normal quantile")
    fig.suptitle("Percentile error after finite-n scaling", y=0.995, fontsize=11)
    fig.subplots_adjust(left=0.08, right=0.88, bottom=0.12, top=0.93, wspace=0.25, hspace=0.30)
    save_figure(fig, figure_dir, "percentile_error_heatmaps")


def latex_escape(value: str) -> str:
    return value.replace("_", r"\_").replace("%", r"\%")


def generate_tex_tables(summary: pd.DataFrame, table_dir: Path) -> None:
    table_dir.mkdir(parents=True, exist_ok=True)
    selected_n = (2, 5, 13, 55, 377)
    d = summary[(summary.normalizer == "corrected") & (summary.n.isin(selected_n))]
    lines = [
        r"\begin{longtable}{llrrrrrr}",
        r"\caption{Selected results for the law-specific finite-$n$ scaling. Block MCSE is shown for the variance.}\label{tab:selected-results}\\",
        r"\toprule",
        r"Law & $n$ & Var$(Z)$ & MCSE & KS & Excess kurt. & Coverage 95\% & $P(|Z|>3)$ \\",
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        r"Law & $n$ & Var$(Z)$ & MCSE & KS & Excess kurt. & Coverage 95\% & $P(|Z|>3)$ \\",
        r"\midrule",
        r"\endhead",
    ]
    for law in LAW_NAMES:
        law_rows = d[d.law == law].sort_values("n")
        for i, row in enumerate(law_rows.itertuples(index=False)):
            display_law = latex_escape(law) if i == 0 else ""
            lines.append(
                f"{display_law} & {int(row.n)} & {row.variance:.4f} & {row.mcse_variance:.4f} "
                f"& {row.ks_to_standard_normal:.4f} & {row.excess_kurtosis:.4f} "
                f"& {row.coverage_95:.4f} & {row.p_abs_gt_3:.4f} \\\\"
            )
        lines.append(r"\addlinespace")
    lines.extend([r"\bottomrule", r"\end{longtable}"])
    (table_dir / "selected_results.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

    n2 = summary[(summary.n == 2) & (summary.normalizer.isin(NORMALIZERS))]
    lines = [
        r"\begin{table}[H]",
        r"\centering",
        r"\caption{At $n=2$, comparison of scale error with residual shape. The oracle column uses sample centering and variance and is diagnostic only.}",
        r"\label{tab:n2-diagnostic}",
        r"\begin{tabular}{lrrrrr}",
        r"\toprule",
        r"Law & Var corr. & KS asym. & KS corr. & KS oracle & Kurtosis \\",
        r"\midrule",
    ]
    for law in LAW_NAMES:
        x = n2[n2.law == law].set_index("normalizer")
        lines.append(
            f"{latex_escape(law)} & {x.loc['corrected','variance']:.4f} "
            f"& {x.loc['asymptotic','ks_to_standard_normal']:.4f} "
            f"& {x.loc['corrected','ks_to_standard_normal']:.4f} "
            f"& {x.loc['oracle','ks_to_standard_normal']:.4f} "
            f"& {x.loc['corrected','excess_kurtosis']:.4f} \\\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}", r"\end{table}"])
    (table_dir / "n2_diagnostic.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

    specs = law_specs()
    lines = [
        r"\begin{table}[H]",
        r"\centering",
        r"\caption{Scale constants and correction formulas used by the audit.}",
        r"\label{tab:constants}",
        r"\begin{tabular}{lrrl}",
        r"\toprule",
        r"Law & $C_F$ & $K_F$ & Correction used \\",
        r"\midrule",
    ]
    for law in LAW_NAMES:
        spec = specs[law]
        formula = (
            r"$n-K_F+A_F/n+B_F/n^2$"
            if spec.A is not None
            else r"$n-K_F$ (analytic note)"
        )
        lines.append(
            f"{latex_escape(law)} & {spec.C:.6f} & {spec.K:.6f} & {formula} \\\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}", r"\end{table}"])
    (table_dir / "constants.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_machine_context(result_dir: Path, args: argparse.Namespace, burn_in: int) -> None:
    specs = law_specs()
    context = {
        "script_version": SCRIPT_VERSION,
        "seed": args.seed,
        "observations_per_law_n": args.observations,
        "burn_in": burn_in,
        "burn_in_rule": "32 * max(lookbacks)",
        "blocks": args.blocks,
        "representative_rows_per_law_n": args.representative,
        "preview_rows_per_law_n": args.preview,
        "lookbacks": list(LOOKBACKS),
        "laws": [asdict(specs[name]) for name in LAW_NAMES],
        "normalizers": list(NORMALIZERS),
        "python": sys.version,
        "platform": platform.platform(),
        "numpy": np.__version__,
        "scipy": scipy.__version__,
        "pandas": pd.__version__,
        "matplotlib": matplotlib.__version__,
    }
    (result_dir / "simulation_config.json").write_text(
        json.dumps(context, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def generate_quality_checks(result_dir: Path) -> None:
    summary = pd.read_csv(result_dir / "summary_metrics.csv")
    blocks = pd.read_csv(result_dir / "block_metrics.csv.gz")
    selected_laws = list(dict.fromkeys(summary.law.tolist()))
    expected_rows = len(selected_laws) * len(LOOKBACKS) * len(NORMALIZERS)

    predicted_variance = np.where(
        summary.normalizer == "asymptotic",
        summary.n / summary.g_empirical,
        np.where(
            summary.normalizer == "corrected",
            summary.g_corrected / summary.g_empirical,
            1.0,
        ),
    )
    identity_error = np.max(np.abs(summary.variance - predicted_variance))

    metric_names = [
        "mean",
        "variance",
        "skewness",
        "excess_kurtosis",
        "coverage_95",
        "coverage_99",
        "p_abs_gt_3",
    ]
    split_rows: list[dict[str, object]] = []
    for keys, group in blocks.groupby(["law", "n", "normalizer"], sort=False):
        group = group.sort_values("block")
        midpoint = len(group) // 2
        first = group.iloc[:midpoint]
        second = group.iloc[midpoint:]
        for metric in metric_names:
            first_mean = float(first[metric].mean())
            second_mean = float(second[metric].mean())
            pooled_se = math.sqrt(
                float(first[metric].var(ddof=1)) / len(first)
                + float(second[metric].var(ddof=1)) / len(second)
            )
            split_rows.append(
                {
                    "law": keys[0],
                    "n": keys[1],
                    "normalizer": keys[2],
                    "metric": metric,
                    "first_half": first_mean,
                    "second_half": second_mean,
                    "difference_second_minus_first": second_mean - first_mean,
                    "pooled_mcse": pooled_se,
                    "difference_z_score": (second_mean - first_mean) / pooled_se
                    if pooled_se > 0
                    else 0.0,
                }
            )
    stability = pd.DataFrame(split_rows)
    stability.to_csv(result_dir / "stability_checks.csv", index=False)

    required_numeric_columns = [
        column
        for column in summary.select_dtypes(include=[np.number]).columns
        if column not in {"A", "B"}
    ]
    numeric_summary = summary[required_numeric_columns]
    checks = {
        "status": "PASS",
        "expected_summary_rows": expected_rows,
        "actual_summary_rows": int(len(summary)),
        "duplicate_summary_keys": int(
            summary.duplicated(["law", "n", "normalizer"]).sum()
        ),
        "nonfinite_summary_values": int((~np.isfinite(numeric_summary.to_numpy())).sum()),
        "max_variance_identity_abs_error": float(identity_error),
        "representative_rows": int(
            sum(
                len(chunk)
                for path in sorted((result_dir / "representative_draws").glob("*.csv.gz"))
                for chunk in pd.read_csv(path, chunksize=100_000)
            )
        ),
        "max_abs_split_half_z_score": float(stability.difference_z_score.abs().max()),
        "split_half_rows_with_abs_z_above_3": int(
            (stability.difference_z_score.abs() > 3.0).sum()
        ),
        "note": (
            "The split-half z scores are diagnostics, not independent hypothesis tests; "
            "hundreds of correlated comparisons are reported without multiplicity adjustment."
        ),
    }
    if (
        checks["actual_summary_rows"] != checks["expected_summary_rows"]
        or checks["duplicate_summary_keys"] != 0
        or checks["nonfinite_summary_values"] != 0
        or identity_error > 1e-10
    ):
        checks["status"] = "FAIL"
    (result_dir / "quality_checks.json").write_text(
        json.dumps(checks, indent=2) + "\n", encoding="utf-8"
    )
    if checks["status"] != "PASS":
        raise RuntimeError(f"Quality checks failed: {checks}")


def generate_figures(result_dir: Path, figure_dir: Path) -> None:
    print("\nGenerating figures from exported CSV files", flush=True)
    generate_quality_checks(result_dir)
    configure_matplotlib()
    summary = pd.read_csv(result_dir / "summary_metrics.csv")
    quantiles = pd.read_csv(result_dir / "quantile_grid.csv.gz")
    generate_tex_tables(summary, figure_dir.parent / "tables")
    plot_overview(summary, figure_dir)
    plot_normalizer_comparison(summary, figure_dir)
    plot_variance_calibration(summary, figure_dir)
    plot_tail_calibration(summary, figure_dir)
    plot_qq_grids(quantiles, summary, figure_dir)
    plot_percentile_error_heatmaps(quantiles, figure_dir)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--observations", type=int, default=DEFAULT_OBSERVATIONS)
    parser.add_argument("--blocks", type=int, default=DEFAULT_BLOCKS)
    parser.add_argument("--representative", type=int, default=DEFAULT_REPRESENTATIVE)
    parser.add_argument("--preview", type=int, default=DEFAULT_PREVIEW)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--plots-only", action="store_true", help="Regenerate figures from existing CSV files")
    parser.add_argument("--force", action="store_true", help="Ignore compatible law-level cache files")
    parser.add_argument(
        "--laws",
        nargs="+",
        choices=LAW_NAMES,
        default=list(LAW_NAMES),
        help="Subset of laws; the final combined outputs contain exactly this subset",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = Path(__file__).resolve().parent
    result_dir = root / "results"
    part_dir = result_dir / "parts"
    figure_dir = root / "figures"
    result_dir.mkdir(parents=True, exist_ok=True)
    part_dir.mkdir(parents=True, exist_ok=True)
    figure_dir.mkdir(parents=True, exist_ok=True)
    burn_in = 32 * max(LOOKBACKS)

    if not args.plots_only:
        specs = law_specs()
        for law in args.laws:
            spec = specs[law]
            expected = expected_part_metadata(
                spec,
                args.observations,
                burn_in,
                args.blocks,
                args.representative,
                args.seed,
            )
            metadata_path = part_dir / f"metadata_{slug(law)}.json"
            if not args.force and metadata_matches(metadata_path, expected):
                print(f"[{law}] compatible cached part found; skipping simulation", flush=True)
                continue
            simulate_law(
                spec=spec,
                observations=args.observations,
                burn_in=burn_in,
                blocks=args.blocks,
                representative=args.representative,
                preview=args.preview,
                seed=args.seed,
                part_dir=part_dir,
            )
            metadata_path.write_text(json.dumps(expected, indent=2) + "\n", encoding="utf-8")
        combine_parts(result_dir, args.laws)
        write_machine_context(result_dir, args, burn_in)

    generate_figures(result_dir, figure_dir)
    print("\nNORMALITY AUDIT COMPLETED", flush=True)


if __name__ == "__main__":
    main()
