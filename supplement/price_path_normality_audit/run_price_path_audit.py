#!/usr/bin/env python3
"""Reproducible price-path robustness audit for the EndpointCoordinate paper.

Symmetric iid unit-variance log returns are multiplied by ``sigma`` and
exponentiated into a positive price path beginning at 10,000.  Classical RSI
uses arithmetic price changes.  The same innovations are also processed as
log-price changes, providing the additive benchmark covered directly by the
manuscript.

The expensive simulation is resumable by law/volatility cell.  Final CSVs are
compressed and figures can be regenerated with ``--plots-only``.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
import os
import platform
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import scipy
from scipy.signal import lfilter
from scipy.special import gammaln, ndtr, ndtri


SCRIPT_VERSION = "1.0.0"
SEED = 20260925
OBSERVATIONS = 3_000_000
BLOCKS = 192
REPRESENTATIVE = 2_500
PREVIEW = 50
INITIAL_PRICE = 10_000.0
LOOKBACKS = (2, 3, 5, 8, 13, 21, 35, 55, 89, 144, 233, 377)
SIGMAS = (0.005, 0.01, 0.02, 0.04, 0.08)
LAW_NAMES = ("Gaussian", "Laplace", "Student-t4", "Student-t5", "Student-t6", "Student-t8")
COORDINATES = ("price", "log_price")
NORMALIZERS = ("asymptotic", "corrected", "corrected_centered", "oracle")


@dataclass(frozen=True)
class LawSpec:
    name: str
    family: str
    nu: float | None
    C: float
    K: float
    A: float | None
    B: float | None
    correction_status: str


def student_constants(nu: float) -> tuple[float, float]:
    lr = gammaln(nu / 2.0) - gammaln((nu - 1.0) / 2.0)
    c = math.sqrt(2.0 * math.pi / (nu - 2.0)) * math.exp(lr)
    k = 1.25 * c * c - 7.0 / 3.0 - 8.0 / (3.0 * (nu - 3.0))
    return c, k


def law_specs() -> dict[str, LawSpec]:
    pi = math.pi
    out = {
        "Gaussian": LawSpec("Gaussian", "Gaussian", None, math.sqrt(pi),
            (15*pi-28)/12, (856+240*pi-159*pi*pi)/144,
            (89220*pi*pi+130784-28344*pi-29475*pi**3)/8640,
            "proved light-tail expansion"),
        "Laplace": LawSpec("Laplace", "Laplace", None, 2.0, 4/3, 5/18, 5/27,
            "proved light-tail expansion"),
    }
    for nu in (4.0, 5.0, 6.0, 8.0):
        c, k = student_constants(nu)
        name = f"Student-t{int(nu)}"
        out[name] = LawSpec(name, "Student-t", nu, c, k, None, None,
                            "conventional first-shift correction; outside Lean")
    return out


def slug(s: str) -> str:
    return s.lower().replace("-", "_").replace(".", "p")


def sigma_slug(sigma: float) -> str:
    return f"{100*sigma:g}pct".replace(".", "p")


def stable_seed(seed: int, *parts: object) -> int:
    b = "|".join([str(seed), *(str(x) for x in parts)]).encode()
    return int.from_bytes(hashlib.sha256(b).digest()[:8], "little")


def innovations(spec: LawSpec, rng: np.random.Generator, size: int) -> np.ndarray:
    if spec.family == "Gaussian":
        return rng.normal(size=size)
    if spec.family == "Laplace":
        return rng.laplace(scale=1/math.sqrt(2), size=size)
    nu = float(spec.nu)
    return rng.standard_t(nu, size=size) * math.sqrt((nu-2)/nu)


def g_corrected(spec: LawSpec, n: int) -> float:
    g = n - spec.K
    if spec.A is not None:
        g += spec.A/n + float(spec.B)/(n*n)
    return float(g)


def linear_quantiles(sorted_x: np.ndarray, p: np.ndarray) -> np.ndarray:
    h = (len(sorted_x)-1)*p
    lo = np.floor(h).astype(np.int64)
    hi = np.ceil(h).astype(np.int64)
    f = h-lo
    return sorted_x[lo]*(1-f) + sorted_x[hi]*f


def exact_ks(sorted_z: np.ndarray) -> float:
    n = len(sorted_z)
    cdf = ndtr(sorted_z)
    return float(max(np.max(np.arange(1,n+1)/n-cdf),
                     np.max(cdf-np.arange(0,n)/n)))


def views(L: np.ndarray, spec: LawSpec, n: int) -> dict[str, np.ndarray]:
    g = g_corrected(spec, n)
    mu = float(L.mean())
    sd = float(L.std(ddof=1))
    return {
        "asymptotic": math.sqrt(n)/spec.C*L,
        "corrected": math.sqrt(g)/spec.C*L,
        "corrected_centered": math.sqrt(g)/spec.C*(L-mu),
        "oracle": (L-mu)/sd,
    }


def summary_row(z: np.ndarray, sorted_z: np.ndarray, qqp: np.ndarray) -> dict[str, float]:
    mu = float(z.mean())
    c = z-mu
    m2 = float(np.mean(c*c))
    m3 = float(np.mean(c*c*c))
    m4 = float(np.mean(c*c*c*c))
    qe = linear_quantiles(sorted_z, qqp)
    qn = ndtri(qqp)
    slope, intercept = np.polyfit(qn, qe, 1)
    fit = intercept+slope*qn
    ssr = float(np.sum((qe-fit)**2))
    sst = float(np.sum((qe-qe.mean())**2))
    return {
        "mean": mu,
        "variance": float(z.var(ddof=1)),
        "skewness": m3/m2**1.5,
        "excess_kurtosis": m4/m2**2-3,
        "ks_to_standard_normal": exact_ks(sorted_z),
        "wasserstein_quantile_grid": float(np.mean(np.abs(qe-qn))),
        "qq_intercept": float(intercept),
        "qq_slope": float(slope),
        "qq_r_squared": 1-ssr/sst,
        "qq_max_abs_error_0_5pct_99_5pct": float(np.max(np.abs(qe-qn))),
        "coverage_95": float(np.mean(np.abs(z)<=1.959963984540054)),
        "coverage_99": float(np.mean(np.abs(z)<=2.5758293035489004)),
        "p_abs_gt_2": float(np.mean(np.abs(z)>2)),
        "p_abs_gt_3": float(np.mean(np.abs(z)>3)),
    }


def block_frame(z: np.ndarray, blocks: int) -> pd.DataFrame:
    bs = len(z)//blocks
    x = z[:bs*blocks].reshape(blocks, bs)
    means = x.mean(1)
    c = x-means[:,None]
    m2 = np.mean(c*c,1)
    return pd.DataFrame({
        "block": np.arange(blocks), "block_size": bs,
        "mean": means, "variance": x.var(1,ddof=1),
        "skewness": np.mean(c**3,1)/m2**1.5,
        "excess_kurtosis": np.mean(c**4,1)/m2**2-3,
        "coverage_95": np.mean(np.abs(x)<=1.959963984540054,1),
        "coverage_99": np.mean(np.abs(x)<=2.5758293035489004,1),
        "p_abs_gt_3": np.mean(np.abs(x)>3,1),
    })


def coordinate_rows(
    increments: np.ndarray,
    spec: LawSpec,
    coordinate: str,
    sigma: float,
    burn: int,
    observations: int,
    blocks: int,
    representative: int,
    preview: int,
    seed: int,
) -> dict[str, list[pd.DataFrame] | list[dict]]:
    up = np.maximum(increments, 0.0)
    down = np.maximum(-increments, 0.0)
    qp = np.unique(np.r_[0.0005, np.linspace(.001,.999,999), .9995])
    qqp = np.linspace(.005,.995,399)
    ecgrid = np.linspace(-5,5,1001)
    hedges = np.linspace(-6,6,481)
    out: dict[str, list] = {k: [] for k in
        ("summary","quantiles","ecdf","histogram","blocks","representative","preview")}

    for n in LOOKBACKS:
        a = 1/n
        lam = 1-a
        U = lfilter([a],[1,-lam],up)[burn:]
        D = lfilter([a],[1,-lam],down)[burn:]
        if np.any(U<=0) or np.any(D<=0):
            raise RuntimeError(f"nonpositive mass: {spec.name}, sigma={sigma}, {coordinate}, n={n}")
        L = np.log(U/D)
        del U,D
        sorted_L = np.sort(L)
        vv = views(L,spec,n)
        lmu = float(L.mean()); lvar = float(L.var(ddof=1))
        g = g_corrected(spec,n); gemp = spec.C**2/lvar

        rr = np.random.default_rng(stable_seed(seed,spec.name,sigma,coordinate,n,"representative"))
        rc = min(representative,observations)
        idx = np.sort(rr.choice(observations,size=rc,replace=False))
        rep = pd.DataFrame({"law":spec.name,"sigma":sigma,"coordinate":coordinate,
                            "n":n,"path_index":idx,"L":L[idx]})
        for nm,z in vv.items(): rep[f"z_{nm}"] = z[idx]
        out["representative"].append(rep)
        pc=min(preview,rc); out["preview"].append(rep.iloc[np.linspace(0,rc-1,pc,dtype=int)].copy())

        for nm,z in vv.items():
            if nm=="oracle": sorted_z=(sorted_L-lmu)/math.sqrt(lvar)
            elif nm=="corrected_centered": sorted_z=(sorted_L-lmu)*math.sqrt(g)/spec.C
            else: sorted_z=sorted_L*(math.sqrt(n) if nm=="asymptotic" else math.sqrt(g))/spec.C
            base={"law":spec.name,"sigma":sigma,"coordinate":coordinate,"n":n,
                  "normalizer":nm}
            sr=base|summary_row(z,sorted_z,qqp)|{
                "observations":observations,"C":spec.C,"K":spec.K,"A":spec.A,"B":spec.B,
                "g_corrected":g,"g_empirical":gemp,"L_mean":lmu,"L_variance":lvar,
                "correction_status":spec.correction_status}
            out["summary"].append(sr)

            qv=linear_quantiles(sorted_z,qp); qn=ndtri(qp)
            out["quantiles"].append(pd.DataFrame(base|{
                "probability":qp,"empirical_quantile":qv,"normal_quantile":qn,
                "quantile_error":qv-qn}))
            ev=np.searchsorted(sorted_z,ecgrid,side="right")/observations
            out["ecdf"].append(pd.DataFrame(base|{"z":ecgrid,"empirical_cdf":ev,
                "normal_cdf":ndtr(ecgrid),"cdf_error":ev-ndtr(ecgrid)}))
            counts,_=np.histogram(z,bins=hedges); ctr=(hedges[:-1]+hedges[1:])/2
            dens=counts/(observations*np.diff(hedges))
            out["histogram"].append(pd.DataFrame(base|{
                "bin_left":hedges[:-1],"bin_right":hedges[1:],"bin_center":ctr,
                "count":counts,"density":dens,
                "normal_density":np.exp(-ctr*ctr/2)/math.sqrt(2*math.pi)}))
            bf=block_frame(z,blocks)
            for k,v in base.items(): bf[k]=v
            out["blocks"].append(bf)
        print(f"  {coordinate:9s} sigma={sigma:.3f} n={n:3d} Var(L)={lvar:.7g} g_emp={gemp:.5f}",flush=True)
    return out


def frames(rows: dict[str,list]) -> dict[str,pd.DataFrame]:
    return {k:(pd.DataFrame(v) if k=="summary" else pd.concat(v,ignore_index=True)) for k,v in rows.items()}


def relabel_sigma(base: dict[str,pd.DataFrame], sigma: float) -> dict[str,pd.DataFrame]:
    out={}
    for k,v in base.items():
        x=v.copy(); x["sigma"]=sigma; out[k]=x
    return out


def write_gzip_csv_atomic(df: pd.DataFrame, path: Path) -> None:
    """Write a complete gzip member and expose it only after close succeeds."""
    tmp = path.with_name(path.name + ".tmp")
    df.to_csv(tmp, index=False, compression={"method": "gzip", "compresslevel": 6})
    os.replace(tmp, path)


def valid_gzip(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        with gzip.open(path, "rb") as fh:
            while fh.read(1024 * 1024):
                pass
        return True
    except (OSError, EOFError):
        return False


def write_cell(part_dir: Path, spec: LawSpec, sigma: float,
               log_base: dict[str,pd.DataFrame], price: dict[str,pd.DataFrame],
               metadata: dict) -> None:
    pfx=f"{slug(spec.name)}_{sigma_slug(sigma)}"
    merged={k:pd.concat([log_base[k],price[k]],ignore_index=True) for k in log_base}
    for k,df in merged.items():
        write_gzip_csv_atomic(df, part_dir/f"{k}_{pfx}.csv.gz")
    meta_tmp = part_dir/f"metadata_{pfx}.json.tmp"
    meta_tmp.write_text(json.dumps(metadata,indent=2),encoding="utf-8")
    os.replace(meta_tmp, part_dir/f"metadata_{pfx}.json")


def simulate_law(spec: LawSpec, args: argparse.Namespace, result_dir: Path) -> None:
    burn=32*max(LOOKBACKS); total=args.observations+burn
    part_dir=result_dir/"parts"; part_dir.mkdir(parents=True,exist_ok=True)
    rng=np.random.default_rng(stable_seed(args.seed,spec.name))
    eps=innovations(spec,rng,total)
    print(f"\n[{spec.name}] {args.observations:,} retained; common path for five sigmas",flush=True)

    # Log-price RSI is homogeneous in sigma, so calculate it once and relabel.
    log_rows=coordinate_rows(eps,spec,"log_price",SIGMAS[0],burn,args.observations,
                             args.blocks,args.representative,args.preview,args.seed)
    log_base=frames(log_rows)

    logp0=math.log(INITIAL_PRICE)
    for sigma in SIGMAS:
        pfx=f"{slug(spec.name)}_{sigma_slug(sigma)}"
        meta_path=part_dir/f"metadata_{pfx}.json"
        expected={"script_version":SCRIPT_VERSION,"law":asdict(spec),"sigma":sigma,
                  "seed":args.seed,"observations":args.observations,"burn_in":burn,
                  "blocks":args.blocks,"representative":args.representative,
                  "preview":args.preview,"lookbacks":list(LOOKBACKS),
                  "initial_price":INITIAL_PRICE}
        required=[part_dir/f"{k}_{pfx}.csv.gz" for k in
                  ("summary","quantiles","ecdf","histogram","blocks","representative","preview")]
        if meta_path.exists() and all(valid_gzip(p) for p in required):
            try:
                if json.loads(meta_path.read_text())==expected:
                    print(f"  sigma={sigma:.3f}: cached",flush=True); continue
            except json.JSONDecodeError: pass

        r=sigma*eps
        logp=np.empty(total+1); logp[0]=logp0; logp[1:]=logp0+np.cumsum(r)
        # A global multiplicative rescaling leaves every U/D ratio unchanged.
        shift=(float(logp.min())+float(logp.max()))/2
        price=np.exp(logp-shift)
        delta=np.diff(price)
        price_rows=frames(coordinate_rows(delta,spec,"price",sigma,burn,args.observations,
                            args.blocks,args.representative,args.preview,args.seed))
        write_cell(part_dir,spec,sigma,relabel_sigma(log_base,sigma),price_rows,expected)
        print(f"  sigma={sigma:.3f}: saved",flush=True)


def combine(result_dir: Path, specs: dict[str,LawSpec]) -> None:
    part=result_dir/"parts"
    keys=("summary","quantiles","ecdf","histogram","blocks","representative","preview")
    outputs={"summary":"summary_metrics.csv","quantiles":"quantile_grid.csv.gz",
             "ecdf":"ecdf_grid.csv.gz","histogram":"histogram_density.csv.gz",
             "blocks":"block_metrics.csv.gz","representative":"representative_draws.csv.gz",
             "preview":"representative_draws_preview.csv"}
    for k in keys:
        ps=[part/f"{k}_{slug(law)}_{sigma_slug(s)}.csv.gz" for law in specs for s in SIGMAS]
        missing=[str(p) for p in ps if not p.exists()]
        if missing: raise FileNotFoundError(f"missing {len(missing)} part files for {k}")
        df=pd.concat((pd.read_csv(p) for p in ps),ignore_index=True)
        out=result_dir/outputs[k]
        df.to_csv(out,index=False,compression="gzip" if out.suffix==".gz" else None)
        print(f"combined {out.name}: {len(df):,} rows",flush=True)

    summary=pd.read_csv(result_dir/"summary_metrics.csv")
    blocks=pd.read_csv(result_dir/"block_metrics.csv.gz")
    group=["law","sigma","coordinate","n","normalizer"]
    cols=["mean","variance","skewness","excess_kurtosis","coverage_95","coverage_99","p_abs_gt_3"]
    se=blocks.groupby(group)[cols].sem().reset_index().rename(columns={c:f"mcse_{c}" for c in cols})
    summary=summary.merge(se,on=group,how="left")
    summary.to_csv(result_dir/"summary_metrics.csv",index=False)


def setup_plot() -> None:
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":8.2,"axes.grid":True,
                         "grid.alpha":.25,"figure.dpi":130,"savefig.bbox":"tight"})


def savefig(fig: plt.Figure, d: Path, stem: str) -> None:
    png = d/f"{stem}.png"; pdf = d/f"{stem}.pdf"
    png_tmp = d/f"{stem}.tmp.png"; pdf_tmp = d/f"{stem}.tmp.pdf"
    fig.savefig(png_tmp,dpi=180)
    fig.savefig(pdf_tmp)
    os.replace(png_tmp,png); os.replace(pdf_tmp,pdf)
    plt.close(fig)


def plot_qq(q: pd.DataFrame, s: pd.DataFrame, figdir: Path) -> None:
    use=q[(q.normalizer=="corrected_centered") & q.probability.between(.005,.995)]
    for law in LAW_NAMES:
        for sigma in SIGMAS:
            fig,axs=plt.subplots(3,4,figsize=(12,8),sharex=True,sharey=True)
            for ax,n in zip(axs.flat,LOOKBACKS):
                for coord,color,label in (("price","#d97706","price RSI"),("log_price","#2563eb","log-price RSI")):
                    x=use[(use.law==law)&np.isclose(use.sigma,sigma)&(use.coordinate==coord)&(use.n==n)]
                    ax.plot(x.normal_quantile,x.empirical_quantile,color=color,lw=1.2,label=label)
                ax.plot([-3,3],[-3,3],color="black",lw=.7,ls="--")
                r=s[(s.law==law)&np.isclose(s.sigma,sigma)&(s.coordinate=="price")&(s.n==n)&(s.normalizer=="corrected_centered")].iloc[0]
                ax.set_title(
                    f"n={n}\nprice: KS={r.ks_to_standard_normal:.3f}, Var={r.variance:.3f}",
                    fontsize=8,
                )
            fig.suptitle(f"{law}, log-return volatility {100*sigma:.1f}%")
            fig.supxlabel("Normal quantile"); fig.supylabel("Empirical quantile")
            axs.flat[-1].legend(loc="lower right",fontsize=7)
            savefig(fig,figdir,f"qq_grid_{slug(law)}_{sigma_slug(sigma)}")


def plot_heatmaps(q: pd.DataFrame, figdir: Path) -> None:
    use=q[(q.normalizer=="corrected_centered") & q.probability.between(.01,.99)]
    for law in LAW_NAMES:
        for coord in COORDINATES:
            x=use[(use.law==law)&(use.coordinate==coord)]
            # RMSE of quantile error by sigma and n.
            tab=x.groupby(["sigma","n"]).quantile_error.apply(lambda z:float(np.sqrt(np.mean(z*z)))).unstack()
            fig,ax=plt.subplots(figsize=(10,3.6))
            im=ax.imshow(tab.values,aspect="auto",cmap="magma",origin="lower")
            ax.set_xticks(range(len(tab.columns)),tab.columns); ax.set_yticks(range(len(tab.index)),[f"{100*v:g}%" for v in tab.index])
            ax.set_xlabel("Lookback n"); ax.set_ylabel("Log-return volatility")
            ax.set_title(f"Quantile RMSE: {law}, {coord.replace('_',' ')}")
            fig.colorbar(im,ax=ax,label="RMSE")
            savefig(fig,figdir,f"percentile_error_{slug(law)}_{coord}")


def plot_overviews(s: pd.DataFrame, figdir: Path) -> None:
    x=s[s.normalizer=="corrected_centered"]
    colors={"price":"#d97706","log_price":"#2563eb"}
    for n in (55,377):
        fig,axs=plt.subplots(2,3,figsize=(11,6),sharex=True,sharey=True)
        for ax,law in zip(axs.flat,LAW_NAMES):
            for coord in COORDINATES:
                y=x[(x.law==law)&(x.n==n)&(x.coordinate==coord)].sort_values("sigma")
                ax.plot(100*y.sigma,y.ks_to_standard_normal,marker="o",color=colors[coord],label=coord.replace('_',' '))
            ax.set_title(law); ax.set_xlabel("Volatility (%)"); ax.set_ylabel("KS")
        axs.flat[-1].legend(fontsize=7)
        fig.suptitle(f"Price versus log-price RSI at n={n}")
        savefig(fig,figdir,f"price_vs_log_ks_n{n}")
    for sigma in (.01,.02):
        fig,axs=plt.subplots(1,2,figsize=(10,4))
        for law in LAW_NAMES:
            y=x[(x.law==law)&np.isclose(x.sigma,sigma)&(x.coordinate=="price")].sort_values("n")
            axs[0].plot(y.n,y.ks_to_standard_normal,marker="o",ms=3,label=law)
            axs[1].plot(y.n,y.variance,marker="o",ms=3,label=law)
        for ax in axs: ax.set_xscale("log"); ax.set_xlabel("Lookback n")
        axs[0].set_ylabel("KS"); axs[1].set_ylabel("Variance")
        axs[1].axhline(1,color="black",lw=.7,ls="--")
        axs[1].legend(fontsize=6,ncol=2)
        fig.suptitle(f"Classical price RSI after correction, volatility {100*sigma:g}%")
        savefig(fig,figdir,f"corrected_price_summary_{sigma_slug(sigma)}")


def quality(result_dir: Path, args: argparse.Namespace) -> dict:
    s=pd.read_csv(result_dir/"summary_metrics.csv")
    required=["mean","variance","skewness","excess_kurtosis","ks_to_standard_normal"]
    expected=len(LAW_NAMES)*len(SIGMAS)*len(LOOKBACKS)*len(COORDINATES)*len(NORMALIZERS)
    dup=int(s.duplicated(["law","sigma","coordinate","n","normalizer"]).sum())
    nonfinite=int((~np.isfinite(s[required].to_numpy())).sum())
    e1=np.max(np.abs(s[s.normalizer=="asymptotic"].variance-
                     s[s.normalizer=="asymptotic"].n/s[s.normalizer=="asymptotic"].g_empirical))
    c=s[s.normalizer=="corrected"]
    e2=np.max(np.abs(c.variance-c.g_corrected/c.g_empirical))
    # Log coordinate must be exactly sigma invariant apart from CSV roundoff.
    lg=s[(s.coordinate=="log_price")&(s.normalizer=="corrected_centered")]
    spread=lg.groupby(["law","n"])["variance"].agg(lambda z:float(z.max()-z.min())).max()
    out={"status":"PASS" if len(s)==expected and dup==0 and nonfinite==0 and e1<2e-12 and e2<2e-12 and spread<2e-12 else "FAIL",
         "expected_summary_rows":expected,"actual_summary_rows":len(s),"duplicate_keys":dup,
         "nonfinite_required_metrics":nonfinite,"max_asymptotic_variance_identity_error":float(e1),
         "max_corrected_variance_identity_error":float(e2),"max_log_coordinate_sigma_variance_spread":float(spread)}
    (result_dir/"quality_checks.json").write_text(json.dumps(out,indent=2),encoding="utf-8")
    return out


def write_context(result_dir: Path,args:argparse.Namespace) -> None:
    obj={"script_version":SCRIPT_VERSION,"seed":args.seed,"observations_per_law_sigma":args.observations,
         "burn_in":32*max(LOOKBACKS),"blocks":args.blocks,"representative_per_coordinate_n":args.representative,
         "preview_per_coordinate_n":args.preview,"initial_price":INITIAL_PRICE,"lookbacks":list(LOOKBACKS),
         "sigmas":list(SIGMAS),"laws":list(LAW_NAMES),"coordinates":list(COORDINATES),
         "normalizers":list(NORMALIZERS),"python":sys.version,"platform":platform.platform(),
         "numpy":np.__version__,"pandas":pd.__version__,"scipy":scipy.__version__,
         "matplotlib":matplotlib.__version__}
    (result_dir/"run_metadata.json").write_text(json.dumps(obj,indent=2),encoding="utf-8")


def parse_args() -> argparse.Namespace:
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path,default=Path(__file__).resolve().parent)
    p.add_argument("--laws",nargs="*",choices=LAW_NAMES,default=list(LAW_NAMES))
    p.add_argument("--observations",type=int,default=OBSERVATIONS)
    p.add_argument("--blocks",type=int,default=BLOCKS)
    p.add_argument("--representative",type=int,default=REPRESENTATIVE)
    p.add_argument("--preview",type=int,default=PREVIEW)
    p.add_argument("--seed",type=int,default=SEED)
    p.add_argument("--simulate-only",action="store_true")
    p.add_argument("--combine-only",action="store_true")
    p.add_argument("--plots-only",action="store_true")
    return p.parse_args()


def main() -> None:
    args=parse_args(); root=args.output; result=root/"results"; fig=root/"figures"
    result.mkdir(parents=True,exist_ok=True); fig.mkdir(parents=True,exist_ok=True)
    specs=law_specs()
    if not args.combine_only and not args.plots_only:
        for name in args.laws: simulate_law(specs[name],args,result)
    if args.simulate_only: return
    if not args.plots_only: combine(result,specs)
    write_context(result,args)
    qc=quality(result,args); print(json.dumps(qc,indent=2),flush=True)
    if qc["status"]!="PASS": raise RuntimeError("quality checks failed")
    setup_plot(); s=pd.read_csv(result/"summary_metrics.csv"); q=pd.read_csv(result/"quantile_grid.csv.gz")
    plot_overviews(s,fig); plot_qq(q,s,fig); plot_heatmaps(q,fig)
    print(f"ALL PRICE-PATH AUDIT CHECKS PASSED; figures={len(list(fig.glob('*')))}",flush=True)


if __name__=="__main__":
    main()
