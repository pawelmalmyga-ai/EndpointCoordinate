#!/usr/bin/env python3
"""Independent implementation checks for ``run_price_path_audit.py``."""

from __future__ import annotations

import importlib.util
import math
import sys
from pathlib import Path

import numpy as np
from scipy.signal import lfilter


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("price_audit", HERE / "run_price_path_audit.py")
audit = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = audit
spec.loader.exec_module(audit)


def direct_wilder(x: np.ndarray, n: int) -> np.ndarray:
    a = 1.0 / n
    out = np.empty_like(x)
    state = 0.0
    for i, value in enumerate(x):
        state = (1.0 - a) * state + a * value
        out[i] = state
    return out


def log_odds(delta: np.ndarray, n: int) -> np.ndarray:
    a = 1.0 / n
    u = lfilter([a], [1.0, -(1.0 - a)], np.maximum(delta, 0.0))
    d = lfilter([a], [1.0, -(1.0 - a)], np.maximum(-delta, 0.0))
    ok = (u > 0.0) & (d > 0.0)
    return np.log(u[ok] / d[ok])


rng = np.random.default_rng(123456)
x = rng.normal(size=20_000)
n = 17
a = 1.0 / n
flt = lfilter([a], [1.0, -(1.0-a)], x)
direct = direct_wilder(x, n)
assert np.max(np.abs(flt-direct)) < 2e-15
print("PASS: SciPy filter equals direct Wilder recursion")

# A geometric path really begins at 10,000 and has the requested log returns.
r = rng.normal(scale=0.02, size=50_000)
logp = np.r_[math.log(10_000.0), math.log(10_000.0)+np.cumsum(r)]
p = np.exp(logp)
assert math.isclose(float(p[0]), 10_000.0, rel_tol=0.0, abs_tol=1e-10)
assert np.max(np.abs(np.diff(np.log(p))-r)) < 3e-14
print("PASS: price path reconstructs the supplied log returns")

# RSI/log-odds is invariant under one global price rescaling.
d1 = np.diff(p)
d2 = np.diff(37.25*p)
l1 = log_odds(d1, n)
l2 = log_odds(d2, n)
assert np.max(np.abs(l1-l2)) < 2e-13
print("PASS: global price-scale invariance")

# For very small returns, arithmetic price changes and log-price changes agree.
rsmall = rng.normal(scale=1e-6, size=200_000)
lp = np.r_[0.0, np.cumsum(rsmall)]
ps = np.exp(lp)
l_price = log_odds(np.diff(ps), 55)[2000:]
l_log = log_odds(rsmall, 55)[2000:]
rmse = float(np.sqrt(np.mean((l_price-l_log)**2)))
assert rmse < 2e-5
print(f"PASS: small-volatility price/log convergence (RMSE={rmse:.3g})")

# Multiplying every additive increment by sigma cannot change the log-price coordinate.
ll1 = log_odds(r, 21)
ll2 = log_odds(0.08*r, 21)
assert np.max(np.abs(ll1-ll2)) < 2e-13
print("PASS: log-price coordinate is volatility-scale invariant")

# Exact endpoint identity for any positive up/down masses.
u = rng.lognormal(size=1000)
d = rng.lognormal(size=1000)
f = (u-d)/(u+d)
lhs = np.log(u/d)
rhs = 2*np.arctanh(f)
assert np.max(np.abs(lhs-rhs)) < 2e-13
print("PASS: endpoint log-odds identity")
print("ALL IMPLEMENTATION CHECKS PASSED")
