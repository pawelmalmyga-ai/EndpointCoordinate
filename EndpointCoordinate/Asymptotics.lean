import EndpointCoordinate.Stationary

set_option linter.style.header false

/-!
# Endpoint coordinate: deterministic asymptotic transfer

This module isolates the analytic step between the bounded endpoint coordinate
`F` and its unbounded log-odds coordinate `L = logOdds F`.

The statements are distribution-free.  Their purpose is to let a later
probability module concentrate on the central limit theorem for `F`: once
`F` tends to zero and a scaled version of `F` has a limit, the factor `2`
in the corresponding first-order limit for `L` is forced by calculus.
-/

namespace EndpointCoordinate

noncomputable section

open Asymptotics Filter Set
open scoped Topology

/-! ## Local calculus of the log-odds map -/

@[simp]
theorem logOdds_zero : logOdds 0 = 0 := by
  simp [logOdds, oddsRatio]

/-- The exact derivative of log-odds on the interior of its natural domain. -/
theorem hasDerivAt_logOdds
    {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt logOdds (2 / (1 - x ^ 2)) x := by
  have hOneSub : 1 - x ≠ 0 := by linarith [hx.2]
  have hOneAdd : 1 + x ≠ 0 := by linarith [hx.1]
  have hOneSq : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero hOneSub hOneAdd
  have hRatio : (1 + x) / (1 - x) ≠ 0 := by
    apply div_ne_zero
    · linarith [hx.1]
    · exact hOneSub
  have hNum : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have hDen : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hQuot :
      HasDerivAt (fun y : ℝ ↦ (1 + y) / (1 - y))
        ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x :=
    hNum.div hDen hOneSub
  have hLog := hQuot.log hRatio
  have hLog' :
      HasDerivAt logOdds
        (((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) /
          ((1 + x) / (1 - x))) x := by
    change HasDerivAt (fun y : ℝ ↦ Real.log ((1 + y) / (1 - y)))
      (((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) /
        ((1 + x) / (1 - x))) x
    exact hLog
  convert hLog' using 1
  field_simp [hOneSub, hOneAdd, hOneSq]
  ring

/-- The derivative at the equilibrium point is exactly `2`. -/
theorem hasDerivAt_logOdds_zero : HasDerivAt logOdds 2 0 := by
  simpa using hasDerivAt_logOdds (x := 0) (by constructor <;> norm_num)

theorem continuousAt_logOdds_zero : ContinuousAt logOdds 0 :=
  hasDerivAt_logOdds_zero.continuousAt

theorem logOdds_tendsto_zero : Tendsto logOdds (𝓝 0) (𝓝 0) := by
  have h : Tendsto logOdds (𝓝 0) (𝓝 (logOdds 0)) :=
    continuousAt_logOdds_zero
  simpa only [logOdds_zero] using h

/-! ## First-order equivalence and the exact factor two -/

/-- Near zero, `logOdds x` is asymptotically equivalent to `2x`. -/
theorem logOdds_isEquivalent_twice_id :
    logOdds ~[𝓝 (0 : ℝ)] (fun x : ℝ ↦ 2 * x) := by
  have hRemainder :
      (fun x : ℝ ↦ logOdds x - 2 * x) =o[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x) := by
    simpa [logOdds_zero, mul_comm] using hasDerivAt_logOdds_zero.isLittleO
  exact (hRemainder.const_mul_right (by norm_num : (2 : ℝ) ≠ 0)).isEquivalent

/-- The nonlinear remainder `logOdds x - 2x` is little-o of `x`. -/
theorem logOdds_sub_twice_isLittleO :
    (fun x : ℝ ↦ logOdds x - 2 * x) =o[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x) := by
  simpa [logOdds_zero, mul_comm] using hasDerivAt_logOdds_zero.isLittleO

/-- The punctured-neighbourhood form of `logOdds x / x → 2`. -/
theorem logOdds_div_tendsto_two :
    Tendsto (fun x : ℝ ↦ logOdds x / x) (𝓝[≠] (0 : ℝ)) (𝓝 2) := by
  simpa [logOdds_zero, div_eq_inv_mul, mul_comm] using
    hasDerivAt_logOdds_zero.tendsto_slope_zero

/-- The removable extension of `logOdds x / x` at the origin. -/
def logOddsSlope (x : ℝ) : ℝ :=
  if x = 0 then 2 else logOdds x / x

@[simp]
theorem logOddsSlope_zero : logOddsSlope 0 = 2 := by
  simp [logOddsSlope]

/-- Exact factorization, including at `x = 0`. -/
theorem logOdds_eq_mul_logOddsSlope (x : ℝ) :
    logOdds x = x * logOddsSlope x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [logOddsSlope, ite_eq_right hx]
    field_simp

/-- The removable slope is continuous at the equilibrium point. -/
theorem continuousAt_logOddsSlope_zero : ContinuousAt logOddsSlope 0 := by
  have hUpdate :
      logOddsSlope = Function.update (fun x : ℝ ↦ logOdds x / x) 0 2 := by
    funext x
    by_cases hx : x = 0 <;> simp [logOddsSlope, hx]
  rw [hUpdate]
  exact continuousAt_update_same.mpr logOdds_div_tendsto_two

/-! ## Transfer along arbitrary filters -/

variable {ι : Type*} {l : Filter ι}

/-- Any family tending to zero inherits the local `logOdds x ~ 2x` equivalence. -/
theorem logOdds_comp_isEquivalent
    {f : ι → ℝ}
    (hf : Tendsto f l (𝓝 0)) :
    (fun i ↦ logOdds (f i)) ~[l] (fun i ↦ 2 * f i) := by
  simpa [Function.comp_def] using logOdds_isEquivalent_twice_id.comp_tendsto hf

/-- Unscaled convergence to equilibrium is preserved by log-odds. -/
theorem logOdds_comp_tendsto_zero
    {f : ι → ℝ}
    (hf : Tendsto f l (𝓝 0)) :
    Tendsto (fun i ↦ logOdds (f i)) l (𝓝 0) :=
  logOdds_tendsto_zero.comp hf

/--
Deterministic delta transfer.  If `f → 0` and `a*f → y`, then
`a*logOdds(f) → 2y`.  No distributional assumption appears here.
-/
theorem scaled_logOdds_tendsto
    {a f : ι → ℝ} {y : ℝ}
    (hf : Tendsto f l (𝓝 0))
    (haf : Tendsto (fun i ↦ a i * f i) l (𝓝 y)) :
    Tendsto (fun i ↦ a i * logOdds (f i)) l (𝓝 (2 * y)) := by
  have hSlope :
      Tendsto (fun i ↦ logOddsSlope (f i)) l (𝓝 2) :=
    by
      simpa [Function.comp_def, logOddsSlope_zero] using
        continuousAt_logOddsSlope_zero.tendsto.comp hf
  have hProduct := haf.mul hSlope
  convert hProduct using 1
  · funext i
    rw [logOdds_eq_mul_logOddsSlope]
    ring
  · congr 1
    ring

/-- Equivalent remainder form of the deterministic delta transfer. -/
theorem scaled_logOdds_remainder_tendsto_zero
    {a f : ι → ℝ} {y : ℝ}
    (hf : Tendsto f l (𝓝 0))
    (haf : Tendsto (fun i ↦ a i * f i) l (𝓝 y)) :
    Tendsto (fun i ↦ a i * (logOdds (f i) - 2 * f i)) l (𝓝 0) := by
  have hLog := scaled_logOdds_tendsto (l := l) hf haf
  have hLinear : Tendsto (fun i ↦ 2 * (a i * f i)) l (𝓝 (2 * y)) :=
    haf.const_mul 2
  have hSub := hLog.sub hLinear
  simpa only [mul_sub, mul_assoc, mul_left_comm, mul_comm, sub_self] using hSub

/-! ## Natural-index specializations used by the paper -/

/-- The transfer theorem with the conventional square-root normalization. -/
theorem sqrt_scaled_logOdds_tendsto
    {f : ℕ → ℝ} {y : ℝ}
    (hf : Tendsto f atTop (𝓝 0))
    (hScaled : Tendsto (fun n : ℕ ↦ Real.sqrt n * f n) atTop (𝓝 y)) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n * logOdds (f n)) atTop (𝓝 (2 * y)) :=
  scaled_logOdds_tendsto hf hScaled

/-- The same result for the exact effective-length scale `sqrt (2n - 1)`. -/
theorem effectiveLength_scaled_logOdds_tendsto
    {f : ℕ → ℝ} {y : ℝ}
    (hf : Tendsto f atTop (𝓝 0))
    (hScaled :
      Tendsto
        (fun n : ℕ ↦ Real.sqrt (2 * (n : ℝ) - 1) * f n)
        atTop (𝓝 y)) :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt (2 * (n : ℝ) - 1) * logOdds (f n))
      atTop (𝓝 (2 * y)) :=
  scaled_logOdds_tendsto hf hScaled

end

end EndpointCoordinate
