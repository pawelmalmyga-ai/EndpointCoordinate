import EndpointCoordinate.Student
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

set_option linter.style.header false
set_option linter.unnecessarySeqFocus false

/-!
# Endpoint coordinate: finite-variance universality

This module proves the distribution-free asymptotic theorem behind the
Gaussian, Laplace, and Student benchmarks.  The exact endpoint identity and
the exact Wilder energy are proved in earlier modules.  Here the only input
law assumptions are independence, identical distribution, zero mean, and a
finite second moment normalized to one.

The proof uses the second-order expansion of the characteristic function at
the origin.  No fourth moment, density, Gaussian approximation assumption, or
Student-specific characteristic function is used.
-/

namespace EndpointCoordinate

noncomputable section

open Asymptotics Complex Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology NNReal

/-! ## The minimal probabilistic interface -/

/-- Precisely the one-law assumptions needed by the finite-variance CLT. -/
structure HasCenteredUnitVariance
    {Omega : Type*} [MeasurableSpace Omega]
    (X : Omega → ℝ) (mu : Measure Omega) : Prop where
  aemeasurable : AEMeasurable X mu
  mean_eq_zero : mu[X] = 0
  secondMoment_eq_one : mu[X ^ 2] = 1

/-! ## Exact finite-row characteristic function -/

/-- Characteristic function of a finite deterministic weighted sum of
independent identically distributed innovations. -/
theorem charFun_finiteWeightedSmoother_iid
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (weight : ℕ → ℝ)
    (innovation : ℕ → Omega → ℝ)
    (count : ℕ)
    (hIndependent : iIndepFun innovation mu)
    (hIdent : ∀ lag, IdentDistrib (innovation lag) (innovation 0) mu mu)
    (t : ℝ) :
    charFun (mu.map (finiteWeightedSmoother weight innovation count)) t =
      ∏ lag ∈ range count,
        charFun (mu.map (innovation 0)) (weight lag * t) := by
  let weighted : ℕ → Omega → ℝ :=
    fun lag omega ↦ weight lag * innovation lag omega
  have hWeightedIndependent : iIndepFun weighted mu := by
    exact hIndependent.comp (fun lag x ↦ weight lag * x) (by fun_prop)
  have hWeightedMeasurable : ∀ lag, AEMeasurable (weighted lag) mu := by
    intro lag
    exact (hIdent lag).aemeasurable_fst.const_mul _
  have hProduct :=
    (hWeightedIndependent.restrict (range count)).charFun_map_fun_finsetSum_eq_prod
      (fun lag hlag ↦ hWeightedMeasurable lag)
  have hAtT := congrFun hProduct t
  calc
    charFun (mu.map (finiteWeightedSmoother weight innovation count)) t =
        charFun (mu.map (fun omega ↦ ∑ lag ∈ range count, weighted lag omega)) t := by
      congr 2
      funext omega
      simp only [finiteWeightedSmoother, Finset.sum_apply, weighted]
    _ = ∏ lag ∈ range count, charFun (mu.map (weighted lag)) t := by
      simpa only [Finset.prod_apply] using hAtT
    _ = ∏ lag ∈ range count,
        charFun (mu.map (innovation 0)) (weight lag * t) := by
      apply prod_congr rfl
      intro lag hlag
      rw [charFun_map_mul_comp (hIdent lag).aemeasurable_fst]
      rw [(hIdent lag).map_eq]

/-- A finite weighted row is measurable under the common-law hypothesis. -/
theorem aemeasurable_finiteWeightedSmoother_iid
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (weight : ℕ → ℝ)
    (innovation : ℕ → Omega → ℝ)
    (count : ℕ)
    (hIdent : ∀ lag, IdentDistrib (innovation lag) (innovation 0) mu mu) :
    AEMeasurable (finiteWeightedSmoother weight innovation count) mu := by
  have hSum := (range count).aemeasurable_sum
    (f := fun lag omega ↦ weight lag * innovation lag omega)
    (fun lag hlag ↦ (hIdent lag).aemeasurable_fst.const_mul _)
  simpa only [finiteWeightedSmoother, Finset.sum_apply] using hSum

/-! ## Second-order local normal form -/

/-- The Gaussian exponential has the same second-order germ as
`1 - u^2 / 2`. -/
theorem gaussianCharFun_secondOrder :
    (fun u : ℝ ↦
      Complex.exp (-((u : ℂ) ^ 2) / 2) -
        (1 - ((u : ℂ) ^ 2) / 2)) =o[nhds 0]
      (fun u : ℝ ↦ u ^ 2) := by
  have hBase := Complex.exp_sub_sum_range_succ_isLittleO_pow 1
  have hInner :
      Tendsto (fun u : ℝ ↦ -((u : ℂ) ^ 2) / 2) (nhds 0) (nhds 0) := by
    convert (((Complex.continuous_ofReal.tendsto 0).pow 2).neg.div_const 2) using 1 <;>
      norm_num
  have hComp := hBase.comp_tendsto hInner
  rw [isLittleO_iff] at hComp ⊢
  intro c hc
  have hEvent := hComp (show 0 < c / 2 by positivity)
  filter_upwards [hEvent] with u hu
  norm_num [Finset.sum_range_succ, norm_div, norm_neg, norm_pow] at hu
  calc
    ‖Complex.exp (-((u : ℂ) ^ 2) / 2) -
        (1 - ((u : ℂ) ^ 2) / 2)‖ =
        ‖Complex.exp (-((u : ℂ) ^ 2) / 2) -
          (1 + -((u : ℂ) ^ 2) / 2)‖ := by ring_nf
    _ ≤ c / 2 * (u ^ 2 / 2) := hu
    _ ≤ c * ‖u ^ 2‖ := by
      rw [Real.norm_eq_abs, abs_sq]
      nlinarith [mul_nonneg hc.le (sq_nonneg u)]

/-- Every centered unit-variance law has the standard Gaussian
characteristic function to second order at the origin. -/
theorem charFun_gaussian_remainder_isLittleO
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ}
    (hX : HasCenteredUnitVariance X mu) :
    (fun u : ℝ ↦
      charFun (mu.map X) u -
        Complex.exp (-((u : ℂ) ^ 2) / 2)) =o[nhds 0]
      (fun u : ℝ ↦ u ^ 2) := by
  have hChar := taylor_charFun_two
    hX.aemeasurable hX.mean_eq_zero hX.secondMoment_eq_one
  have hDifference := hChar.sub gaussianCharFun_secondOrder
  convert hDifference using 1
  funext u
  ring

/-! ## A finite-product stability inequality -/

/-- Products of points in the closed unit disk are one-Lipschitz in the
sum metric. -/
theorem norm_prod_sub_prod_le
    {iota : Type*}
    (s : Finset iota) (z w : iota → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) :
    ‖(∏ i ∈ s, z i) - ∏ i ∈ s, w i‖ ≤
      ∑ i ∈ s, ‖z i - w i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hza : ‖z a‖ ≤ 1 := hz a (Finset.mem_insert_self a s)
      have hws : ∀ i ∈ s, ‖w i‖ ≤ 1 := by
        intro i hi
        exact hw i (Finset.mem_insert_of_mem hi)
      have hzs : ∀ i ∈ s, ‖z i‖ ≤ 1 := by
        intro i hi
        exact hz i (Finset.mem_insert_of_mem hi)
      have hwprod : ‖∏ i ∈ s, w i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun i hi ↦ norm_nonneg _) hws
      have hih := ih hzs hws
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      calc
        ‖z a * ∏ i ∈ s, z i - w a * ∏ i ∈ s, w i‖ =
            ‖z a * ((∏ i ∈ s, z i) - ∏ i ∈ s, w i) +
              (z a - w a) * ∏ i ∈ s, w i‖ := by
                congr 1
                ring
        _ ≤ ‖z a * ((∏ i ∈ s, z i) - ∏ i ∈ s, w i)‖ +
              ‖(z a - w a) * ∏ i ∈ s, w i‖ := norm_add_le _ _
        _ = ‖z a‖ * ‖(∏ i ∈ s, z i) - ∏ i ∈ s, w i‖ +
              ‖z a - w a‖ * ‖∏ i ∈ s, w i‖ := by
                rw [norm_mul, norm_mul]
        _ ≤ 1 * (∑ i ∈ s, ‖z i - w i‖) +
              ‖z a - w a‖ * 1 := by
                gcongr
        _ = ‖z a - w a‖ + ∑ i ∈ s, ‖z i - w i‖ := by ring

/-! ## The normalized Wilder triangular array -/

/-- The finite-variance normalization is the exact effective-length factor.
It is definitionally the same normalization used in the Gaussian and Laplace
modules. -/
def finiteVarianceNormalizedWilderWeight (n lag : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) - 1) * wilderWeight n lag

theorem finiteVarianceNormalizedWilderWeight_eq_gaussian
    (n lag : ℕ) :
    finiteVarianceNormalizedWilderWeight n lag =
      gaussianNormalizedWilderWeight n lag := by
  rfl

def finiteVarianceWilderRow
    {Omega : Type*}
    (n count : ℕ)
    (innovation : ℕ → Omega → ℝ) : Omega → ℝ :=
  finiteWeightedSmoother
    (finiteVarianceNormalizedWilderWeight n) innovation count

theorem finiteVarianceWilderRow_eq_gaussianRow
    {Omega : Type*}
    (n count : ℕ)
    (innovation : ℕ → Omega → ℝ) :
    finiteVarianceWilderRow n count innovation =
      finiteGaussianWilderRow n count innovation := by
  rfl

theorem finiteVarianceNormalizedWilderWeight_sq_sum_range
    (n count : ℕ)
    (hN : 1 ≤ n) :
    (∑ lag ∈ range count,
      (finiteVarianceNormalizedWilderWeight n lag) ^ 2) =
      1 - (wilderDecay n) ^ (2 * count) := by
  simpa only [finiteVarianceNormalizedWilderWeight_eq_gaussian] using
    gaussianNormalizedWilderWeight_sq_sum_range n count hN

theorem finiteVarianceNormalizedWilderWeight_nonnegative
    (n lag : ℕ) (hN : 1 ≤ n) :
    0 ≤ finiteVarianceNormalizedWilderWeight n lag := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact wilderWeight_nonnegative n hN lag

theorem finiteVarianceNormalizedWilderWeight_le_leading
    (n lag : ℕ) (hN : 1 ≤ n) :
    finiteVarianceNormalizedWilderWeight n lag ≤
      finiteVarianceNormalizedWilderWeight n 0 := by
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  simpa only [wilderWeight_zero] using wilderWeight_le_gain n lag hN

theorem finiteVarianceNormalizedWilderWeight_sq_eq_lindebergWeightSq
    (n lag : ℕ) (hN : 1 ≤ n) :
    (finiteVarianceNormalizedWilderWeight n lag) ^ 2 =
      lindebergWeightSq n lag := by
  simpa only [finiteVarianceNormalizedWilderWeight_eq_gaussian,
    ← laplaceNormalizedWilderWeight_eq_gaussian] using
    laplaceNormalizedWilderWeight_sq_eq_lindebergWeightSq n lag hN

theorem finiteVarianceWilder_leading_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ finiteVarianceNormalizedWilderWeight (n + 1) 0)
      atTop (nhds 0) := by
  have hSq : Tendsto
      (fun n : ℕ ↦
        (finiteVarianceNormalizedWilderWeight (n + 1) 0) ^ 2)
      atTop (nhds 0) := by
    have hShift := lindebergLeadingWeightSq_tendsto_zero.comp
      (tendsto_add_atTop_nat 1)
    apply hShift.congr'
    filter_upwards with n
    exact (finiteVarianceNormalizedWilderWeight_sq_eq_lindebergWeightSq
      (n + 1) 0 (by omega)).symm
  have hSqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hSq
  have hFunction :
      (fun n : ℕ ↦ finiteVarianceNormalizedWilderWeight (n + 1) 0) =
        (fun n : ℕ ↦
          Real.sqrt ((finiteVarianceNormalizedWilderWeight (n + 1) 0) ^ 2)) := by
    funext n
    rw [Real.sqrt_sq
      (finiteVarianceNormalizedWilderWeight_nonnegative (n + 1) 0 (by omega))]
  rw [hFunction]
  change Tendsto
    (fun n : ℕ ↦
      Real.sqrt ((finiteVarianceNormalizedWilderWeight (n + 1) 0) ^ 2))
    atTop (nhds (Real.sqrt 0)) at hSqrt
  simpa only [Real.sqrt_zero] using hSqrt

/-! ## The row remainder -/

/-- Sum of the local second-order characteristic-function errors in one row. -/
def finiteVarianceWilderRowError
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (X : Omega → ℝ)
    (count : ℕ → ℕ)
    (t : ℝ)
    (n : ℕ) : ℝ :=
  ∑ lag ∈ range (count n),
    ‖charFun (mu.map X)
        (finiteVarianceNormalizedWilderWeight (n + 1) lag * t) -
      Complex.exp
        (-(((finiteVarianceNormalizedWilderWeight (n + 1) lag * t : ℝ) : ℂ) ^ 2) / 2)‖

theorem finiteVarianceNormalizedWilderWeight_sq_sum_range_le_one
    (n count : ℕ) (hN : 1 ≤ n) :
    (∑ lag ∈ range count,
      (finiteVarianceNormalizedWilderWeight n lag) ^ 2) ≤ 1 := by
  rw [finiteVarianceNormalizedWilderWeight_sq_sum_range n count hN]
  exact sub_le_self 1
    (pow_nonneg (wilderDecay_nonnegative n hN) (2 * count))

/-- Finite variance alone makes the total second-order error of every Wilder
row vanish.  This is the step that replaces a fourth-moment Lyapunov bound. -/
theorem finiteVarianceWilderRowError_tendsto_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ}
    (hX : HasCenteredUnitVariance X mu)
    (count : ℕ → ℕ)
    (t : ℝ) :
    Tendsto
      (finiteVarianceWilderRowError mu X count t)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hEpsilon
  let c : ℝ := epsilon / (t ^ 2 + 1)
  have hC : 0 < c := by
    dsimp [c]
    positivity
  have hLocal := charFun_gaussian_remainder_isLittleO hX
  rw [isLittleO_iff] at hLocal
  have hEventuallyLocal := hLocal hC
  obtain ⟨delta, hDelta, hDeltaBound⟩ :=
    Metric.eventually_nhds_iff_ball.mp hEventuallyLocal
  have hLeadingTimes : Tendsto
      (fun n : ℕ ↦
        finiteVarianceNormalizedWilderWeight (n + 1) 0 * |t|)
      atTop (nhds 0) := by
    simpa using finiteVarianceWilder_leading_tendsto_zero.mul_const |t|
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hLeadingTimes delta hDelta
  refine ⟨N, fun n hn ↦ ?_⟩
  have hLeadingNonnegative :
      0 ≤ finiteVarianceNormalizedWilderWeight (n + 1) 0 :=
    finiteVarianceNormalizedWilderWeight_nonnegative (n + 1) 0 (by omega)
  have hLeadingSmall :
      finiteVarianceNormalizedWilderWeight (n + 1) 0 * |t| < delta := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_mul,
      abs_of_nonneg hLeadingNonnegative] at h
    simpa only [abs_abs] using h
  have hTermBound : ∀ lag ∈ range (count n),
      ‖charFun (mu.map X)
          (finiteVarianceNormalizedWilderWeight (n + 1) lag * t) -
        Complex.exp
          (-(((finiteVarianceNormalizedWilderWeight (n + 1) lag * t : ℝ) : ℂ) ^ 2) / 2)‖ ≤
        c * ‖(finiteVarianceNormalizedWilderWeight (n + 1) lag * t) ^ 2‖ := by
    intro lag hlag
    have hWeightNonnegative :
        0 ≤ finiteVarianceNormalizedWilderWeight (n + 1) lag :=
      finiteVarianceNormalizedWilderWeight_nonnegative (n + 1) lag (by omega)
    have hWeightLe :
        finiteVarianceNormalizedWilderWeight (n + 1) lag ≤
          finiteVarianceNormalizedWilderWeight (n + 1) 0 :=
      finiteVarianceNormalizedWilderWeight_le_leading (n + 1) lag (by omega)
    have hArgumentInBall :
        finiteVarianceNormalizedWilderWeight (n + 1) lag * t ∈
          Metric.ball (0 : ℝ) delta := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      calc
        |finiteVarianceNormalizedWilderWeight (n + 1) lag * t| =
            finiteVarianceNormalizedWilderWeight (n + 1) lag * |t| := by
              rw [abs_mul, abs_of_nonneg hWeightNonnegative]
        _ ≤ finiteVarianceNormalizedWilderWeight (n + 1) 0 * |t| :=
          mul_le_mul_of_nonneg_right hWeightLe (abs_nonneg t)
        _ < delta := hLeadingSmall
    exact hDeltaBound _ hArgumentInBall
  have hErrorNonnegative :
      0 ≤ finiteVarianceWilderRowError mu X count t n := by
    exact sum_nonneg fun lag hlag ↦ norm_nonneg _
  have hEnergy :=
    finiteVarianceNormalizedWilderWeight_sq_sum_range_le_one
      (n + 1) (count n) (by omega)
  calc
    dist (finiteVarianceWilderRowError mu X count t n) 0 =
        finiteVarianceWilderRowError mu X count t n := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hErrorNonnegative]
    _ ≤ ∑ lag ∈ range (count n),
        c * ‖(finiteVarianceNormalizedWilderWeight (n + 1) lag * t) ^ 2‖ := by
      exact sum_le_sum hTermBound
    _ = c * t ^ 2 *
        ∑ lag ∈ range (count n),
          (finiteVarianceNormalizedWilderWeight (n + 1) lag) ^ 2 := by
      simp_rw [Real.norm_eq_abs, abs_sq, mul_pow]
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro lag hlag
      ring
    _ ≤ c * t ^ 2 * 1 := by
      gcongr
    _ < epsilon := by
      have hDenominator : 0 < t ^ 2 + 1 := by positivity
      dsimp [c]
      rw [div_mul_eq_mul_div, mul_one]
      apply (div_lt_iff₀ hDenominator).2
      nlinarith [sq_nonneg t]

/-! ## Characteristic-function convergence -/

/-- Product of the Gaussian second-order factors in one finite row. -/
def finiteVarianceWilderGaussianProduct
    (count : ℕ → ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  ∏ lag ∈ range (count n),
    Complex.exp
      (-(((finiteVarianceNormalizedWilderWeight (n + 1) lag * t : ℝ) : ℂ) ^ 2) / 2)

theorem finiteVarianceWilderGaussianProduct_eq
    (count : ℕ → ℕ) (t : ℝ) (n : ℕ) :
    finiteVarianceWilderGaussianProduct count t n =
      Complex.exp
        (-((t : ℂ) ^ 2) / 2 *
          ((∑ lag ∈ range (count n),
            (finiteVarianceNormalizedWilderWeight (n + 1) lag) ^ 2 : ℝ) : ℂ)) := by
  rw [finiteVarianceWilderGaussianProduct, ← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro lag hlag
  norm_cast
  ring

theorem finiteVarianceWilderGaussianProduct_tendsto
    (count : ℕ → ℕ)
    (t : ℝ)
    (hTail : Tendsto
      (fun n : ℕ ↦ (wilderDecay (n + 1)) ^ (2 * count n))
      atTop (nhds 0)) :
    Tendsto
      (finiteVarianceWilderGaussianProduct count t)
      atTop
      (nhds (Complex.exp (-((t : ℂ) ^ 2) / 2))) := by
  have hEnergy : Tendsto
      (fun n : ℕ ↦
        ∑ lag ∈ range (count n),
          (finiteVarianceNormalizedWilderWeight (n + 1) lag) ^ 2)
      atTop (nhds 1) := by
    have hOneMinus : Tendsto
        (fun n : ℕ ↦ 1 - (wilderDecay (n + 1)) ^ (2 * count n))
        atTop (nhds (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hTail
    apply hOneMinus.congr'
    filter_upwards with n
    exact (finiteVarianceNormalizedWilderWeight_sq_sum_range
      (n + 1) (count n) (by omega)).symm
  have hEnergyComplex : Tendsto
      (fun n : ℕ ↦
        ((∑ lag ∈ range (count n),
          (finiteVarianceNormalizedWilderWeight (n + 1) lag) ^ 2 : ℝ) : ℂ))
      atTop (nhds (1 : ℂ)) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp hEnergy
    change Tendsto
      (fun n : ℕ ↦
        ((∑ lag ∈ range (count n),
          (finiteVarianceNormalizedWilderWeight (n + 1) lag) ^ 2 : ℝ) : ℂ))
      atTop (nhds ((1 : ℝ) : ℂ)) at h
    norm_num at h ⊢
    exact h
  have hExponent :=
    hEnergyComplex.const_mul (-((t : ℂ) ^ 2) / 2)
  have hExp := Complex.continuous_exp.continuousAt.tendsto.comp hExponent
  change Tendsto
    (fun n : ℕ ↦ Complex.exp
      (-((t : ℂ) ^ 2) / 2 *
        ((∑ lag ∈ range (count n),
          (finiteVarianceNormalizedWilderWeight (n + 1) lag) ^ 2 : ℝ) : ℂ)))
    atTop
    (nhds (Complex.exp (-((t : ℂ) ^ 2) / 2 * 1))) at hExp
  have hExp' : Tendsto
      (fun n : ℕ ↦ Complex.exp
        (-((t : ℂ) ^ 2) / 2 *
          ((∑ lag ∈ range (count n),
            (finiteVarianceNormalizedWilderWeight (n + 1) lag) ^ 2 : ℝ) : ℂ)))
      atTop
      (nhds (Complex.exp (-((t : ℂ) ^ 2) / 2))) := by
    simpa only [mul_one] using hExp
  apply hExp'.congr'
  filter_upwards with n
  rw [finiteVarianceWilderGaussianProduct_eq]

/-- Product of the innovation characteristic functions in one normalized
Wilder row. -/
def finiteVarianceWilderCharacteristicProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (X : Omega → ℝ)
    (count : ℕ → ℕ)
    (t : ℝ)
    (n : ℕ) : ℂ :=
  ∏ lag ∈ range (count n),
    charFun (mu.map X)
      (finiteVarianceNormalizedWilderWeight (n + 1) lag * t)

/-- The normalized Wilder characteristic product converges to the standard
Gaussian characteristic function for every centered unit-variance input law. -/
theorem finiteVarianceWilderCharacteristicProduct_tendsto
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ}
    (hX : HasCenteredUnitVariance X mu)
    (count : ℕ → ℕ)
    (t : ℝ)
    (hTail : Tendsto
      (fun n : ℕ ↦ (wilderDecay (n + 1)) ^ (2 * count n))
      atTop (nhds 0)) :
    Tendsto
      (finiteVarianceWilderCharacteristicProduct mu X count t)
      atTop
      (nhds (Complex.exp (-((t : ℂ) ^ 2) / 2))) := by
  have hError := finiteVarianceWilderRowError_tendsto_zero hX count t
  have hProductBound : ∀ n,
      ‖finiteVarianceWilderCharacteristicProduct mu X count t n -
        finiteVarianceWilderGaussianProduct count t n‖ ≤
        finiteVarianceWilderRowError mu X count t n := by
    intro n
    apply norm_prod_sub_prod_le
    · intro lag hlag
      exact norm_charFun_le_one _
    · intro lag hlag
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      norm_num [pow_two]
      nlinarith [sq_nonneg
        (finiteVarianceNormalizedWilderWeight (n + 1) lag * t)]
  have hNormDifference : Tendsto
      (fun n ↦
        ‖finiteVarianceWilderCharacteristicProduct mu X count t n -
          finiteVarianceWilderGaussianProduct count t n‖)
      atTop (nhds 0) :=
    Filter.Tendsto.squeeze tendsto_const_nhds hError
      (fun n ↦ norm_nonneg _) hProductBound
  have hDifference : Tendsto
      (fun n ↦
        finiteVarianceWilderCharacteristicProduct mu X count t n -
          finiteVarianceWilderGaussianProduct count t n)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero] using hNormDifference
  have hReference :=
    finiteVarianceWilderGaussianProduct_tendsto count t hTail
  have hAdd := hDifference.add hReference
  convert hAdd using 1
  · funext n
    ring
  · ring_nf

/-! ## Lévy bridge and the finite-variance Wilder CLT -/

theorem charFun_finiteVarianceWilderRow
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (innovation : ℕ → Omega → ℝ)
    (count : ℕ → ℕ)
    (hIndependent : iIndepFun innovation mu)
    (hIdent : ∀ lag, IdentDistrib (innovation lag) (innovation 0) mu mu)
    (n : ℕ)
    (t : ℝ) :
    charFun
        (mu.map
          (finiteVarianceWilderRow (n + 1) (count n) innovation)) t =
      finiteVarianceWilderCharacteristicProduct
        mu (innovation 0) count t n := by
  exact charFun_finiteWeightedSmoother_iid
    (finiteVarianceNormalizedWilderWeight (n + 1))
    innovation (count n) hIndependent hIdent t

theorem aemeasurable_finiteVarianceWilderRow
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (innovation : ℕ → Omega → ℝ)
    (count : ℕ → ℕ)
    (hIdent : ∀ lag, IdentDistrib (innovation lag) (innovation 0) mu mu)
    (n : ℕ) :
    AEMeasurable
      (finiteVarianceWilderRow (n + 1) (count n) innovation) mu := by
  exact aemeasurable_finiteWeightedSmoother_iid
    (finiteVarianceNormalizedWilderWeight (n + 1))
    innovation (count n) hIdent

/-- **Finite-variance Wilder CLT.** For independent identically distributed,
centered, unit-variance innovations, the effective-length normalized row
converges to a standard Gaussian.  The only truncation condition says that
the omitted geometric variance tends to zero. -/
theorem finiteVarianceWilderRow_clt
    {Omega Omega' : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {mu' : Measure Omega'} [IsProbabilityMeasure mu']
    (innovation : ℕ → Omega → ℝ)
    (count : ℕ → ℕ)
    (Y : Omega' → ℝ)
    (hIndependent : iIndepFun innovation mu)
    (hIdent : ∀ lag, IdentDistrib (innovation lag) (innovation 0) mu mu)
    (hX : HasCenteredUnitVariance (innovation 0) mu)
    (hY : HasLaw Y (gaussianReal 0 1) mu')
    (hTail : Tendsto
      (fun n : ℕ ↦ (wilderDecay (n + 1)) ^ (2 * count n))
      atTop (nhds 0)) :
    TendstoInDistribution
      (fun n ↦ finiteVarianceWilderRow (n + 1) (count n) innovation)
      atTop Y (fun _ ↦ mu) mu' := by
  apply TendstoInDistribution.of_tendsto_charFun
  · intro n
    exact aemeasurable_finiteVarianceWilderRow
      innovation count hIdent n
  · exact hY.aemeasurable
  · intro t
    rw! [hY.map_eq]
    have hRows :
        (fun n : ℕ ↦
          charFun
            (mu.map
              (finiteVarianceWilderRow (n + 1) (count n) innovation)) t) =
        finiteVarianceWilderCharacteristicProduct
          mu (innovation 0) count t := by
      funext n
      exact charFun_finiteVarianceWilderRow
        innovation count hIndependent hIdent n t
    rw [hRows, charFun_gaussianReal]
    convert finiteVarianceWilderCharacteristicProduct_tendsto
      hX count t hTail using 1
    norm_num
    ring_nf

/-! ## Student compatibility -/

/-- The Student moment profile from the preceding module implies the minimal
finite-variance interface. -/
theorem HasUnitVarianceStudentMomentProfile.toHasCenteredUnitVariance
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {nu : ℝ}
    (hX : HasUnitVarianceStudentMomentProfile X mu nu) :
    HasCenteredUnitVariance X mu := by
  refine
    { aemeasurable := hX.aemeasurable
      mean_eq_zero := hX.mean_eq_zero
      secondMoment_eq_one := ?_ }
  rw [← hX.variance_eq_one, variance_eq_integral hX.aemeasurable]
  simp only [hX.mean_eq_zero, sub_zero, Pi.pow_apply]

/-- Student-input specialization.  The asymptotic normalization remains
`sqrt (2n - 1)`; Student-specific constants belong to the finite-`n`
first-shift calibration, not to the CLT scale. -/
theorem finiteStudentWilderRow_clt_of_momentProfile
    {Omega Omega' : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {mu' : Measure Omega'} [IsProbabilityMeasure mu']
    (innovation : ℕ → Omega → ℝ)
    (count : ℕ → ℕ)
    (Y : Omega' → ℝ)
    {nu : ℝ}
    (hIndependent : iIndepFun innovation mu)
    (hIdent : ∀ lag, IdentDistrib (innovation lag) (innovation 0) mu mu)
    (hStudent : HasUnitVarianceStudentMomentProfile
      (innovation 0) mu nu)
    (hY : HasLaw Y (gaussianReal 0 1) mu')
    (hTail : Tendsto
      (fun n : ℕ ↦ (wilderDecay (n + 1)) ^ (2 * count n))
      atTop (nhds 0)) :
    TendstoInDistribution
      (fun n ↦ finiteVarianceWilderRow (n + 1) (count n) innovation)
      atTop Y (fun _ ↦ mu) mu' := by
  exact finiteVarianceWilderRow_clt
    innovation count Y hIndependent hIdent
    hStudent.toHasCenteredUnitVariance hY hTail

end
end EndpointCoordinate
