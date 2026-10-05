import EndpointCoordinate.Laplace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.header false

/-!
# Endpoint coordinate: triangular-array product limit

This module closes the deterministic analytic step left explicit in
`EndpointCoordinate.Laplace`.

For a finite row of nonnegative energies `q_(n,k)`, assume

* the total row energy tends to one, and
* the sum of squared row energies tends to zero.

Then, for every `c >= 0`,

`product_k (1 + c q_(n,k))^(-1) -> exp(-c)`.

The proof is elementary and quantitative.  It sums the bound

`0 <= x - log(1+x) <= x^2`

and then exponentiates.  Applied with `c = t^2 / 2` and with the squared
normalized Wilder weights, this proves the characteristic-product limit for
unit-variance Laplace innovations.  Levy's theorem from the preceding module
then gives the unconditional Laplace-input central limit theorem.
-/

namespace EndpointCoordinate

noncomputable section

open Complex Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology NNReal

/-! ## A quantitative logarithmic remainder -/

/-- The logarithmic remainder on the nonnegative half-line is nonnegative and
quadratically bounded. -/
theorem log_one_add_remainder_bounds
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - Real.log (1 + x) ∧
      x - Real.log (1 + x) ≤ x ^ 2 := by
  have hPositive : 0 < 1 + x := by linarith
  have hLogUpper : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hPositive
    linarith
  have hLogLower : 2 * x / (x + 2) ≤ Real.log (1 + x) :=
    Real.le_log_one_add_of_nonneg hx
  have hDenominator : 0 < x + 2 := by linarith
  have hRational : x - 2 * x / (x + 2) ≤ x ^ 2 := by
    have hIdentity : x - 2 * x / (x + 2) = x ^ 2 / (x + 2) := by
      field_simp
      ring
    rw [hIdentity, div_le_iff₀ hDenominator]
    nlinarith [sq_nonneg x]
  constructor
  · linarith
  · linarith

/-- Summed logarithmic remainder for one finite triangular-array row. -/
def rowLogRemainder
    (q : ℕ → ℕ → ℝ) (count : ℕ → ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  c * (∑ k ∈ range (count n), q n k) -
    ∑ k ∈ range (count n), Real.log (1 + c * q n k)

theorem rowLogRemainder_nonnegative
    (q : ℕ → ℕ → ℝ)
    (count : ℕ → ℕ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hq : ∀ n k, 0 ≤ q n k)
    (n : ℕ) :
    0 ≤ rowLogRemainder q count c n := by
  rw [rowLogRemainder, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact sum_nonneg fun k hk ↦
    (log_one_add_remainder_bounds (mul_nonneg hc (hq n k))).1

theorem rowLogRemainder_le
    (q : ℕ → ℕ → ℝ)
    (count : ℕ → ℕ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hq : ∀ n k, 0 ≤ q n k)
    (n : ℕ) :
    rowLogRemainder q count c n ≤
      c ^ 2 * ∑ k ∈ range (count n), (q n k) ^ 2 := by
  rw [rowLogRemainder, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply sum_le_sum
  intro k hk
  have h :=
    (log_one_add_remainder_bounds (mul_nonneg hc (hq n k))).2
  calc
    c * q n k - Real.log (1 + c * q n k) ≤
        (c * q n k) ^ 2 := h
    _ = c ^ 2 * (q n k) ^ 2 := by ring

/-- If the squared row mass tends to zero, then the summed logarithmic
remainder tends to zero. -/
theorem rowLogRemainder_tendsto_zero
    (q : ℕ → ℕ → ℝ)
    (count : ℕ → ℕ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hq : ∀ n k, 0 ≤ q n k)
    (hQuadratic : Tendsto
      (fun n ↦ ∑ k ∈ range (count n), (q n k) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (rowLogRemainder q count c) atTop (𝓝 0) := by
  have hUpper : Tendsto
      (fun n ↦ c ^ 2 * ∑ k ∈ range (count n), (q n k) ^ 2)
      atTop (𝓝 0) := by
    simpa using hQuadratic.const_mul (c ^ 2)
  exact Filter.Tendsto.squeeze tendsto_const_nhds hUpper
    (rowLogRemainder_nonnegative q count c hc hq)
    (rowLogRemainder_le q count c hc hq)

/-! ## Generic finite-product limit -/

/-- Algebraic representation of the reciprocal product through the summed
real logarithm. -/
theorem prod_one_add_inv_eq_exp_neg_sum_log
    (q : ℕ → ℝ)
    (s : Finset ℕ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hq : ∀ k, 0 ≤ q k) :
    (∏ k ∈ s, (1 + c * q k)⁻¹) =
      Real.exp (-∑ k ∈ s, Real.log (1 + c * q k)) := by
  calc
    (∏ k ∈ s, (1 + c * q k)⁻¹) =
        ∏ k ∈ s, Real.exp (-Real.log (1 + c * q k)) := by
      apply prod_congr rfl
      intro k hk
      rw [Real.exp_neg, Real.exp_log]
      linarith [mul_nonneg hc (hq k)]
    _ = Real.exp (∑ k ∈ s, -Real.log (1 + c * q k)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-∑ k ∈ s, Real.log (1 + c * q k)) := by
      rw [Finset.sum_neg_distrib]

/-- Universal reciprocal-product limit for infinitesimal finite rows. -/
theorem tendsto_prod_one_add_inv
    (q : ℕ → ℕ → ℝ)
    (count : ℕ → ℕ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hq : ∀ n k, 0 ≤ q n k)
    (hEnergy : Tendsto
      (fun n ↦ ∑ k ∈ range (count n), q n k)
      atTop (𝓝 1))
    (hQuadratic : Tendsto
      (fun n ↦ ∑ k ∈ range (count n), (q n k) ^ 2)
      atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ ∏ k ∈ range (count n), (1 + c * q n k)⁻¹)
      atTop (𝓝 (Real.exp (-c))) := by
  have hRemainder :=
    rowLogRemainder_tendsto_zero q count c hc hq hQuadratic
  have hLinear : Tendsto
      (fun n ↦ c * ∑ k ∈ range (count n), q n k)
      atTop (𝓝 c) := by
    simpa using hEnergy.const_mul c
  have hLogSum : Tendsto
      (fun n ↦ ∑ k ∈ range (count n), Real.log (1 + c * q n k))
      atTop (𝓝 c) := by
    have hDifference := hLinear.sub hRemainder
    have hFunction :
        (fun n ↦ c * ∑ k ∈ range (count n), q n k -
          rowLogRemainder q count c n) =
        (fun n ↦ ∑ k ∈ range (count n), Real.log (1 + c * q n k)) := by
      funext n
      simp only [rowLogRemainder]
      ring
    rw [hFunction] at hDifference
    simpa using hDifference
  have hNegative : Tendsto
      (fun n ↦ -∑ k ∈ range (count n), Real.log (1 + c * q n k))
      atTop (𝓝 (-c)) := hLogSum.neg
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp hNegative
  apply hExp.congr'
  filter_upwards with n
  exact (prod_one_add_inv_eq_exp_neg_sum_log
    (q n) (range (count n)) c hc (hq n)).symm

/-! ## Wilder-array specialization -/

theorem laplaceNormalizedWilderWeight_sq_eq_lindebergWeightSq
    (n lag : ℕ)
    (hN : 1 ≤ n) :
    (laplaceNormalizedWilderWeight n lag) ^ 2 =
      lindebergWeightSq n lag := by
  have hNReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
  have hFactorNonnegative : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
  simp only [laplaceNormalizedWilderWeight, lindebergWeightSq, mul_pow,
    Real.sq_sqrt hFactorNonnegative]

theorem lindebergWeightSq_sum_range
    (n count : ℕ)
    (hN : 1 ≤ n) :
    (∑ lag ∈ range count, lindebergWeightSq n lag) =
      1 - (wilderDecay n) ^ (2 * count) := by
  calc
    (∑ lag ∈ range count, lindebergWeightSq n lag) =
        ∑ lag ∈ range count,
          (laplaceNormalizedWilderWeight n lag) ^ 2 := by
      apply sum_congr rfl
      intro lag hlag
      exact (laplaceNormalizedWilderWeight_sq_eq_lindebergWeightSq
        n lag hN).symm
    _ = 1 - (wilderDecay n) ^ (2 * count) :=
      laplaceNormalizedWilderWeight_sq_sum_range n count hN

theorem lindebergWeightSq_quadraticMass_tendsto_zero
    (count : ℕ → ℕ) :
    Tendsto
      (fun n ↦ ∑ lag ∈ range (count n),
        (lindebergWeightSq (n + 1) lag) ^ 2)
      atTop (𝓝 0) := by
  have h := (laplaceFourthLyapunovMass_tendsto_zero count).const_mul (1 / 6)
  simpa [laplaceFourthLyapunovMass] using h

/-- The Laplace characteristic product converges to the standard-Gaussian
characteristic function whenever the omitted variance tends to zero. -/
theorem laplaceWilderCharacteristicLimit_of_tail
    (count : ℕ → ℕ)
    (hTail : Tendsto
      (fun n : ℕ ↦ (wilderDecay (n + 1)) ^ (2 * count n))
      atTop (𝓝 0)) :
    LaplaceWilderCharacteristicLimit count := by
  intro t
  let q : ℕ → ℕ → ℝ :=
    fun n lag ↦ lindebergWeightSq (n + 1) lag
  let c : ℝ := t ^ 2 / 2
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hq : ∀ n lag, 0 ≤ q n lag := by
    intro n lag
    exact lindebergWeightSq_nonnegative (n + 1) lag (by omega)
  have hEnergy : Tendsto
      (fun n ↦ ∑ lag ∈ range (count n), q n lag)
      atTop (𝓝 1) := by
    have hOneMinus : Tendsto
        (fun n : ℕ ↦ 1 - (wilderDecay (n + 1)) ^ (2 * count n))
        atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hTail)
    apply hOneMinus.congr'
    filter_upwards with n
    rw [lindebergWeightSq_sum_range (n + 1) (count n) (by omega)]
  have hQuadratic : Tendsto
      (fun n ↦ ∑ lag ∈ range (count n), (q n lag) ^ 2)
      atTop (𝓝 0) := by
    exact lindebergWeightSq_quadraticMass_tendsto_zero count
  have hReal := tendsto_prod_one_add_inv q count c hc hq hEnergy hQuadratic
  have hComplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
  have hRowIdentity :
      (fun n : ℕ ↦
        ∏ lag ∈ range (count n),
          unitVarianceLaplaceCharFun
            (laplaceNormalizedWilderWeight (n + 1) lag * t)) =
      (fun n : ℕ ↦
        ((∏ lag ∈ range (count n),
          (1 + c * q n lag)⁻¹ : ℝ) : ℂ)) := by
    funext n
    rw [Complex.ofReal_prod]
    apply prod_congr rfl
    intro lag hlag
    have hRealDenominator :
        1 + (laplaceNormalizedWilderWeight (n + 1) lag * t) ^ 2 / 2 =
          1 + c * q n lag := by
      rw [mul_pow,
        laplaceNormalizedWilderWeight_sq_eq_lindebergWeightSq
          (n + 1) lag (by omega)]
      dsimp [c, q]
      ring
    simp only [unitVarianceLaplaceCharFun]
    have hComplexDenominator :
        (1 : ℂ) +
            ((laplaceNormalizedWilderWeight (n + 1) lag * t : ℝ) : ℂ) ^ 2 / 2 =
          ((1 + c * q n lag : ℝ) : ℂ) := by
      norm_cast
    rw [hComplexDenominator]
    norm_cast
  have hLimitIdentity :
      ((Real.exp (-c) : ℝ) : ℂ) =
        Complex.exp (-((t : ℂ) ^ 2) / 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    norm_cast
    dsimp [c]
    ring
  rw [hRowIdentity]
  have hComplex' : Tendsto
      (fun n : ℕ ↦
        ((∏ lag ∈ range (count n), (1 + c * q n lag)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 ((Real.exp (-c) : ℝ) : ℂ)) := by
    change Tendsto
      (fun n : ℕ ↦
        ((∏ lag ∈ range (count n), (1 + c * q n lag)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 ((Real.exp (-c) : ℝ) : ℂ)) at hComplex
    exact hComplex
  rw [hLimitIdentity] at hComplex'
  exact hComplex'

/-- Fully discharged Laplace-input Wilder CLT.  The only truncation condition
is that the omitted geometric variance tends to zero. -/
theorem finiteLaplaceWilderRow_clt
    {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ → ℕ)
    (Y : Ω' → ℝ)
    (hIndependent : iIndepFun innovation μ)
    (hLaplace : ∀ lag, HasUnitVarianceLaplaceCF (innovation lag) μ)
    (hY : HasLaw Y (gaussianReal 0 1) μ')
    (hTail : Tendsto
      (fun n : ℕ ↦ (wilderDecay (n + 1)) ^ (2 * count n))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ↦ finiteLaplaceWilderRow (n + 1) (count n) innovation)
      atTop Y (fun _ ↦ μ) μ' := by
  exact finiteLaplaceWilderRow_clt_of_characteristicLimit
    innovation count Y hIndependent hLaplace hY
    (laplaceWilderCharacteristicLimit_of_tail count hTail)

end
end EndpointCoordinate
