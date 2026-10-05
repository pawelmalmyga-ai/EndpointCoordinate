import EndpointCoordinate.Core
set_option linter.style.header false
/-!
# Exponentially weighted endpoint coordinate: probability layer I

This file starts the probabilistic layer of the endpoint-coordinate paper.
It is deliberately separated from `EndpointCoordinateCore.lean`:

* the imported core is finite-path and distribution-free;
* this module studies the deterministic kernel behind Wilder smoothing;
* the final section proves an exact variance identity for finite sums of
  independent innovations.

No Gaussian, Laplace, Student, or asymptotic approximation is assumed here.
In particular, the factor `2 * n - 1` below is an exact consequence of the
Wilder weights, not a fitted distributional parameter.
-/

namespace EndpointCoordinate

noncomputable section

open scoped BigOperators
open Finset Filter MeasureTheory ProbabilityTheory

/-! ## The exponential kernel -/

/-- The generic exponentially decaying weight with gain `alpha`. -/
def exponentialWeight (alpha : ℝ) (lag : ℕ) : ℝ :=
  alpha * (1 - alpha) ^ lag

/-- Wilder's gain for an integer period `n`. -/
def wilderGain (n : ℕ) : ℝ :=
  1 / (n : ℝ)

/-- Wilder's decay for an integer period `n`. -/
def wilderDecay (n : ℕ) : ℝ :=
  1 - wilderGain n

/-- The weight at lag `lag` in a Wilder smoother of period `n`. -/
def wilderWeight (n lag : ℕ) : ℝ :=
  exponentialWeight (wilderGain n) lag

@[simp]
theorem exponentialWeight_zero (alpha : ℝ) :
    exponentialWeight alpha 0 = alpha := by
  simp [exponentialWeight]

theorem exponentialWeight_succ (alpha : ℝ) (lag : ℕ) :
    exponentialWeight alpha (lag + 1) =
      (1 - alpha) * exponentialWeight alpha lag := by
  simp only [exponentialWeight, pow_succ]
  ring

theorem exponentialWeight_sum_range (alpha : ℝ) (count : ℕ) :
    (∑ lag ∈ range count, exponentialWeight alpha lag) =
      1 - (1 - alpha) ^ count := by
  simp only [exponentialWeight, ← Finset.mul_sum]
  calc
    alpha * ∑ lag ∈ range count, (1 - alpha) ^ lag =
        (∑ lag ∈ range count, (1 - alpha) ^ lag) * alpha := by ring
    _ = 1 - (1 - alpha) ^ count := by
      simpa using geom_sum_mul_neg (1 - alpha) count

theorem exponentialWeight_hasSum_one
    (alpha : ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaAtMostOne : alpha ≤ 1) :
    HasSum (exponentialWeight alpha) 1 := by
  have hDecayNonnegative : 0 ≤ 1 - alpha := sub_nonneg.mpr hAlphaAtMostOne
  have hDecayBelowOne : 1 - alpha < 1 := by linarith
  have hGeometric :=
    (hasSum_geometric_of_lt_one hDecayNonnegative hDecayBelowOne).mul_left alpha
  convert hGeometric using 1
  · ext lag
    rfl
  · have hAlphaNe : alpha ≠ 0 := ne_of_gt hAlphaPositive
    simp [hAlphaNe]

theorem exponentialWeight_tsum_one
    (alpha : ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaAtMostOne : alpha ≤ 1) :
    ∑' lag : ℕ, exponentialWeight alpha lag = 1 :=
  (exponentialWeight_hasSum_one alpha hAlphaPositive hAlphaAtMostOne).tsum_eq

theorem exponentialWeight_nonnegative
    (alpha : ℝ)
    (hAlphaNonnegative : 0 ≤ alpha)
    (hAlphaAtMostOne : alpha ≤ 1)
    (lag : ℕ) :
    0 ≤ exponentialWeight alpha lag := by
  exact mul_nonneg hAlphaNonnegative
    (pow_nonneg (sub_nonneg.mpr hAlphaAtMostOne) lag)

theorem exponentialWeight_le_gain
    (alpha : ℝ)
    (hAlphaNonnegative : 0 ≤ alpha)
    (hAlphaAtMostOne : alpha ≤ 1)
    (lag : ℕ) :
    exponentialWeight alpha lag ≤ alpha := by
  have hDecayNonnegative : 0 ≤ 1 - alpha := sub_nonneg.mpr hAlphaAtMostOne
  have hDecayAtMostOne : 1 - alpha ≤ 1 := by linarith
  have hPower : (1 - alpha) ^ lag ≤ 1 := by
    exact pow_le_one₀ hDecayNonnegative hDecayAtMostOne
  simpa [exponentialWeight] using
    mul_le_mul_of_nonneg_left hPower hAlphaNonnegative

/-! ## Squared mass and effective length -/

theorem exponentialWeight_sq_hasSum
    (alpha : ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaAtMostOne : alpha ≤ 1) :
    HasSum (fun lag : ℕ ↦ (exponentialWeight alpha lag) ^ 2)
      (alpha / (2 - alpha)) := by
  have hDecayNonnegative : 0 ≤ 1 - alpha := sub_nonneg.mpr hAlphaAtMostOne
  have hDecayBelowOne : 1 - alpha < 1 := by linarith
  have hSquareNonnegative : 0 ≤ (1 - alpha) ^ 2 := sq_nonneg _
  have hSquareBelowOne : (1 - alpha) ^ 2 < 1 := by
    nlinarith [sq_nonneg (1 - alpha)]
  have hGeometric :=
    (hasSum_geometric_of_lt_one hSquareNonnegative hSquareBelowOne).mul_left
      (alpha ^ 2)
  convert hGeometric using 1
  · ext lag
    simp only [exponentialWeight, mul_pow]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  · have hDenominator : 2 - alpha ≠ 0 := by linarith
    have hFactor : 1 - (1 - alpha) ^ 2 = alpha * (2 - alpha) := by ring
    rw [hFactor]
    field_simp [ne_of_gt hAlphaPositive, hDenominator]

theorem exponentialWeight_sq_tsum
    (alpha : ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaAtMostOne : alpha ≤ 1) :
    ∑' lag : ℕ, (exponentialWeight alpha lag) ^ 2 =
      alpha / (2 - alpha) :=
  (exponentialWeight_sq_hasSum alpha hAlphaPositive hAlphaAtMostOne).tsum_eq

/-- Reciprocal concentration of the weight vector (Kish effective size). -/
def effectiveLength (alpha : ℝ) : ℝ :=
  1 / (∑' lag : ℕ, (exponentialWeight alpha lag) ^ 2)

theorem effectiveLength_eq
    (alpha : ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaAtMostOne : alpha ≤ 1) :
    effectiveLength alpha = (2 - alpha) / alpha := by
  rw [effectiveLength, exponentialWeight_sq_tsum alpha
    hAlphaPositive hAlphaAtMostOne]
  have hAlphaNe : alpha ≠ 0 := ne_of_gt hAlphaPositive
  have hDenominator : 2 - alpha ≠ 0 := by linarith
  field_simp

/-! ## Wilder specialization -/

theorem wilderGain_pos (n : ℕ) (hN : 0 < n) :
    0 < wilderGain n := by
  simp [wilderGain, Nat.cast_pos.mpr hN]

theorem wilderGain_le_one (n : ℕ) (hN : 1 ≤ n) :
    wilderGain n ≤ 1 := by
  have hNReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
  have hNPositive : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hNReal
  rw [wilderGain]
  exact (div_le_iff₀ hNPositive).2 (by simpa using hNReal)

theorem wilderDecay_nonnegative (n : ℕ) (hN : 1 ≤ n) :
    0 ≤ wilderDecay n := by
  rw [wilderDecay]
  exact sub_nonneg.mpr (wilderGain_le_one n hN)

theorem wilderDecay_lt_one (n : ℕ) (hN : 0 < n) :
    wilderDecay n < 1 := by
  rw [wilderDecay]
  linarith [wilderGain_pos n hN]

@[simp]
theorem wilderWeight_zero (n : ℕ) :
    wilderWeight n 0 = wilderGain n := by
  simp [wilderWeight]

theorem wilderWeight_succ (n lag : ℕ) :
    wilderWeight n (lag + 1) =
      wilderDecay n * wilderWeight n lag := by
  simp [wilderWeight, wilderDecay, exponentialWeight_succ]

theorem wilderWeight_sum_range (n count : ℕ) :
    (∑ lag ∈ range count, wilderWeight n lag) =
      1 - (wilderDecay n) ^ count := by
  simpa [wilderWeight, wilderDecay] using
    exponentialWeight_sum_range (wilderGain n) count

theorem wilderWeight_hasSum_one
    (n : ℕ)
    (hN : 1 ≤ n) :
    HasSum (wilderWeight n) 1 := by
  change HasSum (exponentialWeight (wilderGain n)) 1
  exact exponentialWeight_hasSum_one (wilderGain n)
    (wilderGain_pos n (lt_of_lt_of_le Nat.zero_lt_one hN))
    (wilderGain_le_one n hN)

theorem wilderWeight_tsum_one
    (n : ℕ)
    (hN : 1 ≤ n) :
    ∑' lag : ℕ, wilderWeight n lag = 1 :=
  (wilderWeight_hasSum_one n hN).tsum_eq

theorem wilderWeight_nonnegative
    (n : ℕ)
    (hN : 1 ≤ n)
    (lag : ℕ) :
    0 ≤ wilderWeight n lag := by
  exact exponentialWeight_nonnegative (wilderGain n)
    (le_of_lt (wilderGain_pos n (lt_of_lt_of_le Nat.zero_lt_one hN)))
    (wilderGain_le_one n hN) lag

theorem wilderWeight_sq_tsum
    (n : ℕ)
    (hN : 1 ≤ n) :
    ∑' lag : ℕ, (wilderWeight n lag) ^ 2 =
      1 / (2 * (n : ℝ) - 1) := by
  change (∑' lag : ℕ, (exponentialWeight (wilderGain n) lag) ^ 2) = _
  rw [exponentialWeight_sq_tsum (wilderGain n)
    (wilderGain_pos n (lt_of_lt_of_le Nat.zero_lt_one hN))
    (wilderGain_le_one n hN)]
  have hNNe : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  simp only [wilderGain]
  field_simp [hNNe]

theorem wilder_effectiveLength
    (n : ℕ)
    (hN : 1 ≤ n) :
    effectiveLength (wilderGain n) = 2 * (n : ℝ) - 1 := by
  rw [effectiveLength_eq (wilderGain n)
    (wilderGain_pos n (lt_of_lt_of_le Nat.zero_lt_one hN))
    (wilderGain_le_one n hN)]
  have hNNe : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  simp only [wilderGain]
  field_simp [hNNe]

theorem wilderWeight_sq_hasSum
    (n : ℕ)
    (hN : 1 ≤ n) :
    HasSum (fun lag : ℕ ↦ (wilderWeight n lag) ^ 2)
      (1 / (2 * (n : ℝ) - 1)) := by
  have hBase := exponentialWeight_sq_hasSum (wilderGain n)
    (wilderGain_pos n (lt_of_lt_of_le Nat.zero_lt_one hN))
    (wilderGain_le_one n hN)
  convert hBase using 1
  · ext lag
    rfl
  · have hNNe : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
    simp only [wilderGain]
    field_simp [hNNe]

/-! ## Finite weighted smoothers and exact variance -/

section Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite causal weighted sum of innovations. -/
def finiteWeightedSmoother
    (weight : ℕ → ℝ)
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ) : Ω → ℝ :=
  ∑ lag ∈ range count, fun ω ↦ weight lag * innovation lag ω

/-- Finite Wilder smoother, truncated after `count` lags. -/
def finiteWilderSmoother
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ) : Ω → ℝ :=
  finiteWeightedSmoother (wilderWeight n) innovation count

theorem variance_finiteWeightedSmoother
    (mu : Measure Ω)
    (weight : ℕ → ℝ)
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ)
    (hMemLp : ∀ lag < count, MemLp (innovation lag) 2 mu)
    (hIndependent :
      Set.Pairwise (↑(range count))
        (fun i j ↦ innovation i ⟂ᵢ[mu] innovation j)) :
    variance (finiteWeightedSmoother weight innovation count) mu =
      ∑ lag ∈ range count,
        (weight lag) ^ 2 * variance (innovation lag) mu := by
  let weighted : ℕ → Ω → ℝ :=
    fun lag ω ↦ weight lag * innovation lag ω
  have hWeightedMemLp :
      ∀ lag ∈ range count, MemLp (weighted lag) 2 mu := by
    intro lag hLag
    exact (hMemLp lag (mem_range.mp hLag)).const_mul (weight lag)
  have hWeightedIndependent :
      Set.Pairwise (↑(range count))
        (fun i j ↦ weighted i ⟂ᵢ[mu] weighted j) := by
    intro i hi j hj hij
    have hBase := hIndependent hi hj hij
    have hLeft : Measurable (fun x : ℝ ↦ weight i * x) :=
      measurable_const.mul measurable_id
    have hRight : Measurable (fun x : ℝ ↦ weight j * x) :=
      measurable_const.mul measurable_id
    have hScaled := hBase.comp hLeft hRight
    simpa only [weighted, Function.comp_def] using hScaled
  calc
    variance (finiteWeightedSmoother weight innovation count) mu =
        variance (∑ lag ∈ range count, weighted lag) mu := by
          rfl
    _ = ∑ lag ∈ range count, variance (weighted lag) mu :=
      IndepFun.variance_sum hWeightedMemLp hWeightedIndependent
    _ = ∑ lag ∈ range count,
          (weight lag) ^ 2 * variance (innovation lag) mu := by
      apply sum_congr rfl
      intro lag hLag
      exact variance_const_mul (weight lag) (innovation lag) mu

theorem variance_finiteWeightedSmoother_iid
    (mu : Measure Ω)
    (weight : ℕ → ℝ)
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ)
    (sigmaSq : ℝ)
    (hMemLp : ∀ lag < count, MemLp (innovation lag) 2 mu)
    (hIndependent :
      Set.Pairwise (↑(range count))
        (fun i j ↦ innovation i ⟂ᵢ[mu] innovation j))
    (hVariance : ∀ lag < count, variance (innovation lag) mu = sigmaSq) :
    variance (finiteWeightedSmoother weight innovation count) mu =
      sigmaSq * ∑ lag ∈ range count, (weight lag) ^ 2 := by
  rw [variance_finiteWeightedSmoother mu weight innovation count
    hMemLp hIndependent]
  calc
    (∑ lag ∈ range count,
        weight lag ^ 2 * variance (innovation lag) mu) =
        ∑ lag ∈ range count, weight lag ^ 2 * sigmaSq := by
          apply sum_congr rfl
          intro lag hLag
          rw [hVariance lag (mem_range.mp hLag)]
    _ = sigmaSq * ∑ lag ∈ range count, weight lag ^ 2 := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro lag hLag
      ring

theorem variance_finiteWilderSmoother_iid
    (mu : Measure Ω)
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ)
    (sigmaSq : ℝ)
    (hMemLp : ∀ lag < count, MemLp (innovation lag) 2 mu)
    (hIndependent :
      Set.Pairwise (↑(range count))
        (fun i j ↦ innovation i ⟂ᵢ[mu] innovation j))
    (hVariance : ∀ lag < count, variance (innovation lag) mu = sigmaSq) :
    variance (finiteWilderSmoother n count innovation) mu =
      sigmaSq * ∑ lag ∈ range count, (wilderWeight n lag) ^ 2 := by
  exact variance_finiteWeightedSmoother_iid
    mu (wilderWeight n) innovation count sigmaSq
    hMemLp hIndependent hVariance

/-- The exact infinite-kernel variance scale suggested by finite truncations. -/
def wilderVarianceScale (n : ℕ) (sigmaSq : ℝ) : ℝ :=
  sigmaSq * ∑' lag : ℕ, (wilderWeight n lag) ^ 2

theorem wilderVarianceScale_eq
    (n : ℕ)
    (sigmaSq : ℝ)
    (hN : 1 ≤ n) :
    wilderVarianceScale n sigmaSq =
      sigmaSq / (2 * (n : ℝ) - 1) := by
  rw [wilderVarianceScale, wilderWeight_sq_tsum n hN]
  ring

theorem finiteWilderVariance_tendsto_exactScale
    (n : ℕ)
    (sigmaSq : ℝ)
    (hN : 1 ≤ n) :
    Tendsto
      (fun count ↦
        sigmaSq * ∑ lag ∈ range count, (wilderWeight n lag) ^ 2)
      atTop
      (nhds (sigmaSq / (2 * (n : ℝ) - 1))) := by
  have hHasSum :
      HasSum (fun lag : ℕ ↦ (wilderWeight n lag) ^ 2)
        (1 / (2 * (n : ℝ) - 1)) := by
    exact wilderWeight_sq_hasSum n hN
  have hPartial := hHasSum.tendsto_sum_nat
  simpa [div_eq_mul_inv] using hPartial.const_mul sigmaSq

end Probability

end

end EndpointCoordinate
