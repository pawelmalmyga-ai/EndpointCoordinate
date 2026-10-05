import EndpointCoordinate.Probability
set_option linter.style.header false
/-!
# Exponentially weighted endpoint coordinate: stationary series and law constants

This file supplies the bridge between the exact finite-horizon layer and the
asymptotic statements in the paper.

The first half constructs the infinite-past Wilder smoother in an arbitrary
complete normed real vector space.  Taking that space to be `L²` gives the
stationary random smoother.  The construction uses absolute convergence and
therefore does not need independence.

The second half records the exact tail-energy and infinitesimal-row identities
used by the triangular-array CLT.  The last part formalizes the algebra behind
the law-dependent Gaussian, Laplace, and Student first variance shifts.

This module does not claim the CLT or the heavy-tail localization theorem.
Those require separate probability-limit arguments.  Everything stated here
is exact and contains no proof placeholders.
-/

namespace EndpointCoordinate

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Finset Filter MeasureTheory ProbabilityTheory

/-! ## Exact tails of the Wilder kernel -/

theorem wilderWeight_add
    (n lag cutoff : ℕ) :
    wilderWeight n (lag + cutoff) =
      (wilderDecay n) ^ cutoff * wilderWeight n lag := by
  simp only [wilderWeight, exponentialWeight, wilderDecay]
  rw [pow_add]
  ring

theorem wilderWeight_tail_hasSum
    (n cutoff : ℕ)
    (hN : 1 ≤ n) :
    HasSum (fun lag : ℕ ↦ wilderWeight n (lag + cutoff))
      ((wilderDecay n) ^ cutoff) := by
  have hBase := (wilderWeight_hasSum_one n hN).const_smul
    ((wilderDecay n) ^ cutoff)
  convert hBase using 1
  · ext lag
    simp only [smul_eq_mul]
    exact wilderWeight_add n lag cutoff
  · simp

theorem wilderWeight_tail_tsum
    (n cutoff : ℕ)
    (hN : 1 ≤ n) :
    ∑' lag : ℕ, wilderWeight n (lag + cutoff) =
      (wilderDecay n) ^ cutoff :=
  (wilderWeight_tail_hasSum n cutoff hN).tsum_eq

theorem wilderWeight_sq_add
    (n lag cutoff : ℕ) :
    (wilderWeight n (lag + cutoff)) ^ 2 =
      (wilderDecay n) ^ (2 * cutoff) *
        (wilderWeight n lag) ^ 2 := by
  rw [wilderWeight_add]
  simp only [mul_pow]
  rw [← pow_mul]
  congr 2
  omega

theorem wilderWeight_sq_tail_hasSum
    (n cutoff : ℕ)
    (hN : 1 ≤ n) :
    HasSum
      (fun lag : ℕ ↦ (wilderWeight n (lag + cutoff)) ^ 2)
      ((wilderDecay n) ^ (2 * cutoff) /
        (2 * (n : ℝ) - 1)) := by
  have hBase := (wilderWeight_sq_hasSum n hN).const_smul
    ((wilderDecay n) ^ (2 * cutoff))
  convert hBase using 1
  · ext lag
    simp only [smul_eq_mul]
    exact wilderWeight_sq_add n lag cutoff
  · ring

theorem wilderWeight_sq_tail_tsum
    (n cutoff : ℕ)
    (hN : 1 ≤ n) :
    ∑' lag : ℕ, (wilderWeight n (lag + cutoff)) ^ 2 =
      (wilderDecay n) ^ (2 * cutoff) /
        (2 * (n : ℝ) - 1) :=
  (wilderWeight_sq_tail_hasSum n cutoff hN).tsum_eq

theorem wilderWeight_sq_sum_range
    (n count : ℕ)
    (hN : 1 ≤ n) :
    (∑ lag ∈ range count, (wilderWeight n lag) ^ 2) =
      (1 - (wilderDecay n) ^ (2 * count)) /
        (2 * (n : ℝ) - 1) := by
  have hSummable := (wilderWeight_sq_hasSum n hN).summable
  have hSplit := hSummable.sum_add_tsum_nat_add count
  rw [wilderWeight_sq_tail_tsum n count hN,
    wilderWeight_sq_tsum n hN] at hSplit
  calc
    (∑ lag ∈ range count, (wilderWeight n lag) ^ 2) =
        1 / (2 * (n : ℝ) - 1) -
          (wilderDecay n) ^ (2 * count) /
            (2 * (n : ℝ) - 1) := by linarith
    _ = (1 - (wilderDecay n) ^ (2 * count)) /
          (2 * (n : ℝ) - 1) := by ring

theorem wilderWeight_sq_tail_fraction
    (n cutoff : ℕ)
    (hN : 1 ≤ n) :
    (∑' lag : ℕ, (wilderWeight n (lag + cutoff)) ^ 2) /
        (∑' lag : ℕ, (wilderWeight n lag) ^ 2) =
      (wilderDecay n) ^ (2 * cutoff) := by
  rw [wilderWeight_sq_tail_tsum n cutoff hN,
    wilderWeight_sq_tsum n hN]
  have hNReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
  have hDenominator : 2 * (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem wilderWeight_le_gain
    (n lag : ℕ)
    (hN : 1 ≤ n) :
    wilderWeight n lag ≤ wilderGain n := by
  exact exponentialWeight_le_gain (wilderGain n)
    (le_of_lt (wilderGain_pos n
      (lt_of_lt_of_le Nat.zero_lt_one hN)))
    (wilderGain_le_one n hN) lag

/-! ## Infinite-past smoother in a complete normed space -/

section CompleteNormedSpace

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One term of the stationary infinite-past Wilder series. -/
def stationaryWilderTerm
    (n : ℕ)
    (innovation : ℕ → E)
    (lag : ℕ) : E :=
  (wilderWeight n lag) • innovation lag

/-- The stationary infinite-past Wilder smoother as a convergent series. -/
def stationaryWilderSeries
    (n : ℕ)
    (innovation : ℕ → E) : E :=
  ∑' lag : ℕ, stationaryWilderTerm n innovation lag

theorem stationaryWilderTerm_summable
    (n : ℕ)
    (innovation : ℕ → E)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    Summable (stationaryWilderTerm n innovation) := by
  have hMajor : Summable (fun lag : ℕ ↦ bound * wilderWeight n lag) := by
    have h := (wilderWeight_hasSum_one n hN).summable.const_smul bound
    simpa only [smul_eq_mul] using h
  apply Summable.of_norm_bounded hMajor
  intro lag
  rw [stationaryWilderTerm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (wilderWeight_nonnegative n hN lag)]
  calc
    wilderWeight n lag * ‖innovation lag‖ ≤
        wilderWeight n lag * bound :=
      mul_le_mul_of_nonneg_left (hBound lag)
        (wilderWeight_nonnegative n hN lag)
    _ = bound * wilderWeight n lag := by ring

theorem stationaryWilderSeries_hasSum
    (n : ℕ)
    (innovation : ℕ → E)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    HasSum (stationaryWilderTerm n innovation)
      (stationaryWilderSeries n innovation) :=
  (stationaryWilderTerm_summable n innovation bound hN hBound).hasSum

theorem finiteWilderSeries_tendsto_stationary
    (n : ℕ)
    (innovation : ℕ → E)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    Tendsto
      (fun count ↦
        ∑ lag ∈ range count, stationaryWilderTerm n innovation lag)
      atTop
      (nhds (stationaryWilderSeries n innovation)) :=
  (stationaryWilderSeries_hasSum n innovation bound hN hBound).tendsto_sum_nat

theorem stationaryWilderTail_norm_le
    (n cutoff : ℕ)
    (innovation : ℕ → E)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    ‖∑' lag : ℕ,
        (wilderWeight n (lag + cutoff)) •
          innovation (lag + cutoff)‖ ≤
      bound * (wilderDecay n) ^ cutoff := by
  let tailTerm : ℕ → E := fun lag ↦
    (wilderWeight n (lag + cutoff)) • innovation (lag + cutoff)
  have hWeightTail := wilderWeight_tail_hasSum n cutoff hN
  have hMajor :
      HasSum (fun lag : ℕ ↦ bound * wilderWeight n (lag + cutoff))
        (bound * (wilderDecay n) ^ cutoff) := by
    simpa only [smul_eq_mul] using hWeightTail.const_smul bound
  have hTermSummable : Summable tailTerm := by
    apply Summable.of_norm_bounded hMajor.summable
    intro lag
    simp only [tailTerm, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg
      (wilderWeight_nonnegative n hN (lag + cutoff))]
    calc
      wilderWeight n (lag + cutoff) * ‖innovation (lag + cutoff)‖ ≤
          wilderWeight n (lag + cutoff) * bound :=
        mul_le_mul_of_nonneg_left (hBound (lag + cutoff))
          (wilderWeight_nonnegative n hN (lag + cutoff))
      _ = bound * wilderWeight n (lag + cutoff) := by ring
  apply hTermSummable.hasSum.norm_le_of_bounded hMajor
  intro lag
  simp only [tailTerm, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (wilderWeight_nonnegative n hN (lag + cutoff))]
  calc
    wilderWeight n (lag + cutoff) * ‖innovation (lag + cutoff)‖ ≤
        wilderWeight n (lag + cutoff) * bound :=
      mul_le_mul_of_nonneg_left (hBound (lag + cutoff))
        (wilderWeight_nonnegative n hN (lag + cutoff))
    _ = bound * wilderWeight n (lag + cutoff) := by ring

theorem stationaryWilderSeries_eq_finite_add_tail
    (n cutoff : ℕ)
    (innovation : ℕ → E)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    stationaryWilderSeries n innovation =
      (∑ lag ∈ range cutoff,
        stationaryWilderTerm n innovation lag) +
      ∑' lag : ℕ,
        stationaryWilderTerm n innovation (lag + cutoff) := by
  have hSummable := stationaryWilderTerm_summable
    n innovation bound hN hBound
  exact (hSummable.sum_add_tsum_nat_add cutoff).symm

theorem stationaryWilderSeries_recursion
    (n : ℕ)
    (innovation : ℕ → E)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    stationaryWilderSeries n innovation =
      (wilderGain n) • innovation 0 +
      (wilderDecay n) •
        stationaryWilderSeries n (fun lag ↦ innovation (lag + 1)) := by
  have hSummable := stationaryWilderTerm_summable
    n innovation bound hN hBound
  have hShiftBound :
      ∀ lag, ‖innovation (lag + 1)‖ ≤ bound :=
    fun lag ↦ hBound (lag + 1)
  have hShiftSummable := stationaryWilderTerm_summable
    n (fun lag ↦ innovation (lag + 1)) bound hN hShiftBound
  rw [stationaryWilderSeries, hSummable.tsum_eq_zero_add]
  congr 1
  · simp [stationaryWilderTerm, wilderWeight_zero]
  · rw [stationaryWilderSeries]
    rw [← hShiftSummable.tsum_const_smul (wilderDecay n)]
    apply tsum_congr
    intro lag
    simp only [stationaryWilderTerm, wilderWeight_succ]
    rw [mul_smul]

end CompleteNormedSpace

/-! ## `L²` specialization -/

section LpConstruction

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Stationary Wilder smoothing performed directly in the complete `L²` space. -/
def stationaryWilderLp
    (mu : Measure Ω)
    (n : ℕ)
    (innovation : ℕ → Lp ℝ 2 mu) : Lp ℝ 2 mu :=
  stationaryWilderSeries n innovation

theorem finiteWilderLp_tendsto_stationary
    (mu : Measure Ω)
    (n : ℕ)
    (innovation : ℕ → Lp ℝ 2 mu)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    Tendsto
      (fun count ↦
        ∑ lag ∈ range count,
          stationaryWilderTerm n innovation lag)
      atTop
      (nhds (stationaryWilderLp mu n innovation)) := by
  exact finiteWilderSeries_tendsto_stationary
    n innovation bound hN hBound

theorem stationaryWilderLp_tail_norm_le
    (mu : Measure Ω)
    (n cutoff : ℕ)
    (innovation : ℕ → Lp ℝ 2 mu)
    (bound : ℝ)
    (hN : 1 ≤ n)
    (hBound : ∀ lag, ‖innovation lag‖ ≤ bound) :
    ‖∑' lag : ℕ,
        (wilderWeight n (lag + cutoff)) •
          innovation (lag + cutoff)‖ ≤
      bound * (wilderDecay n) ^ cutoff :=
  stationaryWilderTail_norm_le n cutoff innovation bound hN
    hBound

end LpConstruction

/-! ## Infinitesimal triangular-array identities -/

/-- Squared normalized coefficient used in the Lindeberg row. -/
def lindebergWeightSq (n lag : ℕ) : ℝ :=
  (2 * (n : ℝ) - 1) * (wilderWeight n lag) ^ 2

theorem lindebergWeightSq_hasSum_one
    (n : ℕ)
    (hN : 1 ≤ n) :
    HasSum (lindebergWeightSq n) 1 := by
  have h := (wilderWeight_sq_hasSum n hN).const_smul
    (2 * (n : ℝ) - 1)
  convert h using 1
  · ext lag
    simp [lindebergWeightSq, smul_eq_mul]
  · have hNReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
    have hDenominator : 2 * (n : ℝ) - 1 ≠ 0 := by linarith
    simp [smul_eq_mul, hDenominator]

theorem lindebergWeightSq_tsum_one
    (n : ℕ)
    (hN : 1 ≤ n) :
    ∑' lag : ℕ, lindebergWeightSq n lag = 1 :=
  (lindebergWeightSq_hasSum_one n hN).tsum_eq

theorem lindebergWeightSq_nonnegative
    (n lag : ℕ)
    (hN : 1 ≤ n) :
    0 ≤ lindebergWeightSq n lag := by
  have hNReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
  exact mul_nonneg (by linarith) (sq_nonneg _)

theorem lindebergWeightSq_le_leading
    (n lag : ℕ)
    (hN : 1 ≤ n) :
    lindebergWeightSq n lag ≤ lindebergWeightSq n 0 := by
  have hNReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
  have hFactor : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
  apply mul_le_mul_of_nonneg_left _ hFactor
  exact (sq_le_sq₀
    (wilderWeight_nonnegative n hN lag)
    (by simpa [wilderWeight_zero] using
      wilderWeight_nonnegative n hN 0)).2
    (by simpa [wilderWeight_zero] using
      wilderWeight_le_gain n lag hN)

theorem lindebergLeadingWeightSq_eq
    (n : ℕ)
    (hN : 1 ≤ n) :
    lindebergWeightSq n 0 =
      (2 * (n : ℝ) - 1) / (n : ℝ) ^ 2 := by
  have hNNe : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  simp only [lindebergWeightSq, wilderWeight_zero, wilderGain]
  field_simp

theorem lindebergLeadingWeightSq_nonnegative
    (n : ℕ) :
    0 ≤ lindebergWeightSq n 0 := by
  by_cases hN : n = 0
  · simp [hN, lindebergWeightSq, wilderWeight_zero, wilderGain]
  · exact lindebergWeightSq_nonnegative n 0 (Nat.one_le_iff_ne_zero.mpr hN)

theorem lindebergLeadingWeightSq_le_two_div
    (n : ℕ) :
    lindebergWeightSq n 0 ≤ 2 / (n : ℝ) := by
  by_cases hN : n = 0
  · simp [hN, lindebergWeightSq, wilderWeight_zero, wilderGain]
  · have hOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hN
    rw [lindebergLeadingWeightSq_eq n hOne]
    have hNReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_iff₀ (sq_pos_of_pos hNReal)).2
    field_simp [ne_of_gt hNReal]
    nlinarith

theorem lindebergLeadingWeightSq_tendsto_zero :
    Tendsto (fun n : ℕ ↦ lindebergWeightSq n 0)
      atTop (nhds 0) := by
  have hUpper :
      Tendsto (fun n : ℕ ↦ 2 / (n : ℝ)) atTop (nhds 0) := by
    have hInv :
        Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv] using hInv.const_mul (2 : ℝ)
  exact Filter.Tendsto.squeeze tendsto_const_nhds hUpper
    lindebergLeadingWeightSq_nonnegative
    lindebergLeadingWeightSq_le_two_div

theorem wilder_scaled_energy_tendsto_half :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) /
        (2 * (n : ℝ) - 1))
      atTop
      (nhds (1 / 2 : ℝ)) := by
  have hInv :
      Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hDenom :
      Tendsto (fun n : ℕ ↦ 2 - 1 / (n : ℝ))
        atTop (nhds (2 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hInv
  have hOne :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hRatio := hOne.div hDenom (by norm_num : (2 : ℝ) ≠ 0)
  apply hRatio.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
  have hNNe : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  change 1 / (2 - 1 / (n : ℝ)) =
    (n : ℝ) / (2 * (n : ℝ) - 1)
  field_simp [hNNe]

/-! ## Law-dependent asymptotic scales -/

/-- Squared first-order scale `C_F² = 2 Var(ε) / E|ε|²`. -/
def firstOrderScaleSq (variance firstAbsoluteMoment : ℝ) : ℝ :=
  2 * variance / firstAbsoluteMoment ^ 2

/-- Positive square-root version of the first-order scale. -/
def firstOrderScale (variance firstAbsoluteMoment : ℝ) : ℝ :=
  Real.sqrt (firstOrderScaleSq variance firstAbsoluteMoment)

theorem firstOrderScaleSq_scale_invariant
    (variance firstAbsoluteMoment scale : ℝ)
    (hScale : scale ≠ 0) :
    firstOrderScaleSq (scale ^ 2 * variance)
      (|scale| * firstAbsoluteMoment) =
      firstOrderScaleSq variance firstAbsoluteMoment := by
  simp only [firstOrderScaleSq]
  rw [mul_pow, sq_abs]
  field_simp

/-- Unit-variance Gaussian value of `E|ε|`. -/
def gaussianFirstAbsoluteMoment : ℝ :=
  Real.sqrt (2 / Real.pi)

/-- Unit-variance Laplace value of `E|ε|`. -/
def laplaceFirstAbsoluteMoment : ℝ :=
  1 / Real.sqrt 2

theorem gaussian_firstOrderScaleSq :
    firstOrderScaleSq 1 gaussianFirstAbsoluteMoment = Real.pi := by
  have hNonnegative : 0 ≤ 2 / Real.pi := by positivity
  have hPiNe : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [firstOrderScaleSq, gaussianFirstAbsoluteMoment,
    Real.sq_sqrt hNonnegative]
  field_simp

theorem gaussian_firstOrderScale :
    firstOrderScale 1 gaussianFirstAbsoluteMoment = Real.sqrt Real.pi := by
  rw [firstOrderScale, gaussian_firstOrderScaleSq]

theorem laplace_firstOrderScaleSq :
    firstOrderScaleSq 1 laplaceFirstAbsoluteMoment = 4 := by
  have hSqrtTwoPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hSquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [firstOrderScaleSq, laplaceFirstAbsoluteMoment]
  field_simp
  nlinarith

theorem laplace_firstOrderScale :
    firstOrderScale 1 laplaceFirstAbsoluteMoment = 2 := by
  rw [firstOrderScale, laplace_firstOrderScaleSq]
  norm_num

/-! ## First finite-horizon variance shift -/

/-- Coefficient of `alpha²` in the symmetric-law variance expansion. -/
def secondVarianceCoefficient (m2 m3 : ℝ) : ℝ :=
  (15 * m2 ^ 2 + 2 * m2 - 8 * m3) / 3

/-- Constant shift produced by inversion of the two-term variance series. -/
def firstVarianceShift (m2 m3 : ℝ) : ℝ :=
  secondVarianceCoefficient m2 m3 / (2 * m2)

theorem firstVarianceShift_eq
    (m2 m3 : ℝ)
    (hM2 : m2 ≠ 0) :
    firstVarianceShift m2 m3 =
      (15 * m2 ^ 2 + 2 * m2 - 8 * m3) / (6 * m2) := by
  simp only [firstVarianceShift, secondVarianceCoefficient]
  field_simp
  ring

theorem exact_two_term_normalizer_identity
    (alpha leading second : ℝ)
    (hAlpha : alpha ≠ 0)
    (hLeading : leading ≠ 0)
    (hPerturbed : leading + second * alpha ≠ 0) :
    leading / (leading * alpha + second * alpha ^ 2) =
      1 / alpha - second / leading +
        second ^ 2 * alpha /
          (leading * (leading + second * alpha)) := by
  rw [show leading * alpha + second * alpha ^ 2 =
    alpha * (leading + second * alpha) by ring]
  have hPerturbed' : leading + alpha * second ≠ 0 := by
    simpa [mul_comm] using hPerturbed
  field_simp [hAlpha, hLeading, hPerturbed, hPerturbed']
  ring

theorem two_term_normalizer_remainder_tendsto_zero
    (leading second : ℝ)
    (hLeading : leading ≠ 0) :
    Tendsto
      (fun alpha : ℝ ↦
        second ^ 2 * alpha /
          (leading * (leading + second * alpha)))
      (nhds 0)
      (nhds 0) := by
  have hNumerator :
      Tendsto (fun alpha : ℝ ↦ second ^ 2 * alpha)
        (nhds 0) (nhds 0) := by
    have hConst :
        Tendsto (fun _ : ℝ ↦ second ^ 2)
          (nhds 0) (nhds (second ^ 2)) := tendsto_const_nhds
    simpa using hConst.mul tendsto_id
  have hDenominator :
      Tendsto
        (fun alpha : ℝ ↦ leading * (leading + second * alpha))
        (nhds 0) (nhds (leading * leading)) := by
    have hLeadingConst :
        Tendsto (fun _ : ℝ ↦ leading)
          (nhds 0) (nhds leading) := tendsto_const_nhds
    have hSecondConst :
        Tendsto (fun _ : ℝ ↦ second)
          (nhds 0) (nhds second) := tendsto_const_nhds
    simpa using hLeadingConst.mul
      (hLeadingConst.add (hSecondConst.mul tendsto_id))
  change Tendsto
    ((fun alpha : ℝ ↦ second ^ 2 * alpha) /
      (fun alpha : ℝ ↦ leading * (leading + second * alpha)))
    (nhds 0) (nhds 0)
  simpa only [zero_div] using
    hNumerator.div hDenominator (mul_ne_zero hLeading hLeading)

theorem laplace_firstVarianceShift :
    firstVarianceShift 2 6 = 4 / 3 := by
  norm_num [firstVarianceShift, secondVarianceCoefficient]

theorem gaussian_firstVarianceShift :
    firstVarianceShift (Real.pi / 2) Real.pi =
      (15 * Real.pi - 28) / 12 := by
  have hPiNe : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [firstVarianceShift_eq (Real.pi / 2) Real.pi (div_ne_zero hPiNe (by norm_num))]
  field_simp
  ring

/-! ## Student-t first-shift audit -/

/-- Student shift expressed through its squared first-order scale. -/
def studentFirstVarianceShift (nu scaleSq : ℝ) : ℝ :=
  (5 / 4) * scaleSq - 7 / 3 - 8 / (3 * (nu - 3))

theorem studentFirstVarianceShift_four :
    studentFirstVarianceShift 4 4 = 0 := by
  norm_num [studentFirstVarianceShift]

theorem studentFirstVarianceShift_six :
    studentFirstVarianceShift 6 (32 / 9) = 11 / 9 := by
  norm_num [studentFirstVarianceShift]

theorem studentFirstVarianceShift_eq_one_iff
    (nu scaleSq : ℝ)
    (hNu : nu ≠ 3) :
    studentFirstVarianceShift nu scaleSq = 1 ↔
      scaleSq =
        (4 / 5) * (10 / 3 + 8 / (3 * (nu - 3))) := by
  simp only [studentFirstVarianceShift]
  constructor <;> intro h
  · field_simp at h ⊢
    linarith
  · rw [h]
    field_simp
    ring

/-- Gaussian endpoint of the Student shift formula as `nu → ∞`. -/
def gaussianLimitVarianceShift : ℝ :=
  (5 / 4) * Real.pi - 7 / 3

theorem gaussianLimitVarianceShift_eq :
    gaussianLimitVarianceShift =
      (15 * Real.pi - 28) / 12 := by
  simp only [gaussianLimitVarianceShift]
  ring

end

end EndpointCoordinate
