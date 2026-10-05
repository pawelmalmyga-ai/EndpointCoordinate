import EndpointCoordinate.Gaussian
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

set_option linter.style.header false

/-!
# Endpoint coordinate: Laplace benchmark

Mathlib does not currently provide a named Laplace probability measure.  This
module therefore characterizes the centered unit-variance Laplace law by its
characteristic function

`phi(t) = 1 / (1 + t^2 / 2)`.

For independent innovations with that characteristic function we prove the
exact characteristic function of every finite weighted smoother.  For the
Wilder triangular array we also prove the exact finite variance and a
fourth-order Lyapunov bound that vanishes uniformly in the truncation length.

The last theorem is the precise Levy bridge: pointwise convergence of the
explicit finite products implies convergence in distribution to the standard
Gaussian.  Thus the probabilistic statement is reduced to a deterministic
analytic product limit, with no hidden distributional approximation.
-/

namespace EndpointCoordinate

noncomputable section

open Complex Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology NNReal

/-! ## Unit-variance Laplace characteristic function -/

/-- Characteristic function of a centered Laplace variable with variance one.
Its scale parameter is `1 / sqrt 2`. -/
def unitVarianceLaplaceCharFun (t : ℝ) : ℂ :=
  ((1 : ℂ) + (t : ℂ) ^ 2 / 2)⁻¹

@[simp]
theorem unitVarianceLaplaceCharFun_zero :
    unitVarianceLaplaceCharFun 0 = 1 := by
  simp [unitVarianceLaplaceCharFun]

theorem unitVarianceLaplaceCharFun_neg (t : ℝ) :
    unitVarianceLaplaceCharFun (-t) = unitVarianceLaplaceCharFun t := by
  simp [unitVarianceLaplaceCharFun]

/-- A random variable has the unit-variance Laplace characteristic profile. -/
def HasUnitVarianceLaplaceCF
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  AEMeasurable X μ ∧
    ∀ t : ℝ, charFun (μ.map X) t = unitVarianceLaplaceCharFun t

theorem HasUnitVarianceLaplaceCF.aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω}
    (hX : HasUnitVarianceLaplaceCF X μ) :
    AEMeasurable X μ :=
  hX.1

theorem HasUnitVarianceLaplaceCF.charFun_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω}
    (hX : HasUnitVarianceLaplaceCF X μ)
    (t : ℝ) :
    charFun (μ.map X) t = unitVarianceLaplaceCharFun t :=
  hX.2 t

/-- Scaling a unit-variance Laplace variable evaluates its characteristic
function at the correspondingly scaled argument. -/
theorem charFun_const_mul_of_unitVarianceLaplaceCF
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω}
    (hX : HasUnitVarianceLaplaceCF X μ)
    (c t : ℝ) :
    charFun (μ.map (fun ω ↦ c * X ω)) t =
      unitVarianceLaplaceCharFun (c * t) := by
  rw [charFun_map_mul_comp hX.aemeasurable c t]
  exact hX.charFun_eq (c * t)

/-! ## Exact finite-product law -/

/-- Exact characteristic function of a finite deterministic weighted sum of
independent unit-variance Laplace innovations. -/
theorem charFun_finiteWeightedSmoother_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    (weight : ℕ → ℝ)
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ)
    (hIndependent : iIndepFun innovation μ)
    (hLaplace : ∀ lag, HasUnitVarianceLaplaceCF (innovation lag) μ)
    (t : ℝ) :
    charFun (μ.map (finiteWeightedSmoother weight innovation count)) t =
      ∏ lag ∈ range count,
        unitVarianceLaplaceCharFun (weight lag * t) := by
  let weighted : ℕ → Ω → ℝ :=
    fun lag ω ↦ weight lag * innovation lag ω
  have hWeightedIndependent : iIndepFun weighted μ := by
    exact hIndependent.comp (fun lag x ↦ weight lag * x) (by fun_prop)
  have hWeightedMeasurable : ∀ lag, AEMeasurable (weighted lag) μ := by
    intro lag
    exact (hLaplace lag).aemeasurable.const_mul _
  have hProduct :=
    (hWeightedIndependent.restrict (range count)).charFun_map_fun_finsetSum_eq_prod
      (fun lag hlag ↦ hWeightedMeasurable lag)
  have hAtT := congrFun hProduct t
  calc
    charFun (μ.map (finiteWeightedSmoother weight innovation count)) t =
        charFun (μ.map (fun ω ↦ ∑ lag ∈ range count, weighted lag ω)) t := by
      congr 2
      funext ω
      simp only [finiteWeightedSmoother, Finset.sum_apply, weighted]
    _ = ∏ lag ∈ range count, charFun (μ.map (weighted lag)) t := by
      simpa only [Finset.prod_apply] using hAtT
    _ = ∏ lag ∈ range count,
        unitVarianceLaplaceCharFun (weight lag * t) := by
      apply prod_congr rfl
      intro lag hlag
      simpa only [weighted] using
        charFun_const_mul_of_unitVarianceLaplaceCF
          (hLaplace lag) (weight lag) t

/-! ## Variance-normalized Wilder rows -/

/-- The variance normalization is the same `sqrt (2n - 1)` for every
unit-variance input law. -/
def laplaceNormalizedWilderWeight (n lag : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) - 1) * wilderWeight n lag

theorem laplaceNormalizedWilderWeight_eq_gaussian
    (n lag : ℕ) :
    laplaceNormalizedWilderWeight n lag =
      gaussianNormalizedWilderWeight n lag := by
  rfl

def finiteLaplaceWilderRow
    {Ω : Type*}
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ) : Ω → ℝ :=
  finiteWeightedSmoother (laplaceNormalizedWilderWeight n) innovation count

theorem finiteLaplaceWilderRow_eq_gaussianRow
    {Ω : Type*}
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ) :
    finiteLaplaceWilderRow n count innovation =
      finiteGaussianWilderRow n count innovation := by
  rfl

theorem laplaceNormalizedWilderWeight_sq_sum_range
    (n count : ℕ)
    (hN : 1 ≤ n) :
    (∑ lag ∈ range count,
      (laplaceNormalizedWilderWeight n lag) ^ 2) =
      1 - (wilderDecay n) ^ (2 * count) := by
  simpa only [laplaceNormalizedWilderWeight_eq_gaussian] using
    gaussianNormalizedWilderWeight_sq_sum_range n count hN

/-- Exact finite-row characteristic function for Laplace innovations. -/
theorem charFun_finiteLaplaceWilderRow
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ)
    (hIndependent : iIndepFun innovation μ)
    (hLaplace : ∀ lag, HasUnitVarianceLaplaceCF (innovation lag) μ)
    (t : ℝ) :
    charFun (μ.map (finiteLaplaceWilderRow n count innovation)) t =
      ∏ lag ∈ range count,
        unitVarianceLaplaceCharFun
          (laplaceNormalizedWilderWeight n lag * t) := by
  exact charFun_finiteWeightedSmoother_laplace
    (laplaceNormalizedWilderWeight n) innovation count
    hIndependent hLaplace t

theorem aemeasurable_finiteLaplaceWilderRow
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ)
    (hLaplace : ∀ lag, HasUnitVarianceLaplaceCF (innovation lag) μ) :
    AEMeasurable (finiteLaplaceWilderRow n count innovation) μ := by
  have hSum := (range count).aemeasurable_sum
    (f := fun lag ω ↦
      laplaceNormalizedWilderWeight n lag * innovation lag ω)
    (fun lag hlag ↦ (hLaplace lag).aemeasurable.const_mul _)
  simpa only [finiteLaplaceWilderRow, finiteWeightedSmoother,
    Finset.sum_apply] using hSum

/-- Exact variance of a finite normalized Wilder row.  The only missing
variance is the squared geometric tail. -/
theorem variance_finiteLaplaceWilderRow
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ)
    (hN : 1 ≤ n)
    (hMemLp : ∀ lag < count, MemLp (innovation lag) 2 μ)
    (hIndependent : iIndepFun innovation μ)
    (hVariance : ∀ lag < count, variance (innovation lag) μ = 1) :
    variance (finiteLaplaceWilderRow n count innovation) μ =
      1 - (wilderDecay n) ^ (2 * count) := by
  have hPairwise :
      Set.Pairwise (↑(range count))
        (fun i j ↦ innovation i ⟂ᵢ[μ] innovation j) := by
    intro i hi j hj hij
    exact hIndependent.indepFun hij
  unfold finiteLaplaceWilderRow
  rw [variance_finiteWeightedSmoother_iid μ
    (laplaceNormalizedWilderWeight n) innovation count 1
    hMemLp hPairwise hVariance]
  simp only [one_mul]
  exact laplaceNormalizedWilderWeight_sq_sum_range n count hN

/-! ## The deterministic Lyapunov quantity -/

/-- For unit-variance Laplace innovations `E[X^4] = 6`.  Consequently this
is exactly the sum of the fourth moments of the normalized row terms. -/
def laplaceFourthLyapunovMass (n count : ℕ) : ℝ :=
  6 * ∑ lag ∈ range count, (lindebergWeightSq n lag) ^ 2

theorem laplaceFourthLyapunovMass_nonnegative
    (n count : ℕ)
    (_hN : 1 ≤ n) :
    0 ≤ laplaceFourthLyapunovMass n count := by
  exact mul_nonneg (by norm_num) (sum_nonneg fun lag hlag ↦ sq_nonneg _)

/-- The complete fourth-order error is controlled by the largest normalized
weight.  The bound is independent of the truncation length. -/
theorem laplaceFourthLyapunovMass_le
    (n count : ℕ)
    (hN : 1 ≤ n) :
    laplaceFourthLyapunovMass n count ≤
      6 * lindebergWeightSq n 0 := by
  have hTerm : ∀ lag,
      (lindebergWeightSq n lag) ^ 2 ≤
        lindebergWeightSq n 0 * lindebergWeightSq n lag := by
    intro lag
    have hNonnegative := lindebergWeightSq_nonnegative n lag hN
    have hLe := lindebergWeightSq_le_leading n lag hN
    nlinarith
  have hPartial :
      (∑ lag ∈ range count, lindebergWeightSq n lag) ≤ 1 := by
    have hSummable := (lindebergWeightSq_hasSum_one n hN).summable
    simpa [lindebergWeightSq_tsum_one n hN] using
      hSummable.sum_le_tsum (range count)
        (fun lag hlag ↦ lindebergWeightSq_nonnegative n lag hN)
  calc
    laplaceFourthLyapunovMass n count =
        6 * ∑ lag ∈ range count, (lindebergWeightSq n lag) ^ 2 := rfl
    _ ≤ 6 * ∑ lag ∈ range count,
        lindebergWeightSq n 0 * lindebergWeightSq n lag := by
      gcongr with lag hlag
      exact hTerm lag
    _ = 6 * (lindebergWeightSq n 0 *
        ∑ lag ∈ range count, lindebergWeightSq n lag) := by
      rw [← Finset.mul_sum]
    _ ≤ 6 * (lindebergWeightSq n 0 * 1) := by
      gcongr
      exact lindebergLeadingWeightSq_nonnegative n
    _ = 6 * lindebergWeightSq n 0 := by ring

/-- The Laplace fourth-order Lyapunov mass vanishes for every choice of row
truncation lengths. -/
theorem laplaceFourthLyapunovMass_tendsto_zero
    (count : ℕ → ℕ) :
    Tendsto
      (fun n : ℕ ↦ laplaceFourthLyapunovMass (n + 1) (count n))
      atTop (𝓝 0) := by
  have hUpper : Tendsto
      (fun n : ℕ ↦ 6 * lindebergWeightSq (n + 1) 0)
      atTop (𝓝 0) := by
    have hShift := lindebergLeadingWeightSq_tendsto_zero.comp
      (tendsto_add_atTop_nat 1)
    simpa using hShift.const_mul 6
  apply Filter.Tendsto.squeeze tendsto_const_nhds hUpper
  · intro n
    exact laplaceFourthLyapunovMass_nonnegative (n + 1) (count n) (by omega)
  · intro n
    exact laplaceFourthLyapunovMass_le (n + 1) (count n) (by omega)

/-! ## Levy bridge to the Gaussian limit -/

/-- The explicit deterministic characteristic-product limit required for the
Laplace Wilder CLT.  It is separated as a named proposition so that the exact
probabilistic reduction remains visible. -/
def LaplaceWilderCharacteristicLimit (count : ℕ → ℕ) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun n : ℕ ↦
        ∏ lag ∈ range (count n),
          unitVarianceLaplaceCharFun
            (laplaceNormalizedWilderWeight (n + 1) lag * t))
      atTop
      (𝓝 (Complex.exp (-((t : ℂ) ^ 2) / 2)))

/-- Levy's theorem turns the explicit product limit into the Laplace-input
Wilder central limit theorem. -/
theorem finiteLaplaceWilderRow_clt_of_characteristicLimit
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
    (hProductLimit : LaplaceWilderCharacteristicLimit count) :
    TendstoInDistribution
      (fun n ↦ finiteLaplaceWilderRow (n + 1) (count n) innovation)
      atTop Y (fun _ ↦ μ) μ' := by
  apply TendstoInDistribution.of_tendsto_charFun
  · intro n
    exact aemeasurable_finiteLaplaceWilderRow
      (n + 1) (count n) innovation hLaplace
  · exact hY.aemeasurable
  · intro t
    rw! [hY.map_eq]
    have hRows :
        (fun n : ℕ ↦
          charFun
            (μ.map (finiteLaplaceWilderRow (n + 1) (count n) innovation)) t) =
        (fun n : ℕ ↦
          ∏ lag ∈ range (count n),
            unitVarianceLaplaceCharFun
              (laplaceNormalizedWilderWeight (n + 1) lag * t)) := by
      funext n
      exact charFun_finiteLaplaceWilderRow
        (n + 1) (count n) innovation hIndependent hLaplace t
    rw [hRows, charFun_gaussianReal]
    convert hProductLimit t using 1
    norm_num
    ring_nf

/-! ## Paper-facing calibration constants -/

theorem laplace_calibration_constants :
    firstOrderScale 1 laplaceFirstAbsoluteMoment = 2 ∧
      firstVarianceShift 2 6 = 4 / 3 := by
  exact ⟨laplace_firstOrderScale, laplace_firstVarianceShift⟩

end
end EndpointCoordinate
