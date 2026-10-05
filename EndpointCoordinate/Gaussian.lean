import EndpointCoordinate.CLT
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

set_option linter.style.header false

/-!
# Endpoint coordinate: exact Gaussian benchmark

For Gaussian innovations the finite weighted smoother is itself exactly
Gaussian. Thus the square-root effective-length normalization is not merely
asymptotic: after the full Wilder kernel is included, its variance is exactly
one. Finite truncations expose the only approximation error, namely the
omitted geometric tail energy.
-/

namespace EndpointCoordinate

noncomputable section

open Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology NNReal

section FiniteGaussianSmoother

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A finite deterministic linear combination of independent Gaussian
innovations is Gaussian. -/
theorem finiteWeightedSmoother_hasGaussianLaw
    (weight : ℕ → ℝ)
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ)
    (hIndependent : iIndepFun innovation μ)
    (hGaussian : ∀ lag, HasLaw (innovation lag) (gaussianReal 0 1) μ) :
    HasGaussianLaw (finiteWeightedSmoother weight innovation count) μ := by
  let weighted : ℕ → Ω → ℝ :=
    fun lag ω ↦ weight lag * innovation lag ω
  have hWeightedIndependent : iIndepFun weighted μ := by
    exact hIndependent.comp (fun lag x ↦ weight lag * x) (by fun_prop)
  have hWeightedGaussian : ∀ lag, HasGaussianLaw (weighted lag) μ := by
    intro lag
    exact (gaussianReal_const_mul (hGaussian lag) (weight lag)).hasGaussianLaw
  have hSum := iIndepFun.hasGaussianLaw_fun_sum
    (fun i : ↥(range count) ↦ hWeightedGaussian i)
    (hWeightedIndependent.restrict (range count))
  refine hSum.congr (ae_of_all μ fun ω ↦ ?_)
  simp only [weighted, finiteWeightedSmoother, Finset.sum_apply]
  change
    (∑ i : ↥(range count), weight i * innovation i ω) =
      ∑ lag ∈ range count, weight lag * innovation lag ω
  exact (Finset.sum_subtype (range count) (fun _ ↦ Iff.rfl)
    (fun lag ↦ weight lag * innovation lag ω)).symm

/-- Exact law of a finite weighted sum of independent standard Gaussian
innovations. The variance is the squared Euclidean norm of the weight vector. -/
theorem finiteWeightedSmoother_hasLaw_gaussianReal
    (weight : ℕ → ℝ)
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ)
    [IsProbabilityMeasure μ]
    (hIndependent : iIndepFun innovation μ)
    (hGaussian : ∀ lag, HasLaw (innovation lag) (gaussianReal 0 1) μ) :
    HasLaw (finiteWeightedSmoother weight innovation count)
      (gaussianReal 0
        (∑ lag ∈ range count, (weight lag) ^ 2).toNNReal) μ := by
  have hMemLp : ∀ lag < count, MemLp (innovation lag) 2 μ := by
    intro lag hlag
    exact (hGaussian lag).memLp (memLp_id_gaussianReal 2)
  have hPairwise :
      Set.Pairwise (↑(range count))
        (fun i j ↦ innovation i ⟂ᵢ[μ] innovation j) := by
    intro i hi j hj hij
    exact hIndependent.indepFun hij
  have hVariance : ∀ lag < count, variance (innovation lag) μ = 1 := by
    intro lag hlag
    rw [(hGaussian lag).variance_eq]
    simp
  have hMean :
      ∫ ω, finiteWeightedSmoother weight innovation count ω ∂μ = 0 := by
    simp only [finiteWeightedSmoother, Finset.sum_apply]
    rw [integral_finsetSum]
    · apply sum_eq_zero
      intro lag hlag
      rw [integral_const_mul, (hGaussian lag).integral_eq]
      simp
    · intro lag hlag
      exact (hMemLp lag (mem_range.mp hlag)).integrable (by norm_num) |>.const_mul _
  have hVar :
      variance (finiteWeightedSmoother weight innovation count) μ =
        ∑ lag ∈ range count, (weight lag) ^ 2 := by
    rw [variance_finiteWeightedSmoother_iid μ weight innovation count 1
      hMemLp hPairwise hVariance]
    simp
  have hGaussianSum :=
    finiteWeightedSmoother_hasGaussianLaw weight innovation count
      hIndependent hGaussian
  refine HasLaw.mk hGaussianSum.aemeasurable ?_
  rw [hGaussianSum.map_eq_gaussianReal, hMean, hVar]

end FiniteGaussianSmoother

/-- Wilder weights multiplied by the exact effective-length factor
`sqrt (2n - 1)`. -/
def gaussianNormalizedWilderWeight (n lag : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) - 1) * wilderWeight n lag

/-- A finite row of the Gaussian-normalized Wilder triangular array. -/
def finiteGaussianWilderRow
    {Ω : Type*}
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ) : Ω → ℝ :=
  finiteWeightedSmoother (gaussianNormalizedWilderWeight n) innovation count

/-- The normalized row is the ordinary finite Wilder smoother multiplied by
`sqrt (2n - 1)`. -/
theorem finiteGaussianWilderRow_eq
    {Ω : Type*}
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ) :
    finiteGaussianWilderRow n count innovation =
      fun ω ↦ Real.sqrt (2 * (n : ℝ) - 1) *
        finiteWilderSmoother n count innovation ω := by
  funext ω
  simp only [finiteGaussianWilderRow, finiteWeightedSmoother,
    finiteWilderSmoother, gaussianNormalizedWilderWeight,
    Finset.sum_apply, Finset.mul_sum]
  apply sum_congr rfl
  intro lag hlag
  ring

/-- Exact captured variance of a finite normalized Wilder row. -/
theorem gaussianNormalizedWilderWeight_sq_sum_range
    (n count : ℕ)
    (hN : 1 ≤ n) :
    (∑ lag ∈ range count,
      (gaussianNormalizedWilderWeight n lag) ^ 2) =
      1 - (wilderDecay n) ^ (2 * count) := by
  have hNReal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hN
  have hFactorNonnegative : 0 ≤ 2 * (n : ℝ) - 1 := by
    linarith
  have hFactorNe : 2 * (n : ℝ) - 1 ≠ 0 := by
    linarith
  simp_rw [gaussianNormalizedWilderWeight, mul_pow]
  rw [← Finset.mul_sum, Real.sq_sqrt hFactorNonnegative,
    wilderWeight_sq_sum_range n count hN]
  field_simp

section GaussianWilderLaw

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exact finite-row law. Its variance is one minus the omitted geometric
tail energy. -/
theorem finiteGaussianWilderRow_hasLaw
    (n count : ℕ)
    (innovation : ℕ → Ω → ℝ)
    (hN : 1 ≤ n)
    (hIndependent : iIndepFun innovation μ)
    (hGaussian : ∀ lag, HasLaw (innovation lag) (gaussianReal 0 1) μ) :
    HasLaw (finiteGaussianWilderRow n count innovation)
      (gaussianReal 0
        (1 - (wilderDecay n) ^ (2 * count)).toNNReal) μ := by
  have hLaw := finiteWeightedSmoother_hasLaw_gaussianReal
    (gaussianNormalizedWilderWeight n) innovation count
    hIndependent hGaussian
  rw [gaussianNormalizedWilderWeight_sq_sum_range n count hN] at hLaw
  exact hLaw

end GaussianWilderLaw

/-- Rowwise equality in distribution transports weak convergence. -/
theorem tendstoInDistribution_of_identDistrib_rows
    {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ℕ → Ω → ℝ}
    {Y : ℕ → Ω' → ℝ}
    {Z : Ω' → ℝ}
    (hXY : ∀ n, IdentDistrib (X n) (Y n) μ μ')
    (hY : TendstoInDistribution Y atTop Z (fun _ ↦ μ') μ') :
    TendstoInDistribution X atTop Z (fun _ ↦ μ) μ' := by
  refine
    { forall_aemeasurable := fun n ↦ (hXY n).aemeasurable_fst
      aemeasurable_limit := hY.aemeasurable_limit
      tendsto := ?_ }
  apply hY.tendsto.congr'
  filter_upwards with n
  exact Subtype.ext (hXY n).map_eq.symm

/-- Variance of a finite Gaussian-normalized Wilder row. -/
def finiteGaussianWilderRowVariance (n count : ℕ) : ℝ :=
  1 - (wilderDecay n) ^ (2 * count)

theorem finiteGaussianWilderRowVariance_nonnegative
    (n count : ℕ)
    (hN : 1 ≤ n) :
    0 ≤ finiteGaussianWilderRowVariance n count := by
  have hDecayNonnegative := wilderDecay_nonnegative n hN
  have hDecayLeOne := le_of_lt (wilderDecay_lt_one n
    (lt_of_lt_of_le Nat.zero_lt_one hN))
  have hPowLeOne : (wilderDecay n) ^ (2 * count) ≤ 1 :=
    pow_le_one₀ hDecayNonnegative hDecayLeOne
  exact sub_nonneg.mpr hPowLeOne

section GaussianCLT

variable
    {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- Exact-Gaussian triangular-array limit. If the omitted tail energy tends to
zero, the normalized finite Wilder row converges in distribution to a standard
Gaussian. Unlike the non-Gaussian CLT, every row already has an exact Gaussian
law. -/
theorem finiteGaussianWilderRow_clt
    (innovation : ℕ → Ω → ℝ)
    (count : ℕ → ℕ)
    (Y : Ω' → ℝ)
    (hIndependent : iIndepFun innovation μ)
    (hGaussian : ∀ lag, HasLaw (innovation lag) (gaussianReal 0 1) μ)
    (hY : HasLaw Y (gaussianReal 0 1) μ')
    (hTail : Tendsto
      (fun n : ℕ ↦
        (wilderDecay (n + 1)) ^ (2 * count n))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ↦ finiteGaussianWilderRow (n + 1) (count n) innovation)
      atTop Y (fun _ ↦ μ) μ' := by
  let rowVariance : ℕ → ℝ :=
    fun n ↦ finiteGaussianWilderRowVariance (n + 1) (count n)
  have hRowVarianceNonnegative : ∀ n, 0 ≤ rowVariance n := by
    intro n
    exact finiteGaussianWilderRowVariance_nonnegative (n + 1) (count n)
      (by omega)
  have hRowVariance : Tendsto rowVariance atTop (𝓝 1) := by
    simpa only [rowVariance, finiteGaussianWilderRowVariance,
      sub_zero] using tendsto_const_nhds.sub hTail
  have hRowStdDev :
      Tendsto (fun n ↦ Real.sqrt (rowVariance n)) atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hRowVariance
    simpa only [Function.comp_def, Real.sqrt_one] using h
  let comparison : ℕ → Ω' → ℝ :=
    fun n ω ↦ Real.sqrt (rowVariance n) * Y ω
  have hComparison :
      TendstoInDistribution comparison atTop Y (fun _ ↦ μ') μ' := by
    apply tendstoInDistribution_of_ae_tendsto
    · intro n
      exact hY.aemeasurable.const_mul _
    · exact hY.aemeasurable
    · filter_upwards with ω
      have hω := hRowStdDev.mul_const (Y ω)
      simpa only [comparison, one_mul] using hω
  have hIdentDistrib : ∀ n,
      IdentDistrib
        (finiteGaussianWilderRow (n + 1) (count n) innovation)
        (comparison n) μ μ' := by
    intro n
    have hRowLaw :
        HasLaw (finiteGaussianWilderRow (n + 1) (count n) innovation)
          (gaussianReal 0 (rowVariance n).toNNReal) μ := by
      simpa only [rowVariance, finiteGaussianWilderRowVariance] using
        finiteGaussianWilderRow_hasLaw (n + 1) (count n) innovation
          (by omega) hIndependent hGaussian
    have hComparisonLawRaw :=
      gaussianReal_const_mul hY (Real.sqrt (rowVariance n))
    have hVarianceNN :
        NNReal.mk (Real.sqrt (rowVariance n) ^ 2) (sq_nonneg _) * 1 =
          (rowVariance n).toNNReal := by
      apply NNReal.eq
      simp only [NNReal.coe_mk, mul_one,
        Real.sq_sqrt (hRowVarianceNonnegative n),
        Real.coe_toNNReal _ (hRowVarianceNonnegative n)]
    have hComparisonLaw :
        HasLaw (comparison n)
          (gaussianReal 0 (rowVariance n).toNNReal) μ' := by
      simpa only [comparison, mul_zero, hVarianceNN] using hComparisonLawRaw
    exact hRowLaw.identDistrib hComparisonLaw
  exact tendstoInDistribution_of_identDistrib_rows hIdentDistrib hComparison

end GaussianCLT

end
end EndpointCoordinate
