import EndpointCoordinate.Asymptotics

set_option linter.style.header false

/-!
# Endpoint coordinate: central-limit transfer through log-odds

This module formalizes the probabilistic delta step of the paper.  It is
deliberately separated from a particular central limit theorem for the input
process.

Suppose that a bounded endpoint coordinate `Fₙ` satisfies

* `Fₙ → 0` in probability, and
* `aₙ Fₙ ⟶ᵈ Z`.

Then the exact factorization

`logOdds Fₙ = Fₙ * logOddsSlope Fₙ`

and continuity of the removable slope at zero imply

`aₙ logOdds(Fₙ) ⟶ᵈ 2 Z`.

Equivalently, the half-normalized log-odds coordinate

`(aₙ / 2) logOdds(Fₙ)`

has exactly the same weak limit `Z` as `aₙ Fₙ`.  This is the rigorous reason
for the factor `2` in the first-order scale.  Gaussianity, Laplace tails, and
Student tails play no role in this transfer theorem; they enter only through
the premise that identifies the weak limit of the bounded coordinate.
-/

namespace EndpointCoordinate

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-! ## Measurability of the nonlinear coordinate maps -/

/-- The log-odds map is Borel measurable on the whole real line. -/
theorem measurable_logOdds : Measurable logOdds := by
  unfold logOdds oddsRatio
  fun_prop

/-- The removable extension `logOddsSlope` is Borel measurable. -/
theorem measurable_logOddsSlope : Measurable logOddsSlope := by
  unfold logOddsSlope
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_logOdds.div measurable_id)

/-! ## Continuous mapping in probability at the equilibrium point -/

/--
If `Fₙ → 0` in probability, then the removable slope
`logOddsSlope(Fₙ) → 2` in probability.

The proof uses the subsequence characterization of convergence in measure:
every subsequence has an almost-everywhere convergent subsubsequence, and
continuity of `logOddsSlope` at zero transfers that pointwise limit.
-/
theorem tendstoInMeasure_logOddsSlope
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : ℕ → Ω → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_zero : TendstoInMeasure μ F atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ
      (fun n ω ↦ logOddsSlope (F n ω)) atTop (fun _ ↦ 2) := by
  have hSlope_meas :
      ∀ n, AEStronglyMeasurable (fun ω ↦ logOddsSlope (F n ω)) μ := by
    intro n
    exact
      (measurable_logOddsSlope.comp_aemeasurable
        (hF_meas n).aemeasurable).aestronglyMeasurable
  refine (exists_seq_tendstoInMeasure_atTop_iff hSlope_meas).2 ?_
  intro ns hns
  have hSubsequence :
      TendstoInMeasure μ (fun n ↦ F (ns n)) atTop (fun _ ↦ 0) := by
    exact hF_zero.comp hns.tendsto_atTop
  obtain ⟨ns', hns', hAE⟩ := hSubsequence.exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hAE] with ω hω
  have hContinuous := continuousAt_logOddsSlope_zero.tendsto
  simpa only [Function.comp_def, logOddsSlope_zero] using
    hContinuous.comp hω

/-! ## Slutsky transfer to the log-odds coordinate -/

variable
    {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/--
Probabilistic delta theorem for log-odds.

Any weak limit theorem for the scaled bounded coordinate `aₙ Fₙ` transfers
to the scaled log-odds coordinate, with the forced multiplicative factor `2`.
-/
theorem logOdds_clt_transfer
    {F : ℕ → Ω → ℝ}
    {a : ℕ → ℝ}
    {Z : Ω' → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_zero : TendstoInMeasure μ F atTop (fun _ ↦ 0))
    (hCLT : TendstoInDistribution
      (fun n ω ↦ a n * F n ω) atTop Z (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun n ω ↦ a n * logOdds (F n ω)) atTop
      (fun ω ↦ 2 * Z ω) (fun _ ↦ μ) μ' := by
  have hSlope := tendstoInMeasure_logOddsSlope hF_meas hF_zero
  have hSlope_meas :
      ∀ n, AEMeasurable (fun ω ↦ logOddsSlope (F n ω)) μ := by
    intro n
    exact measurable_logOddsSlope.comp_aemeasurable
      (hF_meas n).aemeasurable
  have hProduct :
      TendstoInDistribution
        (fun n ω ↦ (a n * F n ω) * logOddsSlope (F n ω)) atTop
        (fun ω ↦ Z ω * 2) (fun _ ↦ μ) μ' := by
    exact hCLT.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ ↦ p.1 * p.2) (by fun_prop)
      hSlope hSlope_meas
  apply TendstoInDistribution.congr
    (X := fun n ω ↦ (a n * F n ω) * logOddsSlope (F n ω))
    (Z := fun ω ↦ Z ω * 2)
  · intro n
    filter_upwards with ω
    rw [logOdds_eq_mul_logOddsSlope]
    ring
  · filter_upwards with ω
    ring
  · exact hProduct

/--
Normalized form of the delta theorem.  Dividing the log-odds normalization by
two cancels the derivative at equilibrium, so the limiting random variable is
exactly the same `Z` as for the bounded coordinate.
-/
theorem half_scaled_logOdds_clt_transfer
    {F : ℕ → Ω → ℝ}
    {a : ℕ → ℝ}
    {Z : Ω' → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_zero : TendstoInMeasure μ F atTop (fun _ ↦ 0))
    (hCLT : TendstoInDistribution
      (fun n ω ↦ a n * F n ω) atTop Z (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun n ω ↦ (a n / 2) * logOdds (F n ω)) atTop
      Z (fun _ ↦ μ) μ' := by
  have hRaw := logOdds_clt_transfer hF_meas hF_zero hCLT
  have hHalf := hRaw.continuous_comp
    (g := fun x : ℝ ↦ x / 2) (by fun_prop)
  apply TendstoInDistribution.congr
    (X := fun n ↦ (fun x : ℝ ↦ x / 2) ∘
      (fun ω ↦ a n * logOdds (F n ω)))
    (Z := (fun x : ℝ ↦ x / 2) ∘ (fun ω ↦ 2 * Z ω))
  · intro n
    filter_upwards with ω
    simp only [Function.comp_apply]
    ring
  · filter_upwards with ω
    simp only [Function.comp_apply]
    ring
  · exact hHalf

/-! ## Paper-facing square-root specializations -/

/-- CLT transfer with the conventional `sqrt n` normalization. -/
theorem sqrt_logOdds_clt_transfer
    {F : ℕ → Ω → ℝ}
    {Z : Ω' → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_zero : TendstoInMeasure μ F atTop (fun _ ↦ 0))
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (n : ℝ) * F n ω)
      atTop Z (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (n : ℝ) * logOdds (F n ω)) atTop
      (fun ω ↦ 2 * Z ω) (fun _ ↦ μ) μ' :=
  logOdds_clt_transfer hF_meas hF_zero hCLT

/--
Unit-limit form for the conventional normalization: if `sqrt n * Fₙ`
converges to `Z`, then `(sqrt n / 2) * logOdds(Fₙ)` converges to the same `Z`.
-/
theorem sqrt_half_logOdds_clt_transfer
    {F : ℕ → Ω → ℝ}
    {Z : Ω' → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_zero : TendstoInMeasure μ F atTop (fun _ ↦ 0))
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (n : ℝ) * F n ω)
      atTop Z (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦
        (Real.sqrt (n : ℝ) / 2) * logOdds (F n ω)) atTop
      Z (fun _ ↦ μ) μ' :=
  half_scaled_logOdds_clt_transfer hF_meas hF_zero hCLT

/-- CLT transfer at the exact exponential-weight effective-length scale. -/
theorem effectiveLength_logOdds_clt_transfer
    {F : ℕ → Ω → ℝ}
    {Z : Ω' → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_zero : TendstoInMeasure μ F atTop (fun _ ↦ 0))
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (2 * (n : ℝ) - 1) * F n ω)
      atTop Z (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦
        Real.sqrt (2 * (n : ℝ) - 1) * logOdds (F n ω))
      atTop (fun ω ↦ 2 * Z ω) (fun _ ↦ μ) μ' :=
  logOdds_clt_transfer hF_meas hF_zero hCLT

/--
Same effective-length theorem with the derivative factor normalized away.
-/
theorem effectiveLength_half_logOdds_clt_transfer
    {F : ℕ → Ω → ℝ}
    {Z : Ω' → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF_zero : TendstoInMeasure μ F atTop (fun _ ↦ 0))
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (2 * (n : ℝ) - 1) * F n ω)
      atTop Z (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦
        (Real.sqrt (2 * (n : ℝ) - 1) / 2) * logOdds (F n ω))
      atTop Z (fun _ ↦ μ) μ' :=
  half_scaled_logOdds_clt_transfer hF_meas hF_zero hCLT

end

end EndpointCoordinate
