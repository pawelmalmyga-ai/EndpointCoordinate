import EndpointCoordinate.TriangularArray
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

set_option linter.style.header false

/-!
# Endpoint coordinate: Student-t calibration layer

This module formalizes the deterministic and moment-algebra part of the
Student-t extension of the endpoint-coordinate paper.

For a variance-one Student-t innovation with `nu > 3`, put

`R = |epsilon| / E|epsilon|`, `m2 = E[R^2]`, `m3 = E[R^3]`.

The standard Student moment formula gives

`C_nu^2 = 2 m2`

and

`m3 / m2 = 2 (nu - 2) / (nu - 3)`.

Substitution in the universal first-shift formula yields

`K_nu = (5/4) C_nu^2 - 7/3 - 8/(3(nu-3))`.

The file proves that algebra exactly, derives the Gamma-function expression
for `C_nu^2`, checks the special values `nu = 4, 5, 6, 8`, proves that the
`n - 1` calibration is bracketed between `nu = 5` and `nu = 6`, and records
the admissible parameter region used by the polynomial-tail localization
argument.

Mathlib currently has no named Student-t probability measure.  Accordingly,
the probabilistic law is represented below by an explicit moment-profile
interface.  This module does not claim the shrinking-cutoff localization
theorem or the finite-variance triangular-array CLT; those are separate
modules.  There are no proof placeholders in this file.
-/

namespace EndpointCoordinate

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-! ## Gamma values used by the audit points -/

theorem Gamma_three_halves :
    Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  rw [Real.Gamma_one_half_eq] at h
  norm_num at h ⊢
  simpa [div_eq_mul_inv, mul_comm] using h

theorem Gamma_five_halves :
    Real.Gamma (5 / 2 : ℝ) = 3 * Real.sqrt Real.pi / 4 := by
  have h := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
  rw [Gamma_three_halves] at h
  norm_num at h ⊢
  linarith

theorem Gamma_seven_halves :
    Real.Gamma (7 / 2 : ℝ) = 15 * Real.sqrt Real.pi / 8 := by
  have h := Real.Gamma_add_one (s := (5 / 2 : ℝ)) (by norm_num)
  rw [Gamma_five_halves] at h
  norm_num at h ⊢
  linarith

theorem Gamma_two : Real.Gamma (2 : ℝ) = 1 := by
  norm_num

theorem Gamma_three : Real.Gamma (3 : ℝ) = 2 := by
  norm_num [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]

theorem Gamma_four : Real.Gamma (4 : ℝ) = 6 := by
  norm_num [show (4 : ℝ) = (3 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]

/-! ## Unit-variance Student first absolute moment and scale -/

/-- First absolute moment of a variance-normalized Student-t variable.

For `nu > 2`, rescaling a raw Student-t variable to variance one gives

`E|epsilon| = sqrt(nu-2) Gamma((nu-1)/2) /
  (sqrt(pi) Gamma(nu/2))`.
-/
def studentFirstAbsoluteMoment (nu : ℝ) : ℝ :=
  Real.sqrt (nu - 2) * Real.Gamma ((nu - 1) / 2) /
    (Real.sqrt Real.pi * Real.Gamma (nu / 2))

/-- Squared first-order log-odds scale for variance-one Student-t input. -/
def studentFirstOrderScaleSq (nu : ℝ) : ℝ :=
  (2 * Real.pi / (nu - 2)) *
    (Real.Gamma (nu / 2) / Real.Gamma ((nu - 1) / 2)) ^ 2

/-- Positive square-root version of the Student first-order scale. -/
def studentFirstOrderScale (nu : ℝ) : ℝ :=
  Real.sqrt (studentFirstOrderScaleSq nu)

theorem studentFirstAbsoluteMoment_pos
    {nu : ℝ} (hNu : 2 < nu) :
    0 < studentFirstAbsoluteMoment nu := by
  unfold studentFirstAbsoluteMoment
  have hNuTwo : 0 < nu - 2 := by linarith
  have hNuHalf : 0 < nu / 2 := by linarith
  have hNuMinusHalf : 0 < (nu - 1) / 2 := by linarith
  positivity

theorem studentFirstOrderScaleSq_pos
    {nu : ℝ} (hNu : 2 < nu) :
    0 < studentFirstOrderScaleSq nu := by
  unfold studentFirstOrderScaleSq
  have hNuTwo : 0 < nu - 2 := by linarith
  have hNumeratorGamma : 0 < Real.Gamma (nu / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hDenominatorGamma : 0 < Real.Gamma ((nu - 1) / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  positivity

theorem studentFirstOrderScaleSq_from_firstAbsoluteMoment
    {nu : ℝ} (hNu : 2 < nu) :
    firstOrderScaleSq 1 (studentFirstAbsoluteMoment nu) =
      studentFirstOrderScaleSq nu := by
  have hNuTwo : 0 < nu - 2 := by linarith
  have hPiSqrtNe : Real.sqrt Real.pi ≠ 0 := by positivity
  have hGammaNumeratorNe : Real.Gamma (nu / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGammaDenominatorNe : Real.Gamma ((nu - 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [firstOrderScaleSq, studentFirstAbsoluteMoment,
    studentFirstOrderScaleSq]
  simp only [div_pow, mul_pow, Real.sq_sqrt hNuTwo.le,
    Real.sq_sqrt Real.pi_pos.le]
  field_simp

theorem studentFirstOrderScale_eq_general
    {nu : ℝ} (hNu : 2 < nu) :
    firstOrderScale 1 (studentFirstAbsoluteMoment nu) =
      studentFirstOrderScale nu := by
  rw [firstOrderScale, studentFirstOrderScale,
    studentFirstOrderScaleSq_from_firstAbsoluteMoment hNu]

/-! ## Scale-free radial moments -/

/-- `m2 = E[R^2]` for `R = |epsilon| / E|epsilon|`. -/
def studentRadialSecondMoment (nu : ℝ) : ℝ :=
  studentFirstOrderScaleSq nu / 2

/-- `m3 = E[R^3]` for `R = |epsilon| / E|epsilon|`.

The definition uses the exact Student identity
`m3 / m2 = 2 (nu - 2) / (nu - 3)`.
-/
def studentRadialThirdMoment (nu : ℝ) : ℝ :=
  studentFirstOrderScaleSq nu * (nu - 2) / (nu - 3)

theorem studentRadialMoment_ratio
    {nu : ℝ} (hNu : 3 < nu) :
    studentRadialThirdMoment nu / studentRadialSecondMoment nu =
      2 * (nu - 2) / (nu - 3) := by
  have hScale : studentFirstOrderScaleSq nu ≠ 0 :=
    (studentFirstOrderScaleSq_pos (by linarith)).ne'
  have hNuThree : nu - 3 ≠ 0 := by linarith
  rw [studentRadialThirdMoment, studentRadialSecondMoment]
  field_simp

/-- Third absolute moment of a unit-variance Student-t variable, expressed
through its first absolute moment. -/
def studentThirdAbsoluteMoment (nu : ℝ) : ℝ :=
  studentFirstAbsoluteMoment nu * (2 * (nu - 2) / (nu - 3))

/-! ## Moment-profile interface for the probabilistic layer -/

/-- The moment facts about a centered, variance-one Student-t innovation that
are needed by the first-shift theorem.

This is deliberately an interface rather than a construction of the Student
measure.  A later density module may discharge it from the Student density;
the heavy-tail proof may use it immediately without hiding assumptions.
-/
structure HasUnitVarianceStudentMomentProfile
    {Omega : Type*} [MeasurableSpace Omega]
    (X : Omega → ℝ) (mu : Measure Omega) (nu : ℝ) : Prop where
  nu_gt_three : 3 < nu
  aemeasurable : AEMeasurable X mu
  memLp_three : MemLp X 3 mu
  mean_eq_zero : ∫ omega, X omega ∂mu = 0
  variance_eq_one : variance X mu = 1
  first_abs_moment :
    ∫ omega, |X omega| ∂mu = studentFirstAbsoluteMoment nu
  third_abs_moment :
    ∫ omega, |X omega| ^ 3 ∂mu = studentThirdAbsoluteMoment nu

theorem HasUnitVarianceStudentMomentProfile.nu_gt_two
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega → ℝ} {mu : Measure Omega} {nu : ℝ}
    (hX : HasUnitVarianceStudentMomentProfile X mu nu) :
    2 < nu := by
  linarith [hX.nu_gt_three]

theorem HasUnitVarianceStudentMomentProfile.firstOrderScaleSq_eq
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega → ℝ} {mu : Measure Omega} {nu : ℝ}
    (hX : HasUnitVarianceStudentMomentProfile X mu nu) :
    firstOrderScaleSq 1 (studentFirstAbsoluteMoment nu) =
      studentFirstOrderScaleSq nu :=
  studentFirstOrderScaleSq_from_firstAbsoluteMoment hX.nu_gt_two

/-! ## Exact derivation of the Student first variance shift -/

theorem student_firstVarianceShift_from_radial_moments
    {nu : ℝ} (hNu : 3 < nu) :
    firstVarianceShift
        (studentRadialSecondMoment nu)
        (studentRadialThirdMoment nu) =
      studentFirstVarianceShift nu (studentFirstOrderScaleSq nu) := by
  have hScale : studentFirstOrderScaleSq nu ≠ 0 :=
    (studentFirstOrderScaleSq_pos (by linarith)).ne'
  have hNuThree : nu - 3 ≠ 0 := by linarith
  rw [firstVarianceShift_eq]
  · simp only [studentRadialSecondMoment, studentRadialThirdMoment,
      studentFirstVarianceShift]
    field_simp
    ring
  · exact div_ne_zero hScale (by norm_num)

theorem student_secondVarianceCoefficient_eq
    {nu : ℝ} (hNu : 3 < nu) :
    secondVarianceCoefficient
        (studentRadialSecondMoment nu)
        (studentRadialThirdMoment nu) =
      studentFirstOrderScaleSq nu *
        studentFirstVarianceShift nu (studentFirstOrderScaleSq nu) := by
  have hScale : studentFirstOrderScaleSq nu ≠ 0 :=
    (studentFirstOrderScaleSq_pos (by linarith)).ne'
  have hNuThree : nu - 3 ≠ 0 := by linarith
  simp only [secondVarianceCoefficient, studentRadialSecondMoment,
    studentRadialThirdMoment, studentFirstVarianceShift]
  field_simp
  ring

/-! ## Audited special values -/

theorem studentFirstOrderScaleSq_four :
    studentFirstOrderScaleSq 4 = 4 := by
  rw [studentFirstOrderScaleSq]
  norm_num [Gamma_two, Gamma_three_halves]
  simp only [div_pow, Real.sq_sqrt Real.pi_pos.le]
  field_simp
  norm_num

theorem studentFirstOrderScale_four :
    studentFirstOrderScale 4 = 2 := by
  rw [studentFirstOrderScale, studentFirstOrderScaleSq_four]
  norm_num

theorem studentFirstOrderScaleSq_five :
    studentFirstOrderScaleSq 5 = 3 * Real.pi ^ 2 / 8 := by
  rw [studentFirstOrderScaleSq]
  norm_num [Gamma_five_halves, Gamma_two]
  have hSqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  nlinarith

theorem studentFirstOrderScaleSq_six :
    studentFirstOrderScaleSq 6 = 32 / 9 := by
  rw [studentFirstOrderScaleSq]
  norm_num [Gamma_three, Gamma_five_halves]
  have hSqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  field_simp
  nlinarith

theorem studentFirstOrderScaleSq_eight :
    studentFirstOrderScaleSq 8 = 256 / 75 := by
  rw [studentFirstOrderScaleSq]
  norm_num [Gamma_four, Gamma_seven_halves]
  have hSqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  field_simp
  nlinarith

theorem studentFirstVarianceShift_four_exact :
    studentFirstVarianceShift 4 (studentFirstOrderScaleSq 4) = 0 := by
  rw [studentFirstOrderScaleSq_four]
  exact studentFirstVarianceShift_four

theorem studentFirstVarianceShift_five_exact :
    studentFirstVarianceShift 5 (studentFirstOrderScaleSq 5) =
      15 * Real.pi ^ 2 / 32 - 11 / 3 := by
  rw [studentFirstOrderScaleSq_five]
  simp only [studentFirstVarianceShift]
  ring

theorem studentFirstVarianceShift_six_exact :
    studentFirstVarianceShift 6 (studentFirstOrderScaleSq 6) = 11 / 9 := by
  rw [studentFirstOrderScaleSq_six]
  exact studentFirstVarianceShift_six

theorem studentFirstVarianceShift_eight_exact :
    studentFirstVarianceShift 8 (studentFirstOrderScaleSq 8) = 7 / 5 := by
  rw [studentFirstOrderScaleSq_eight]
  norm_num [studentFirstVarianceShift]

/-! ## The `n - 1` calibration is bracketed between nu = 5 and nu = 6 -/

theorem studentFirstVarianceShift_five_lt_one :
    studentFirstVarianceShift 5 (studentFirstOrderScaleSq 5) < 1 := by
  rw [studentFirstVarianceShift_five_exact]
  have hPiUpper : Real.pi < 3.15 := Real.pi_lt_d2
  have hPiPos : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem one_lt_studentFirstVarianceShift_six :
    1 < studentFirstVarianceShift 6 (studentFirstOrderScaleSq 6) := by
  rw [studentFirstVarianceShift_six_exact]
  norm_num

/-! ## Admissible parameters for the polynomial-tail localization -/

/-- Parameter constraints from the shrinking-big-jump-cutoff proof.

The moment order is `p = 3 + delta`.  The chosen `q` controls the logarithmic
lower tail and `gamma` is the shrinking-cutoff exponent.
-/
def StudentLocalizationAdmissible
    (nu delta q gamma : ℝ) : Prop :=
  0 < delta ∧
    3 + delta < nu ∧
    2 * (2 + delta) / delta < q ∧
    0 < gamma ∧
    gamma < delta / (3 + delta) ∧
    gamma < (2 + delta - 2 * q / (q - 2)) / (3 + delta)

theorem student_q_gt_two
    {delta q : ℝ}
    (hDelta : 0 < delta)
    (hQ : 2 * (2 + delta) / delta < q) :
    2 < q := by
  have hThreshold : 2 < 2 * (2 + delta) / delta := by
    rw [lt_div_iff₀ hDelta]
    nlinarith
  linarith

theorem student_second_gamma_cap_pos
    {delta q : ℝ}
    (hDelta : 0 < delta)
    (hQ : 2 * (2 + delta) / delta < q) :
    0 < (2 + delta - 2 * q / (q - 2)) / (3 + delta) := by
  have hQTwo : 0 < q - 2 := by
    linarith [student_q_gt_two hDelta hQ]
  have hDen : 0 < 3 + delta := by linarith
  rw [div_pos_iff]
  left
  constructor
  · rw [sub_pos, div_lt_iff₀ hQTwo]
    have hScaled := (div_lt_iff₀ hDelta).1 hQ
    nlinarith
  · exact hDen

theorem exists_student_localization_gamma
    {delta q : ℝ}
    (hDelta : 0 < delta)
    (hQ : 2 * (2 + delta) / delta < q) :
    ∃ gamma : ℝ,
      0 < gamma ∧
        gamma < delta / (3 + delta) ∧
        gamma < (2 + delta - 2 * q / (q - 2)) / (3 + delta) := by
  let a := delta / (3 + delta)
  let b := (2 + delta - 2 * q / (q - 2)) / (3 + delta)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    exact student_second_gamma_cap_pos hDelta hQ
  refine ⟨min a b / 2, ?_, ?_, ?_⟩
  · positivity
  · have hMin : min a b ≤ a := min_le_left _ _
    have hMinPos : 0 < min a b := lt_min ha hb
    linarith
  · have hMin : min a b ≤ b := min_le_right _ _
    have hMinPos : 0 < min a b := lt_min ha hb
    linarith

theorem exists_StudentLocalizationAdmissible
    {nu : ℝ} (hNu : 3 < nu) :
    ∃ delta q gamma : ℝ,
      StudentLocalizationAdmissible nu delta q gamma := by
  let delta := (nu - 3) / 2
  have hDelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hMoment : 3 + delta < nu := by
    dsimp [delta]
    linarith
  let q := 2 * (2 + delta) / delta + 1
  have hQ : 2 * (2 + delta) / delta < q := by
    dsimp [q]
    linarith
  obtain ⟨gamma, hGammaPos, hGammaOne, hGammaTwo⟩ :=
    exists_student_localization_gamma hDelta hQ
  refine ⟨delta, q, gamma, ?_⟩
  exact ⟨hDelta, hMoment, hQ, hGammaPos, hGammaOne, hGammaTwo⟩

/-! ## Gaussian endpoint, conditional only on the Gamma-ratio scale limit -/

/-- Once `C_nu^2 -> pi` is supplied by the standard Gamma-ratio asymptotic,
the Student first shift converges to the Gaussian first shift.  The separation
keeps the dependency explicit. -/
theorem studentFirstVarianceShift_tendsto_gaussian_of_scale
    (scaleSq : ℝ → ℝ)
    (hScale : Tendsto scaleSq atTop (nhds Real.pi)) :
    Tendsto
      (fun nu : ℝ ↦ studentFirstVarianceShift nu (scaleSq nu))
      atTop (nhds gaussianLimitVarianceShift) := by
  have hNuMinusThree : Tendsto (fun nu : ℝ ↦ nu - 3) atTop atTop :=
    by
      simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-3 : ℝ) tendsto_id)
  have hPole : Tendsto (fun nu : ℝ ↦ 1 / (nu - 3)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp hNuMinusThree
  have hScaled : Tendsto (fun nu ↦ (5 / 4) * scaleSq nu)
      atTop (nhds ((5 / 4) * Real.pi)) := by
    simpa using hScale.const_mul (5 / 4)
  have hPoleScaled : Tendsto (fun nu : ℝ ↦ (8 / 3) * (1 / (nu - 3)))
      atTop (nhds 0) := by
    simpa using hPole.const_mul (8 / 3)
  have hConst : Tendsto (fun _ : ℝ ↦ (7 / 3 : ℝ))
      atTop (nhds (7 / 3 : ℝ)) := tendsto_const_nhds
  have hCombined : Tendsto
      (fun nu : ℝ ↦
        (5 / 4) * scaleSq nu - 7 / 3 - (8 / 3) * (1 / (nu - 3)))
      atTop (nhds ((5 / 4) * Real.pi - 7 / 3 - 0)) :=
    (hScaled.sub hConst).sub hPoleScaled
  convert hCombined using 1
  · funext nu
    simp only [studentFirstVarianceShift]
    by_cases hNu : nu = 3
    · subst nu
      norm_num
    · field_simp
  · simp only [gaussianLimitVarianceShift]
    ring_nf

/-! ## Paper-facing bundle -/

theorem student_calibration_audit :
    studentFirstOrderScaleSq 4 = 4 ∧
      studentFirstVarianceShift 4 (studentFirstOrderScaleSq 4) = 0 ∧
      studentFirstOrderScaleSq 6 = 32 / 9 ∧
      studentFirstVarianceShift 6 (studentFirstOrderScaleSq 6) = 11 / 9 ∧
      studentFirstOrderScaleSq 8 = 256 / 75 ∧
      studentFirstVarianceShift 8 (studentFirstOrderScaleSq 8) = 7 / 5 := by
  exact ⟨studentFirstOrderScaleSq_four,
    studentFirstVarianceShift_four_exact,
    studentFirstOrderScaleSq_six,
    studentFirstVarianceShift_six_exact,
    studentFirstOrderScaleSq_eight,
    studentFirstVarianceShift_eight_exact⟩

end
end EndpointCoordinate
