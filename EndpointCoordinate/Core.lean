import Mathlib
set_option linter.style.header false
/-!
# Exponentially weighted endpoint coordinate: exact core

This file formalizes the first distribution-free part of the paper.
There are no probabilistic assumptions and no use of `sorry`.

Notation used below:

* `alpha`          -- exponential gain
* `previousValue`  -- X_(t-1)
* `previousMean`   -- M_(t-1)
* `previousSigned` -- S_(t-1)
* `increment`      -- epsilon_t = X_t - X_(t-1)

The current value is therefore `previousValue + increment`.
-/

namespace EndpointCoordinate

noncomputable section

/-- One step of the matched exponential mean. -/
def emaStep (alpha previousMean currentValue : ℝ) : ℝ :=
  (1 - alpha) * previousMean + alpha * currentValue

/-- One step of the exponentially weighted signed increment. -/
def signedStep (alpha previousSigned increment : ℝ) : ℝ :=
  (1 - alpha) * previousSigned + alpha * increment

/-- One step of exponentially weighted absolute movement. -/
def activityStep (alpha previousActivity increment : ℝ) : ℝ :=
  (1 - alpha) * previousActivity + alpha * |increment|

/--
The exact endpoint identity is preserved by one matched recursion step.

If at time `t - 1`

`X_(t-1) - M_(t-1) = ((1 - alpha) / alpha) * S_(t-1)`,

then at time `t`

`X_t - M_t = ((1 - alpha) / alpha) * S_t`.
-/
theorem matched_endpoint_identity
    (alpha previousValue previousMean previousSigned increment : ℝ)
    (hAlpha : alpha ≠ 0)
    (hPrevious :
      previousValue - previousMean =
        ((1 - alpha) / alpha) * previousSigned) :
    (previousValue + increment) -
        emaStep alpha previousMean (previousValue + increment) =
      ((1 - alpha) / alpha) *
        signedStep alpha previousSigned increment := by
  calc
    (previousValue + increment) -
          emaStep alpha previousMean (previousValue + increment) =
        (1 - alpha) *
          (previousValue - previousMean + increment) := by
            simp only [emaStep]
            ring
    _ = (1 - alpha) *
          (((1 - alpha) / alpha) * previousSigned + increment) := by
            rw [hPrevious]
    _ = ((1 - alpha) / alpha) *
          signedStep alpha previousSigned increment := by
            simp only [signedStep]
            field_simp [hAlpha]

/--
The domination `|S| ≤ A` is preserved by one matched recursion step.
-/
theorem signedStep_abs_le_activityStep
    (alpha previousSigned previousActivity increment : ℝ)
    (hAlphaNonnegative : 0 ≤ alpha)
    (hAlphaAtMostOne : alpha ≤ 1)
    (hPrevious : |previousSigned| ≤ previousActivity) :
    |signedStep alpha previousSigned increment| ≤
      activityStep alpha previousActivity increment := by
  have hDecayNonnegative : 0 ≤ 1 - alpha :=
    sub_nonneg.mpr hAlphaAtMostOne
  calc
    |signedStep alpha previousSigned increment| =
        |(1 - alpha) * previousSigned + alpha * increment| := by
          rfl
    _ ≤ |(1 - alpha) * previousSigned| + |alpha * increment| :=
      abs_add_le _ _
    _ = (1 - alpha) * |previousSigned| + alpha * |increment| := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg hDecayNonnegative,
        abs_of_nonneg hAlphaNonnegative]
    _ ≤ (1 - alpha) * previousActivity + alpha * |increment| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hPrevious hDecayNonnegative)
        (le_refl (alpha * |increment|))
    _ = activityStep alpha previousActivity increment := by
      rfl

/-! ## Finite paths and induction -/

/-- Complete state of the matched exponential construction. -/
structure EWState where
  value : ℝ
  mean : ℝ
  signed : ℝ
  activity : ℝ

/-- Natural zero-movement initialization at level `x0`. -/
def initialState (x0 : ℝ) : EWState where
  value := x0
  mean := x0
  signed := 0
  activity := 0

/-- Advance every matched component using the same gain and increment. -/
def stateStep (alpha : ℝ) (state : EWState) (increment : ℝ) : EWState where
  value := state.value + increment
  mean := emaStep alpha state.mean (state.value + increment)
  signed := signedStep alpha state.signed increment
  activity := activityStep alpha state.activity increment

/-- The exact endpoint relation, expressed as a state invariant. -/
def EndpointInvariant (alpha : ℝ) (state : EWState) : Prop :=
  state.value - state.mean =
    ((1 - alpha) / alpha) * state.signed

/-- Signed movement never exceeds absolute movement. -/
def DominanceInvariant (state : EWState) : Prop :=
  |state.signed| ≤ state.activity

theorem initial_endpointInvariant (alpha x0 : ℝ) :
    EndpointInvariant alpha (initialState x0) := by
  simp [EndpointInvariant, initialState]

theorem initial_dominanceInvariant (x0 : ℝ) :
    DominanceInvariant (initialState x0) := by
  simp [DominanceInvariant, initialState]

theorem endpointInvariant_stateStep
    (alpha : ℝ)
    (state : EWState)
    (increment : ℝ)
    (hAlpha : alpha ≠ 0)
    (hInvariant : EndpointInvariant alpha state) :
    EndpointInvariant alpha (stateStep alpha state increment) := by
  change
    (state.value + increment) -
        emaStep alpha state.mean (state.value + increment) =
      ((1 - alpha) / alpha) *
        signedStep alpha state.signed increment
  exact matched_endpoint_identity
    alpha state.value state.mean state.signed increment hAlpha hInvariant

theorem dominanceInvariant_stateStep
    (alpha : ℝ)
    (state : EWState)
    (increment : ℝ)
    (hAlphaNonnegative : 0 ≤ alpha)
    (hAlphaAtMostOne : alpha ≤ 1)
    (hInvariant : DominanceInvariant state) :
    DominanceInvariant (stateStep alpha state increment) := by
  change
    |signedStep alpha state.signed increment| ≤
      activityStep alpha state.activity increment
  exact signedStep_abs_le_activityStep
    alpha state.signed state.activity increment
    hAlphaNonnegative hAlphaAtMostOne hInvariant

/-- Run the matched recursion along a finite list of increments. -/
def run (alpha : ℝ) : EWState → List ℝ → EWState
  | state, [] => state
  | state, increment :: rest =>
      run alpha (stateStep alpha state increment) rest

theorem endpointInvariant_run
    (alpha : ℝ)
    (increments : List ℝ)
    (state : EWState)
    (hAlpha : alpha ≠ 0)
    (hInvariant : EndpointInvariant alpha state) :
    EndpointInvariant alpha (run alpha state increments) := by
  induction increments generalizing state with
  | nil =>
      simpa [run] using hInvariant
  | cons increment rest inductionHypothesis =>
      apply inductionHypothesis
      exact endpointInvariant_stateStep
        alpha state increment hAlpha hInvariant

theorem dominanceInvariant_run
    (alpha : ℝ)
    (increments : List ℝ)
    (state : EWState)
    (hAlphaNonnegative : 0 ≤ alpha)
    (hAlphaAtMostOne : alpha ≤ 1)
    (hInvariant : DominanceInvariant state) :
    DominanceInvariant (run alpha state increments) := by
  induction increments generalizing state with
  | nil =>
      simpa [run] using hInvariant
  | cons increment rest inductionHypothesis =>
      apply inductionHypothesis
      exact dominanceInvariant_stateStep
        alpha state increment
        hAlphaNonnegative hAlphaAtMostOne hInvariant

/-- The endpoint identity holds along every finite path from matched initialization. -/
theorem endpointInvariant_from_initial
    (alpha x0 : ℝ)
    (increments : List ℝ)
    (hAlpha : alpha ≠ 0) :
    EndpointInvariant alpha
      (run alpha (initialState x0) increments) := by
  exact endpointInvariant_run
    alpha increments (initialState x0) hAlpha
    (initial_endpointInvariant alpha x0)

/-- The domination `|S_t| ≤ A_t` holds along every finite path. -/
theorem dominanceInvariant_from_initial
    (alpha x0 : ℝ)
    (increments : List ℝ)
    (hAlphaNonnegative : 0 ≤ alpha)
    (hAlphaAtMostOne : alpha ≤ 1) :
    DominanceInvariant
      (run alpha (initialState x0) increments) := by
  exact dominanceInvariant_run
    alpha increments (initialState x0)
    hAlphaNonnegative hAlphaAtMostOne
    (initial_dominanceInvariant x0)

/--
Both exact geometric invariants hold for every finite path when `0 < alpha < 1`.
-/
theorem finite_path_geometry
    (alpha x0 : ℝ)
    (increments : List ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaBelowOne : alpha < 1) :
    EndpointInvariant alpha
        (run alpha (initialState x0) increments) ∧
      DominanceInvariant
        (run alpha (initialState x0) increments) := by
  constructor
  · exact endpointInvariant_from_initial
      alpha x0 increments (ne_of_gt hAlphaPositive)
  · exact dominanceInvariant_from_initial
      alpha x0 increments
      (le_of_lt hAlphaPositive) (le_of_lt hAlphaBelowOne)

/-- The first-order unit coordinate `F = S / A`. -/
def unitCoordinate (signed activity : ℝ) : ℝ :=
  signed / activity

/--
If absolute signed movement does not exceed total absolute movement,
then the unit coordinate lies in `[-1, 1]`.
-/
theorem unitCoordinate_abs_le_one
    (signed activity : ℝ)
    (hActivity : 0 < activity)
    (hSigned : |signed| ≤ activity) :
    |unitCoordinate signed activity| ≤ 1 := by
  simp only [unitCoordinate, abs_div, abs_of_pos hActivity]
  exact (div_le_one hActivity).2 hSigned

/--
Endpoint displacement in units of exponentially weighted absolute movement.
By the matched identity this equals `((1 - alpha) / alpha) * (S / A)`.
-/
def endpointCoordinate (alpha signed activity : ℝ) : ℝ :=
  ((1 - alpha) / alpha) * unitCoordinate signed activity

/--
For `0 < alpha < 1`, the endpoint coordinate has the deterministic bound

`|B| ≤ (1 - alpha) / alpha`.
-/
theorem endpointCoordinate_abs_bound
    (alpha signed activity : ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaBelowOne : alpha < 1)
    (hActivity : 0 < activity)
    (hSigned : |signed| ≤ activity) :
    |endpointCoordinate alpha signed activity| ≤
      (1 - alpha) / alpha := by
  have hScale : 0 ≤ (1 - alpha) / alpha := by
    exact div_nonneg
      (sub_nonneg.mpr (le_of_lt hAlphaBelowOne))
      (le_of_lt hAlphaPositive)
  have hUnit : |unitCoordinate signed activity| ≤ 1 :=
    unitCoordinate_abs_le_one signed activity hActivity hSigned
  calc
    |endpointCoordinate alpha signed activity| =
        ((1 - alpha) / alpha) *
          |unitCoordinate signed activity| := by
            simp [endpointCoordinate, abs_mul, abs_of_nonneg hScale]
    _ ≤ ((1 - alpha) / alpha) * 1 :=
      mul_le_mul_of_nonneg_left hUnit hScale
    _ = (1 - alpha) / alpha := by ring

/--
For Wilder's gain `alpha = 1 / n`, the endpoint bound is exactly `n - 1`.
-/
theorem wilder_scale
    (n : ℝ)
    (hN : n ≠ 0) :
    (1 - (1 / n)) / (1 / n) = n - 1 := by
  field_simp [hN]

/-! ## Direct displacement, Wilder specialization, and RSI -/

/-- The observable displacement from the matched exponential mean,
normalized by exponentially weighted absolute movement. -/
def displacementCoordinate (state : EWState) : ℝ :=
  (state.value - state.mean) / state.activity

/-- Under the exact endpoint invariant, the direct displacement coordinate
is the endpoint coordinate built from signed and absolute movement. -/
theorem displacementCoordinate_eq_endpointCoordinate
    (alpha : ℝ)
    (state : EWState)
    (hInvariant : EndpointInvariant alpha state) :
    displacementCoordinate state =
      endpointCoordinate alpha state.signed state.activity := by
  unfold displacementCoordinate endpointCoordinate unitCoordinate
  rw [hInvariant]
  ring

/--
For every finite path, the current observation cannot lie farther than
`(1 - alpha) / alpha` activity units from its matched exponential mean.

The positive-activity assumption excludes the degenerate zero-movement path.
-/
theorem finite_path_displacement_bound
    (alpha x0 : ℝ)
    (increments : List ℝ)
    (hAlphaPositive : 0 < alpha)
    (hAlphaBelowOne : alpha < 1)
    (hActivityPositive :
      0 < (run alpha (initialState x0) increments).activity) :
    |displacementCoordinate
        (run alpha (initialState x0) increments)| ≤
      (1 - alpha) / alpha := by
  have hEndpoint :
      EndpointInvariant alpha
        (run alpha (initialState x0) increments) :=
    endpointInvariant_from_initial
      alpha x0 increments (ne_of_gt hAlphaPositive)
  have hDominance :
      DominanceInvariant
        (run alpha (initialState x0) increments) :=
    dominanceInvariant_from_initial
      alpha x0 increments
      (le_of_lt hAlphaPositive) (le_of_lt hAlphaBelowOne)
  calc
    |displacementCoordinate
        (run alpha (initialState x0) increments)| =
        |endpointCoordinate alpha
          (run alpha (initialState x0) increments).signed
          (run alpha (initialState x0) increments).activity| := by
            rw [displacementCoordinate_eq_endpointCoordinate
              alpha (run alpha (initialState x0) increments) hEndpoint]
    _ ≤ (1 - alpha) / alpha :=
      endpointCoordinate_abs_bound
        alpha
        (run alpha (initialState x0) increments).signed
        (run alpha (initialState x0) increments).activity
        hAlphaPositive hAlphaBelowOne hActivityPositive hDominance

/--
For Wilder's gain `alpha = 1 / n`, the finite-path displacement bound is
exactly `n - 1` activity units.
-/
theorem wilder_finite_path_displacement_bound
    (n x0 : ℝ)
    (increments : List ℝ)
    (hN : 1 < n)
    (hActivityPositive :
      0 < (run (1 / n) (initialState x0) increments).activity) :
    |displacementCoordinate
        (run (1 / n) (initialState x0) increments)| ≤
      n - 1 := by
  have hNPositive : 0 < n := lt_trans zero_lt_one hN
  have hAlphaPositive : 0 < 1 / n := one_div_pos.mpr hNPositive
  have hAlphaBelowOne : 1 / n < 1 :=
    (div_lt_one hNPositive).2 hN
  calc
    |displacementCoordinate
        (run (1 / n) (initialState x0) increments)| ≤
        (1 - (1 / n)) / (1 / n) :=
      finite_path_displacement_bound
        (1 / n) x0 increments
        hAlphaPositive hAlphaBelowOne hActivityPositive
    _ = n - 1 := wilder_scale n (ne_of_gt hNPositive)

/-!
The signed and absolute movement variables determine nonnegative directional
masses whenever `|signed| ≤ activity`:

`up = (activity + signed) / 2`,

`down = (activity - signed) / 2`.

Thus `signed = up - down` and `activity = up + down`.
-/

/-- Reconstructed exponentially weighted positive movement. -/
def positiveMass (signed activity : ℝ) : ℝ :=
  (activity + signed) / 2

/-- Reconstructed exponentially weighted negative movement. -/
def negativeMass (signed activity : ℝ) : ℝ :=
  (activity - signed) / 2

theorem positiveMass_sub_negativeMass
    (signed activity : ℝ) :
    positiveMass signed activity - negativeMass signed activity = signed := by
  unfold positiveMass negativeMass
  ring

theorem positiveMass_add_negativeMass
    (signed activity : ℝ) :
    positiveMass signed activity + negativeMass signed activity = activity := by
  unfold positiveMass negativeMass
  ring

theorem positiveMass_nonnegative
    (signed activity : ℝ)
    (hDominance : |signed| ≤ activity) :
    0 ≤ positiveMass signed activity := by
  have hLower : -activity ≤ signed := (abs_le.mp hDominance).1
  unfold positiveMass
  linarith

theorem negativeMass_nonnegative
    (signed activity : ℝ)
    (hDominance : |signed| ≤ activity) :
    0 ≤ negativeMass signed activity := by
  have hUpper : signed ≤ activity := (abs_le.mp hDominance).2
  unfold negativeMass
  linarith

/-- RSI as a unit fraction, before multiplication by 100. -/
def rsiFraction (up down : ℝ) : ℝ :=
  up / (up + down)

/--
The RSI fraction generated by the reconstructed directional masses is exactly
the affine image of the unit coordinate:

`RSI / 100 = (1 + F) / 2`, where `F = signed / activity`.
-/
theorem rsiFraction_eq_affine_unitCoordinate
    (signed activity : ℝ)
    (hActivity : activity ≠ 0) :
    rsiFraction
        (positiveMass signed activity)
        (negativeMass signed activity) =
      (1 + unitCoordinate signed activity) / 2 := by
  unfold rsiFraction
  rw [positiveMass_add_negativeMass]
  unfold positiveMass unitCoordinate
  field_simp [hActivity]

/-- RSI on its conventional `[0, 100]` scale. -/
def rsiValue (up down : ℝ) : ℝ :=
  100 * rsiFraction up down

/-- The conventional RSI value is `50 * (1 + F)`. -/
theorem rsiValue_eq_affine_unitCoordinate
    (signed activity : ℝ)
    (hActivity : activity ≠ 0) :
    rsiValue
        (positiveMass signed activity)
        (negativeMass signed activity) =
      50 * (1 + unitCoordinate signed activity) := by
  unfold rsiValue
  rw [rsiFraction_eq_affine_unitCoordinate signed activity hActivity]
  ring

/-! ## Classical directional increments and Wilder masses -/

/-- Positive part of an increment: `g = max increment 0`. -/
def gainPart (increment : ℝ) : ℝ :=
  max increment 0

/-- Negative movement written as a positive magnitude: `ell = max (-increment) 0`. -/
def lossPart (increment : ℝ) : ℝ :=
  max (-increment) 0

/-- The positive-minus-negative decomposition recovers the signed increment. -/
theorem gainPart_sub_lossPart (increment : ℝ) :
    gainPart increment - lossPart increment = increment := by
  by_cases hIncrement : 0 ≤ increment
  · have hNegative : -increment ≤ 0 := neg_nonpos.mpr hIncrement
    simp [gainPart, lossPart, max_eq_left hIncrement,
      max_eq_right hNegative]
  · have hIncrementNonpositive : increment ≤ 0 := le_of_not_ge hIncrement
    have hNegativeNonnegative : 0 ≤ -increment :=
      neg_nonneg.mpr hIncrementNonpositive
    simp [gainPart, lossPart, max_eq_right hIncrementNonpositive,
      max_eq_left hNegativeNonnegative]

/-- The positive-plus-negative decomposition recovers absolute movement. -/
theorem gainPart_add_lossPart (increment : ℝ) :
    gainPart increment + lossPart increment = |increment| := by
  by_cases hIncrement : 0 ≤ increment
  · have hNegative : -increment ≤ 0 := neg_nonpos.mpr hIncrement
    simp [gainPart, lossPart, max_eq_left hIncrement,
      max_eq_right hNegative, abs_of_nonneg hIncrement]
  · have hIncrementNonpositive : increment ≤ 0 := le_of_not_ge hIncrement
    have hNegativeNonnegative : 0 ≤ -increment :=
      neg_nonneg.mpr hIncrementNonpositive
    simp [gainPart, lossPart, max_eq_right hIncrementNonpositive,
      max_eq_left hNegativeNonnegative, abs_of_nonpos hIncrementNonpositive]

/-- One Wilder step of positive directional movement. -/
def positiveStep (alpha previousUp increment : ℝ) : ℝ :=
  (1 - alpha) * previousUp + alpha * gainPart increment

/-- One Wilder step of negative directional movement. -/
def negativeStep (alpha previousDown increment : ℝ) : ℝ :=
  (1 - alpha) * previousDown + alpha * lossPart increment

/-- Difference of the two classical Wilder masses follows `signedStep`. -/
theorem positiveStep_sub_negativeStep
    (alpha previousUp previousDown increment : ℝ) :
    positiveStep alpha previousUp increment -
        negativeStep alpha previousDown increment =
      signedStep alpha (previousUp - previousDown) increment := by
  calc
    positiveStep alpha previousUp increment -
          negativeStep alpha previousDown increment =
        (1 - alpha) * (previousUp - previousDown) +
          alpha * (gainPart increment - lossPart increment) := by
            unfold positiveStep negativeStep
            ring
    _ = (1 - alpha) * (previousUp - previousDown) +
          alpha * increment := by
            rw [gainPart_sub_lossPart]
    _ = signedStep alpha (previousUp - previousDown) increment := by
          rfl

/-- Sum of the two classical Wilder masses follows `activityStep`. -/
theorem positiveStep_add_negativeStep
    (alpha previousUp previousDown increment : ℝ) :
    positiveStep alpha previousUp increment +
        negativeStep alpha previousDown increment =
      activityStep alpha (previousUp + previousDown) increment := by
  calc
    positiveStep alpha previousUp increment +
          negativeStep alpha previousDown increment =
        (1 - alpha) * (previousUp + previousDown) +
          alpha * (gainPart increment + lossPart increment) := by
            unfold positiveStep negativeStep
            ring
    _ = (1 - alpha) * (previousUp + previousDown) +
          alpha * |increment| := by
            rw [gainPart_add_lossPart]
    _ = activityStep alpha (previousUp + previousDown) increment := by
          rfl

/-- A classical pair of Wilder-smoothed positive and negative masses. -/
structure DirectionalState where
  up : ℝ
  down : ℝ

/-- Advance both directional masses with the same gain and increment. -/
def directionalStep
    (alpha : ℝ) (state : DirectionalState) (increment : ℝ) :
    DirectionalState where
  up := positiveStep alpha state.up increment
  down := negativeStep alpha state.down increment

/-- Signed movement carried by a directional state. -/
def directionalSigned (state : DirectionalState) : ℝ :=
  state.up - state.down

/-- Absolute movement carried by a directional state. -/
def directionalActivity (state : DirectionalState) : ℝ :=
  state.up + state.down

theorem directionalSigned_step
    (alpha : ℝ) (state : DirectionalState) (increment : ℝ) :
    directionalSigned (directionalStep alpha state increment) =
      signedStep alpha (directionalSigned state) increment := by
  exact positiveStep_sub_negativeStep
    alpha state.up state.down increment

theorem directionalActivity_step
    (alpha : ℝ) (state : DirectionalState) (increment : ℝ) :
    directionalActivity (directionalStep alpha state increment) =
      activityStep alpha (directionalActivity state) increment := by
  exact positiveStep_add_negativeStep
    alpha state.up state.down increment

/-- Natural zero-movement initialization for the classical Wilder masses. -/
def initialDirectionalState : DirectionalState where
  up := 0
  down := 0

/-- Run the classical positive/negative Wilder recursion along a finite path. -/
def directionalRun (alpha : ℝ) :
    DirectionalState → List ℝ → DirectionalState
  | state, [] => state
  | state, increment :: rest =>
      directionalRun alpha (directionalStep alpha state increment) rest

/--
Along every finite path, the difference and sum of the classical Wilder masses
agree with the signed and activity components of the matched endpoint state,
provided they agree at initialization.
-/
theorem directionalRun_matches_run
    (alpha : ℝ)
    (increments : List ℝ)
    (directionalState : DirectionalState)
    (state : EWState)
    (hSigned : directionalSigned directionalState = state.signed)
    (hActivity : directionalActivity directionalState = state.activity) :
    directionalSigned
        (directionalRun alpha directionalState increments) =
        (run alpha state increments).signed ∧
      directionalActivity
        (directionalRun alpha directionalState increments) =
        (run alpha state increments).activity := by
  induction increments generalizing directionalState state with
  | nil =>
      simpa [directionalRun, run] using And.intro hSigned hActivity
  | cons increment rest inductionHypothesis =>
      apply inductionHypothesis
      · rw [directionalSigned_step]
        change signedStep alpha (directionalSigned directionalState) increment =
          signedStep alpha state.signed increment
        rw [hSigned]
      · rw [directionalActivity_step]
        change activityStep alpha (directionalActivity directionalState) increment =
          activityStep alpha state.activity increment
        rw [hActivity]

/--
Starting from zero directional masses and matched endpoint initialization,
the classical Wilder recursion produces exactly the signed and activity
components used by the endpoint formalization.
-/
theorem directionalRun_from_initial_matches
    (alpha x0 : ℝ)
    (increments : List ℝ) :
    directionalSigned
        (directionalRun alpha initialDirectionalState increments) =
        (run alpha (initialState x0) increments).signed ∧
      directionalActivity
        (directionalRun alpha initialDirectionalState increments) =
        (run alpha (initialState x0) increments).activity := by
  apply directionalRun_matches_run
  · simp [directionalSigned, initialDirectionalState, initialState]
  · simp [directionalActivity, initialDirectionalState, initialState]

/-- Reconstructing positive mass from a directional state returns its `up` field. -/
theorem positiveMass_directionalState (state : DirectionalState) :
    positiveMass (directionalSigned state) (directionalActivity state) =
      state.up := by
  unfold positiveMass directionalSigned directionalActivity
  ring

/-- Reconstructing negative mass from a directional state returns its `down` field. -/
theorem negativeMass_directionalState (state : DirectionalState) :
    negativeMass (directionalSigned state) (directionalActivity state) =
      state.down := by
  unfold negativeMass directionalSigned directionalActivity
  ring

/-! ## Interior bounds and the exact RSI/log-odds chain -/

/-- Balance written directly from positive and negative masses. -/
def balanceCoordinate (up down : ℝ) : ℝ :=
  (up - down) / (up + down)

theorem balanceCoordinate_eq_unitCoordinate (up down : ℝ) :
    balanceCoordinate up down =
      unitCoordinate (up - down) (up + down) := by
  rfl

/-- Reconstructing the directional masses from `(signed, activity)` preserves balance. -/
theorem balanceCoordinate_reconstructed_masses
    (signed activity : ℝ) :
    balanceCoordinate
        (positiveMass signed activity)
        (negativeMass signed activity) =
      unitCoordinate signed activity := by
  unfold balanceCoordinate unitCoordinate
  rw [positiveMass_sub_negativeMass, positiveMass_add_negativeMass]

/-- Strict dominance makes the reconstructed positive mass strictly positive. -/
theorem positiveMass_pos
    (signed activity : ℝ)
    (hStrict : |signed| < activity) :
    0 < positiveMass signed activity := by
  have hLower : -activity < signed := (abs_lt.mp hStrict).1
  unfold positiveMass
  linarith

/-- Strict dominance makes the reconstructed negative mass strictly positive. -/
theorem negativeMass_pos
    (signed activity : ℝ)
    (hStrict : |signed| < activity) :
    0 < negativeMass signed activity := by
  have hUpper : signed < activity := (abs_lt.mp hStrict).2
  unfold negativeMass
  linarith

/-- Strict signed-versus-absolute dominance places the unit coordinate in `(-1, 1)`. -/
theorem unitCoordinate_mem_Ioo
    (signed activity : ℝ)
    (hActivity : 0 < activity)
    (hStrict : |signed| < activity) :
    unitCoordinate signed activity ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hAbsolute : |unitCoordinate signed activity| < 1 := by
    simp only [unitCoordinate, abs_div, abs_of_pos hActivity]
    exact (div_lt_one hActivity).2 hStrict
  exact abs_lt.mp hAbsolute

/-- Positive directional masses place their balance strictly inside `(-1, 1)`. -/
theorem balanceCoordinate_mem_Ioo
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    balanceCoordinate up down ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hSum : 0 < up + down := add_pos hUp hDown
  unfold balanceCoordinate
  constructor
  · rw [lt_div_iff₀ hSum]
    linarith
  · rw [div_lt_iff₀ hSum]
    linarith

/-- The RSI fraction generated by positive masses lies strictly between zero and one. -/
theorem rsiFraction_mem_Ioo_zero_one
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    rsiFraction up down ∈ Set.Ioo (0 : ℝ) 1 := by
  have hSum : 0 < up + down := add_pos hUp hDown
  constructor
  · exact div_pos hUp hSum
  · exact (div_lt_one hSum).2 (lt_add_of_pos_right up hDown)

/-- The conventional RSI value lies strictly between zero and one hundred. -/
theorem rsiValue_mem_Ioo_zero_hundred
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    rsiValue up down ∈ Set.Ioo (0 : ℝ) 100 := by
  obtain ⟨hFractionPositive, hFractionBelowOne⟩ :=
    rsiFraction_mem_Ioo_zero_one up down hUp hDown
  unfold rsiValue
  constructor
  · exact mul_pos (by norm_num) hFractionPositive
  · nlinarith

/-- For arbitrary positive masses, RSI is the affine image of balance. -/
theorem rsiFraction_eq_affine_balanceCoordinate
    (up down : ℝ)
    (hSum : up + down ≠ 0) :
    rsiFraction up down =
      (1 + balanceCoordinate up down) / 2 := by
  unfold rsiFraction balanceCoordinate
  field_simp [hSum]
  ring

/-- The rational odds map associated with a bounded balance coordinate. -/
def oddsRatio (balance : ℝ) : ℝ :=
  (1 + balance) / (1 - balance)

/-- The logarithmic odds coordinate of a bounded balance. -/
def logOdds (balance : ℝ) : ℝ :=
  Real.log (oddsRatio balance)

/-- The primitive logarithmic ratio of positive and negative masses. -/
def directionalLogRatio (up down : ℝ) : ℝ :=
  Real.log (up / down)

/-- Logit of a unit fraction. -/
def logitCoordinate (fraction : ℝ) : ℝ :=
  Real.log (fraction / (1 - fraction))

/-- The odds of balance are exactly the ratio of directional masses. -/
theorem oddsRatio_balanceCoordinate_eq_massRatio
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    oddsRatio (balanceCoordinate up down) = up / down := by
  have hSum : up + down ≠ 0 := ne_of_gt (add_pos hUp hDown)
  have hDownNonzero : down ≠ 0 := ne_of_gt hDown
  unfold oddsRatio balanceCoordinate
  field_simp [hSum, hDownNonzero]
  ring

/-- The log-odds of balance is exactly the log ratio of directional masses. -/
theorem logOdds_balanceCoordinate_eq_directionalLogRatio
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    logOdds (balanceCoordinate up down) =
      directionalLogRatio up down := by
  unfold logOdds directionalLogRatio
  rw [oddsRatio_balanceCoordinate_eq_massRatio up down hUp hDown]

/-- The odds of the RSI fraction are exactly the ratio of directional masses. -/
theorem rsiOdds_eq_massRatio
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    rsiFraction up down / (1 - rsiFraction up down) = up / down := by
  have hSum : up + down ≠ 0 := ne_of_gt (add_pos hUp hDown)
  have hDownNonzero : down ≠ 0 := ne_of_gt hDown
  unfold rsiFraction
  field_simp [hSum, hDownNonzero]
  ring

/-- The logit of RSI equals the primitive log ratio `log (up / down)`. -/
theorem logit_rsiFraction_eq_directionalLogRatio
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    logitCoordinate (rsiFraction up down) =
      directionalLogRatio up down := by
  unfold logitCoordinate directionalLogRatio
  rw [rsiOdds_eq_massRatio up down hUp hDown]

/-- Exact equality between RSI logit and balance log-odds. -/
theorem logit_rsiFraction_eq_logOdds_balanceCoordinate
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    logitCoordinate (rsiFraction up down) =
      logOdds (balanceCoordinate up down) := by
  rw [logit_rsiFraction_eq_directionalLogRatio up down hUp hDown]
  symm
  exact logOdds_balanceCoordinate_eq_directionalLogRatio
    up down hUp hDown

/-- On the interior, log-odds is exactly twice the real inverse hyperbolic tangent. -/
theorem logOdds_eq_twice_artanh
    (balance : ℝ)
    (hBalance : balance ∈ Set.Ioo (-1 : ℝ) 1) :
    logOdds balance = 2 * Real.artanh balance := by
  unfold logOdds oddsRatio
  rw [Real.artanh_eq_half_log
    ⟨le_of_lt hBalance.1, le_of_lt hBalance.2⟩]
  ring

/-- The log-odds map is strictly increasing on its natural open interval. -/
theorem logOdds_strictMonoOn :
    StrictMonoOn logOdds (Set.Ioo (-1 : ℝ) 1) := by
  intro left hLeft right hRight hOrder
  rw [logOdds_eq_twice_artanh left hLeft,
    logOdds_eq_twice_artanh right hRight]
  have hArtanh : Real.artanh left < Real.artanh right :=
    Real.artanh_lt_artanh hLeft.1 hRight.2 hOrder
  linarith

/-- Complete exact identity used by the RSI paper. -/
theorem exact_rsi_logOdds_chain
    (up down : ℝ)
    (hUp : 0 < up)
    (hDown : 0 < down) :
    logitCoordinate (rsiFraction up down) =
        directionalLogRatio up down ∧
      directionalLogRatio up down =
        logOdds (balanceCoordinate up down) ∧
      logOdds (balanceCoordinate up down) =
        2 * Real.artanh (balanceCoordinate up down) := by
  have hBalance := balanceCoordinate_mem_Ioo up down hUp hDown
  constructor
  · exact logit_rsiFraction_eq_directionalLogRatio up down hUp hDown
  constructor
  · symm
    exact logOdds_balanceCoordinate_eq_directionalLogRatio
      up down hUp hDown
  · exact logOdds_eq_twice_artanh
      (balanceCoordinate up down) hBalance

/-! ## Arbitrary initialization and exact geometric error decay -/

/-- Error in the endpoint identity for an arbitrary state. -/
def endpointError (alpha : ℝ) (state : EWState) : ℝ :=
  (state.value - state.mean) -
    ((1 - alpha) / alpha) * state.signed

/-- The endpoint invariant is equivalent to zero endpoint error. -/
theorem endpointInvariant_iff_endpointError_eq_zero
    (alpha : ℝ) (state : EWState) :
    EndpointInvariant alpha state ↔ endpointError alpha state = 0 := by
  unfold EndpointInvariant endpointError
  constructor <;> intro hInvariant <;> linarith

/-- One matched update multiplies arbitrary initialization error by `1 - alpha`. -/
theorem endpointError_stateStep
    (alpha : ℝ)
    (state : EWState)
    (increment : ℝ)
    (hAlpha : alpha ≠ 0) :
    endpointError alpha (stateStep alpha state increment) =
      (1 - alpha) * endpointError alpha state := by
  simp only [endpointError, stateStep, emaStep, signedStep]
  field_simp [hAlpha]
  ring

/-- After any finite path, endpoint error has an exact geometric multiplier. -/
theorem endpointError_run
    (alpha : ℝ)
    (increments : List ℝ)
    (state : EWState)
    (hAlpha : alpha ≠ 0) :
    endpointError alpha (run alpha state increments) =
      (1 - alpha) ^ increments.length * endpointError alpha state := by
  induction increments generalizing state with
  | nil =>
      simp [run]
  | cons increment rest inductionHypothesis =>
      calc
        endpointError alpha (run alpha state (increment :: rest)) =
            endpointError alpha
              (run alpha (stateStep alpha state increment) rest) := by
                rfl
        _ = (1 - alpha) ^ rest.length *
              endpointError alpha (stateStep alpha state increment) :=
            inductionHypothesis (stateStep alpha state increment)
        _ = (1 - alpha) ^ rest.length *
              ((1 - alpha) * endpointError alpha state) := by
            rw [endpointError_stateStep alpha state increment hAlpha]
        _ = (1 - alpha) ^ (increment :: rest).length *
              endpointError alpha state := by
            simp [pow_succ]
            ring

/-- Exact decay of the absolute endpoint error for an arbitrary gain. -/
theorem endpointError_run_abs
    (alpha : ℝ)
    (increments : List ℝ)
    (state : EWState)
    (hAlpha : alpha ≠ 0) :
    |endpointError alpha (run alpha state increments)| =
      |1 - alpha| ^ increments.length * |endpointError alpha state| := by
  rw [endpointError_run alpha increments state hAlpha]
  simp [abs_mul, abs_pow]

/-- If `0 < alpha ≤ 1`, the absolute error multiplier is `(1 - alpha)^t`. -/
theorem endpointError_run_abs_of_gain
    (alpha : ℝ)
    (increments : List ℝ)
    (state : EWState)
    (hAlphaPositive : 0 < alpha)
    (hAlphaAtMostOne : alpha ≤ 1) :
    |endpointError alpha (run alpha state increments)| =
      (1 - alpha) ^ increments.length * |endpointError alpha state| := by
  rw [endpointError_run_abs
    alpha increments state (ne_of_gt hAlphaPositive)]
  rw [abs_of_nonneg (sub_nonneg.mpr hAlphaAtMostOne)]

/-- Wilder specialization of exact initialization-error decay. -/
theorem wilder_endpointError_run
    (n : ℝ)
    (increments : List ℝ)
    (state : EWState)
    (hN : n ≠ 0) :
    endpointError (1 / n) (run (1 / n) state increments) =
      (1 - 1 / n) ^ increments.length *
        endpointError (1 / n) state := by
  exact endpointError_run
    (1 / n) increments state (div_ne_zero one_ne_zero hN)

/-- Absolute initialization error under Wilder gain decays by `(1 - 1/n)^t`. -/
theorem wilder_endpointError_run_abs
    (n : ℝ)
    (increments : List ℝ)
    (state : EWState)
    (hN : 1 < n) :
    |endpointError (1 / n) (run (1 / n) state increments)| =
      (1 - 1 / n) ^ increments.length *
        |endpointError (1 / n) state| := by
  have hNPositive : 0 < n := lt_trans zero_lt_one hN
  have hGainPositive : 0 < 1 / n := one_div_pos.mpr hNPositive
  have hGainAtMostOne : 1 / n ≤ 1 :=
    le_of_lt ((div_lt_one hNPositive).2 hN)
  exact endpointError_run_abs_of_gain
    (1 / n) increments state hGainPositive hGainAtMostOne

/-! ## Direct endpoint form of the log-odds coordinate -/

/-- Balance read directly from price displacement under Wilder gain `1 / n`. -/
def wilderEndpointBalance (n : ℝ) (state : EWState) : ℝ :=
  (state.value - state.mean) / ((n - 1) * state.activity)

/-- Under the endpoint invariant, direct normalized displacement equals `S / A`. -/
theorem wilderEndpointBalance_eq_unitCoordinate
    (n : ℝ)
    (state : EWState)
    (hN : 1 < n)
    (hActivity : state.activity ≠ 0)
    (hInvariant : EndpointInvariant (1 / n) state) :
    wilderEndpointBalance n state =
      unitCoordinate state.signed state.activity := by
  have hNPositive : 0 < n := lt_trans zero_lt_one hN
  have hNNonzero : n ≠ 0 := ne_of_gt hNPositive
  have hScaleNonzero : n - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hN)
  unfold wilderEndpointBalance unitCoordinate
  unfold EndpointInvariant at hInvariant
  rw [hInvariant, wilder_scale n hNNonzero]
  field_simp [hScaleNonzero, hActivity]

/--
The paper's direct endpoint log-odds equals the primitive directional log ratio.
This is the complete deterministic bridge from price and EMA to RSI log-odds.
-/
theorem wilder_endpoint_logOdds_identity
    (n : ℝ)
    (state : EWState)
    (hN : 1 < n)
    (hStrict : |state.signed| < state.activity)
    (hInvariant : EndpointInvariant (1 / n) state) :
    logOdds (wilderEndpointBalance n state) =
      directionalLogRatio
        (positiveMass state.signed state.activity)
        (negativeMass state.signed state.activity) := by
  have hActivityPositive : 0 < state.activity :=
    lt_of_le_of_lt (abs_nonneg state.signed) hStrict
  have hActivityNonzero : state.activity ≠ 0 :=
    ne_of_gt hActivityPositive
  have hPositive :
      0 < positiveMass state.signed state.activity :=
    positiveMass_pos state.signed state.activity hStrict
  have hNegative :
      0 < negativeMass state.signed state.activity :=
    negativeMass_pos state.signed state.activity hStrict
  rw [wilderEndpointBalance_eq_unitCoordinate
    n state hN hActivityNonzero hInvariant]
  rw [← balanceCoordinate_reconstructed_masses
    state.signed state.activity]
  exact logOdds_balanceCoordinate_eq_directionalLogRatio
    (positiveMass state.signed state.activity)
    (negativeMass state.signed state.activity)
    hPositive hNegative

/-- Direct endpoint log-odds is also twice `artanh` of normalized displacement. -/
theorem wilder_endpoint_logOdds_eq_twice_artanh
    (n : ℝ)
    (state : EWState)
    (hN : 1 < n)
    (hStrict : |state.signed| < state.activity)
    (hInvariant : EndpointInvariant (1 / n) state) :
    logOdds (wilderEndpointBalance n state) =
      2 * Real.artanh (wilderEndpointBalance n state) := by
  have hActivityPositive : 0 < state.activity :=
    lt_of_le_of_lt (abs_nonneg state.signed) hStrict
  have hActivityNonzero : state.activity ≠ 0 :=
    ne_of_gt hActivityPositive
  have hUnitInterior :
      unitCoordinate state.signed state.activity ∈
        Set.Ioo (-1 : ℝ) 1 :=
    unitCoordinate_mem_Ioo
      state.signed state.activity hActivityPositive hStrict
  have hEndpointInterior :
      wilderEndpointBalance n state ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [wilderEndpointBalance_eq_unitCoordinate
      n state hN hActivityNonzero hInvariant]
    exact hUnitInterior
  exact logOdds_eq_twice_artanh
    (wilderEndpointBalance n state) hEndpointInterior

/-! ## Finite-path paper statements in final form -/

/-- Final matched state after a finite path under Wilder gain `1 / n`. -/
def wilderFinalState (n x0 : ℝ) (increments : List ℝ) : EWState :=
  run (1 / n) (initialState x0) increments

theorem wilderFinalState_endpointInvariant
    (n x0 : ℝ)
    (increments : List ℝ)
    (hN : 1 < n) :
    EndpointInvariant (1 / n)
      (wilderFinalState n x0 increments) := by
  have hNPositive : 0 < n := lt_trans zero_lt_one hN
  unfold wilderFinalState
  exact endpointInvariant_from_initial
    (1 / n) x0 increments
    (div_ne_zero one_ne_zero (ne_of_gt hNPositive))

theorem wilderFinalState_dominanceInvariant
    (n x0 : ℝ)
    (increments : List ℝ)
    (hN : 1 < n) :
    DominanceInvariant (wilderFinalState n x0 increments) := by
  have hNPositive : 0 < n := lt_trans zero_lt_one hN
  have hGainPositive : 0 < 1 / n := one_div_pos.mpr hNPositive
  have hGainAtMostOne : 1 / n ≤ 1 :=
    le_of_lt ((div_lt_one hNPositive).2 hN)
  unfold wilderFinalState
  exact dominanceInvariant_from_initial
    (1 / n) x0 increments
    (le_of_lt hGainPositive) hGainAtMostOne

/--
The direct displacement coordinate has deterministic floor `-(n - 1)` and
ceiling `n - 1` on every nondegenerate finite path.
-/
theorem wilder_finite_path_displacement_interval
    (n x0 : ℝ)
    (increments : List ℝ)
    (hN : 1 < n)
    (hActivityPositive :
      0 < (wilderFinalState n x0 increments).activity) :
    -(n - 1) ≤
        displacementCoordinate (wilderFinalState n x0 increments) ∧
      displacementCoordinate (wilderFinalState n x0 increments) ≤
        n - 1 := by
  apply abs_le.mp
  simpa [wilderFinalState] using
    wilder_finite_path_displacement_bound
      n x0 increments hN hActivityPositive

/--
For every finite path with both directional masses present, the following
identities hold simultaneously:

`logit(RSI / 100) = log-odds(endpoint balance)`

and

`log-odds(endpoint balance) = 2 * artanh(endpoint balance)`.
-/
theorem wilder_finite_path_rsi_logOdds_chain
    (n x0 : ℝ)
    (increments : List ℝ)
    (hN : 1 < n)
    (hStrict :
      |(wilderFinalState n x0 increments).signed| <
        (wilderFinalState n x0 increments).activity) :
    logitCoordinate
        (rsiFraction
          (positiveMass
            (wilderFinalState n x0 increments).signed
            (wilderFinalState n x0 increments).activity)
          (negativeMass
            (wilderFinalState n x0 increments).signed
            (wilderFinalState n x0 increments).activity)) =
        logOdds
          (wilderEndpointBalance n
            (wilderFinalState n x0 increments)) ∧
      logOdds
          (wilderEndpointBalance n
            (wilderFinalState n x0 increments)) =
        2 * Real.artanh
          (wilderEndpointBalance n
            (wilderFinalState n x0 increments)) := by
  have hEndpoint :
      EndpointInvariant (1 / n)
        (wilderFinalState n x0 increments) :=
    wilderFinalState_endpointInvariant n x0 increments hN
  have hPositive :
      0 < positiveMass
        (wilderFinalState n x0 increments).signed
        (wilderFinalState n x0 increments).activity :=
    positiveMass_pos
      (wilderFinalState n x0 increments).signed
      (wilderFinalState n x0 increments).activity
      hStrict
  have hNegative :
      0 < negativeMass
        (wilderFinalState n x0 increments).signed
        (wilderFinalState n x0 increments).activity :=
    negativeMass_pos
      (wilderFinalState n x0 increments).signed
      (wilderFinalState n x0 increments).activity
      hStrict
  constructor
  · calc
      logitCoordinate
          (rsiFraction
            (positiveMass
              (wilderFinalState n x0 increments).signed
              (wilderFinalState n x0 increments).activity)
            (negativeMass
              (wilderFinalState n x0 increments).signed
              (wilderFinalState n x0 increments).activity)) =
          directionalLogRatio
            (positiveMass
              (wilderFinalState n x0 increments).signed
              (wilderFinalState n x0 increments).activity)
            (negativeMass
              (wilderFinalState n x0 increments).signed
              (wilderFinalState n x0 increments).activity) :=
        logit_rsiFraction_eq_directionalLogRatio
          (positiveMass
            (wilderFinalState n x0 increments).signed
            (wilderFinalState n x0 increments).activity)
          (negativeMass
            (wilderFinalState n x0 increments).signed
            (wilderFinalState n x0 increments).activity)
          hPositive hNegative
      _ = logOdds
            (wilderEndpointBalance n
              (wilderFinalState n x0 increments)) := by
        symm
        exact wilder_endpoint_logOdds_identity
          n (wilderFinalState n x0 increments)
          hN hStrict hEndpoint
  · exact wilder_endpoint_logOdds_eq_twice_artanh
      n (wilderFinalState n x0 increments)
      hN hStrict hEndpoint

/--
The exact finite-path RSI/log-odds chain for the classical Wilder recursion
itself.  The RSI fraction on the left is computed from the recursively smoothed
positive and negative increments, not from reconstructed masses.
-/
theorem wilder_directionalRun_rsi_logOdds_chain
    (n x0 : ℝ)
    (increments : List ℝ)
    (hN : 1 < n)
    (hStrict :
      |(wilderFinalState n x0 increments).signed| <
        (wilderFinalState n x0 increments).activity) :
    logitCoordinate
        (rsiFraction
          (directionalRun (1 / n) initialDirectionalState increments).up
          (directionalRun (1 / n) initialDirectionalState increments).down) =
        logOdds
          (wilderEndpointBalance n
            (wilderFinalState n x0 increments)) ∧
      logOdds
          (wilderEndpointBalance n
            (wilderFinalState n x0 increments)) =
        2 * Real.artanh
          (wilderEndpointBalance n
            (wilderFinalState n x0 increments)) := by
  let directionalFinal :=
    directionalRun (1 / n) initialDirectionalState increments
  let endpointFinal := wilderFinalState n x0 increments
  have hMatches :
      directionalSigned directionalFinal = endpointFinal.signed ∧
        directionalActivity directionalFinal = endpointFinal.activity := by
    simpa only [directionalFinal, endpointFinal, wilderFinalState] using
      directionalRun_from_initial_matches (1 / n) x0 increments
  have hUp :
      directionalFinal.up =
        positiveMass endpointFinal.signed endpointFinal.activity := by
    calc
      directionalFinal.up =
          positiveMass
            (directionalSigned directionalFinal)
            (directionalActivity directionalFinal) := by
              symm
              exact positiveMass_directionalState directionalFinal
      _ = positiveMass endpointFinal.signed endpointFinal.activity := by
            rw [hMatches.1, hMatches.2]
  have hDown :
      directionalFinal.down =
        negativeMass endpointFinal.signed endpointFinal.activity := by
    calc
      directionalFinal.down =
          negativeMass
            (directionalSigned directionalFinal)
            (directionalActivity directionalFinal) := by
              symm
              exact negativeMass_directionalState directionalFinal
      _ = negativeMass endpointFinal.signed endpointFinal.activity := by
            rw [hMatches.1, hMatches.2]
  have hChain :=
    wilder_finite_path_rsi_logOdds_chain n x0 increments hN hStrict
  simpa only [directionalFinal, endpointFinal, hUp, hDown] using hChain

end

end EndpointCoordinate
