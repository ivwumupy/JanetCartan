module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderSobolev.Localization
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Realization.Amplitude
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.IntegerBounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Literal

/-!
# Euclidean realization of the localized Taylor remainder

The fixed physical cutoffs use the existing paired-position projections.
`IntegerBounds` supplies the L² realization and its literal Hilbert adjoint.
Source: the error paragraph following `app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound JanetCartan.ContinuumNormal
namespace JanetCartan.ContinuumRow.TransportKernel
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin (2 * n))
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The paired amplitude is exactly the localized original amplitude in
`app:ch_background:eq:bg-real-symbol`; no change of measure is involved. -/
@[simp] theorem localizedRemainderAmplitude_pairedPosition
    (c : E → E → E → ℂ) (α γ : E → ℝ) (x y ξ : E) :
    localizedRemainderAmplitude (freezingOutputProjection.prod freezingSourceProjection)
      c α γ ξ (pairedPosition x y) = α x • (γ y • c x y ξ) := by
  simp [localizedRemainderAmplitude]

/-- The two fixed physical support boxes supply precisely the support input
of `twoPositionL2Operator` for the error following
`app:ch_background:eq:bg-real-symbol`. -/
theorem supportedInCenteredBox_localizedRemainderAmplitude
    (c : E → E → E → ℂ) (α γ : E → ℝ) (R : ℝ)
    (hα : ∀ x, α x ≠ 0 → ∀ j, |x j| ≤ R)
    (hγ : ∀ y, γ y ≠ 0 → ∀ j, |y j| ≤ R) (ξ : E) :
    SupportedInCenteredBox R
      (localizedRemainderAmplitude (freezingOutputProjection.prod freezingSourceProjection)
        c α γ ξ) := by
  intro z hz j
  have ha : α (freezingOutputProjection z) ≠ 0 := by
    intro h
    simp [localizedRemainderAmplitude, h] at hz
  have hg : γ (freezingSourceProjection z) ≠ 0 := by
    intro h
    simp [localizedRemainderAmplitude, h] at hz
  by_cases hj : j.val < n
  · exact hα _ ha ⟨j.val, hj⟩
  · simpa [freezingSourceProjection, show n + (j.val - n) = j.val by omega] using
      hγ _ hg ⟨j.val - n, by omega⟩

/-- The localized L² realization is the literal full-amplitude operator on
compact smooth tests. Apply this with the original diagonal remainder used
in `PrincipalReduction`. Source: `app:ch_background:eq:bg-real-symbol`. -/
theorem localizedRemainderL2Operator_toLp_ae_fullAmplitudeOperator
    (hn : 0 < n) (R : ℝ) (c : E → E → E → ℂ) (α γ : E → ℝ)
    (hb : ContDiff ℝ ∞ (Function.uncurry (localizedRemainderAmplitude
      (freezingOutputProjection.prod freezingSourceProjection) c α γ)))
    (hs : ∀ ξ, SupportedInCenteredBox R (localizedRemainderAmplitude
      (freezingOutputProjection.prod freezingSourceProjection) c α γ ξ))
    (M : ℝ) (hM : HasAmplitudeDerivativeBound (localizedRemainderAmplitude
      (freezingOutputProjection.prod freezingSourceProjection) c α γ) (2 * (n + 1)) M)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    twoPositionL2Operator hn R _ hb hs M hM
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ α x • (γ y • c x y ξ)) u := by
  simpa only [localizedRemainderAmplitude_pairedPosition] using
    twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget hn R _ hb hs M hM
      u (hu.continuous.memLp_of_hasCompactSupport hus) (hu.of_le (by simp)) hus

/-- The actual Hilbert adjoint is the reversed conjugate localized integral
on compact smooth tests; the original physical budget suffices.
Source: the adjoint error claim following `app:ch_background:eq:bg-real-symbol`. -/
theorem localizedRemainderL2Operator_adjoint_toLp_ae_fullAmplitudeOperator
    (hn : 0 < n) (R : ℝ) (c : E → E → E → ℂ) (α γ : E → ℝ)
    (hb : ContDiff ℝ ∞ (Function.uncurry (localizedRemainderAmplitude
      (freezingOutputProjection.prod freezingSourceProjection) c α γ)))
    (hs : ∀ ξ, SupportedInCenteredBox R (localizedRemainderAmplitude
      (freezingOutputProjection.prod freezingSourceProjection) c α γ ξ))
    (M : ℝ) (hM : HasAmplitudeDerivativeBound (localizedRemainderAmplitude
      (freezingOutputProjection.prod freezingSourceProjection) c α γ) (2 * (n + 1)) M)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    (twoPositionL2Operator hn R _ hb hs M hM).adjoint
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ star (α y • (γ x • c y x ξ))) u := by
  simpa only [localizedRemainderAmplitude_pairedPosition] using
    twoPositionL2Operator_adjoint_toLp_ae_fullAmplitudeOperator_of_physicalBudget
      hn R _ hb hs M hM u hu hus

/-- The all-data gain-one bounds for an amplitude and its literal Hilbert
adjoint can use one common constant. This is used only after the physical
budgets of the actual remainder have been constructed.
Source: the error paragraph following `app:ch_background:eq:bg-real-symbol`. -/
theorem exists_remainder_integer_gain_and_adjoint_constant
    (hn : 0 < n) (R : ℝ) (s : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : E → P → ℂ)
      (hb : ContDiff ℝ ∞ (Function.uncurry b))
      (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
      (hM : ∀ ξ is, is.length ≤ 2 * (n + 1) + 1 → ∀ z,
        (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ M),
      (∀ ξ is, is.length ≤ 2 * (n + 1) + (s + 1) → ∀ z,
        (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ H) →
      ∀ f : L², MemFourierSobolev (s : ℝ) f →
      let T := twoPositionL2Operator hn R b hb hs M
        (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM) (Nat.le_succ _))
      (MemFourierSobolev ((s : ℝ) + 1) (T f) ∧
        fourierSobolevNorm ((s : ℝ) + 1) (T f) ≤
          C * (fourierSobolevNorm (s : ℝ) f + max 1 H * ‖f‖)) ∧
      (MemFourierSobolev ((s : ℝ) + 1) (T.adjoint f) ∧
        fourierSobolevNorm ((s : ℝ) + 1) (T.adjoint f) ≤
          C * (fourierSobolevNorm (s : ℝ) f + max 1 H * ‖f‖)) := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_twoPositionL2Operator_integer_gain_tame_constant_all_data hn R s M
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_twoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data hn R s M
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), ?_⟩
  intro b hb hs H hM hH f hf
  obtain ⟨hm₁, he₁⟩ := h₁ b hb hs H hM hH f hf
  obtain ⟨hm₂, he₂⟩ := h₂ b hb hs H hM hH f hf
  have hnonneg : 0 ≤ fourierSobolevNorm (s : ℝ) f + max 1 H * ‖f‖ := by
    exact add_nonneg (fourierSobolevNorm_nonneg _ _) (by positivity)
  exact ⟨⟨hm₁, he₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg)⟩,
    ⟨hm₂, he₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnonneg)⟩⟩

end JanetCartan.ContinuumRow.TransportKernel
