module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.EnvelopeJets.Moments
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.EnvelopeJets.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.EnvelopeJets.InverseJets

/-!
# Pointwise Euclidean envelope jets from Sobolev bounds

The actual Sobolev envelope profile
`app:ch_response:eq:response-graded-source` implies pointwise bounds for every
jet, with fixed loss `n + 1`. Absolute Fourier moments supply both pointwise
reconstruction and differentiation of the inverse integral. The envelope need
not be L¹. For order `r`, only Sobolev orders up to `r + (n + 1)` are used.

These bounds supply the envelope input to the concrete `SourceShellBounds`
construction for the original-source negative estimate immediately before
`app:ch_response:eq:response-graded-reduced`. The derivative constant retains
Mathlib's exact `2π` normalization and is independent of the envelope, its
amplitude and its scale.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.ResponseTransfer.SourceNegative

/-- The uniform constant for the `r`-th envelope jet derived from
`app:ch_response:eq:response-graded-source`, with fixed Sobolev loss `n + 1`.
It depends only on dimension and derivative order, even for Hilbert targets. -/
def envelopeJetConstant (n r : ℕ) : ℝ :=
  (2 * Real.pi) ^ r * envelopeMomentConstant n

/-- Nonnegativity of the jet constant used by the source-shell construction
before `app:ch_response:eq:response-graded-reduced`. -/
theorem envelopeJetConstant_nonneg (n r : ℕ) : 0 ≤ envelopeJetConstant n r :=
  mul_nonneg (by positivity) (envelopeMomentConstant_nonneg n)

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The actual Fourier Sobolev profile
`app:ch_response:eq:response-graded-source` bounds every pointwise envelope jet.
This supplies the envelope derivatives for the parent's `SourceShellBounds`
construction. Reconstruction and the needed moments are proved from the given
profile; no Fourier inversion or pointwise estimate is an additional premise. -/
theorem SobolevEnvelopeBounds.norm_iteratedFDeriv_le
    {f : Euclidean n → F} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) (r : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ r f x‖ ≤
      envelopeJetConstant n r * C (r + (n + 1)) * A * K ^ (r + (n + 1)) := by
  have hjet := norm_iteratedFDeriv_fourierInv_le_moment
    (fun ξ ↦ (𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) ξ) r
    (Lp.aestronglyMeasurable _) (fun j _ ↦ h.fourier_moment_integrable j) x
  rw [← eq_fourierInv_l2_of_continuous h.smooth.continuous hf
    h.fourier_integrable] at hjet
  exact hjet.trans ((mul_le_mul_of_nonneg_left (h.fourier_moment_le r)
    (by positivity : 0 ≤ (2 * Real.pi) ^ r)).trans_eq (by
      dsimp [envelopeJetConstant]
      ring))

/-- Uniformity of the pointwise envelope bound from
`app:ch_response:eq:response-graded-source`: the constant is chosen before the
envelope and its amplitude, scale and Sobolev profile. The fixed loss `n + 1`
is the one absorbed in the original-source negative estimate before
`app:ch_response:eq:response-graded-reduced`. -/
theorem exists_envelope_jet_bound (n : ℕ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Euclidean n → F) (hf : MemLp f 2 volume)
      (A K : ℝ) (C : ℕ → ℝ), SobolevEnvelopeBounds f hf A K C →
      ∀ x, ‖iteratedFDeriv ℝ r f x‖ ≤
        D * C (r + (n + 1)) * A * K ^ (r + (n + 1)) := by
  refine ⟨envelopeJetConstant n r, envelopeJetConstant_nonneg n r, ?_⟩
  intro f hf A K C h x
  exact h.norm_iteratedFDeriv_le r x

end JanetCartan.ResponseTransfer.SourceNegative
