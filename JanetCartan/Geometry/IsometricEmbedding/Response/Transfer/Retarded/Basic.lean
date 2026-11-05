module

public import JanetCartan.Analysis.Operator.RetardedSobolev.PositiveExtension
public import JanetCartan.Analysis.Operator.RetardedSobolev.LiteralPairing
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier

/-!
# Buffered cutoffs and literal carrier cancellation

The retarded factors of `app:ch_response:eq:fixed-factor-transfer`. The data
below contain only the fixed smooth cutoffs and their endpoint buffers. Bounds
are proved from `RetardedSobolev`, never included as fields. The transverse
carrier uses the shared physical covector convention: torus covectors, if used,
must first be multiplied by `2π`. No torus/Lebesgue identification is made.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer

open RetardedSobolev RetardedSobolev.Spaces

/-- Fixed cutoff data for `app:ch_osc:setup:osc-retarded` and its upper adjoint.
The lower input and the exchanged upper input retain positive endpoint buffers.
This is geometric input to the transfer deduction, not an operator estimate. -/
structure RetardedCutoffs (d : ℕ) where
  lowerEndpoint : ℝ
  upperEndpoint : ℝ
  endpoints_le : lowerEndpoint ≤ upperEndpoint
  buffer : ℝ
  buffer_pos : 0 < buffer
  input : ℝ × (Fin d → ℝ) → ℝ
  output : ℝ × (Fin d → ℝ) → ℝ
  input_smooth : ContDiff ℝ ∞ input
  output_smooth : ContDiff ℝ ∞ output
  input_compact : HasCompactSupport input
  output_compact : HasCompactSupport output
  lower_input_buffer : tsupport input ⊆
    Icc (lowerEndpoint + buffer) upperEndpoint ×ˢ univ
  upper_input_buffer : tsupport output ⊆
    Icc lowerEndpoint (upperEndpoint - buffer) ×ˢ univ

namespace RetardedCutoffs

variable {d : ℕ} (W : RetardedCutoffs d)

/-- The buffered lower input lies in the fixed strip
(`app:ch_osc:setup:osc-retarded`). -/
theorem input_support_strip : tsupport W.input ⊆
    Icc W.lowerEndpoint W.upperEndpoint ×ˢ univ := by
  intro x hx
  have h := W.lower_input_buffer hx
  exact ⟨⟨by linarith [h.1.1, W.buffer_pos], h.1.2⟩, h.2⟩

/-- The buffered upper input lies in the same strip
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem output_support_strip : tsupport W.output ⊆
    Icc W.lowerEndpoint W.upperEndpoint ×ˢ univ := by
  intro x hx
  have h := W.upper_input_buffer hx
  exact ⟨⟨h.1.1, by linarith [h.1.2, W.buffer_pos]⟩, h.2⟩

/-- The actual lower operator on smooth supported fields
(`app:ch_osc:setup:osc-retarded`). -/
def lower : Test d →ₗ[ℂ] Test d :=
  lowerTest W.lowerEndpoint W.input W.output W.input_smooth W.output_smooth W.output_compact

/-- The actual upper operator, with the exchanged weights, on smooth supported
fields (`app:ch_osc:eq:retarded-literal-adjoint`). -/
def upper : Test d →ₗ[ℂ] Test d :=
  upperTest W.upperEndpoint W.input W.output W.input_smooth W.output_smooth W.input_compact

/-- Exact lower cancellation of the shared physical zero-time carrier
(`app:ch_osc:eq:osc-retarded-commute`). Identification of the actual geometric
phase with this carrier is the separate PhaseChoice obligation. -/
theorem lower_carrier_cancel (ρ : ℝ) (ζ : Euclidean d)
    (f : ℝ × (Fin d → ℝ) → ℂ) (x : ℝ × (Fin d → ℝ)) :
    carrier (-ρ) (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 x.2) *
      Retarded.lower W.lowerEndpoint W.input W.output
        (fun z ↦ carrier ρ (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 z.2) * f z) x =
      Retarded.lower W.lowerEndpoint W.input W.output f x := by
  simpa only [carrier, neg_mul, Complex.ofReal_neg, mul_neg] using
    Retarded.lower_modulation W.lowerEndpoint W.input W.output f
      (fun y ↦ ρ * inner ℝ (WithLp.toLp 2 y) ζ) x

/-- Exact upper cancellation with its original orientation and exchanged
weights (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem upper_carrier_cancel (ρ : ℝ) (ζ : Euclidean d)
    (f : ℝ × (Fin d → ℝ) → ℂ) (x : ℝ × (Fin d → ℝ)) :
    carrier (-ρ) (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 x.2) *
      Retarded.upper W.upperEndpoint W.input W.output
        (fun z ↦ carrier ρ (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 z.2) * f z) x =
      Retarded.upper W.upperEndpoint W.input W.output f x := by
  simpa only [carrier, neg_mul, Complex.ofReal_neg, mul_neg] using
    Retarded.upper_modulation W.upperEndpoint W.input W.output f
      (fun y ↦ ρ * inner ℝ (WithLp.toLp 2 y) ζ) x

/-- The supported smooth field given by the literal demodulated lower formula
in `app:ch_response:eq:fixed-factor-transfer`. Its regularity follows from exact
cancellation, so no frequency-dependent derivative bound is used. -/
def demodulatedLower (ρ : ℝ) (ζ : Euclidean d) (f : Test d) : Test d :=
  ⟨fun x ↦ carrier (-ρ) (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 x.2) *
      Retarded.lower W.lowerEndpoint W.input W.output
        (fun z ↦ carrier ρ (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 z.2) * f.val z) x,
    by
      have he := funext (W.lower_carrier_cancel ρ ζ f)
      rw [he]
      exact (W.lower f).property⟩

/-- The supported smooth field given by the literal demodulated upper formula
in `app:ch_response:eq:fixed-factor-transfer`. -/
def demodulatedUpper (ρ : ℝ) (ζ : Euclidean d) (f : Test d) : Test d :=
  ⟨fun x ↦ carrier (-ρ) (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 x.2) *
      Retarded.upper W.upperEndpoint W.input W.output
        (fun z ↦ carrier ρ (fun y ↦ inner ℝ y ζ) (WithLp.toLp 2 z.2) * f.val z) x,
    by
      have he := funext (W.upper_carrier_cancel ρ ζ f)
      rw [he]
      exact (W.upper f).property⟩

/-- Equality as supported smooth fields, before taking any norm or derivative
(`app:ch_response:eq:fixed-factor-transfer`). -/
@[simp] theorem demodulatedLower_eq (ρ : ℝ) (ζ : Euclidean d) (f : Test d) :
    W.demodulatedLower ρ ζ f = W.lower f :=
  Subtype.ext (funext (W.lower_carrier_cancel ρ ζ f))

/-- Upper equality as supported smooth fields
(`app:ch_response:eq:fixed-factor-transfer`). -/
@[simp] theorem demodulatedUpper_eq (ρ : ℝ) (ζ : Euclidean d) (f : Test d) :
    W.demodulatedUpper ρ ζ f = W.upper f :=
  Subtype.ext (funext (W.upper_carrier_cancel ρ ζ f))

/-- Demodulation retains the literal ambient adjoint pairing, including the
exchanged weights (`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem demodulated_adjoint_pairing (ρ : ℝ) (ζ : Euclidean d) (f g : Test d) :
    smoothPairing g (W.demodulatedLower ρ ζ f) =
      smoothPairing (W.demodulatedUpper ρ ζ g) f := by
  simpa only [demodulatedLower_eq, demodulatedUpper_eq, lower, upper] using
    retardedTest_adjoint_pairing W.lowerEndpoint W.upperEndpoint W.endpoints_le
      W.input W.output W.input_smooth W.output_smooth W.input_compact W.output_compact
      W.input_support_strip W.output_support_strip f g

end RetardedCutoffs
end JanetCartan.ResponseTransfer
