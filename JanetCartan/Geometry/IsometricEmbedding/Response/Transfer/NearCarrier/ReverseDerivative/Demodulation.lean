module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Regularized
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact demodulation of the selected reverse graph

The physical frequency translation in `app:ch_response:eq:direct-envelope-profile`
identifies the integral used in the weak derivative theorem with the literal
selected graph acting on a carrier-modulated datum. The compatible central
phase identity is required only on the physical source support. No convergence
or differentiation identity for the graph is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.ReverseDerivative
variable {n r : ℕ}
/-- Exact carrier removal and physical frequency translation for the selected
reverse graph (`app:ch_response:eq:direct-envelope-profile`). The central phase
identity is supplied by `jc-compatible-phase-geometry` on the source support. -/
theorem demodulated_selected_reverseGraph
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FourierIntegral.FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (q : Euclidean n → ℂ) (f : Euclidean n → Fin r → ℂ) (y : Euclidean n)
    (hc : ∀ δ, ∀ x ∈ tsupport (fun z ↦ A y z (ρ • ζ + δ)),
      S x (ρ • ζ) = ρ * φ x) :
    carrier (-ρ) (fun z ↦ inner ℝ z ζ) y •
      reverseGraph S (selectedAmplitude A ζ ρ q) (fun x ↦ carrier ρ φ x • f x) y =
      envelopeGraph S ζ ρ (fun y x δ ↦ q δ • A y x (ρ • ζ + δ)) f y := by
  unfold reverseGraph envelopeGraph
  rw [smul_comm (carrier (-ρ) (fun z ↦ inner ℝ z ζ) y)]
  congr 1
  rw [← integral_smul]
  rw [← integral_add_left_eq_self (fun η ↦ carrier (-ρ) (fun z ↦ inner ℝ z ζ) y •
    ∫ x, star (FourierIntegral.graphOscillation S x y η) •
      (selectedAmplitude A ζ ρ q y x η).mulVec (carrier ρ φ x • f x)) (ρ • ζ)]
  apply integral_congr_ae
  filter_upwards [] with δ
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport (fun z ↦ A y z (ρ • ζ + δ))
  · simp only [selectedAmplitude, add_sub_cancel_left, Matrix.smul_mulVec,
      Matrix.mulVec_smul, smul_smul]
    simp only [← mul_assoc, demodulated_reverse_oscillation S φ ζ ρ x y δ (hc δ x hx)]
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [selectedAmplitude, hz, smul_zero, Matrix.zero_mulVec]
end JanetCartan.ResponseTransfer.ReverseDerivative
