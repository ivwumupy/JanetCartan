module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Literal forward carrier removal

The exact integral in `app:ch_response:eq:direct-envelope-profile` is the
demodulated selected full graph. This identity retains both physical positions,
the original cutoffs, and the physical `(2π)⁻ⁿ` normalization. The reverse
identity and the full `j_S U⁻¹` amplitude are imported from the independently
proved reverse derivative leaf.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

open FourierIntegral

/-- Exact demodulation of the literal selected forward integral. The input is
the compatible central phase equality; no operator equality or bound is an
assumption. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem demodulated_selected_graphOperator {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (q : Euclidean n → ℂ) (f : Euclidean n → Fin r → ℂ) (x : Euclidean n)
    (hcentral : S x (ρ • ζ) = ρ * φ x) :
    carrier (-ρ) φ x • graphOperator S (selectedAmplitude A ζ ρ q)
        (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • f y) x =
      graphOperator (phaseIncrement S ζ ρ) (forwardSelectedAmplitude A ζ ρ q) f x := by
  unfold graphOperator
  rw [smul_comm (carrier (-ρ) φ x)]
  congr 1
  rw [← integral_smul]
  rw [← integral_add_left_eq_self (fun η ↦ carrier (-ρ) φ x •
    ∫ y, graphOscillation S x y η •
      (selectedAmplitude A ζ ρ q x y η).mulVec
        (carrier ρ (fun z ↦ inner ℝ z ζ) y • f y)) (ρ • ζ)]
  apply integral_congr_ae
  filter_upwards [] with δ
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [forwardSelectedAmplitude, Matrix.mulVec_smul, smul_smul, ← mul_assoc]
  rw [demodulated_graphOscillation S φ ζ ρ x y δ hcentral]
  rfl

end JanetCartan.ResponseTransfer
