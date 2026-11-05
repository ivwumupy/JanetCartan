module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Limits
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Demodulation

/-!
# Reverse selected-graph derivative transfer

The reverse derivative transfer in `app:ch_response:eq:direct-envelope-profile`,
using source integration by parts from
`app:ch_regular_base:eq:actual-adjoint-trade`. The full remainder differentiates
the inverse matrix and retains both physical amplitude positions.

The selected theorems below apply the calculation to the literal `j_S U⁻¹`
amplitude, including every source/target cutoff and selector. The derivative is
first proved for actual regularized integrals from primitive local domination,
then passed through explicitly supplied distributional or strong L² limits.
`reverseGraph_literalAmplitude` identifies the full unshifted amplitude with
`FourierIntegral.weightedReverseGraph`, preserving `(2π)⁻ⁿ` normalization.

Conditional scope: `jc-compatible-phase-geometry` supplies the phase-gradient
and inverse identities; `jc-finite-fio-calculus` supplies smoothness, compact
source support, integrability, domination, and the limits of every actual graph
term. The consumer `jc-response-near-carrier` must instantiate these inputs.
No output derivative identity or Sobolev membership is assumed, and this
conditional deduction does not prove the unconditional response construction.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.ReverseDerivative

open LineDeriv

/-- The fixed-frequency derivative trade for the literal inverse weight
`j_S U⁻¹`, with every cutoff and selector retained
(`app:ch_response:eq:direct-envelope-profile`). All derivatives are actual
Fréchet coordinate derivatives. No graph-operator derivative identity is an
input. The finite-calculus and compatible-phase producers must discharge the
displayed analytic and geometric hypotheses. -/
theorem integral_selectedWeighted_output_derivative_transfer {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (q : Euclidean n → ℂ) (y δ : Euclidean n) (j : Fin n)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (f : Euclidean n → Fin r → ℂ) :
    let A := selectedWeightedAmplitude S U χs χt χg ζ ρ q
    ContDiff ℝ ∞ (fun x ↦ phaseIncrement S ζ ρ x δ) →
    (∀ l, ContDiff ℝ ∞ (fun x ↦ C x δ j l)) →
    ContDiff ℝ ∞ (fun x ↦ A y x δ) →
    (∀ x, DifferentiableAt ℝ (fun z ↦ A z x δ) y) →
    HasCompactSupport (fun x ↦ A y x δ) → ContDiff ℝ ∞ f →
    (∀ x ∈ tsupport (fun x ↦ A y x δ), C x δ * B x δ = 1) →
    (∀ x ∈ tsupport (fun x ↦ A y x δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l) →
    Integrable (fun x ↦ oscillation S ζ ρ y x δ •
      (partialDeriv (fun z ↦ A z x δ) y j).mulVec (f x)) →
    (∫ x, partialDeriv (fun z ↦ oscillation S ζ ρ z x δ • (A z x δ).mulVec (f x)) y j) =
      (∑ l, ∫ x, oscillation S ζ ρ y x δ •
        (datumAmplitude C A j l y x δ).mulVec (partialDeriv f x l)) +
      ∫ x, oscillation S ζ ρ y x δ • (remainderAmplitude C A j y x δ).mulVec (f x) :=
  integral_output_derivative_transfer S ζ ρ y δ j B C
    (selectedWeightedAmplitude S U χs χt χg ζ ρ q) f

/-- Reverse derivative transfer for distributional limits of the selected
literal inverse weight. The selector may include each compact-frequency
regularizer; all other weights and cutoffs remain in their original positions.
The actual convergence of these graphs is an input, while the weak derivative
identity is proved. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedWeightedGraph_distributional_limit_derivative {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (q : ℕ → Euclidean n → ℂ)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (f : Euclidean n → Fin r → ℂ) (j : Fin n)
    (hreg : ∀ k, TransferRegularization S ζ ρ
      (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) B C f j)
    (F R : 𝓢'(Euclidean n, Fin r → ℂ)) (D : Fin n → 𝓢'(Euclidean n, Fin r → ℂ))
    (hF : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto (fun k ↦ ∫ y, φ y •
      envelopeGraph S ζ ρ (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) f y)
      atTop (𝓝 (F φ)))
    (hR : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto (fun k ↦ ∫ y, φ y •
      envelopeGraph S ζ ρ
        (remainderAmplitude C (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) j) f y)
      atTop (𝓝 (R φ)))
    (hD : ∀ (φ : 𝓢(Euclidean n, ℂ)) l, Tendsto (fun k ↦ ∫ y, φ y •
      envelopeGraph S ζ ρ
        (datumAmplitude C (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) j l)
        (fun x ↦ partialDeriv f x l) y) atTop (𝓝 (D l φ))) :
    lineDerivOp (EuclideanSpace.single j (1 : ℝ)) F = R + ∑ l, D l :=
  envelopeGraph_distributional_limit_derivative S ζ ρ
    (fun k ↦ selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) B C f j hreg F R D hF hR hD

/-- Strong L² version for the actual selected `j_S U⁻¹` amplitude. The output
weak derivative is represented by the sum of the L² limits of the full
remainder and datum-derivative graphs, without assuming output Sobolev
membership. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedWeightedGraph_L2_limit_derivative {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (q : ℕ → Euclidean n → ℂ)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (f : Euclidean n → Fin r → ℂ) (j : Fin n)
    (hreg : ∀ k, TransferRegularization S ζ ρ
      (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) B C f j)
    (F R : Lp (Fin r → ℂ) 2 (volume : Measure (Euclidean n)))
    (D : Fin n → Lp (Fin r → ℂ) 2 (volume : Measure (Euclidean n)))
    (hmF : ∀ k, MemLp
      (envelopeGraph S ζ ρ (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) f) 2)
    (hmR : ∀ k, MemLp (envelopeGraph S ζ ρ
      (remainderAmplitude C (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) j) f) 2)
    (hmD : ∀ k l, MemLp (envelopeGraph S ζ ρ
      (datumAmplitude C (selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) j l)
      (fun x ↦ partialDeriv f x l)) 2)
    (hF : Tendsto (fun k ↦ (hmF k).toLp _) atTop (𝓝 F))
    (hR : Tendsto (fun k ↦ (hmR k).toLp _) atTop (𝓝 R))
    (hD : ∀ l, Tendsto (fun k ↦ (hmD k l).toLp _) atTop (𝓝 (D l))) :
    lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (F : 𝓢'(Euclidean n, Fin r → ℂ)) =
      (R : 𝓢'(Euclidean n, Fin r → ℂ)) + ∑ l, (D l : 𝓢'(Euclidean n, Fin r → ℂ)) :=
  envelopeGraph_L2_limit_derivative S ζ ρ
    (fun k ↦ selectedWeightedAmplitude S U χs χt χg ζ ρ (q k)) B C f j hreg F R D
    hmF hmR hmD hF hR hD

end JanetCartan.ResponseTransfer.ReverseDerivative
