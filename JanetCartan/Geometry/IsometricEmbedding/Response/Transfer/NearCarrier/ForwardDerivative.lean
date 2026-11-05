module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Limits

/-!
# Forward weak derivative transfer for the selected graph

This module proves the conditional forward derivative step in
`app:ch_response:thm:response-literal-transfer`, feeding
`app:ch_response:eq:direct-envelope-profile`. It retains the full two-position
amplitude, source weights and selector, uses physical covectors and Euclidean
volume, and preserves `FourierIntegral.graphOperator`'s `(2π)⁻ⁿ` normalization.

The actual analytic inputs remain the responsibility of `jc-finite-fio-calculus`
and `jc-compatible-phase-geometry`: the phase derivative identity, smoothness,
compact source support, primitive integral domination and integrability, and
convergence of each literal regularized graph. `jc-response-near-carrier` must
instantiate these inputs. The theorems neither construct those limits nor assume
output Sobolev membership. `forwardGraph_L2_limit_derivative` provides the strong
L² version of the distributional limit theorem specialized below.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer
open FourierIntegral LineDeriv
variable {n r : ℕ}

/-- The selector in shifted physical covectors multiplies the unchanged full
amplitude, as in `app:ch_response:thm:response-literal-transfer`. A frequency
regularizer can be included in `q` without changing any physical source weight. -/
theorem forwardSelectedAmplitude_apply (A : FullAmplitude n r) (ζ : Euclidean n)
    (ρ : ℝ) (q : Euclidean n → ℂ) (x y δ : Euclidean n) :
    forwardSelectedAmplitude A ζ ρ q x y δ = q δ • A x y (ρ • ζ + δ) := by
  simp [forwardSelectedAmplitude, selectedAmplitude]

/-- Forward derivative transfer for actual distributional limits of the selected,
shifted graph. The datum-derivative amplitudes are `Bⱼₗ A`; the remainder is
`∂ₓⱼ A + Σₗ Bⱼₗ ∂ᵧₗ A`, where `A` is the complete selected amplitude at each
regularization. Every convergence premise refers to its displayed literal graph.
Source: `app:ch_response:thm:response-literal-transfer`, forward paragraph. -/
theorem selectedForwardGraph_distributional_limit_derivative
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ζ : Euclidean n) (ρ : ℝ) (q : ℕ → Euclidean n → ℂ)
    (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (u : Euclidean n → Fin r → ℂ) (j : Fin n)
    (hreg : ∀ k, ForwardTransferRegularization (phaseIncrement S ζ ρ)
      (forwardSelectedAmplitude A ζ ρ (q k)) B u j)
    (F R : 𝓢'(Euclidean n, Fin r → ℂ)) (D : Fin n → 𝓢'(Euclidean n, Fin r → ℂ))
    (hF : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto (fun k ↦ ∫ x, φ x •
      graphOperator (phaseIncrement S ζ ρ) (forwardSelectedAmplitude A ζ ρ (q k)) u x)
      atTop (𝓝 (F φ)))
    (hR : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto (fun k ↦ ∫ x, φ x •
      graphOperator (phaseIncrement S ζ ρ)
        (forwardRemainderAmplitude B (forwardSelectedAmplitude A ζ ρ (q k)) j) u x)
      atTop (𝓝 (R φ)))
    (hD : ∀ (φ : 𝓢(Euclidean n, ℂ)) l, Tendsto (fun k ↦ ∫ x, φ x •
      graphOperator (phaseIncrement S ζ ρ)
        (forwardDatumAmplitude B (forwardSelectedAmplitude A ζ ρ (q k)) j l)
        (fun y ↦ partialDeriv u y l) x) atTop (𝓝 (D l φ))) :
    lineDerivOp (EuclideanSpace.single j (1 : ℝ)) F = R + ∑ l, D l :=
  forwardGraph_distributional_limit_derivative (phaseIncrement S ζ ρ)
    (fun k ↦ forwardSelectedAmplitude A ζ ρ (q k)) B u j hreg F R D hF hR hD

end JanetCartan.ResponseTransfer
