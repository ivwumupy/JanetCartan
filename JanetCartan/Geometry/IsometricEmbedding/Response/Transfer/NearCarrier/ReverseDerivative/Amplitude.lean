module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.SourceIntegration
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Full matrix amplitudes in the reverse derivative trade

The product rule needed for `app:ch_response:eq:direct-envelope-profile` keeps
matrix derivatives in the Frobenius norm. In particular it applies to the full
weighted inverse amplitude, not merely its scalar principal symbol.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.ReverseDerivative

variable {n r : ℕ}

/-- Matrix action as a continuous real bilinear map, used by the product rule
in `app:ch_regular_base:eq:actual-adjoint-trade`. The matrix norm is Frobenius. -/
def matrixAction : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) :=
  (Matrix.mulVecBilin ℝ ℝ).toContinuousBilinearMap

/-- The full matrix/datum product rule for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem partialDeriv_matrix_mulVec
    (A : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (f : Euclidean n → Fin r → ℂ)
    (x : Euclidean n) (l : Fin n)
    (hA : DifferentiableAt ℝ A x) (hf : DifferentiableAt ℝ f x) :
    partialDeriv (fun z ↦ (A z).mulVec (f z)) x l =
      (A x).mulVec (partialDeriv f x l) + (partialDeriv A x l).mulVec (f x) := by
  exact congrArg (fun L : Euclidean n →L[ℝ] (Fin r → ℂ) ↦
    L (EuclideanSpace.single l 1)) (matrixAction.fderiv_of_bilinear hA hf)

/-- Compact support is supplied by the literal matrix amplitude, with no
support restriction on the datum (`app:ch_response:eq:direct-envelope-profile`). -/
theorem hasCompactSupport_matrix_mulVec
    (A : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (f : Euclidean n → Fin r → ℂ)
    (hA : HasCompactSupport A) : HasCompactSupport (fun x ↦ (A x).mulVec (f x)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hA ⊢
  exact hA.mono fun x hx ↦ by simp only [Pi.zero_apply] at hx ⊢; rw [hx, Matrix.zero_mulVec]

/-- The source derivative in the integration-by-parts identity splits into
the datum-derivative amplitude and its full divergence. The inverse matrix
derivative is retained inside `partialDeriv (datumAmplitude ...)`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem integral_oscillation_matrix_frequency
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y δ : Euclidean n) (j : Fin n)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (hS : ContDiff ℝ ∞ (fun x ↦ phaseIncrement S ζ ρ x δ))
    (hC : ∀ l, ContDiff ℝ ∞ (fun x ↦ C x δ j l))
    (hA : ContDiff ℝ ∞ (fun x ↦ A y x δ))
    (hAs : HasCompactSupport (fun x ↦ A y x δ)) (hf : ContDiff ℝ ∞ f)
    (hCB : ∀ x ∈ tsupport (fun x ↦ A y x δ), C x δ * B x δ = 1)
    (hgrad : ∀ x ∈ tsupport (fun x ↦ A y x δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l) :
    (∫ x, (oscillation S ζ ρ y x δ * Complex.I * (δ j : ℂ)) • (A y x δ).mulVec (f x)) =
      ∑ l, ∫ x, oscillation S ζ ρ y x δ •
        ((datumAmplitude C A j l y x δ).mulVec (partialDeriv f x l) +
          (partialDeriv (fun z ↦ datumAmplitude C A j l y z δ) x l).mulVec (f x)) := by
  have hg : ContDiff ℝ ∞ (fun x ↦ (A y x δ).mulVec (f x)) :=
    (matrixAction.contDiff.comp hA).clm_apply hf
  have hsupport : tsupport (fun x ↦ (A y x δ).mulVec (f x)) ⊆
      tsupport (fun x ↦ A y x δ) := by
    apply closure_mono
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
    rw [hx, Matrix.zero_mulVec]
  have h := integral_oscillation_frequency_smul S ζ ρ y δ j
    (fun x ↦ B x δ) (fun x ↦ C x δ) (fun x ↦ (A y x δ).mulVec (f x)) hS hC hg
    (hasCompactSupport_matrix_mulVec _ _ hAs)
    (fun x hx ↦ hCB x (hsupport hx)) (fun x hx ↦ hgrad x (hsupport hx))
  rw [h]
  apply Finset.sum_congr rfl
  intro l _
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp only [← Matrix.smul_mulVec]
  exact partialDeriv_matrix_mulVec _ f x l
    (((Complex.ofRealCLM.contDiff.comp (hC l)).smul hA).differentiable (by simp) x)
    (hf.differentiable (by simp) x)

end JanetCartan.ResponseTransfer.ReverseDerivative
