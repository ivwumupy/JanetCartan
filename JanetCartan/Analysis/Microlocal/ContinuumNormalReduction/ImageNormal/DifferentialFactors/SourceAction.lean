module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.FormalAdjoint

/-!
# Unregularized source action of the image differential factors

The literal compactly supported adjoint is made into a Schwartz function,
and both actual Bessel multipliers are applied to it. The resulting inverse
Fourier integral has the source factor obtained by integration by parts in
`app:ch_background:prop:bg-frame`, Step 1. Its frequency convergence is proved
from this Schwartz realization, without a frequency cutoff or an assumed
adjoint identity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff RealInnerProductSpace FourierTransform SchwartzMap
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Source Fourier transform after the literal divergence factor has been
integrated by parts (`app:ch_background:prop:bg-frame`, Step 1). The source
field `v` includes the measurement mask when this is used in the normal. -/
def differentialAdjointSourceTransform
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ) (ξ : E) (j : J) : ℂ :=
  𝓕 (fun y ↦ ∑ i, (-Complex.I * differentialPencil A y ((2 * Real.pi) • ξ) i j +
    Z y i j) * v y i) ξ

/-- The computed source factor is the actual Fourier transform of the
literal adjoint (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem fourier_coefficientFormalAdjoint
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (ξ : E) (j : J) :
    𝓕 (fun y ↦ coefficientFormalAdjoint A Z v y j) ξ =
      differentialAdjointSourceTransform A Z v ξ j := by
  have h := integral_sourcePhase_coefficientFormalAdjoint A Z v hA hZ hv hc 0 ξ j
  simpa only [differentialAdjointSourceTransform, Real.fourier_eq, Circle.smul_def,
    smul_eq_mul, zero_sub, inner_neg_right, real_inner_comm] using h

/-- The actual adjoint test is Schwartz because it is smooth and compactly
supported, rather than because an adjoint realization is assumed
(`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientAdjointSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (j : J) : 𝓢(E, ℂ) :=
  (hasCompactSupport_coefficientFormalAdjoint A Z v hc j).toSchwartzMap
    (contDiff_coefficientFormalAdjoint A Z v hA hZ hv j)

/-- Exact realization of both Bessel factors on the actual adjoint. The
source integration is performed before the unregularized inverse Fourier
integral (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselSquared_coefficientAdjointSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (x : E) (j : J) :
    schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
        (coefficientAdjointSchwartz A Z v hA hZ hv hc j)) x =
      𝓕⁻ (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
        differentialAdjointSourceTransform A Z v ξ j) x := by
  rw [schwartzFrequencyMultiplier, SchwartzMap.fourierInv_coe,
    SchwartzMap.smulLeftCLM_apply hasTemperateGrowth_complex_imageBesselSymbol]
  apply congrArg (fun f : E → ℂ ↦ 𝓕⁻ f x)
  funext ξ
  rw [smul_eq_mul, fourier_imageBesselMultiplier]
  have hf : (𝓕 (coefficientAdjointSchwartz A Z v hA hZ hv hc j) : 𝓢(E, ℂ)) ξ =
      differentialAdjointSourceTransform A Z v ξ j :=
    fourier_coefficientFormalAdjoint A Z v hA hZ hv hc ξ j
  rw [hf, ← mul_assoc, ← Complex.ofReal_mul, imageBesselSymbol_sq]

/-- Absolute convergence in frequency for the source-tested, unregularized
`J²P*` integral. This is derived from the actual compact smooth source test,
not supplied as an extra normal-reduction premise
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_imageBesselSquared_adjointSourceTransform
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (j : J) :
    Integrable (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
      differentialAdjointSourceTransform A Z v ξ j) := by
  let w := coefficientAdjointSchwartz A Z v hA hZ hv hc j
  let t := SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
    (𝓕 (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) w))
  have ht : (t : E → ℂ) = fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
      differentialAdjointSourceTransform A Z v ξ j := by
    funext ξ
    simp only [t, SchwartzMap.smulLeftCLM_apply_apply
      hasTemperateGrowth_complex_imageBesselSymbol, smul_eq_mul, fourier_imageBesselMultiplier]
    have hf : (𝓕 w : 𝓢(E, ℂ)) ξ = differentialAdjointSourceTransform A Z v ξ j :=
      fourier_coefficientFormalAdjoint A Z v hA hZ hv hc ξ j
    rw [hf, ← mul_assoc, ← Complex.ofReal_mul, imageBesselSymbol_sq]
  rw [← ht]
  exact t.integrable


variable [Fintype J]

/-- The literal Euclidean leading composite after separating the source
commutator: `μ P χ² J J P* μ`. All differential operators and Fourier
multipliers are applied to the actual input; no normal-reduction property is
part of this definition (`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientImageNormal
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (χ μ : E → ℝ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i)) (x : E) (i : I) : ℂ :=
  (μ x : ℂ) * coefficientOperator A Z (fun z j ↦ (χ z ^ 2 : ℝ) *
    schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
        (coefficientAdjointSchwartz A Z (fun y l ↦ (μ y : ℂ) * v y l) hA hZ
          (fun l ↦ (Complex.ofRealCLM.contDiff.comp hμ).mul (hv l))
          (fun _ ↦ (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right) j)) z) x i

/-- Exact source-tested unregularized realization of `μ P χ² J² P* μ`.
Both measurement cutoffs and the source square remain literal. The remaining
output differentiation needed to obtain `differentialFullAmplitude` is a
separate step (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientImageNormal_eq_sourceTested
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (χ μ : E → ℝ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i)) (x : E) (i : I) :
    coefficientImageNormal A Z χ μ v hA hZ hμ hμc hv x i =
      (μ x : ℂ) * coefficientOperator A Z
        (fun z j ↦ (χ z ^ 2 : ℝ) *
          𝓕⁻ (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
            differentialAdjointSourceTransform A Z (fun y l ↦ (μ y : ℂ) * v y l) ξ j) z) x i := by
  unfold coefficientImageNormal
  apply congrArg ((μ x : ℂ) * ·)
  apply congrArg (fun u : E → J → ℂ ↦ coefficientOperator A Z u x i)
  funext z j
  rw [imageBesselSquared_coefficientAdjointSchwartz]

omit [Fintype J] in
/-- The source-tested frequency integrals in the actual masked composite
converge even for a merely smooth, noncompact input. The fixed measurement
mask supplies compact support (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_coefficientImageNormal_source
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (μ : E → ℝ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i)) (j : J) :
    Integrable (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
      differentialAdjointSourceTransform A Z (fun y l ↦ (μ y : ℂ) * v y l) ξ j) := by
  exact integrable_imageBesselSquared_adjointSourceTransform A Z _ hA hZ
    (fun l ↦ (Complex.ofRealCLM.contDiff.comp hμ).mul (hv l))
    (fun _ ↦ (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right) j

end JanetCartan.ContinuumNormalReduction.ImageNormal
