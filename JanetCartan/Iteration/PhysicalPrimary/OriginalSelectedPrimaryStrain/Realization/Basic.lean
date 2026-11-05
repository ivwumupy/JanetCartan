module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Quadratures
public import JanetCartan.Iteration.PhysicalPairs.OriginalMaskRows

/-! # The first-mask realization of a primary strain quadrature

Combine the actual raw derivative identity and original zero extension with
the germ of the same finite-menu phase representative. The phase and source
cutoff are unchanged on the entire source support (`main:eq:primary-strain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain

open LocalSobolev SmallSupport CorrectedAtoms ResponseSourceExtension
open PhysicalPairs.SampledMask OriginalPrimaryStrainMaskData

/-- The original local inverse input, through its one zero extension, is the
reduced plus wave at the same ordinary phase. Only the second derivative
amplitude is rotated for the imaginary quadrature. -/
theorem quadrature_realization_on_chart {d N : ℕ}
    {U W : Set (Euclidean (d+1))} (hW : MeasurableSet W)
    (F : Euclidean (d+1) → Euclidean N)
    (Z : Euclidean (d+1) → EuclideanSpace ℂ (Fin N))
    (χ η φ φext : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (u : LocalL2 W (Euclidean (d+1))) (imaginary : Bool)
    (hχU : tsupport χ ⊆ U) (hgerm : ∀ x ∈ U, φext =ᶠ[𝓝 x] φ)
    (hfactor : ∀ x ∈ tsupport χ,
      rawJacobian Z x = Complex.exp (Complex.I * (ρ * φ x : ℝ)) • D x)
    (he : zeroExtend hW u =ᵐ[volume]
      euclideanCutoffStressSource Q η
        (tensorFieldRealPart (quadratureScalar imaginary • complexAtomicSource F χ Z))) :
    zeroExtend hW u =ᵐ[volume] fun y ↦
      euclideanRealPart (reduced_wave χ η Q (twiceSourceJacobian F)
        (quadratureScalar imaginary • D) false φext ρ y) := by
  have hr := he.trans (Eventually.of_forall
    (cutoff_stress_quadrature_eq F Z χ η φ Q D ρ hfactor (quadratureScalar imaginary)))
  exact PhysicalPairs.OriginalMaskRows.measured_phase (zeroExtend hW u)
    χ φ φext _ ρ hχU hgerm hr

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
end
