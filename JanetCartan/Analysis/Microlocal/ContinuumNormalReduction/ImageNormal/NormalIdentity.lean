module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image

/-!
# The exact cut-off image normal

The algebraic starting point of `app:ch_background:prop:bg-frame`, Step 1.
The abstract identity is instantiated with the constructed continuum-row
realization of `P_G J`. No bounded L² realization of the first-order factor
`P_G` alone is assumed. The source square stays between that realization and
its literal adjoint. This leaf does not assert a pseudodifferential reduction
or an error estimate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

open ContinuumRow
variable {n : ℕ}

/-- Multiplying the same real source cutoff twice gives its actual square,
used in the image normal of `app:ch_background:prop:bg-frame`, Step 1. -/
theorem cutoffMultiplier_comp_self (χ : C(Torus n, ℝ)) :
    (cutoffMultiplier χ).comp (cutoffMultiplier χ) = cutoffMultiplier (χ * χ) := by
  ext1 f
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn χ (cutoffMultiplier χ f),
    cutoffMultiplier_coeFn χ f, cutoffMultiplier_coeFn (χ * χ) f] with x h₁ h₂ h₃
  change (cutoffMultiplier χ (cutoffMultiplier χ f)) x = (cutoffMultiplier (χ * χ) f) x
  rw [h₁, h₂, h₃, smul_smul]
  rfl

/-- The image-channel normal with both measurement cutoffs and the source
square in their literal positions (`app:ch_background:prop:bg-frame`, Step 1).
The only operator input is the bounded realization `B = P_G J`. -/
theorem cutoffImage_normal (B : OutputL2 n →L[ℝ] OutputL2 n)
    (χmeas χsrc : C(Torus n, ℝ)) :
    let A := (cutoffMultiplier χmeas).comp (B.comp (cutoffMultiplier χsrc))
    A.comp A.adjoint = (cutoffMultiplier χmeas).comp
      (B.comp ((cutoffMultiplier (χsrc * χsrc)).comp
        (B.adjoint.comp (cutoffMultiplier χmeas)))) := by
  dsimp only
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    cutoffMultiplier_adjoint, cutoffMultiplier_adjoint]
  ext1 f
  change cutoffMultiplier χmeas (B (cutoffMultiplier χsrc
    (cutoffMultiplier χsrc (B.adjoint (cutoffMultiplier χmeas f))))) = _
  exact congrArg (fun v ↦ cutoffMultiplier χmeas (B v))
    (DFunLike.congr_fun (cutoffMultiplier_comp_self χsrc)
      (B.adjoint (cutoffMultiplier χmeas f)))


/-- The source-square commutator of the self-adjoint inverse multiplier is
skew-adjoint (`app:ch_background:prop:bg-frame`, Step 1). This identifies the
literal adjoint before any regularity estimate is used. -/
theorem sourceSquareCommutator_adjoint (J : OutputL2 n →L[ℝ] OutputL2 n)
    (hJ : J.adjoint = J) (χsrc : C(Torus n, ℝ)) :
    (J.comp (cutoffMultiplier (χsrc * χsrc)) -
      (cutoffMultiplier (χsrc * χsrc)).comp J).adjoint =
      -(J.comp (cutoffMultiplier (χsrc * χsrc)) -
        (cutoffMultiplier (χsrc * χsrc)).comp J) := by
  simp only [map_sub, ContinuousLinearMap.adjoint_comp,
    cutoffMultiplier_adjoint, hJ, neg_sub]

/-- The actual continuum-row image channel has the literal source-square
normal. The bounded `P J` factor is constructed using the H¹-valued Bessel
lift, discharging the realization premise of `cutoffImage_normal`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageChannel_normal
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    (imageChannel c χmeas χsrc).comp (imageChannel c χmeas χsrc).adjoint =
      (cutoffMultiplier χmeas).comp
        ((reducedWeakOperator c ∘L periodicBesselLift).comp
          ((cutoffMultiplier (χsrc * χsrc)).comp
            ((reducedWeakOperator c ∘L periodicBesselLift).adjoint.comp
              (cutoffMultiplier χmeas)))) := by
  simpa only [imageChannel, ContinuousLinearMap.comp_assoc] using
    cutoffImage_normal (reducedWeakOperator c ∘L periodicBesselLift) χmeas χsrc

/-- The source-square commutator of the actual periodic inverse is
skew-adjoint. Self-adjointness is supplied by the constructed Fourier
multiplier, without an extra analytic premise
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem periodicBesselSourceSquareCommutator_adjoint (χsrc : C(Torus n, ℝ)) :
    (periodicBesselInverse.comp (cutoffMultiplier (χsrc * χsrc)) -
      (cutoffMultiplier (χsrc * χsrc)).comp periodicBesselInverse).adjoint =
      -(periodicBesselInverse.comp (cutoffMultiplier (χsrc * χsrc)) -
        (cutoffMultiplier (χsrc * χsrc)).comp periodicBesselInverse) :=
  sourceSquareCommutator_adjoint periodicBesselInverse periodicBesselInverse_adjoint χsrc

end JanetCartan.ContinuumNormalReduction.ImageNormal
