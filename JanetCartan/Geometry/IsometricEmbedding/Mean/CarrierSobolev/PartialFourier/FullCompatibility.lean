module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization

/-!
# Full Fourier action of partial unitary synthesis

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
the full Fourier transform of the actual partial radian inverse is parameter
Fourier followed by the inverse transverse normalization dilation. This
assembles the proved full Fourier factorization and transverse compatibility;
no Fourier action or analytic construction is assumed.

The initial carrier Sobolev construction consumes the exact rescaling and
the norm identities for bounded transverse operators. In particular these
apply to truncated η-weights before passing to unbounded weights. Every
statement includes transverse dimension zero.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.CarrierSobolev
open ContinuumRow
variable {n : ℕ}

/-- Under Fubini, full Fourier transformation of partial radian synthesis
is parameter Fourier applied to the inverse transverse dilation. This is the
factorization needed for the initial Sobolev transverse-weight estimate in
`app:ch_background:prop:bg-adjoint`. -/
theorem carrierFubiniEquiv_initialFourier_partialUnitaryInverse (f : CarrierL2 n) :
    carrierFubiniEquiv n (initialFourier n (partialUnitaryInverse n f)) =
      iteratedParameterFourier n
        ((iteratedTransverseDilation n).symm (carrierFubiniEquiv n f)) := by
  exact (carrierFubiniEquiv_initialFourier n _).trans
    (congrArg (iteratedParameterFourier n)
      ((congrArg (iteratedTransverseFourier n)
        (carrierFubiniEquiv_partialUnitaryInverse f)).trans
          (iteratedTransverseFourier_unitaryInverse _)))

/-- Full Fourier action on the literal product-measure carrier L² space,
with normalization applied after parameter Fourier transformation
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialFourier_partialUnitaryInverse (f : CarrierL2 n) :
    initialFourier n (partialUnitaryInverse n f) =
      (carrierFubiniEquiv n).symm ((iteratedTransverseDilation n).symm
        (iteratedParameterFourier n (carrierFubiniEquiv n f))) := by
  apply (carrierFubiniEquiv n).injective
  exact (carrierFubiniEquiv_initialFourier_partialUnitaryInverse f).trans
    ((iteratedParameterFourier_dilation_symm _).trans
      ((carrierFubiniEquiv n).apply_symm_apply _).symm)

/-- The full Fourier representative has exactly the `synthesisFactor n`
amplitude and `2π` transverse rescaling. The nested a.e. formulation does not
assume joint measurability of evaluation of an arbitrary L²-valued section
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialFourier_partialUnitaryInverse_coeFn (f : CarrierL2 n) :
    ∀ᵐ ζ ∂(volume.prod volume : Measure CarrierParameter),
      (fun ξ => initialFourier n (partialUnitaryInverse n f) (ζ, ξ)) =ᵐ[volume]
        fun ξ => synthesisFactor n •
          (iteratedParameterFourier n (carrierFubiniEquiv n f)) ζ ((2 * Real.pi) • ξ) := by
  let g := iteratedParameterFourier n (carrierFubiniEquiv n f)
  filter_upwards [carrierFubiniEquiv_symm_coeFn n ((iteratedTransverseDilation n).symm g),
    iteratedTransverseEquiv_symm_coeFn (transverseDilation n ℂ) g] with ζ hζ hd
  change (iteratedTransverseDilation n).symm g ζ =
    (transverseDilation n ℂ).symm (g ζ) at hd
  filter_upwards [hζ, transverseDilation_symm_coeFn (g ζ)] with ξ hξ hscale
  exact (congrArg (fun h : CarrierL2 n => h (ζ, ξ))
    (initialFourier_partialUnitaryInverse f)).trans
      (hξ.trans ((congrArg (fun h : TransverseL2 n => h ξ) hd).trans hscale))

/-- Undoing the transverse frequency rescaling leaves precisely parameter
Fourier transformation. This identifies the radian frequency variable used
in η-weight control for `app:ch_background:prop:bg-adjoint`. -/
theorem initialFourier_partialUnitaryInverse_rescaled (f : CarrierL2 n) :
    iteratedTransverseDilation n
        (carrierFubiniEquiv n (initialFourier n (partialUnitaryInverse n f))) =
      iteratedParameterFourier n (carrierFubiniEquiv n f) := by
  exact (congrArg (iteratedTransverseDilation n)
    ((carrierFubiniEquiv_initialFourier_partialUnitaryInverse f).trans
      (iteratedParameterFourier_dilation_symm _))).trans
        ((iteratedTransverseDilation n).apply_symm_apply _)

/-- A bounded transverse operator has the same L² norm before and after
parameter Fourier transformation in the full synthesis formula. Bounded
frequency weights are a special case, consumed by the parent's initial
Sobolev estimate (`app:ch_background:prop:bg-adjoint`). -/
theorem initialFourier_partialUnitaryInverse_compLp_norm
    (L : TransverseL2 n →L[ℂ] TransverseL2 n) (f : CarrierL2 n) :
    ‖L.compLp (carrierFubiniEquiv n (initialFourier n (partialUnitaryInverse n f)))‖ =
      ‖L.compLp ((iteratedTransverseDilation n).symm (carrierFubiniEquiv n f))‖ := by
  exact (congrArg (fun g : IteratedCarrierL2 n => ‖L.compLp g‖)
    (carrierFubiniEquiv_initialFourier_partialUnitaryInverse f)).trans
      (iteratedParameterFourier_compLp_norm L _)

/-- After restoring the radian transverse frequency, every bounded
transverse operator has exactly its norm on the original carrier datum.
This supplies truncated η-weight Plancherel for the initial carrier Sobolev
construction (`app:ch_background:prop:bg-adjoint`). -/
theorem initialFourier_partialUnitaryInverse_rescaled_compLp_norm
    (L : TransverseL2 n →L[ℂ] TransverseL2 n) (f : CarrierL2 n) :
    ‖L.compLp (iteratedTransverseDilation n
      (carrierFubiniEquiv n (initialFourier n (partialUnitaryInverse n f))))‖ =
      ‖L.compLp (carrierFubiniEquiv n f)‖ := by
  rw [initialFourier_partialUnitaryInverse_rescaled f]
  exact iteratedParameterFourier_compLp_norm L _

end JanetCartan.CarrierSobolev
