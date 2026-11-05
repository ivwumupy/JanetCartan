module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Fubini.Surjective

/-!
# The carrier L² Fubini equivalence

The actual identification of product-measure carrier L² with L²-valued L²
sections, for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse`. The construction proves measurability,
the Fubini norm identity and surjectivity. Both representative formulas are
nested almost-everywhere statements; no joint measurability of the evaluation
of an arbitrary iterated representative is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace JanetCartan.CarrierSobolev
open ContinuumRow

/-- Actual complex linear isometric Fubini equivalence, used to conjugate the
fiberwise unitary Fourier transform in `app:ch_background:prop:bg-adjoint`.
Surjectivity is proved by explicit indicator preimages and L² density. -/
def carrierFubiniEquiv (n : ℕ) : CarrierL2 n ≃ₗᵢ[ℂ] IteratedCarrierL2 n :=
  LinearIsometryEquiv.ofSurjective (Fubini.linearIsometry n)
    (Fubini.linearIsometry_surjective n)

/-- Forward representative formula in the precise nested a.e. sense required
by the partial Fourier integral formula (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierFubiniEquiv_coeFn (n : ℕ) (f : CarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (carrierFubiniEquiv n f) z =ᵐ[volume] fun η => f (z, η) :=
  Fubini.toIterated_coeFn_coeFn f

/-- Inverse representative formula. It requires no jointly measurable
representative for the iterated input (`app:ch_background:prop:bg-inverse`). -/
theorem carrierFubiniEquiv_symm_coeFn (n : ℕ) (g : IteratedCarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun η => ((carrierFubiniEquiv n).symm g) (z, η)) =ᵐ[volume] g z := by
  have h := carrierFubiniEquiv_coeFn n ((carrierFubiniEquiv n).symm g)
  rw [(carrierFubiniEquiv n).apply_symm_apply] at h
  exact h.mono fun _ hz => hz.symm

/-- Forward formula for any product-space L² representative, in particular
compact smooth tests (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierFubiniEquiv_toLp_coeFn {n : ℕ} {f : CarrierVariable n → ℂ}
    (hf : MemLp f 2 (carrierMeasure n)) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (carrierFubiniEquiv n (hf.toLp f)) z =ᵐ[volume] fun η => f (z, η) := by
  filter_upwards [carrierFubiniEquiv_coeFn n (hf.toLp f),
    ae_ae_of_ae_prod hf.coeFn_toLp] with z hz hfz
  exact hz.trans hfz

/-- The carrier Fubini norm identity (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierFubiniEquiv_norm (n : ℕ) (f : CarrierL2 n) :
    ‖carrierFubiniEquiv n f‖ = ‖f‖ :=
  (carrierFubiniEquiv n).norm_map f

/-- Squared L² Fubini identity, displaying the outer integral explicitly
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierFubiniEquiv_integral_norm_sq (n : ℕ) (f : CarrierL2 n) :
    (∫ z, ‖(carrierFubiniEquiv n f) z‖ ^ 2 ∂volume.prod volume) =
      ∫ p, ‖f p‖ ^ 2 ∂carrierMeasure n := by
  rw [← Fubini.norm_sq, ← Fubini.norm_sq, carrierFubiniEquiv_norm]

/-- All slices of compact continuous tests belong to transverse L², with no
positive-dimension restriction. Compact smooth product-space tests consumed by
the partial Fourier formula satisfy these hypotheses
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrier_memLp_slice_of_continuous_hasCompactSupport {n : ℕ}
    {f : CarrierVariable n → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (z : CarrierParameter) : MemLp (fun η => f (z, η)) 2 volume :=
  Fubini.memLp_slice_of_continuous_hasCompactSupport hf hc z

end JanetCartan.CarrierSobolev
