module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization.Tensors
/-! # Fourier integrals on carrier product tests -/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
open JanetCartan JanetCartan.CarrierSobolev JanetCartan.ContinuumRow
namespace JanetCartan.CarrierSobolev.Factorization
/-- The Fourier integral of a product splits into the Fourier integrals of its
factors in the actual Hilbert coordinates. This supplies the product-test
calculation for `app:ch_background:prop:bg-adjoint`; it includes dimension zero. -/
theorem fourierIntegral_product {n : ℕ} (g : ParameterSpace → ℂ) (c : Euclidean (n - 1) → ℂ)
    (ξ : InitialSpace n) :
    𝓕 (fun x : InitialSpace n => g x.fst * c x.snd) ξ = 𝓕 g ξ.fst * 𝓕 c ξ.snd := by
  rw [Real.fourier_eq, ← (WithLp.volume_preserving_toLp ParameterSpace
    (Euclidean (n - 1))).integral_comp (MeasurableEquiv.toLp 2 _).measurableEmbedding (fun v : InitialSpace n =>
      Real.fourierChar (-⟪v, ξ⟫) • (g v.fst * c v.snd))]
  calc
    _ = ∫ p : ParameterSpace × Euclidean (n - 1),
        (Real.fourierChar (-⟪p.1, ξ.fst⟫) • g p.1) *
          (Real.fourierChar (-⟪p.2, ξ.snd⟫) • c p.2) := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [WithLp.prod_inner_apply]
      change (Real.fourierChar (-(⟪p.1, ξ.fst⟫ + ⟪p.2, ξ.snd⟫))) •
        (g p.1 * c p.2) = _
      rw [neg_add, AddChar.map_add_eq_mul]
      simp only [Circle.smul_def, Circle.coe_mul, smul_eq_mul]
      ring
    _ = _ := by
      rw [Measure.volume_eq_prod]
      simpa only [Real.fourier_eq] using
        (integral_prod_mul (μ := (volume : Measure ParameterSpace)) (ν := volume)
          (fun z => Real.fourierChar (-⟪z, ξ.fst⟫) • g z)
          (fun y => Real.fourierChar (-⟪y, ξ.snd⟫) • c y))
end JanetCartan.CarrierSobolev.Factorization
