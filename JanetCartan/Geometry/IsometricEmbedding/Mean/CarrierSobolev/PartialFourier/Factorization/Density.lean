module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization.Tensors

/-!
# Density of carrier product tests

This leaf reduces the full Fourier factorization in
`app:ch_background:prop:bg-adjoint` to its action on scalar products.
-/

set_option maxHeartbeats 1000000

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal
namespace JanetCartan.CarrierSobolev
open ContinuumRow
namespace Factorization
variable {n : ℕ}

/-- Every outer simple-function generator is a product test, supplying the
L² density step for `app:ch_background:prop:bg-adjoint`. -/
theorem tensor_indicator (c : TransverseL2 n) {s : Set ParameterSpace}
    (hs : MeasurableSet s) (hμs : volume s ≠ ∞) :
    tensor n c (indicatorConstLp 2 hs hμs (1 : ℂ)) = indicatorConstLp 2 hs hμs c := by
  classical
  apply Lp.ext
  filter_upwards [tensor_coeFn c (indicatorConstLp 2 hs hμs (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c)] with z ht h₁ h₂
  rw [ht, h₁, h₂]
  by_cases hz : z ∈ s <;> simp [hz]

/-- Equality of continuous linear operators on all carrier product tests
implies equality on every carrier L² datum. This discharges the density
obligation in the Fourier factorization (`app:ch_background:prop:bg-adjoint`). -/
theorem ext_of_carrierTensor (L M : CarrierL2 n →L[ℂ] IteratedCarrierL2 n)
    (h : ∀ (c : TransverseL2 n) (g : Lp ℂ 2 (volume : Measure ParameterSpace)),
      L (carrierTensor n c g) = M (carrierTensor n c g)) (f : CarrierL2 n) : L f = M f := by
  let e := (carrierFubiniEquiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (parameterL2Equiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he : ∀ u, L (e u) = M (e u) := by
    intro u
    refine Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun u => L (e u) = M (e u)) ?_ ?_ ?_ u
    · intro c s hs hμs
      change L (e (indicatorConstLp 2 hs hμs.ne c)) =
        M (e (indicatorConstLp 2 hs hμs.ne c))
      rw [← tensor_indicator c hs hμs.ne]
      exact h c (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
    · intro u v hu hv huv h₁ h₂
      simp only [map_add, h₁, h₂]
    · exact isClosed_eq (L.continuous.comp e.continuous) (M.continuous.comp e.continuous)
  simpa only [e, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.symm_apply_apply] using he (parameterL2Equiv n (carrierFubiniEquiv n f))

end Factorization
end JanetCartan.CarrierSobolev
