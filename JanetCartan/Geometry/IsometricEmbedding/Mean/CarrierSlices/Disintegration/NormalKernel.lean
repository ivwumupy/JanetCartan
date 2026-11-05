module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration.Adjoint
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Action

/-!
# The actual finite-band carrier normal kernel

The forward AE formula for `app:ch_background:eq:bg-T` and the compact kernel
bounds determine the actual Hilbert adjoint, hence the actual normal. The literal
matrix calculation and its Fubini estimates are reused from `TransportKernel`;
in particular, `TransportKernel.integrable_carrierNormalDensity` proves absolute
integrability of every density at every pair of output positions.

The resulting formula is consumed by the square-partition normal assembly in
`app:ch_waves:eq:sampling-prefix-normal`. No adjoint or normal formula is an input.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}

/-- Every entry of the matrix normal applied to an L² output is integrable.
This supplies the finite sum exchange in `carrier_normal_ae_eq_matrix_integral`
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_carrierNormal_matrix_entry_mul (h : FiniteCarrierKernelBounds d m)
    (w : ComplexOutputL2 n) (x : Torus n) (i j : Fin n) :
    Integrable (fun y ↦ (∫ u, carrierNormalDensity d m x y i j u ∂carrierMeasure n) *
      w y j) volume := by
  have hw : Integrable (fun y ↦ w y j) volume :=
    ((Lp.memLp w).integrable (by norm_num)).eval_piLp j
  simpa only [integral_mul_const] using
    (TransportKernel.integrable_carrierNormalDensity_mul h x i j hw).integral_prod_left

/-- The full matrix integrand for the actual finite-band normal is integrable
for every output position and component (`app:ch_waves:eq:sampling-prefix-normal`).
This is the integrability needed by the downstream square-partition assembly. -/
theorem integrable_carrierNormal_matrix_action (h : FiniteCarrierKernelBounds d m)
    (w : ComplexOutputL2 n) (x : Torus n) (i : Fin n) :
    Integrable (fun y ↦ ∑ j : Fin n,
      (∫ u, carrierNormalDensity d m x y i j u ∂carrierMeasure n) * w y j) volume :=
  integrable_finsetSum _ (fun j _ ↦ integrable_carrierNormal_matrix_entry_mul h w x i j)

/-- The actual Hilbert normal of the finite-band channel has its literal matrix
kernel (`app:ch_background:eq:bg-T`, `app:ch_waves:eq:sampling-prefix-normal`).
Only the forward AE formula and finite-band bounds are assumed. The adjoint
formula is derived by `carrier_adjoint_ae_eq_integral`, and all integral exchanges
follow from the bounds. -/
theorem carrier_normal_ae_eq_matrix_integral (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (h : FiniteCarrierKernelBounds d m)
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ f, (T f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
      regularizedCarrierIntegral d m f) (w : ComplexOutputL2 n) :
    ∀ᵐ x ∂volume, ∀ i : Fin n, ((T ∘L T.adjoint) w) x i =
      ∫ y, ∑ j : Fin n,
        (∫ u, carrierNormalDensity d m x y i j u ∂carrierMeasure n) * w y j := by
  have hAdj : (T.adjoint w : CarrierVariable n → ℂ) =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) * carrierAdjointIntegral d w u := by
    filter_upwards [carrier_adjoint_ae_eq_integral d m h T hT w] with u hu
    exact hu.trans (TransportKernel.masked_adjoint_integral w u).symm
  filter_upwards [TransportKernel.carrierHilbertNormal_eq_matrix h T hT w hAdj] with x hx
  intro i
  change T (T.adjoint w) x i = _
  rw [hx i]
  simp only [TransportKernel.regularizedNormalEntry_eq_integral_carrierNormalDensity]
  exact (integral_finsetSum Finset.univ
    (fun j _ ↦ integrable_carrierNormal_matrix_entry_mul h w x i j)).symm

end JanetCartan.ContinuumRow
