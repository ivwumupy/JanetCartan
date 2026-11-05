module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Transverse
/-!
# Fiberwise unitary inverse Fourier transformation

The iterated carrier L² space for `app:ch_background:prop:bg-adjoint` keeps
`z = (s,v)` as its outer variable. Applying the transverse equivalence in each
fiber gives an actual surjective linear isometry and an ordinary integral
formula whenever the transverse representatives are integrable. The separate
Fubini construction must identify this space with `ContinuumRow.CarrierL2`.
-/

open MeasureTheory
@[expose] public noncomputable section
namespace JanetCartan.CarrierSobolev
open ContinuumRow
/-- Transverse Hilbert fiber for the carrier realization in
`app:ch_background:prop:bg-adjoint`. -/
abbrev TransverseL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (Euclidean (n - 1)))
/-- Iterated L² space with the literal measure `ds dv` on the outer
carrier parameters (`app:ch_background:prop:bg-adjoint`). The Fubini isometry
must connect this space to the published product-measure carrier space. -/
abbrev IteratedCarrierL2 (n : ℕ) :=
  Lp (TransverseL2 n) 2 (volume.prod volume : Measure CarrierParameter)

/-- Apply the actual unitary radian inverse Fourier equivalence in each
transverse fiber, leaving `z` fixed (`app:ch_background:prop:bg-adjoint`). -/
def iteratedUnitaryInverse (n : ℕ) : IteratedCarrierL2 n ≃ₗᵢ[ℂ] IteratedCarrierL2 n where
  __ := (transverseUnitaryInverse n ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ
    2 (volume.prod volume)
  invFun := (transverseUnitaryInverse n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
  left_inv f := by
    apply Lp.ext
    let U := (transverseUnitaryInverse n ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    let V := (transverseUnitaryInverse n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change V.compLp (U.compLp f) =ᵐ[volume.prod volume] f
    filter_upwards [V.coeFn_compLp (U.compLp f), U.coeFn_compLp f] with z hz hz'
    rw [hz, hz']
    exact (transverseUnitaryInverse n ℂ).symm_apply_apply _
  right_inv f := by
    apply Lp.ext
    let U := (transverseUnitaryInverse n ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    let V := (transverseUnitaryInverse n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change U.compLp (V.compLp f) =ᵐ[volume.prod volume] f
    filter_upwards [U.coeFn_compLp (V.compLp f), V.coeFn_compLp f] with z hz hz'
    rw [hz, hz']
    exact (transverseUnitaryInverse n ℂ).apply_symm_apply _
  norm_map' f := by
    let U := (transverseUnitaryInverse n ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    change ‖U.compLp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.memLp _).aestronglyMeasurable
      (Lp.memLp _).aestronglyMeasurable
    filter_upwards [U.coeFn_compLp f] with z hz
    rw [hz]
    exact (transverseUnitaryInverse n ℂ).norm_map _

/-- The forward operator leaves the carrier parameter unchanged
(`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedUnitaryInverse_coeFn (n : ℕ) (f : IteratedCarrierL2 n) :
    iteratedUnitaryInverse n f =ᵐ[volume.prod volume]
      fun z => transverseUnitaryInverse n ℂ (f z) :=
  (transverseUnitaryInverse n ℂ).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

/-- The inverse operator also acts independently at each carrier parameter
(`app:ch_background:prop:bg-inverse`). -/
theorem iteratedUnitaryInverse_symm_coeFn (n : ℕ) (f : IteratedCarrierL2 n) :
    (iteratedUnitaryInverse n).symm f =ᵐ[volume.prod volume]
      fun z => (transverseUnitaryInverse n ℂ).symm (f z) :=
  (transverseUnitaryInverse n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

/-- Ordinary integral realization for integrable transverse fibers. The
partial transform on compact smooth product-space tests consumes this formula
through the Fubini identification (`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedUnitaryInverse_integral (n : ℕ) (f : IteratedCarrierL2 n)
    (hf : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      Integrable (f z : Euclidean (n - 1) → ℂ)) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (iteratedUnitaryInverse n f) z =ᵐ[volume]
        unitaryInverseIntegral (f z : Euclidean (n - 1) → ℂ) := by
  filter_upwards [iteratedUnitaryInverse_coeFn n f, hf] with z hz hi
  rw [hz]
  exact transverseUnitaryInverse_coeFn (f z) hi
/-- Fiberwise Plancherel, before integrating in the carrier parameter
(`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedUnitaryInverse_norm_ae (n : ℕ) (f : IteratedCarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      ‖(iteratedUnitaryInverse n f) z‖ = ‖f z‖ := by
  filter_upwards [iteratedUnitaryInverse_coeFn n f] with z hz
  rw [hz, transverseUnitaryInverse_norm]

/-- Plancherel on the iterated carrier space
(`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedUnitaryInverse_norm (n : ℕ) (f : IteratedCarrierL2 n) :
    ‖iteratedUnitaryInverse n f‖ = ‖f‖ :=
  (iteratedUnitaryInverse n).norm_map f

/-- Left inverse identity on the iterated carrier space
(`app:ch_background:prop:bg-inverse`). -/
theorem iteratedUnitaryInverse_symm_apply_apply (n : ℕ) (f : IteratedCarrierL2 n) :
    (iteratedUnitaryInverse n).symm (iteratedUnitaryInverse n f) = f :=
  (iteratedUnitaryInverse n).symm_apply_apply f

/-- Right inverse identity on the iterated carrier space
(`app:ch_background:prop:bg-inverse`). -/
theorem iteratedUnitaryInverse_apply_symm_apply (n : ℕ) (f : IteratedCarrierL2 n) :
    iteratedUnitaryInverse n ((iteratedUnitaryInverse n).symm f) = f :=
  (iteratedUnitaryInverse n).apply_symm_apply f

end JanetCartan.CarrierSobolev
