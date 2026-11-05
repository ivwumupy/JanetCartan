module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.Synthesis
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.TransverseWeight

/-!
# Raw Sobolev inputs for the literal density synthesis

The shared full raw norm controls the transverse weight on the very same
Lebesgue L² classes. This supplies the domain of the unbounded density symbol
and proves the complete order-zero density estimate in
`app:ch_background:eq:bg-density-adjoint`. It also supplies the full-norm
version of the raw cutoff estimate following `app:ch_background:defn:bg-mixed`.
No mixed-jet approximation or inverse estimate is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow RawCutoffBounds CarrierSobolev
variable {n : ℕ}

/-- The density multiplier and raw scale use literally the same transverse
weight (`app:ch_background:defn:bg-mixed`). -/
theorem etaBesselWeight_eq_transverseBesselWeight (s : ℕ) :
    etaBesselWeight (n := n) s = transverseBesselWeight s := rfl

/-- Full raw regularity supplies the actual weighted multiplier domain,
without a separate integrability premise (`app:ch_background:eq:bg-density-adjoint`). -/
theorem carrierWeightedMem_etaBesselWeight_of_rawSobolev {s : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev s f) : CarrierWeightedMem (etaBesselWeight s) f :=
  hf.carrierWeightedMem_transverseBesselWeight

/-- The full shared raw norm dominates the multiplier's transverse weighted
norm with constant one (`app:ch_background:defn:bg-mixed`). -/
theorem carrierWeightedNorm_etaBesselWeight_le_rawSobolevNorm {s : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev s f) :
    carrierWeightedNorm (etaBesselWeight s) f
      (carrierWeightedMem_etaBesselWeight_of_rawSobolev hf) ≤ rawSobolevNorm s f :=
  carrierWeightedNorm_transverseBesselWeight_le hf

/-- The actual squared-cutoff tail is controlled by the full raw norm on
its actual domain, for the estimate following `app:ch_background:defn:bg-mixed`.
This uses no identification with auxiliary torus data. -/
theorem carrierSquaredCutoff_tail_of_rawSobolev {K : ℝ} (hK : 1 ≤ K) (s : ℕ)
    (m : Lp ℝ ∞ (carrierMeasure n)) (f : CarrierL2 n)
    (hm : ∀ᵐ x ∂carrierMeasure n, m x ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ᵐ x ∂carrierMeasure n, f x ≠ 0 → ‖x.2‖ ≤ K → m x = 1)
    (hf : MemRawSobolev s f) :
    ‖f - carrierSquaredCutoff m f‖ ≤ (K ^ s)⁻¹ * rawSobolevNorm s f := by
  exact (carrierSquaredCutoff_tail hK s m f hm hone (etaBesselWeight s)
    (carrierWeightedMem_etaBesselWeight_of_rawSobolev hf)
    (Filter.Eventually.of_forall fun _ ↦ le_rfl)).trans
      (mul_le_mul_of_nonneg_left
        (carrierWeightedNorm_etaBesselWeight_le_rawSobolevNorm hf) (by positivity))

section FixedMask
variable {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
  (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
  {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
  (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)

/-- The complex full-frequency synthesis has the required raw order-one to
physical order-zero bound (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densitySynthesisL2_le_rawSobolevNorm (f : CarrierL2 n)
    (hf : MemRawSobolev 1 f) :
    ‖densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 f
      (carrierWeightedMem_etaBesselWeight_of_rawSobolev hf)‖ ≤ M * rawSobolevNorm 1 f :=
  (norm_densitySynthesisL2_le hρmeas hχmeas hM hρ hχ hχ0 f _).trans
    (mul_le_mul_of_nonneg_left (carrierWeightedNorm_etaBesselWeight_le_rawSobolevNorm hf) hM)

/-- Before the physical cutoff, the real density has the complete order-zero
bound from the shared full raw norm (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densityUncutL2_le_rawSobolevNorm (f : CarrierL2 n)
    (hf : MemRawSobolev 1 f) :
    ‖densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 f
      (carrierWeightedMem_etaBesselWeight_of_rawSobolev hf)‖ ≤
        (2 * M) * rawSobolevNorm 1 f :=
  (norm_densityUncutL2_le hρmeas hχmeas hM hρ hχ hχ0 f _).trans
    (mul_le_mul_of_nonneg_left
      (carrierWeightedNorm_etaBesselWeight_le_rawSobolevNorm hf) (by positivity))

/-- The full physical density satisfies the complete order-zero estimate,
including the fixed mask and exact factor two
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densityOutputL2_le_rawSobolevNorm (m : Lp ℝ ∞ (carrierMeasure n))
    {B : ℝ} (hB : 0 ≤ B) (hm : ∀ᵐ x ∂carrierMeasure n, |m x| ≤ B)
    (f : CarrierL2 n) (hf : MemRawSobolev 1 f) :
    ‖densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m f
      (carrierWeightedMem_etaBesselWeight_of_rawSobolev hf)‖ ≤
        (2 * B * M) * rawSobolevNorm 1 f :=
  (norm_densityOutputL2_le hρmeas hχmeas hM hρ hχ hχ0 m hB hm f _).trans
    (mul_le_mul_of_nonneg_left
      (carrierWeightedNorm_etaBesselWeight_le_rawSobolevNorm hf) (by positivity))

end FixedMask
end JanetCartan.ContinuumAdjoint.DensityMultiplier
