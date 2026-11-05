module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.CompactMasks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Carrier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Multiplication

/-!
# Compact physical multiplication on the shared Sobolev levels

The fixed physical cutoff in `app:ch_background:eq:bg-density-adjoint` acts
boundedly on every integer physical Sobolev level. We transport the existing
Euclidean distributional product rule and integer multiplier estimate through
the full ordered coordinate chart, which retains all `3 + (n - 1)` directions.
Compact support produces the finite derivative bounds; output membership is
a conclusion. The transported operator is the literal `carrierMultiplier`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev Pseudodifferential IsometricEmbedding.Reconstruction

variable {n : ℕ}

private theorem exists_localizedScalarProduct_sobolev_bound {d : ℕ} (s : ℕ)
    (c : EuclideanSpace ℝ (Fin d) → ℂ) (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      MemFourierSobolev (s : ℝ) u →
      MemFourierSobolev (s : ℝ) (localizedScalarProduct c hc hcs u) ∧
        fourierSobolevNorm (s : ℝ) (localizedScalarProduct c hc hcs u) ≤
          C * fourierSobolevNorm (s : ℝ) u := by
  obtain ⟨B, hB, hb⟩ := hcs.exists_bound_iteratedFDeriv hc s
  refine ⟨localizedMultiplierConstant d s * ((s + 1 : ℕ) : ℝ) * B,
    mul_nonneg (mul_nonneg (localizedMultiplierConstant_pos d s).le (by positivity)) hB, ?_⟩
  intro u hu
  obtain ⟨hmem, hnorm⟩ := localizedScalarProduct_frechet_bound s c hc hcs
    (fun _ ↦ B) (fun _ ↦ hB) hb u hu
  refine ⟨hmem, hnorm.trans ?_⟩
  have hsum : mixedAmplitudeSobolevSum s (fun _ ↦ B) u ≤
      ((s + 1 : ℕ) : ℝ) * B * fourierSobolevNorm (s : ℝ) u := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (s + 1), B * fourierSobolevNorm (s : ℝ) u := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left (fourierSobolevNorm_mono hu ?_) hB
        exact_mod_cast (show k ≤ s by have := Finset.mem_range.mp hk; omega)
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ localizedMultiplierConstant d s *
        (((s + 1 : ℕ) : ℝ) * B * fourierSobolevNorm (s : ℝ) u) :=
      mul_le_mul_of_nonneg_left hsum (localizedMultiplierConstant_pos d s).le
    _ = _ := by ring

/-- Multiplication by a fixed real smooth compact physical mask preserves and
is bounded on every shared integer Sobolev level, including order zero and all
`3 + (n - 1)` physical coordinates. The constant is chosen before the datum.
This supplies the physical cutoff factor in
`app:ch_background:eq:bg-density-adjoint`; the weak product rule and compact
derivative bounds discharge all analytic premises. -/
theorem exists_compactPhysicalMultiplier_sobolev_bound (s : ℕ)
    (χ : CarrierVariable n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    let m := (hχ.continuous.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).toLp χ
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : CarrierL2 n, MemPhysicalSobolev s u →
      MemPhysicalSobolev s (RawCutoffBounds.carrierMultiplier m u) ∧
        physicalSobolevNorm s (RawCutoffBounds.carrierMultiplier m u) ≤
          C * physicalSobolevNorm s u := by
  let m := (hχ.continuous.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).toLp χ
  let e := (initialCoordinatesLinear n).trans (flatInitialEquiv n).toContinuousLinearEquiv
  let c : EuclideanSpace ℝ (Fin (3 + (n - 1))) → ℂ := fun x ↦ (χ (e.symm x) : ℂ)
  have hcsmooth : ContDiff ℝ ∞ c :=
    (Complex.ofRealCLM.contDiff.comp hχ).comp e.symm.contDiff
  have hcsupport : HasCompactSupport c :=
    (hc.comp_left Complex.ofReal_zero).comp_homeomorph e.symm.toHomeomorph
  obtain ⟨C, hC, hbound⟩ :=
    exists_localizedScalarProduct_sobolev_bound s c hcsmooth hcsupport
  refine ⟨(2 * Real.pi) ^ s * C, mul_nonneg (by positivity) hC, ?_⟩
  intro u hu
  have he : flatInitialL2Equiv n (RawCutoffBounds.carrierMultiplier m u) =
      localizedScalarProduct c hcsmooth hcsupport (flatInitialL2Equiv n u) := by
    apply Lp.ext
    filter_upwards [flatInitialL2Equiv_coeFn n (RawCutoffBounds.carrierMultiplier m u),
      (flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
        (RawCutoffBounds.carrierMultiplier_coeFn m u),
      (flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
        (hχ.continuous.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).coeFn_toLp,
      flatInitialL2Equiv_coeFn n u,
      localizedScalarProduct_ae c hcsmooth hcsupport (flatInitialL2Equiv n u)]
      with x hx hmul hm hu' hc'
    simp only [Function.comp_apply] at hx hmul hm hu'
    rw [hx, hmul, hm, hc', hu']
    rfl
  obtain ⟨hmem, hnorm⟩ := hbound (flatInitialL2Equiv n u)
    ((memPhysicalSobolev_iff_memFourierSobolev s u).mp hu)
  rw [← he] at hmem hnorm
  have hout := (memPhysicalSobolev_iff_memFourierSobolev s
    (RawCutoffBounds.carrierMultiplier m u)).mpr hmem
  refine ⟨hout, ?_⟩
  calc
    _ ≤ (2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ)
        (flatInitialL2Equiv n (RawCutoffBounds.carrierMultiplier m u)) :=
      physicalSobolevNorm_le_mul_fourierSobolevNorm s _ hout
    _ ≤ (2 * Real.pi) ^ s * (C * fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n u)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ (2 * Real.pi) ^ s * (C * physicalSobolevNorm s u) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (fourierSobolevNorm_le_physicalSobolevNorm s u hu) hC) (by positivity)
    _ = _ := by ring

end JanetCartan.ContinuumAdjoint.DensityMultiplier
