module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.CompactMasks
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.PhysicalSobolev.RealPart
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.PhysicalSobolev.Multiplier

/-!
# Physical Sobolev output of the density adjoint

The real output in `app:ch_background:eq:bg-density-adjoint` is represented by
literal complexification in the shared physical Sobolev levels. Composing the
checked compact multiplier bound with the uncut real-quadrature bound proves
the physical estimate on all data at every integer order. All three carrier
coordinates and every initial coordinate are included. The bounded Sobolev map
has exactly the existing real L² output, complexified through `Complex.ofRealCLM`.
These are the final physical operations for the parent density multiplier's
`X^(s+1) → H^s` assembly; the partial Fourier construction is separate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- A fixed smooth compact mask followed by twice the real part preserves every
shared integer physical Sobolev level, with a constant independent of the datum.
This uses the actual `densityPhysicalCutoffL2` and literal complexification of
its real output, for `app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_densityPhysicalCutoffL2_sobolev_bound (s : ℕ)
    (χ : CarrierVariable n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    let m := (hχ.continuous.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).toLp χ
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : CarrierL2 n, MemPhysicalSobolev s u →
      MemPhysicalSobolev s (physicalComplexifyL2 (densityPhysicalCutoffL2 m u)) ∧
        physicalSobolevNorm s (physicalComplexifyL2 (densityPhysicalCutoffL2 m u)) ≤
          L * physicalSobolevNorm s u := by
  let m := (hχ.continuous.memLp_top_of_hasCompactSupport hc (carrierMeasure n)).toLp χ
  obtain ⟨C, hC, hb⟩ := exists_compactPhysicalMultiplier_sobolev_bound s χ hχ hc
  let R : ℝ := (4 * Real.pi) ^ s * 2 * (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨R * C, mul_nonneg hR hC, fun u hu ↦ ?_⟩
  obtain ⟨hm, hn⟩ := hb u hu
  change MemPhysicalSobolev s (complexTwoReL2 (RawCutoffBounds.carrierMultiplier m u)) ∧ _
  refine ⟨memPhysicalSobolev_complexTwoReL2 hm, ?_⟩
  calc
    _ ≤ R * physicalSobolevNorm s (RawCutoffBounds.carrierMultiplier m u) :=
      physicalSobolevNorm_complexTwoReL2_le hm
    _ ≤ R * (C * physicalSobolevNorm s u) := mul_le_mul_of_nonneg_left hn hR
    _ = _ := by ring

/-- The all-data physical cutoff estimate for the existing compact-mask L²
operator, with the bound chosen before the input. This supplies the final
physical factor in `app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_compactDensityPhysicalCutoffL2_sobolev_bound (s : ℕ)
    {χ : CarrierVariable n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : CarrierL2 n, MemPhysicalSobolev s u →
      MemPhysicalSobolev s
        (physicalComplexifyL2 (compactDensityPhysicalCutoffL2 hχ.continuous hc u)) ∧
      physicalSobolevNorm s
        (physicalComplexifyL2 (compactDensityPhysicalCutoffL2 hχ.continuous hc u)) ≤
          L * physicalSobolevNorm s u :=
  exists_densityPhysicalCutoffL2_sobolev_bound s χ hχ hc

/-- Output membership follows from the proved multiplier and real-quadrature
bounds; it is not an input to the Sobolev operator construction
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem memPhysicalSobolev_compactDensityPhysicalCutoffL2 {s : ℕ}
    {χ : CarrierVariable n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {u : CarrierL2 n} (hu : MemPhysicalSobolev s u) :
    MemPhysicalSobolev s
      (physicalComplexifyL2 (compactDensityPhysicalCutoffL2 hχ.continuous hc u)) := by
  obtain ⟨L, _, hb⟩ := exists_compactDensityPhysicalCutoffL2_sobolev_bound s hχ hc
  exact (hb u hu).1

/-- The physical cutoff and twice real part as a bounded real-linear map on
the shared complex Sobolev Hilbert space. The full physical norm is controlled
by the preceding all-data estimate (`app:ch_background:eq:bg-density-adjoint`). -/
def compactDensityPhysicalCutoffSobolev (s : ℕ)
    {χ : CarrierVariable n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    PhysicalSobolevSpace n s →L[ℝ] PhysicalSobolevSpace n s :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun u ↦ PhysicalSobolevSpace.ofL2 s
        (physicalComplexifyL2
          (compactDensityPhysicalCutoffL2 hχ.continuous hc (PhysicalSobolevSpace.toL2 s u)))
        (memPhysicalSobolev_compactDensityPhysicalCutoffL2 hχ hc
          (PhysicalSobolevSpace.toL2_mem s u))
      map_add' := by
        intro u v
        apply PhysicalSobolevSpace.toL2_injective s
        simp only [PhysicalSobolevSpace.toL2_ofL2, map_add]
      map_smul' := by
        intro c u
        apply PhysicalSobolevSpace.toL2_injective s
        have hm (w : PhysicalSobolevSpace n s) :
            PhysicalSobolevSpace.toL2 s (c • w) = c • PhysicalSobolevSpace.toL2 s w :=
          ((PhysicalSobolevSpace.toL2 s).restrictScalars ℝ).map_smul c w
        simp only [PhysicalSobolevSpace.toL2_ofL2, hm, map_smul, RingHom.id_apply] }
    (by
      obtain ⟨L, _, hb⟩ := exists_compactDensityPhysicalCutoffL2_sobolev_bound s hχ hc
      refine ⟨L, fun u ↦ ?_⟩
      simp only [PhysicalSobolevSpace.norm_eq]
      exact (hb (PhysicalSobolevSpace.toL2 s u) (PhysicalSobolevSpace.toL2_mem s u)).2)

/-- The constructed Sobolev operator has exactly the complexification of the
already constructed real L² output (`app:ch_background:eq:bg-density-adjoint`). -/
theorem toL2_compactDensityPhysicalCutoffSobolev (s : ℕ)
    {χ : CarrierVariable n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (u : PhysicalSobolevSpace n s) :
    PhysicalSobolevSpace.toL2 s (compactDensityPhysicalCutoffSobolev s hχ hc u) =
      physicalComplexifyL2
        (compactDensityPhysicalCutoffL2 hχ.continuous hc (PhysicalSobolevSpace.toL2 s u)) := rfl

/-- Agreement with the literal original physical mask and twice real part on
representatives, including all `(z,y)` variables
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem compactDensityPhysicalCutoffSobolev_coeFn (s : ℕ)
    {χ : CarrierVariable n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (u : PhysicalSobolevSpace n s) :
    PhysicalSobolevSpace.toL2 s (compactDensityPhysicalCutoffSobolev s hχ hc u) =ᵐ[carrierMeasure n]
      fun x ↦ (densityPhysicalCutoff χ (PhysicalSobolevSpace.toL2 s u) x : ℂ) := by
  rw [toL2_compactDensityPhysicalCutoffSobolev]
  filter_upwards [physicalComplexifyL2_coeFn
    (compactDensityPhysicalCutoffL2 hχ.continuous hc (PhysicalSobolevSpace.toL2 s u)),
    compactDensityPhysicalCutoffL2_coeFn hχ.continuous hc (PhysicalSobolevSpace.toL2 s u)]
    with x hx hy
  exact hx.trans (congrArg (fun r : ℝ ↦ (r : ℂ)) hy)

/-- The fixed cutoff has a uniform bound on the actual shared Hilbert norm
at each integer level (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_compactDensityPhysicalCutoffSobolev_bound (s : ℕ)
    {χ : CarrierVariable n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : PhysicalSobolevSpace n s,
      ‖compactDensityPhysicalCutoffSobolev s hχ hc u‖ ≤ L * ‖u‖ := by
  obtain ⟨L, hL, hb⟩ := exists_compactDensityPhysicalCutoffL2_sobolev_bound s hχ hc
  refine ⟨L, hL, fun u ↦ ?_⟩
  simpa only [PhysicalSobolevSpace.norm_eq, toL2_compactDensityPhysicalCutoffSobolev] using
    (hb (PhysicalSobolevSpace.toL2 s u) (PhysicalSobolevSpace.toL2_mem s u)).2

end JanetCartan.ContinuumAdjoint.DensityMultiplier
