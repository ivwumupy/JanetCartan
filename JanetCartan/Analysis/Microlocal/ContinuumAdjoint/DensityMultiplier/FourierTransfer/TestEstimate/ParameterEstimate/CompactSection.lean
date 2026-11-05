module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.WeightTransfer

/-!
# The actual transverse L² section of a compact carrier test

The parameter Plancherel construction for
`app:ch_background:eq:bg-density-adjoint` differentiates the transverse
L²-valued section of a compact smooth test in all three carrier directions.
Here that section is identified with the published Fubini map, and its
compact parameter support is proved from the actual test support.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The canonical transverse section of a compact test represents the
published Fubini class. This is the representative used by parameter
differentiation for `app:ch_background:eq:bg-density-adjoint`. -/
theorem carrierFubiniEquiv_test_eq_slice (f : carrierInitialTestSpace n) :
    carrierFubiniEquiv n (carrierInitialTestToLp f) =ᵐ[volume.prod volume]
      Fubini.slice f.val := by
  filter_upwards [carrierFubiniEquiv_toLp_coeFn (carrierInitialTest_memLp f)] with z hz
  apply Lp.ext
  exact hz.trans (Fubini.slice_coeFn
    (carrier_memLp_slice_of_continuous_hasCompactSupport
      f.property.1.continuous f.property.2 z)).symm

/-- Projection of the actual compact support controls the transverse
L²-valued section's parameter support. Thus compact-test parameter
Plancherel in `app:ch_background:prop:bg-adjoint` has no support assumption
beyond the given test domain. -/
theorem hasCompactSupport_carrierTestSlice (f : carrierInitialTestSpace n) :
    HasCompactSupport (Fubini.slice f.val) := by
  apply HasCompactSupport.of_support_subset_isCompact (f.property.2.image continuous_fst)
  intro z hz
  by_contra hn
  have hfz (η : Euclidean (n - 1)) : f.val (z, η) = 0 := by
    by_contra hne
    exact hn ⟨(z, η), subset_tsupport f.val hne, rfl⟩
  apply hz
  apply Lp.ext
  filter_upwards [Fubini.slice_coeFn
    (carrier_memLp_slice_of_continuous_hasCompactSupport
      f.property.1.continuous f.property.2 z),
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure (Euclidean (n - 1))))]
      with η hη hzero
  exact hη.trans ((hfz η).trans hzero.symm)

/-- Base L² membership of the actual compact-test section, consumed by
the parameter derivative construction in
`app:ch_background:eq:bg-density-adjoint`. -/
theorem memLp_carrierTestSlice (f : carrierInitialTestSpace n) :
    MemLp (Fubini.slice f.val) 2 (volume.prod volume) :=
  (Lp.memLp (carrierFubiniEquiv n (carrierInitialTestToLp f))).ae_eq
    (carrierFubiniEquiv_test_eq_slice f)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
