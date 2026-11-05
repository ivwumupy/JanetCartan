module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.UnitPeriod.Identity
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.UnitPeriod.CutoffKernel
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.UnitPeriod.Marginal

/-!
# Unit-period partial transforms of compact physical tests

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, the actual unit-period partial
transform is the marginal of a jointly Schwartz cutoff kernel. Transporting
that marginal through the shared Euclidean coordinates gives the representative
consumed by `rawSchwartz_preimage_compactSmooth_of_unitPeriod`. The construction
retains all three carrier coordinates and every transverse dimension, including
zero, with the literal Lebesgue measures.
-/

@[expose] public noncomputable section

open FourierTransform
open scoped SchwartzMap

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

/-- The actual unit-period partial Fourier integral of a compact physical
test has a jointly Schwartz representative in the shared density coordinates.
The cutoff kernel and its marginal are constructed from the test, with no
additional analytic premises. This supplies the representative required by
`rawSchwartz_preimage_compactSmooth_of_unitPeriod` for
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_unitPeriodSchwartz_compactSmooth (n : ℕ)
    (φ : carrierInitialTestSpace n) :
    ∃ f : SchwartzMap (DensityEuclidean n) ℂ, ∀ p : CarrierVariable n,
      f (densityCoordinates n p) = 𝓕 (fun y ↦ φ.val (p.1, y)) p.2 := by
  obtain ⟨χ, hχ⟩ := exists_unitPeriodCutoffKernel_representation φ
  obtain ⟨K, hK⟩ := exists_unitPeriodCutoffKernel_schwartz n χ
    (𝓕 (unitPeriodPhysicalSchwartz φ))
  obtain ⟨g, hg⟩ := exists_unitPeriodSchwartz_marginal n K
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (densityEuclideanEquiv n).symm.toContinuousLinearEquiv g, fun p ↦ ?_⟩
  change g ((densityEuclideanEquiv n).symm
    ((densityEuclideanEquiv n) (initialCoordinatesLinear n p))) = _
  rw [(densityEuclideanEquiv n).symm_apply_apply, hg]
  simp_rw [hK]
  exact (hχ _).trans (unitPeriodPartialIntegral_apply φ p)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
