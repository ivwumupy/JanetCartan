module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Elapsed
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalCoordinates

/-!
# The constructed sector coordinates preserve the physical pairing

For `app:ch_regular:thm:no-return` and `app:ch_regular:lem:finite-chain`,
discharge the coordinate-pairing input of the direct root protection theorems
for the literal split selected by `exists_physical_pencil_kernel`.
The sector's split is a coordinate permutation, so its inverse acts on bases
and covectors with the required pairing. No additional geometric premise is
needed. Common current-family buffers and operator estimates remain separate.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy

open RegularSector.Characteristic

/-- The physical split actually chosen by the sector supplies the exact
`hpair` input of `normalizedPencil_field_eq_root_velocity` and the whole-segment
protection construction (`app:ch_regular:thm:no-return`). -/
theorem coordinateSplit_inverse_pairing {d : ℕ} (i : Fin (d + 1))
    (u v : ℝ × Euclidean d) :
    ⟪(coordinateSplit i).symm u, (coordinateSplit i).symm v⟫_ℝ =
      u.1 * v.1 + ⟪u.2, v.2⟫_ℝ := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    coordinateSplit_covector_pairing i u ((coordinateSplit i).symm v)

/-- The actual physical identification of the elapsed relation preserves its
base-covector pairing, using the sector's constructed coordinates
(`app:ch_regular:lem:finite-chain`). -/
theorem adaptedPhysicalPhaseState_coordinateSplit_pairing {d : ℕ}
    (i : Fin (d + 1)) (z : Euclidean (d + 1) × Euclidean (d + 1)) :
    ⟪(adaptedPhysicalPhaseState (coordinateSplit i) z).1,
      (adaptedPhysicalPhaseState (coordinateSplit i) z).2⟫_ℝ = ⟪z.1, z.2⟫_ℝ :=
  adaptedPhysicalPhaseState_pairing (coordinateSplit i)
    (coordinateSplit_inverse_pairing i) z

end JanetCartan.ArbitraryAccuracy
