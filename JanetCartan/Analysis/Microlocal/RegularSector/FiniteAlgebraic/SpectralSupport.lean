module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.Selection

/-!
# The literal physical multiplier stays in the selected spectral collar

The proof retains the radial shoulder and the coordinate pullback. Its
positive section bound converts the actual algebraic inverse's degree minus
one into the full inhomogeneous frequency weight. Consumer: the same-family
inverse and PDO budgets in `app:ch_regular_base:eq:complement-symbol`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open Characteristic Characteristic.ResidualCoordinates FiniteMasks
open Characteristic.EvolutionIntegral FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The entire closed support of the dilated multiplier, including its
shoulder, lies in the selected positively conic collar. Source:
`app:ch_regular_base:eq:complement-symbol`. -/
theorem dilatedConicMask_tsupport_subset_collar (mask : E → ℝ)
    {V : Set E} (hs : tsupport mask ⊆ V)
    (hcone : ∀ ζ ∈ V, ∀ t : ℝ, 0 < t → t • ζ ∈ V)
    {L : ℝ} (hL : 0 < L) : tsupport (dilatedConicMask mask L) ⊆ V := by
  intro ζ hζ
  have h := dilatedConicMask_tsupport_subset mask hL hζ
  simpa only [NormedSpace.norm_smul_normalize] using
    hcone _ (hs h.2) ‖ζ‖ (hL.trans_le h.1)

/-- The literal pulled-back physical cutoff lies in that same collar, and
its full covector norm retains the original radial threshold. This is used
with the common doubled threshold of `PhysicalCutoff`, without commuting it
past a source mask (`energy-complete-residual`). -/
theorem physical_multiplier_mem_collar (i : Fin (d + 1)) (mask : E → ℝ)
    {V : Set E} (hs : tsupport mask ⊆ V)
    (hcone : ∀ ζ ∈ V, ∀ t : ℝ, 0 < t → t • ζ ∈ V)
    {L : ℝ} (hL : 0 < L) {ζ : E}
    (hζ : ζ ∈ tsupport (fun ζ ↦ (dilatedConicMask mask L (physicalCoordinates i ζ) : ℂ))) :
    physicalCoordinates i ζ ∈ V ∧ L ≤ ‖ζ‖ := by
  have hs' := tsupport_comp_subset Complex.ofReal_zero
    (dilatedConicMask mask L ∘ physicalCoordinates i) hζ
  have hs'' := tsupport_comp_subset_preimage (dilatedConicMask mask L)
    (physicalCoordinates i).continuous hs'
  refine ⟨dilatedConicMask_tsupport_subset_collar mask hs hcone hL hs'', ?_⟩
  simpa only [norm_physicalCoordinates] using
    (dilatedConicMask_tsupport_subset mask hL hs'').1

/-- A bounded normalized FULL covector and the original radial exclusion give
a positive section bound. No spatial cone is substituted for a spectral band
(`complement-symbol`). -/
theorem section_lower_bound_of_normalized_norm
    (ℓ : Euclidean d →L[ℝ] ℝ) {ζ : E} {Λ : ℝ}
    (hΛ : 0 < Λ) (hsection : 0 < ℓ (spatialPart ζ))
    (hnorm : ‖normalizeCovector ℓ ζ‖ ≤ Λ) (hradius : 1 ≤ ‖ζ‖) :
    1 / Λ ≤ ℓ (spatialPart ζ) := by
  have hn : (ℓ (spatialPart ζ))⁻¹ * ‖ζ‖ ≤ Λ := by
    simpa only [normalizeCovector, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.mpr hsection.le)] using hnorm
  have hi : (ℓ (spatialPart ζ))⁻¹ ≤ Λ := by
    nlinarith [inv_pos.mpr hsection]
  have hp := mul_le_mul_of_nonneg_right hi hsection.le
  rw [inv_mul_cancel₀ hsection.ne'] at hp
  exact (div_le_iff₀ hΛ).mpr (by nlinarith)

end JanetCartan.RegularSector.FiniteAlgebraic
