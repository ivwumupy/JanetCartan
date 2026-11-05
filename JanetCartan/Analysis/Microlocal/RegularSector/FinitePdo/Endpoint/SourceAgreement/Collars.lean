module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Geometry

/-!
# The selected spatial collar at an enlarged physical threshold

Doubling a threshold above the selected threshold gives an exact cutoff
factorization and hence closed-support nesting. Only the inner and outer norm
bounds of the fixed bump are used. This recovers the SAME selected spatial
plateau for the source-symbol agreement in `energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily CompatibleResponse
open FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The enlarged multiplier factors through the original one. The doubled
threshold places its entire nonzero region beyond the original cutoff's outer
radius; no radial monotonicity is required. Consumer: the selected spatial
plateau in `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem dilatedConicMask_enlarged_factor (χ : E → ℝ) {R L : ℝ}
    (hR : 0 < R) (hRL : R ≤ L) (ζ : E) :
    dilatedConicMask χ (2 * L) ζ =
      (1 - physicalCutoff 0 ((2 * L)⁻¹ • ζ)) * dilatedConicMask χ R ζ := by
  have hL : 0 < L := hR.trans_le hRL
  by_cases hz : ‖ζ‖ ≤ 2 * L
  · have hb : ‖(2 * L)⁻¹ • ζ‖ ≤ radius 0 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      simp only [radius, Nat.cast_zero, zero_add]
      exact (inv_mul_le_iff₀ (by positivity : 0 < 2 * L)).mpr (by simpa using hz)
    simp only [dilatedConicMask, conicMask, physicalCutoff_eq_one 0 hb, sub_self, zero_mul]
  · have hnorm : 2 ≤ ‖R⁻¹ • ζ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
      exact (le_inv_mul_iff₀ hR).mpr (by linarith)
    change (1 - physicalCutoff 0 ((2 * L)⁻¹ • ζ)) *
      radialSourceCutoff χ ((2 * L)⁻¹ • ζ) =
        (1 - physicalCutoff 0 ((2 * L)⁻¹ • ζ)) * conicMask χ (R⁻¹ • ζ)
    rw [conicMask_eq_radial hnorm]
    simp only [radialSourceCutoff,
      NormedSpace.normalize_smul_of_pos (inv_pos.mpr (by positivity : 0 < 2 * L)),
      NormedSpace.normalize_smul_of_pos (inv_pos.mpr hR)]

/-- Closed-support nesting in the SAME physical coordinates, including all
cutoff shoulders. Consumer: `selectedEndpointMultiplier_spatialMask_plateau`
for `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem tsupport_physical_dilatedConicMask_enlarged_subset
    (χ : E → ℝ) (i : Fin (d+1)) {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) :
    tsupport (dilatedConicMask χ (2 * L) ∘ physicalCoordinates i) ⊆
      tsupport (dilatedConicMask χ R ∘ physicalCoordinates i) := by
  have he : dilatedConicMask χ (2 * L) ∘ physicalCoordinates i =
      (fun ζ ↦ 1 - physicalCutoff 0 ((2 * L)⁻¹ • physicalCoordinates i ζ)) *
        (dilatedConicMask χ R ∘ physicalCoordinates i) :=
    funext fun ζ ↦ dilatedConicMask_enlarged_factor χ hR hRL (physicalCoordinates i ζ)
  rw [he]
  exact tsupport_mul_subset_right

/-- The literal complex endpoint multiplier has closed support inside the
original selected right support. Consumer: the source-symbol agreement and
common-ball identity in `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem selectedEndpointMultiplier_tsupport_subset
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) {L : ℝ}
    (hL : f.radialThreshold ≤ L) :
    tsupport (selectedEndpointMultiplier f p L) ⊆
      tsupport (dilatedConicMask (f.angularMask p) f.radialThreshold ∘
        physicalCoordinates (f.chart p).index) := by
  intro ζ hζ
  apply tsupport_physical_dilatedConicMask_enlarged_subset (f.angularMask p)
    (f.chart p).index (zero_lt_one.trans_le f.radialThreshold_ge_one) hL
  exact tsupport_comp_subset Complex.ofReal_zero
    (dilatedConicMask (f.angularMask p) (2 * L) ∘ physicalCoordinates (f.chart p).index) hζ

/-- Recover the selected spatial collar's germ on the entire enlarged
endpoint support from the actual family's original plateau. Consumer: equality
with the retarded source symbol in `energy-complete-residual`. -/
theorem selectedEndpointMultiplier_spatialMask_plateau
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) {L : ℝ}
    (hL : f.radialThreshold ≤ L) {ζ : E}
    (hζ : ζ ∈ tsupport (selectedEndpointMultiplier f p L)) :
    conicMask (f.spatialMask p) =ᶠ[𝓝 (spatialPart ζ)] (fun _ ↦ 1) :=
  f.spatialMask_plateau p ζ (selectedEndpointMultiplier_tsupport_subset f p hL hζ)

end JanetCartan.RegularSector.FinitePdo
