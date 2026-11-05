module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Neighborhoods
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.DilatedShellCover

/-!
# Spatial collars in each selected coordinate system

Pull the actual angular masks through the selected coordinate permutation
before applying the finite nested-mask producer. One radial threshold works
for the entire family. The plateau includes the full closed right-multiplier
support, not just its nonzero locus.
Consumer: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open Characteristic Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

/-- The chart permutation has precisely the selected time and spatial
components. This identity is used for each mask separately
(`energy-complete-residual`). -/
theorem split_physicalCoordinates (i : Fin (d + 1)) (y : E) :
    coordinateSplit i (physicalCoordinates i y) = (y 0, spatialPart y) :=
  (coordinateSplit i).apply_symm_apply _

/-- Smooth angular masks in physical coordinates stay smooth after their
OWN chart permutation (`thm:sector`). -/
theorem contDiff_chartAngularMask {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (i : Fin (d + 1)) : ContDiff ℝ ∞ (χ ∘ physicalCoordinates i) :=
  hχ.comp (physicalCoordinates i).contDiff

/-- The angular carrier in canonical time-zero coordinates lies in this
chart's actual spatial cone. The support is pulled through the continuous
coordinate permutation explicitly (`energy-complete-residual`). -/
theorem chartAngularMask_spatial_support {ξ : E} (c : LocalChart Ω x RQ A₀ ξ M)
    {χ : E → ℝ} (hχ : tsupport χ ⊆ c.angularNeighborhood)
    {ζ : E} (hζ : ζ ∈ tsupport (χ ∘ physicalCoordinates c.index)) :
    spatialPart ζ ∈ c.spatialCone := by
  have h := hχ (tsupport_comp_subset_preimage χ
    (physicalCoordinates c.index).continuous hζ)
  change (coordinateSplit c.index (physicalCoordinates c.index ζ)).2 ∈ c.spatialCone at h
  simpa only [split_physicalCoordinates] using h

/-- Instantiate the existing finite nesting producer on the ACTUAL chart
cones. Its source masks satisfy the uniform local amplitude producer's
positive-section hypothesis. All selected coordinates are kept explicit.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_chart_nested_spatial_masks {ι : Type*} [Fintype ι]
    (ξ : ι → E) (chart : ∀ p, LocalChart Ω x RQ A₀ (ξ p) M)
    (χ : ι → E → ℝ)
    (hsupp : ∀ p, tsupport (χ p) ⊆ (chart p).angularNeighborhood) :
    ∃ (a : ι → Euclidean d → ℝ) (L : ℝ), 1 ≤ L ∧
      (∀ p, ContDiff ℝ ∞ (a p) ∧ (∀ η, a p η ∈ Icc (0 : ℝ) 1) ∧
        HasCompactSupport (a p) ∧ tsupport (a p) ⊆ (chart p).spatialCone) ∧
      ∀ p, ∀ ζ ∈ tsupport (dilatedConicMask
        (χ p ∘ physicalCoordinates (chart p).index) L),
        conicMask (a p) =ᶠ[𝓝 (spatialPart ζ)] (fun _ ↦ 1) := by
  exact exists_finite_nested_spatial_conicMasks
    (fun p ↦ χ p ∘ physicalCoordinates (chart p).index)
    (fun p ↦ (chart p).spatialCone)
    (fun p ↦ (chart p).isOpen_spatialCone)
    (fun p ↦ (chart p).zero_notMem_spatialCone)
    (fun p _ hη _ ht ↦ (chart p).smul_mem_spatialCone hη ht)
    (fun p _ hζ ↦ chartAngularMask_spatial_support (chart p) (hsupp p) hζ.1)

/-- The actual enlarged canonical right multiplier stays in the same spatial
cone, including every shoulder of its closed support (`retarded-kernel`). -/
theorem spatialCone_of_mem_chartRightSupport {ξ : E} (c : LocalChart Ω x RQ A₀ ξ M)
    {χ : E → ℝ} (hχ : tsupport χ ⊆ c.angularNeighborhood) {L : ℝ} (hL : 1 ≤ L)
    {ζ : E} (hζ : ζ ∈ tsupport (dilatedConicMask
      (χ ∘ physicalCoordinates c.index) L)) :
    spatialPart ζ ∈ c.spatialCone := by
  have hs := dilatedConicMask_tsupport_subset (χ ∘ physicalCoordinates c.index)
    (zero_lt_one.trans_le hL) hζ
  have h := chartAngularMask_spatial_support c hχ hs.2
  have hscale := c.smul_mem_spatialCone h (zero_lt_one.trans_le (hL.trans hs.1))
  simpa only [← spatialPart_smul, NormedSpace.norm_smul_normalize] using hscale

/-- The source plateau holds on the full enlarged right-multiplier support,
using the original physical point and this chart's actual radial section.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem sourceMask_plateau_on_chartRightSupport {ξ : E} (c : LocalChart Ω x RQ A₀ ξ M)
    {χ : E → ℝ} (hχ : tsupport χ ⊆ c.angularNeighborhood) {L : ℝ} (hL : 1 ≤ L)
    {y ζ : E} (hy : y ∈ c.physicalNeighborhood)
    (hζ : ζ ∈ tsupport (dilatedConicMask (χ ∘ physicalCoordinates c.index) L)) :
    ((coordinateSplit c.index y).1, ((coordinateSplit c.index y).2,
      (c.radialSection (spatialPart ζ))⁻¹ • spatialPart ζ)) ∈
        interior {w | c.sourceMask w = 1} := by
  have hcone := spatialCone_of_mem_chartRightSupport c hχ hL hζ
  have hmem : physicalCoordinates c.index ζ ∈ c.angularNeighborhood := by
    change (coordinateSplit c.index (physicalCoordinates c.index ζ)).2 ∈ c.spatialCone
    simpa only [split_physicalCoordinates] using hcone
  simpa only [split_physicalCoordinates] using c.sourceMask_diagonal_plateau hy hmem

end JanetCartan.RegularSector.FiniteMasks.ActualFamily
