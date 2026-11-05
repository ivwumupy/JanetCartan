module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.SourceAgreement

/-!
# Retaining the final radial threshold on the same finite family

The endpoint construction uses the physical multiplier at `2 * L`. Store that
threshold in the original family, using its proved enlarged-support plateau.
No chart, mask, root, inverse interval or angular covering is selected again.
The source partition and the later angular identity defect can therefore use
the identical threshold (`energy-complete-residual`, `resolved-angular-tail`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates
open FiniteMasks FiniteMasks.ActualFamily FinitePdo
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The SAME actual family with its final physical threshold retained.
The only changed field is the radial threshold; its plateau is proved from
closed-support nesting, not assumed (`energy-complete-residual`). -/
def withEnlargedThreshold (f : ActualMaskFamily Ω x RQ A₀ K M)
    (L : ℝ) (hL : f.radialThreshold ≤ L) : ActualMaskFamily Ω x RQ A₀ K M :=
  { f with
    radialThreshold := 2 * L
    radialThreshold_ge_one := by linarith [f.radialThreshold_ge_one]
    spatialMask_plateau := fun p ζ hζ ↦ f.spatialMask_plateau p ζ
      (tsupport_physical_dilatedConicMask_enlarged_subset (f.angularMask p)
        (f.chart p).index (zero_lt_one.trans_le f.radialThreshold_ge_one) hL hζ) }

/-- The final source multiplier is exactly the retained endpoint multiplier,
including its physical radial shoulder (`energy-complete-residual`). -/
theorem withEnlargedThreshold_multiplier
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (p : f.centers) :
    (fun ζ ↦ (dilatedConicMask ((withEnlargedThreshold f L hL).angularMask p)
      (withEnlargedThreshold f L hL).radialThreshold
      (physicalCoordinates ((withEnlargedThreshold f L hL).chart p).index ζ) : ℂ)) =
      selectedEndpointMultiplier f p L := rfl

/-- Every selected source PDO has the same symbol after retaining the final
threshold. This identifies the later stored-threshold source with the actual
retarded construction, without discarding a low-frequency discrepancy
(`prop:complete-residual`). -/
theorem withEnlargedThreshold_sourceSymbol
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (p : f.centers) :
    selectedSourceSymbol (withEnlargedThreshold f L hL) p
        (withEnlargedThreshold f L hL).radialThreshold =
      selectedSourceSymbol f p (2 * L) := rfl

/-- The stored family partition retains precisely the low and angular
complements used by the enlarged source operator (`energy-complete-residual`). -/
theorem withEnlargedThreshold_source_partition
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    {y : E} (hy : y ∈ closedBall x (4 * f.physicalRadius)) (ζ : E) :
    let g := withEnlargedThreshold f L hL
    (∑ p : g.centers, selectedSourceSymbol g p g.radialThreshold
      ((physicalCoordinates (g.chart p).index).symm y)
      ((physicalCoordinates (g.chart p).index).symm ζ)) +
      (dilatedConicMask (fun η ↦ 1 - ∑ p : g.centers, g.angularMask p η)
        g.radialThreshold ζ : ℂ) • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) +
      (FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
        (g.radialThreshold⁻¹ • ζ) : ℂ) • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) = 1 :=
  selectedSourceSymbols_complete_partition (withEnlargedThreshold f L hL) hy ζ

end JanetCartan.RegularSector.FiniteAssembly
