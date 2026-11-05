module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectSmooth.TestedCorrection

/-!
# The complete normalized equation after the fixed source correction

Apply the existing tested-correction proof to the literal normalized half-sums.
The actual normalized constructor supplies the tested equation, and
`exists_normalized_complete_fixed_inverse_of_selected_collar` supplies the core
residual equation. The complete source minus one identity stays explicit.
Sources: `app:ch_regular:eq:exact-physical`, `real-sector-normalization`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.FixedDomainInverse
open LocalSobolev SmallSupport RegularSector.Realization RegularSector.FiniteAssembly
open RegularSector.NormalizedSolver RegularSector.EllipticComplement
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.EvolutionIntegral
open CharacteristicTransport.CompleteResidual ArbitraryAccuracy.ResidualLocalization
open FourierIntegral.LowBounds
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RH" => Lp E 2 (volume : Measure E)

private theorem real_source_residual_half_sum
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) :
    realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
      (1/2 : ℂ) • (sourceCutMultiplier output ho hob).comp
        (selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L) +
      (1/2 : ℂ) • (selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁ +
        (sourceCutMultiplier output ho hob).comp (ellipticResidual f hK L Q B)))) =
      realSource f hK L output ho hob +
        realResidual f hK L Q B output ho hob W₁ retardedPW₁ := by
  rw [physicalPairedSectorSum_add]
  ext1 u
  exact map_add (l2RealPart volume) _ _

/-- The normalized complete right side equals the original datum plus the
literal complete source discrepancy on the SAME inverse core. The core equation
is supplied by the actual fixed inverse (`app:ch_regular:eq:exact-physical`,
`real-sector-normalization`). -/
theorem normalized_correctedSource_right_ae
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H)
    {W U V : Set E} (hW : MeasurableSet W) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (hVW : V ⊆ W) (h z : LocalL2 W E)
    (heq : ∀ᵐ y ∂volume.restrict V,
      z y + localRealCompression hW U
        (pairedResidual f hK L Q B output ho hob W₁ retardedPW₁) z y = h y) :
    (realSource f hK L output ho hob +
      realResidual f hK L Q B output ho hob W₁ retardedPW₁) (zeroExtend hW z)
        =ᵐ[volume.restrict V]
      (zeroExtend hW h + realSource f hK L output ho hob (zeroExtend hW z) -
        zeroExtend hW z : RH) := by
  have hr := realPair_correctedSource_right_ae hW hV hVU hVW
    ((1/2 : ℂ) • (sourceCutMultiplier output ho hob).comp
      (selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L))
    ((1/2 : ℂ) • (selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁ +
      (sourceCutMultiplier output ho hob).comp (ellipticResidual f hK L Q B))) h z heq
  rw [real_source_residual_half_sum] at hr
  exact hr

/-- The actual normalized tested PDE and its fixed inverse give the tested
corrected PDE with one complete source-minus-identity term. Both inputs are
constructed on the same family by `NormalizedConstruction`; this deduction
keeps every half coefficient and physical mask (`app:ch_regular:eq:exact-physical`,
`real-sector-normalization`). -/
theorem normalized_correctedSource_test
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : Fin 2 → H →L[ℂ] H)
    {W U V : Set E} (hW : MeasurableSet W) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (hVW : V ⊆ W)
    (htest : ∀ (u : RH) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (l2ComplexInclusion volume
          (realSolver f hK L Q B output ho hob (retarded 0) u) y).ofLp) φ j =
        ∫ y, φ y • l2ComplexInclusion volume
          ((realSource f hK L output ho hob +
            realResidual f hK L Q B output ho hob W₁ (retarded 1)) u) y j)
    (h z : LocalL2 W E)
    (heq : ∀ᵐ y ∂volume.restrict V,
      z y + localRealCompression hW U
        (pairedResidual f hK L Q B output ho hob W₁ (retarded 1)) z y = h y) :
    ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (l2ComplexInclusion volume
          (realSolver f hK L Q B output ho hob (retarded 0) (zeroExtend hW z)) y).ofLp) φ j =
        ∫ y, φ y • l2ComplexInclusion volume
          (zeroExtend hW h + realSource f hK L output ho hob (zeroExtend hW z) -
            zeroExtend hW z) y j := by
  apply realPair_correctedSource_test hW hV hVU hVW
    (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
    ((1/2 : ℂ) • (selectedFiniteDirectSolver f L Q B output ho hob (retarded 0) +
      (sourceCutMultiplier output ho hob).comp (ellipticSolver f hK L Q)))
    ((1/2 : ℂ) • (sourceCutMultiplier output ho hob).comp
      (selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L))
    ((1/2 : ℂ) • (selectedFiniteDirectResidual f L Q B W₁ output ho hob (retarded 1) +
      (sourceCutMultiplier output ho hob).comp (ellipticResidual f hK L Q B)))
    ?_ h z heq
  simpa only [real_source_residual_half_sum, realSolver, pairedSolver, normalizedPair] using htest

end JanetCartan.FixedDomainInverse
