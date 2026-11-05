module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedCorrectedExpansion
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.LocalComplex

/-!
# The supplied initialized residual on its original complex space

Identify the initializer's actual L²-to-Lᵖ localization with the complex
measured residual. Its original real contraction and one-derivative estimates
therefore apply to the same complex Neumann series. No operator or inverse is
chosen here, and every physical mask stays in its original position.

Consumer: the gain and contraction inputs of
`exists_observed_parameter_remainders_of_original_profiles`,
`app:ch_regular:eq:neumann-series` and
`app:ch_response:eq:response-actual-solver-formula`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport RegularSector Realization NormalizedSolver
open FiniteMasks.ActualFamily FiniteAssembly
open Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization FourierIntegral.LowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual

variable {d : ℕ} {Ω : Set (Euclidean (d + 1))} {center : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d (d + 1)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The literal supplied-family measured residual has the initializer's real
compression, reality, norm and corrected source. Consequently the original
gain estimates and contraction transfer by rewriting, without an additional
analytic premise or equality between independently selected witnesses
(`app:ch_regular:eq:neumann-series`,
`app:ch_response:eq:response-actual-solver-formula`). -/
theorem initialized_complexResidual_identification
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (B : E → MetricTensor (d + 1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d + 1)) (retarded : H →L[ℂ] H)
    {W : Set E} (hW : MeasurableSet W) {r : ℝ} (hr : 0 < r)
    (hball : ball center r ⊆ W)
    (hmem : ∀ v : LocalL2 W E, MemRestrictionSobolev (ball center r) 1
      (localRealCompression hW (ball center r)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded) v))
    {budget : ℝ} (hbudget : 0 ≤ budget)
    (hbound : ∀ v : LocalL2 W E, restrictionSobolevNorm (ball center r) 1
      (localRealCompression hW (ball center r)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded) v) ≤ budget * ‖v‖)
    (χ₂ χ₃ : ContDiffBump center) (hs₂ : tsupport (χ₂ : E → ℝ) ⊆ ball center r) :
    let Rp := residualToLpOnBall center hr hball
      (localRealCompression hW (ball center r)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded)) hmem hbudget hbound
    let Kloc := localizedResidual (two_lt_ballSobolevExponent (F := E) center hr).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp
    let Rcomplex := complexLocalRetardedOperator hW W
      (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
        (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded))
    realOutputCompression Rcomplex = Kloc ∧
      conjugateOperator Rcomplex.toLinearMap = Rcomplex.toLinearMap ∧
      ‖Rcomplex‖ = ‖Kloc‖ ∧
      correctedSource (two_lt_ballSobolevExponent (F := E) center hr).le
        χ₂ χ₃ isOpen_ball.measurableSet Rp =
          (neumannInverse (realOutputCompression Rcomplex)).comp
            (bumpL2 (p := 2) le_rfl χ₂) := by
  intro Rp Kloc Rcomplex
  have hsame : realOutputCompression Rcomplex = Kloc := by
    change localRealCompression hW W
      (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
        (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded)) = Kloc
    symm
    simpa only [Kloc, Rp, pairedResidual, normalizedPair, physicalPair_measuredOperator] using
      localizedResidual_eq_real_measuredOperator (d := d) (q := d + 1) hW center hr hball
        ((1 / 2 : ℂ) • (selectedFiniteDirectResidual f L₀ Q B W₁ output ho hob retarded +
          (sourceCutMultiplier output ho hob).comp
            (EllipticComplement.ellipticResidual f hK L₀ Q B)))
        hmem hbudget hbound χ₂ χ₃ hs₂
  have hreal : conjugateOperator Rcomplex.toLinearMap = Rcomplex.toLinearMap := by
    apply complexLocalRetardedOperator_conjugation
    dsimp only [pairedResidual, normalizedPair]
    rw [← physicalPair_measuredOperator]
    exact physicalPairedSectorSum_conjugation _ _
  refine ⟨hsame, hreal, ?_, ?_⟩
  · exact (realCompression_norm_eq_of_conjugation Rcomplex hreal).symm.trans
      (congrArg norm hsame)
  · exact SignedProductEstimates.normalized_correctedSource_eq_measured_inverse
      f hK L₀ Q B output ho hob W₁ retarded hW hr hball hmem hbudget hbound χ₂ χ₃ hs₂

end JanetCartan.FixedDomainInverse
