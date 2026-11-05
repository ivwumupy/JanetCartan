module

public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Measured
public import JanetCartan.Analysis.Operator.FiniteNeumann.Algebra

/-!
# Corrected-source angular observation for the same normalized inverse

Identify the literal L²-to-Lᵖ implementation of the corrected source with
its measured normalized residual before taking the finite expansion. Every
term retains the original source cutoff and the original restriction and
zero extension. The source observation is the complete normalized source
minus exactly one identity. No equality with the old characteristic-only
source is asserted.

The contraction and low restriction estimates are outputs of the normalized
fixed inverse constructor on the supplied family. The remaining finite-word
decay is the localization producer's input to
`ArbitraryAccuracy.rapidDecayAt_inverse_of_finite_chains`. The signed-source
remainder bound is provided by `RecutInverseRemainder` on the literal inner-bump
datum. `RecutRemainderObservation` derives its original outer plateau and applies
the complete normalized source's order-zero observation cost.
Sources: `app:ch_regular:eq:finite-neumann-identity`,
`app:ch_pairs:eq:pairs-lag-one-error`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

open Set Metric MeasureTheory
open scoped NNReal ENNReal ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FixedDomainInverse
open FourierIntegral.LowBounds
open ArbitraryAccuracy.ResidualLocalization
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)


/-- The actual L²-to-Lᵖ corrected source is the same measured normalized
inverse used by the signed remainder and reduced-size estimates. The
original inner bump stays inside the inverse, and both measurement masks
remain in its residual (`app:ch_regular:thm:exact-correction`,
`app:ch_pairs:eq:pairs-lag-sum-size`). This is an operator identity, so the
normalized constructor's raw tame estimate transfers without any new
inverse or equality of independent choices. -/
theorem normalized_correctedSource_eq_measured_inverse
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : H →L[ℂ] H)
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
    let Krecut := localRealCompression hW W
      (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
        (SmallSupport.bump_norm_le_one χ₂) (SmallSupport.bump_norm_le_one χ₃)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded))
    correctedSource (two_lt_ballSobolevExponent (F := E) center hr).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp =
        (neumannInverse Krecut).comp (SmallSupport.bumpL2 (p := 2) le_rfl χ₂) := by
  intro Rp Krecut
  have hsame : SmallSupport.localizedResidual
      (two_lt_ballSobolevExponent (F := E) center hr).le χ₂ χ₃ isOpen_ball.measurableSet Rp =
        Krecut := by
    simpa only [Krecut, Rp, pairedResidual, normalizedPair,
      RegularSector.FiniteAssembly.physicalPair_measuredOperator] using
      localizedResidual_eq_real_measuredOperator (d := d) (q := d+1) hW center hr hball
        ((1/2 : ℂ) • (selectedFiniteDirectResidual f L₀ Q B W₁ output ho hob retarded +
          (sourceCutMultiplier output ho hob).comp
            (RegularSector.EllipticComplement.ellipticResidual f hK L₀ Q B)))
        hmem hbudget hbound χ₂ χ₃ hs₂
  unfold correctedSource
  rw [hsame]

/-- The finite expansion of the actual normalized angular discrepancy acts
on the original corrected source, including its inner cutoff. The same
normalized residual and both physical masks occur at every depth
(`app:ch_regular:eq:finite-neumann-identity`, `app:ch_pairs:eq:pairs-lag-one-error`). -/
theorem normalized_correctedSource_angular_finite_expansion
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : H →L[ℂ] H)
    {W : Set E} (hW : MeasurableSet W) {r : ℝ} (hr : 0 < r)
    (hball : ball center r ⊆ W)
    (hmem : ∀ v : LocalL2 W E, MemRestrictionSobolev (ball center r) 1
      (localRealCompression hW (ball center r)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded) v))
    {budget : ℝ} (hbudget : 0 ≤ budget)
    (hbound : ∀ v : LocalL2 W E, restrictionSobolevNorm (ball center r) 1
      (localRealCompression hW (ball center r)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded) v) ≤ budget * ‖v‖)
    (χ₂ χ₃ : ContDiffBump center) (hs₂ : tsupport (χ₂ : E → ℝ) ⊆ ball center r)
    (Vout : Set E) (depth : ℕ) (h : LocalL2 W E) :
    let Rp := residualToLpOnBall center hr hball
      (localRealCompression hW (ball center r)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded)) hmem hbudget hbound
    let Kloc : LocalL2 W E →L[ℝ] LocalL2 W E := SmallSupport.localizedResidual (two_lt_ballSobolevExponent (F := E) center hr).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp
    let Krecut : LocalL2 W E →L[ℝ] LocalL2 W E := localRealCompression hW W
      (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
        (SmallSupport.bump_norm_le_one χ₂) (SmallSupport.bump_norm_le_one χ₃)
        (pairedResidual f hK L₀ Q B output ho hob W₁ retarded))
    let A := localRealCompression hW Vout (pairedSource f hK L₀ output ho hob - 1)
    let h₂ := SmallSupport.bumpL2 (p := 2) le_rfl χ₂ h
    ‖Kloc‖ < 1 →
    A (correctedSource (two_lt_ballSobolevExponent (F := E) center hr).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp h) -
        (∑ j ∈ Finset.range depth, ((-1 : ℝ)^j) • A ((Krecut^j) h₂)) =
      ((-1 : ℝ)^depth) • A (neumannInverse Krecut ((Krecut^depth) h₂)) := by
  intro Rp Kloc Krecut A h₂ hKloc
  have hsame : Kloc = Krecut := by
    simpa only [Kloc, Krecut, Rp, pairedResidual, normalizedPair,
      RegularSector.FiniteAssembly.physicalPair_measuredOperator] using
      localizedResidual_eq_real_measuredOperator (d := d) (q := d+1) hW center hr hball
        ((1/2 : ℂ) • (selectedFiniteDirectResidual f L₀ Q B W₁ output ho hob retarded +
          (sourceCutMultiplier output ho hob).comp
            (RegularSector.EllipticComplement.ellipticResidual f hK L₀ Q B)))
        hmem hbudget hbound χ₂ χ₃ hs₂
  have hsmall : ‖Krecut‖ < 1 := hsame ▸ hKloc
  change A (neumannInverse Kloc h₂) - _ = _
  rw [hsame]
  exact finite_neumann_observation_identity Krecut (neumannInverse Krecut)
    (neumannInverse_mul_add Krecut hsmall) A.toLinearMap depth h₂

end JanetCartan.SignedProductEstimates
