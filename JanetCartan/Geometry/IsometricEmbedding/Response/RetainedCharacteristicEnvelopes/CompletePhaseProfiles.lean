module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.WholeImageGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IncidenceProfiles

/-!
# Complete-frequency phase profiles on the selected history chart

The original coefficient shift one supplies the full-frequency phase bound
for the complementary part of the full-source envelope. The cutoff is constant
as a germ on the original support and the complete elapsed interval is retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral
open SymbolBudgets FourierIntegral WholeImageGeometry NormalComparison LowBounds
open RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open RegularSector.FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- The original history supplies the complete-frequency phase jets on the
SAME selected chart, including all time derivatives. Constants precede every
history and frequency. The actual phase budget has coefficient shift one,
paid from reserve four, and the resulting exponent is the natural `j-1`.
The physical cutoff is only required to lie in the original collared cone;
no truncated frequency or new phase estimate is assumed
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_history_complete_phase_profiles
    {Ω : Set E} {x ξ : E} {RQ M : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d + 1)) ξ M)
    {ε aperture : ℝ} (hε : 0 < ε) (hεtarget : 4 * ε ≤ c.targetRadius)
    (hAp : 0 ≤ aperture) (hsrc : c.maskRadius ≤ ε)
    (Gref : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    let z : Z := ((coordinateSplit c.index x).1, ((coordinateSplit c.index x).2,
      (coordinateSplit c.index ξ).2))
    ∃ S₀ : ℝ, 2 ≤ S₀ ∧ ∃ Bphase : ℕ → ℝ, (∀ j, 0 ≤ Bphase j) ∧
    ∀ R₀, S₀ ≤ R₀ →
    ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
    let Q := extendedProjectedStress ext (finiteHistoryMap Gref.map u)
    ∀ C : OpenPartialHomeomorph TC TC,
      closedBall (z.1, z) c.targetRadius ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ j, cNorm (closedBall (z.1, z) c.targetRadius) j (twoTimePhase C) ≤
        c.phaseCost j * (1 + cNorm (closedBall x RQ) (j + 1) Q)) →
    ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 / 2 →
    ∀ χ : TC → ℝ,
      (∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1)) →
    ∀ t ∈ Icc (0 : ℝ) (3 * c.maskRadius / 4),
    ∀ ξ ∈ retainedFrequencyDomain c.radialSection z ε aperture (1 / 2),
    ∀ j y, y ∈ elapsedPhysicalBox z (ε / 2) →
      ‖iteratedFDeriv ℝ j (jointPhase
        (SmoothRepresentative.curriedRepresentative c.radialSection δ hδ χ (twoTimePhase C)))
        (elapsedPoint t ((y, 0), ξ))‖ ≤
          Bphase j * (1 + ‖ξ‖) * currentCoefficientScale R₀ n ^ (j - 1) := by
  intro z
  obtain ⟨S₀, hS₀, AQ, _AB, hAQ, _hAB, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles Gref hr hrR hR ext
      hextcenter hextradius hStar (reserve := 2) (by omega) horder
  let phaseTailCost := retainedPhaseCost c.radialSection z ε
    ((1 / 3) / (1 + aperture + ‖z.2.2‖ + ε)) (1 + ‖c.radialSection‖) c.phaseCost
  have hcost j : 0 ≤ phaseTailCost j :=
    (retainedPhaseCost_pos _ _ _ _ _ c.phaseCost_pos j).le
  refine ⟨S₀, hS₀, fun j ↦ phaseTailCost j * (1 + AQ (j + 1)),
    fun j ↦ mul_nonneg (hcost j) (by linarith [hAQ (j + 1)]), ?_⟩
  intro R₀ hR₀ n u ell hu Q C hbuffer hsmooth hphase δ hδ hδhalf χ hχ t ht ξ hξ j y hy
  have hL := one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) n
  have hq : cNorm (closedBall x RQ) (j + 1) Q ≤
      AQ (j + 1) * currentCoefficientScale R₀ n ^ (j - 1) := by
    simpa only [show j + 1 - 2 = j - 1 by omega] using
      ((hcoeff R₀ hR₀ n u ell hu).2.2 (closedBall x RQ) (isCompact_closedBall x RQ)).1 (j + 1)
  have hpair : 1 + cNorm (closedBall x RQ) (j + 1) Q ≤
      (1 + AQ (j + 1)) * currentCoefficientScale R₀ n ^ (j - 1) := by
    have h1 := one_le_pow₀ hL (n := j - 1)
    nlinarith only [hq, h1]
  apply (retained_complete_representative_jet_le c.radialSection hε hsrc hAp hεtarget
    hbuffer hsmooth hδ hδhalf hχ (closedBall x RQ) Q c.phaseCost hphase j ht hy hξ).trans
  exact (mul_le_mul_of_nonneg_left hpair
    (mul_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖) (hcost j))).trans_eq (by ring)

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
