module

public import JanetCartan.Iteration.PhysicalEllipticWords.Coefficients
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.JointProfiles

/-!
# Actual physical-history endpoint symbol profiles

Apply the retained endpoint certificate of the SAME original fixed inverse to
the literal extended Q and full B of the physical history. Constants precede
histories and frequency. The supplied `W₁` certificate is the index-one output
of `exists_pre_reference_terminal_normalized_physical_inverse`; no endpoint
symbol or response-envelope bound is a premise.
Consumer: `app:ch_response:eq:response-graded-reduced`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalEllipticWords
open ProtectedFlow GeometricProfile ResponseTransfer.RetainedFactors
open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.ResidualLocalization
open RegularSector RegularSector.FinitePdo RegularSector.FinitePdo.RetainedConstruction
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open ResponseTransfer ResponseTransfer.DirectEvolution ResponseTransfer.NearCarrierFullLow FourierIntegral

variable {d : ℕ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
  {K₀ : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)

/-- Actual reserved joint endpoint amplitude on every physical history.
The original finite inverse's `W₁` and coefficient-cost certificate are used
unchanged, including its full input/output masks and both adjoint orientations. -/
theorem exists_history_endpoint_joint_profiles
    (f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K₀ M)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius / 2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (π : E → ℝ) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hzero : (0 : E) ∉ tsupport π)
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p k, 0 ≤ cost p k)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {Cband : ℝ} (hband : 1 ≤ Cband)
    {rStar reserve kMin : ℕ} (hreserve : reserve + 12 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap E (Euclidean (embeddingDimension (d + 1))))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection (d + 1) ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ∀ W : f.centers → TwoTimeAmplitude d (d + 1),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius / 2) (ra p) (rb p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p))) →
      (∀ p k, BoundedTwoTimeOrderSeminorm 1 (J p) k (W p) ∧
        twoTimeOrderSeminorm 1 (J p) k (W p) ≤ cost p k *
          (1 + cNorm (closedBall x RQ) (k + 10) Q + cNorm (closedBall x RQ) (k + 9) B)) →
      ∀ ρ : ℝ, 1 ≤ ρ → ∀ p (backward : Bool),
      let A : FullAmplitude (d + 1) (d + 1) := fun y z ξ ↦ π (ρ⁻¹ • ξ) •
        orientedMaskedPDOAmplitude false (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q (W p)) y z ξ
      let α := fun (q : E × Par) (w : CW) ↦ (ρ ^ (-1 : ℤ))⁻¹ •
        normalizedFullAmplitude (if backward then exchangedAdjointAmplitude A else A) ρ (q.1, w.fst, w.snd)
      ContDiff ℝ ∞ (Function.uncurry α) ∧ ∀ k v,
        ‖iteratedFDeriv ℝ k (Function.uncurry α) v‖ ≤
          D k * currentCoefficientScale R₀ j ^ (k + 2 - reserve) := by
  obtain ⟨S, hS, AQ, AB, hAQ, hAB, hp⟩ :=
    PhysicalGeometry.exists_retained_coefficient_profiles G hr hrR hR ext hextcenter hextradius
      hband (reserve := reserve + 10) (by omega) (by omega) horder
  obtain ⟨D, hD, hb⟩ := exists_selected_endpoint_reserved_joint_profiles
    f hΩ hball threshold ht hft output ho hoc hout hbuffer hmask ra rb hcoverage
      π hπ hcπ hzero AQ AB cost hAQ hAB hcost
  refine ⟨S, hS, D, hD, ?_⟩
  intro R₀ hR₀ j u ell hu F Q B W J hW hbudget ρ hρ p backward A α
  obtain ⟨hQ, _hB, hprofile⟩ := hp R₀ hR₀ j u ell hu
  obtain ⟨hpQ, hpB⟩ := hprofile (closedBall x RQ) (isCompact_closedBall _ _)
  exact hb reserve (reserve + 10) le_rfl (currentCoefficientScale R₀ j) ρ
    (one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) j) hρ
    Q hQ.contDiffOn B hpQ hpB W hW hbudget p backward

end JanetCartan.PhysicalEllipticWords
