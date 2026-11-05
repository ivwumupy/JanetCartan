module

public import JanetCartan.Iteration.PhysicalEllipticWords.Coefficients
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedAlgebraicSymbol.JointProfiles

/-!
# Actual physical-history algebraic symbol profiles

The SAME original solver and complete residual are treated together, with both
adjoint orientations. Original-reference closeness produces actual coefficient
range and profiles; no current admission or symbol-envelope bound is assumed.
Consumer: the algebraic letters of `app:ch_response:eq:response-graded-reduced`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalEllipticWords
open ProtectedFlow GeometricProfile ProjectedStressFrame ResponseTransfer.RetainedFactors
open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.ResidualLocalization
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.ResidualCoordinates RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteAlgebraic
open RegularSector.FinitePdo RegularSector.FiniteAssembly
open FourierIntegral ResponseTransfer ResponseTransfer.DirectEvolution ResponseTransfer.NearCarrierFullLow

variable {d : ℕ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
  {K₀ : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

/-- One pre-reference tolerance constructs the actual reserved full algebraic
profiles on every physical prefix. The original frozen root/complement geometry
is exactly the retained geometry of the supplied regular inverse. -/
theorem exists_history_algebraic_joint_profiles
    (f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K₀ M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hball : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col (cubeStress (d + 1)) p.val.val c.root
        c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall (cubeStress (d + 1)) f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (π : E → ℝ) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hzero : (0 : E) ∉ tsupport π)
    (ext : BallExtension.Parameters E) {r : ℝ}
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference (d + 1), ∀ R : ℝ,
      0 < r → r < R → R < G.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : E) r) 6
        (fun x ↦ projectedStress G.map x i - cubeStress (d + 1) i) < η) →
      ∀ {Cband : ℝ}, 1 ≤ Cband →
      ∀ rStar reserve kMin : ℕ, reserve + 12 ≤ rStar →
      RevisedScales.displacementLoss (d + 1) +
        bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < (kMin : ℝ) →
      ∃ S : ℝ, 2 ≤ S ∧ ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
        ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap E (Euclidean (embeddingDimension (d + 1))))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap G.map u
        let Q := extendedProjectedStress ext F
        let B := reducedZerothProjection (d + 1) ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F
        ∀ ρ : ℝ, 1 ≤ ρ → ∀ (p : f.centers) (o : Fin 2) (backward : Bool),
        let A : FullAmplitude (d + 1) (d + 1) := fun y z ξ ↦ π (ρ⁻¹ • ξ) •
          orientedMaskedPDOAmplitude false (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2 * threshold) Q B o) y z ξ
        let α := fun (q : E × Par) (w : CW) ↦ (ρ ^ (-1 : ℤ))⁻¹ •
          normalizedFullAmplitude (if backward then exchangedAdjointAmplitude A else A) ρ (q.1, w.fst, w.snd)
        ContDiff ℝ ∞ (Function.uncurry α) ∧ ∀ k v,
          ‖iteratedFDeriv ℝ k (Function.uncurry α) v‖ ≤
            D k * currentCoefficientScale R₀ j ^ (k + 2 - reserve) := by
  obtain ⟨η, hη, hadmit⟩ := exists_admitted_history_coefficient_profiles
    ext hextcenter hextradius f.coefficientRadius_pos (δ := 1) zero_lt_one
  refine ⟨η, hη, ?_⟩
  intro G R hr hrR hR href Cband hband rStar reserve kMin hreserve horder
  obtain ⟨S, hS, AQ, AB, hAQ, hAB, hp⟩ := hadmit G R hr hrR hR href hband
    rStar (reserve + 10) kMin (by omega) (by omega) horder
  obtain ⟨D, hD, hb⟩ := FixedDomainInverse.ReservedAlgebraicSymbol.exists_selected_algebraic_joint_reserved_profiles
    f hΩ hRQ hball hc hdom threshold ht output ho hoc hout π hπ hcπ hzero AQ AB hAQ hAB
  refine ⟨S, hS, D, hD, ?_⟩
  intro R₀ hR₀ j u ell hu F Q B ρ hρ p o backward A α
  obtain ⟨hQ, hB, hmap, _hclose, hprofile⟩ := hp R₀ hR₀ j u ell hu
  obtain ⟨hpQ, hpB⟩ := hprofile (closedBall x RQ) (isCompact_closedBall _ _)
  exact hb reserve (reserve + 10) le_rfl (currentCoefficientScale R₀ j) ρ
    (one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) j) hρ Q B
    hQ.contDiffOn hB.contDiffOn (fun y _ ↦ hmap (mem_univ y)) hpQ hpB p o backward

end JanetCartan.PhysicalEllipticWords
