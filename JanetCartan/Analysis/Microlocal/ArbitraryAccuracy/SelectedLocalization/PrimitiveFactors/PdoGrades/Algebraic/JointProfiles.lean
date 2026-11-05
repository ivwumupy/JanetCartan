module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.NoncomparableProfiles

/-!
# One joint and physical profile for the same selected algebraic symbol

This is the branch-three symbol input of `CompleteFactor`, before the parent
combines it with the source and endpoint branches in `Dpdo`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open RegularSector.FiniteEvolution.PhysicalCutoff
open CharacteristicTransport.CompleteResidual ResidualLocalization FourierIntegral
open FourierIntegral.PrimitiveProfiles FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry FiniteChain.Retarded.KernelDecay
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- One profile supplies BOTH symbol-grade inputs for branch three of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
It applies to the SAME `selectedAlgebraicSymbol f p (2*threshold) Q B 1`,
including its entire source product, full `B`, both original masks and literal
adjunction. The exact comparable carrier is used; the noncomparable physical
bound keeps its negative `branchRadius` weight. Constants precede the original
fields, `Rstar,L,ρ` and accuracy; the slow-scale offset is ZERO. The only
inverse-domain input is the retained constant-field complement certificate,
produced by `exists_finite_physical_evolution_and_algebraic_inverse`; no inverse
budget or joint estimate is assumed. Use
`selected_algebraic_residual_amplitude_eq` for the direct four-symbol ledger.
Sources: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_selected_algebraic_joint_grades
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (a b : ℝ) (ha : 0 < a) (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    let J := frequencyAnnulus (n := d+1) (a / (16*annulusFactor 1 1))
      (4 * max 1 (4*annulusFactor 1 1*b))
    let Z := fun p ↦ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)
    let Kpdo := fun p ↦ comparableJointCarrier 1 1 a b ((Prod.fst '' Z p) ×ˢ J)
      (Z p) (frequencyAnnulus a b)
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ A k * L ^ (k - Rstar)) →
      ∀ (p : f.centers) (backward : Bool),
      (∀ k v, v ∈ Kpdo p →
        ‖iteratedFDeriv ℝ k (fun w : V ↦ orientedMaskedPDOAmplitude backward
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) Q B 1) w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
            ρ ^ (-1 : ℝ) * C k * L ^ k) ∧
      ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p), ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦ orientedMaskedPDOAmplitude backward
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) Q B 1) w.1 w.2 (ρ • ξ)) z‖ ≤
            (max 1 (branchRadius low j)) ^ (-1 : ℝ) * C k * L ^ k := by
  intro J Z Kpdo
  obtain ⟨Cj, hCj, hj⟩ := exists_selected_algebraic_comparable_profile
    f hΩ hRQ hKΩ hc hdom threshold ht output ho hoc hos a b ha A hA
  obtain ⟨Cp, hCp, hp⟩ := exists_selected_algebraic_noncomparable_profile_of_retained_domain
    f hΩ hRQ hKΩ hc hdom threshold ht output ho hoc hos A hA
  refine ⟨fun k ↦ Cj k + Cp k, fun k ↦ add_nonneg (hCj k) (hCp k), ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hQr hQp hBp p backward
  constructor
  · intro k v hv
    apply (hj Rstar hR L ρ hL hρ Q B hQ hB hQr hQp hBp p backward k v hv).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (hCp k)) (Real.rpow_nonneg (zero_le_one.trans hρ) _))
      (pow_nonneg (zero_le_one.trans hL) k)
  · intro low j ξ hξ z hz k
    apply (hp Rstar hR L ρ hL (zero_lt_one.trans_le hρ) Q B hQ hB hQr hQp hBp
      p backward low j ξ hξ z hz k).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (hCj k)) (Real.rpow_nonneg (by positivity) _))
      (pow_nonneg (zero_le_one.trans hL) k)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
