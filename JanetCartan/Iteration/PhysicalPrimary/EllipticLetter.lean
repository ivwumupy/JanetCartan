module

public import JanetCartan.Iteration.PhysicalPrimary.SolverStepTemplate
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticApplication.ActualOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.Paired

/-!
# The actual elliptic case of the complete original measured alphabet

Apply the complete global elliptic PDO constructor, not a principal symbol or
assumed response estimate, then retain the original real measurement and source.
The external half, literal conjugate and scalar 1/i stay inside the same operator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary
open ResponseTransfer ResponseTransfer.Complement ResponseTransfer.FullEllipticApplication
open ResponseTransfer.DirectEvolution ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.AnnularComplement
open RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral FourierIntegral.LowBounds FourierIntegral.FullLowBounds Pseudodifferential
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open RegularSector.NormalizedSolver RegularSector.FiniteAssembly
open RegularSector.FiniteResidual.FiniteIdentity
open CharacteristicTransport.CompleteResidual PhysicalEllipticWords
open ArbitraryAccuracy.SelectedLocalization

variable {d : ℕ} {I ι : Type} [Fintype ι]
  {Ωcoeff : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
  {K₀ : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

/-- The literal `Sum.inr ()` branch, with the original full Q/B profiles and
complete PDO. This closes the analytic elliptic case of `hstep` in
`actual_finite_residual_word_reserved_bounds_of_one_step`; its SAME native
coefficient/phase certificates are instantiated by the original history parent
(`energy-complete-residual`, `app:ch_regular:lem:finite-chain`). -/
theorem elliptic_paired_measured_word_bounds
    (fam : ActualMaskFamily Ωcoeff x RQ (cubeStress (d+1)) K₀ M) (hK₀ : IsCompact K₀)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x fam.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (ht : fam.radialThreshold ≤ threshold)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rstar : ℕ) (hRstar : Rsource+fullLowReserve (d+1)+3 ≤ Rstar)
    (AQ AB Aphase : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) (hAphase : ∀ j, 0 ≤ Aphase j)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ωcoeff)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ωcoeff)
    (hmap : ∀ i, MapsTo (Q i) Ωcoeff (closedBall (cubeStress (d+1)) fam.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ M)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ M)
    (hQp : ∀ i j, cNorm (closedBall x RQ) j (Q i) ≤ AQ j * L i ^ (j-Rstar))
    (hBp : ∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i ^ (j-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (hsourceBand : ∀ i c, c ∈ V → ∀ y ∈ ball x (3*fam.physicalRadius),
      a₀ ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ B₀)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ ball x (3*fam.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource))
    (μ ψ : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hψ : Continuous ψ) (hμb : ∀ y, ‖μ y‖ ≤ 1) (hψb : ∀ y, ‖ψ y‖ ≤ 1)
    (hin : ∀ y ∈ S, ψ y = 1)
    (hib : ∀ y, ‖fam.inputMask y‖ ≤ 1)
    (W₁ : I → fam.centers → TwoTimeAmplitude d (d+1))
    (retarded : I → fam.centers → H →L[ℂ] H) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (measuredOperator μ ψ hμ.continuous hψ hμb hψb
          (selectedFullPairedResidualTerm fam hK₀ threshold (Q i) (B i) (W₁ i)
            output ho.continuous hob hib (retarded i) (Sum.inr ())))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))
      Adata K Rsource := by
  let raw := fun i ↦ (sourceCutMultiplier output ho.continuous hob : H →L[ℂ] H).comp
    (ellipticResidual fam hK₀ threshold (Q i) (B i))
  have he := actual_elliptic_normalized_reserved_ordered_bounds fam hK₀ hΩcoeff hball
    output ho hoc hos hob threshold ht basis hV hKpar hVK Rsource Rstar hRstar
    AQ AB Aphase hAQ hAB hAphase hν hν1 ha₀ hB₀ lam L K Adata hlam hL hLK hscale hAdata
    Q B hQ hB hmap hQl hBl hQp hBp φ hφ hcap hφjets hsourceBand S hS hSU a ha has Csource
    hfourier true false
  have hb : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (normalizedPair (raw i))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))
      (fun i ↦ lam i ^ (-1 : ℤ)*Adata i) K Rsource := by
    simpa only [ReservedLetterBounds,annularGraphOrientation,Bool.false_eq_true,↓reduceIte,
      mul_assoc,raw] using he.2
  have hm := reserved_bounds_measured_of_input_plateau hV
    (fun i ↦ normalizedPair (raw i)) lam (fun i ↦ lam i ^ (-1 : ℤ)*Adata i) K Rsource
    φ (fun i c ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    S hS a ha has μ ψ hμ hμc hψ hμb hψb hin hb
  have hfinal := hm.discard_inverse_frequency hlam hAdata
    (fun i ↦ zero_le_one.trans ((hL i).trans (hLK i)))
  simpa only [selectedFullPairedResidualTerm_elliptic,raw] using hfinal

end JanetCartan.PhysicalPrimary
