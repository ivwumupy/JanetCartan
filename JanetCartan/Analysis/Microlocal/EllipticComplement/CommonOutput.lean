module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.TestedEquation
public import JanetCartan.Analysis.Microlocal.EllipticComplement.Sobolev
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Support.Multipliers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.PdoMasks

/-!
# The common outer cutoff in the selected finite sum

The additional multiplication used by `selectedFiniteDirectSolver` can be
retained literally. Its derivative vanishes on the parent's actual plateau
and its adjoint places the multiplier on the right. The existing original
physical masks inside the complementary PDOs are unchanged. Source:
`app:ch_regular_base:eq:energy-complete-residual`, `measured-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open ActualCarriers FiniteMasks.ActualFamily Characteristic.EvolutionIntegral FiniteAssembly
open FiniteResidual.SelectedChart FourierIntegral LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The same extra common output as the characteristic solver may be placed
on all three elliptic terms. The tested equation holds on its proved plateau
inside the original measurement ball (`sector-theorem-identity`). -/
theorem commonOutput_ellipticSolver_tested (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (hsub : U ⊆ ball x f.physicalRadius)
    (hone : ∀ y ∈ U, output y = 1) {L : ℝ} (hL : f.radialThreshold ≤ L)
    (Q : E → Coeff) (B : E → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (hQl : cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M)
    (hBl : cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M) :
    let O := sourceCutMultiplier output ho hob
    ∀ (u : H) φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction (fun y a ↦ pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (O.comp (ellipticSolver f hK L Q) u y).ofLp) φ j =
        ∫ y, φ y • O.comp (ellipticSourcePDO f hK L + ellipticResidual f hK L Q B) u y j :=
  tested_equation_sourceCutMultiplier _ B _ _ output ho hob hU hone
    (fun u φ hφ hc hs j ↦ ellipticSolver_tested f hK hΩ hRQΩ hL Q B hQ hB hmap hQl hBl
      u φ hφ hc (hs.trans hsub) j)

/-- The original source cutoff and the common output are on the same
respective sides of each complementary term, so the retained restriction
plateaux of the parent absorb literally. Consumer:
`exists_local_sourceCut_paired_restriction_constants` (`measured-adjoint`). -/
theorem commonOutput_elliptic_plateau_identities (L : ℝ) (Q : E → Coeff) (B : E → Mat)
    (output χ ψ : E → ℝ) (ho : Continuous output) (hχ : ContDiff ℝ ∞ χ) (hψ : Continuous ψ)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hχb : ∀ y, ‖χ y‖ ≤ 1) (hψb : ∀ y, ‖ψ y‖ ≤ 1)
    (hχp : ∀ y ∈ tsupport f.inputMask, χ y = 1) (hψp : ∀ y ∈ tsupport output, ψ y = 1) :
    ∀ T ∈ ({ellipticSolver f hK L Q, ellipticResidual f hK L Q B} : Set (H →L[ℂ] H)),
    let S := (sourceCutMultiplier output ho hob).comp T
    S.comp (sourceCutMultiplier χ hχ.continuous hχb) = S ∧
      (sourceCutMultiplier ψ hψ hψb).comp S = S := by
  intro T hT S
  have hp (s : E → E → CMat) :
      (maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ)) (fun z ↦ (f.inputMask z : ℂ)) s).comp
        (sourceCutMultiplier χ hχ.continuous hχb) =
        maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ)) (fun z ↦ (f.inputMask z : ℂ)) s :=
    (maskedPhysicalPDO_plateau_identities _ _ s (fun _ ↦ 1) χ continuous_const hχ
      (fun _ ↦ by simp) hχb (fun _ _ ↦ rfl)
      (fun y hy ↦ hχp y (tsupport_comp_subset Complex.ofReal_zero f.inputMask hy))).2
  have hTχ : T.comp (sourceCutMultiplier χ hχ.continuous hχb) = T := by
    rcases hT with he | he
    · rw [he, ellipticSolver, ContinuousLinearMap.smul_comp, hp]
    · change T = ellipticResidual f hK L Q B at he
      rw [he, ellipticResidual, ContinuousLinearMap.smul_comp, hp]
  refine ⟨by dsimp only [S]; rw [ContinuousLinearMap.comp_assoc, hTχ], ?_⟩
  dsimp only [S]
  rw [← ContinuousLinearMap.comp_assoc, (sourceCutMultiplier_plateau_comp
    (q := d+1) output ψ ho hψ hob hψb hψp).2]

end JanetCartan.RegularSector.EllipticComplement
