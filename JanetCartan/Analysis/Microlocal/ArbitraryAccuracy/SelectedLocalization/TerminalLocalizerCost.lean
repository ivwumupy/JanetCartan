module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.WholeSpaceRestriction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Ordinary
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerAdjoint
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Chains.Decay

/-!
# Polynomial cost of the prescribed terminal right localizer

The terminal mask is fixed before history and accuracy. Its actual compact
kernel supplies the cost on the whole-space restriction scale used in
`app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph LocalSobolev ResponseTransfer
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral
open ResidualLocalization ResidualLocalization.IdentityDefect
variable {d q : ℕ} {ι : Type*}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- The SAME bounded right realization of the fixed terminal symbol has
polynomial Sobolev cost. This applies the primitive kernel estimate and the
literal adjoint identity; it imposes no new bound on the realization
(`app:ch_regular:eq:chain-tail`). -/
theorem terminalRightLocalizer_hasPolynomialRestrictionCost
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    (ρ : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (Mt : ι → H →L[ℂ] H)
    (hMt : ∀ i u, Mt i u =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (rightLocalizer (ρ i) mt (fun z ↦ (u z).ofLp) y)) :
    HasPolynomialSobolevCost
      (restrictionSobolevScale univ V MeasurableSet.univ)
      (restrictionSobolevScale univ V MeasurableSet.univ) ρ
      (fun i ↦ (localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap) := by
  intro s
  obtain ⟨C, hC, hbound⟩ := exists_leftLocalizer_adjoint_sobolev_bound (r := q) mt ht htc s
  obtain ⟨D, hD, hcompare⟩ := exists_restrictionScale_fourier_comparison (d+1) q s
  refine ⟨0, (d+1+s : ℕ), D*C, mul_nonneg hD.le hC, ?_⟩
  intro i u _
  have hl := leftLocalizer_adjoint_ae_of_rightLocalizer
    (zero_lt_one.trans_le (hρ i)).ne' mt ht.continuous htc (Mt i) (hMt i)
  have h := hbound (ρ i) (hρ i) (Mt i).adjoint hl (SmallSupport.zeroExtend MeasurableSet.univ u)
  simp only [ContinuousLinearMap.adjoint_adjoint] at h
  obtain ⟨hm, hn⟩ := hcompare univ MeasurableSet.univ _ _ h.1
    (restrictL2_coeFn univ _).symm
  refine ⟨hm, hn.trans ?_⟩
  simpa only [GradedScale.gradeNorm_zero, LinearIsometry.norm_map, Real.rpow_natCast, mul_assoc]
    using mul_le_mul_of_nonneg_left h.2 hD.le

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
