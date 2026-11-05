module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.RestrictionFactors.RealCompression
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly

/-!
# The original real source tail in the complex word chain

Only the first even proof localizer is compressed. Its reality identifies the
source leakage with complex inclusion of the existing real source leakage.
Individual complex residual letters are subsequently composed without projections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph LocalSobolev ResidualLocalization
open RegularSector.Realization RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- Complex inclusion identifies the original real source error for the SAME
bounded even right localizer. The restriction and zero extension are retained
(`app:ch_regular:eq:source-tail`, `app:ch_regular:lem:finite-chain`). -/
theorem complex_source_leakage_eq_of_even {U : Set E} (hU : MeasurableSet U)
    (ρ : ℝ) (mi : LocalizerSymbol (d+1))
    (heven : ∀ y ξ, mi (y,-ξ) = mi (y,ξ)) (M : H →L[ℂ] H)
    (hM : ∀ u, M u =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) (u : LocalL2 U RF) :
    l2ComplexInclusion (volume.restrict U) u -
        localRetardedOperator hU U M (l2ComplexInclusion (volume.restrict U) u) =
      l2ComplexInclusion (volume.restrict U) (u-localRealCompression hU U M u) := by
  rw [map_sub, inclusion_localRealCompression_of_star hU M
    (boundedRightLocalizer_star_of_even ρ mi heven M hM)]

/-- Apply the real first-mask source estimate to the complex input of every
signed residual word. The producer is
`InitialSourceLocalization.exists_retained_admittedSource_firstMask_rapidDecayAt`;
only its fixed fiber inclusion cost is added. This does not assume reality of
individual residual letters (`app:ch_regular:eq:source-tail`,
`app:ch_regular:lem:finite-chain`). -/
theorem complex_source_rapidDecayAt_of_even {ι : Type*} {U : Set E} (hU : MeasurableSet U)
    (ρ A : ι → ℝ) (mi : ι → LocalizerSymbol (d+1))
    (heven : ∀ i y ξ, mi i (y,-ξ) = mi i (y,ξ)) (M : ι → H →L[ℂ] H)
    (hM : ∀ i u, M i u =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (rightLocalizer (ρ i) (mi i) (fun z ↦ (u z).ofLp) y))
    (u : ι → LocalL2 U RF) (s : ℕ)
    (hsource : RapidDecayAt (restrictionSobolevScale U RF hU) s ρ A
      (fun i ↦ u i-localRealCompression hU U (M i) (u i))) :
    RapidDecayAt (restrictionSobolevScale U F hU) s ρ A
      (fun i ↦ l2ComplexInclusion (volume.restrict U) (u i) -
        localRetardedOperator hU U (M i) (l2ComplexInclusion (volume.restrict U) (u i))) := by
  intro accuracy
  obtain ⟨C, hC, hbound⟩ := hsource accuracy
  refine ⟨(‖euclideanComplexInclusion (ι := Fin q)‖+1)*C, by positivity, ?_⟩
  intro i
  dsimp only
  rw [complex_source_leakage_eq_of_even hU (ρ i) (mi i) (heven i) (M i) (hM i)]
  obtain ⟨hm, hn⟩ := compLp_restrictionSobolev_bound
    (euclideanComplexInclusion (ι := Fin q)) (hbound i).1
  refine ⟨hm, ?_⟩
  change (restrictionSobolevScale U F hU).gradeNorm s
    ((euclideanComplexInclusion (ι := Fin q)).compLp _) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU hm]
  apply hn.trans
  rw [← restrictionSobolevScale_gradeNorm hU (hbound i).1]
  exact (mul_le_mul_of_nonneg_left (hbound i).2 (by positivity)).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
