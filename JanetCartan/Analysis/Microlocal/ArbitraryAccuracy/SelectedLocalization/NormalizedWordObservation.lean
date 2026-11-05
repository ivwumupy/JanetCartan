module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedWordSupport
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedQuadratures

/-!
# Exact normalized observation after a complete measured word

The actual normalized source commutes with real projection of the complete
complex word. The original measurements justify every zero extension. No real
projection is inserted between letters (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.NormalizedSolver RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteResidual.FiniteIdentity
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization
open LocalSobolev ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

/-- The corrected source discrepancy acts on real part after the whole
local complex input. The supplied zero extension and target restriction are
literal; the single identity subtraction is unchanged
(`app:ch_regular:eq:resolved-angular-tail`, `real-sector-normalization`). -/
theorem local_normalizedSource_realPart_defect
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (W : Set E) (u : LocalL2 U V) :
    localRealCompression hU W (pairedSource f hK L output ho hob-1)
      (l2RealPart (volume.restrict U) u) =
    l2RealPart (volume.restrict W) (restrictL2 W
      ((pairedSource f hK L output ho hob-1) (SmallSupport.zeroExtend hU u))) := by
  apply Lp.ext
  have h := localRealCompression_coeFn hU W (pairedSource f hK L output ho hob-1)
    (l2RealPart (volume.restrict U) u)
  have he := compLp_zeroExtend (euclideanRealPart (ι := Fin (d+1))) hU u
  change l2RealPart volume (SmallSupport.zeroExtend hU u) =
    SmallSupport.zeroExtend hU (l2RealPart (volume.restrict U) u) at he
  rw [← he, ← SignedProductEstimates.normalizedSource_real_defect_eq_compression,
    show l2RealPart volume (SmallSupport.zeroExtend hU u) =
      l2RealPart volume ((1 : ℂ) • SmallSupport.zeroExtend hU u) by rw [one_smul],
    SignedProductEstimates.normalizedSource_real_quadrature_defect, one_smul] at h
  have hr : l2RealPart (volume.restrict W) (restrictL2 W
      ((pairedSource f hK L output ho hob-1) (SmallSupport.zeroExtend hU u))) =ᵐ[volume.restrict W]
    l2RealPart volume ((pairedSource f hK L output ho hob-1) (SmallSupport.zeroExtend hU u)) := by
    filter_upwards [euclideanRealPart.coeFn_compLpL (restrictL2 W
        ((pairedSource f hK L output ho hob-1) (SmallSupport.zeroExtend hU u))),
      restrictL2_coeFn W ((pairedSource f hK L output ho hob-1) (SmallSupport.zeroExtend hU u)),
      ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL
        ((pairedSource f hK L output ho hob-1) (SmallSupport.zeroExtend hU u)))] with y hy hz hw
    exact hy.trans ((congrArg euclideanRealPart hz).trans hw.symm)
  exact h.trans hr.symm

/-- Identify the normalized observation of every complete signed local
word with the restriction of its whole-space complex observation. The original
measurements prove intermediate support absorption, including elliptic and
reflected letters. Consumer: the local-word finite sum of
`NormalizedResidualWords.measured_realResidual_hchain_of_words`
(`app:ch_regular:eq:chain-tail`). -/
theorem normalizedSource_selectedWord_observation_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U)
    (hμU : tsupport μ ⊆ U) (hνU : tsupport ν ⊆ U)
    (W : Set E) (w : List (((f.centers × Fin 3) ⊕ Unit) × Bool)) (u : LocalL2 U RV) :
    let P := fun a ↦ measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a)
    let J := fun a ↦ localRetardedOperator hU U (P a)
    let D := pairedSource f hK L output ho hob-1
    localRealCompression hU W D (l2RealPart (volume.restrict U)
      ((w.map J).prod (l2ComplexInclusion (volume.restrict U) u))) =
    l2RealPart (volume.restrict W) (restrictL2 W (D ((w.map P).prod
      (l2ComplexInclusion volume (SmallSupport.zeroExtend hU u))))) := by
  intro P J D
  rw [local_normalizedSource_realPart_defect]
  rw [selectedFullPhysicalResidualWord_zeroExtend f hK L Q B W₁ output ho hob hib T
    μ ν hμ hν hμb hνb hU hμU hνU]
  have hi := compLp_zeroExtend (euclideanComplexInclusion (ι := Fin (d+1))) hU u
  change l2ComplexInclusion volume (SmallSupport.zeroExtend hU u) =
    SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) at hi
  rw [hi]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
