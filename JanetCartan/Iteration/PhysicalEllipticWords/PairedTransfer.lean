module

public import JanetCartan.Iteration.PhysicalEllipticWords.PairedOperations
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.PhysicalSourceProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PhysicalPairing
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Physical

/-!
# Literal physical sources and measurement of paired chart letters

The source is pulled back only by the original coordinate permutation. The
measurement keeps its two original masks; the input plateau is used only on the
actual supported datum, and the output multiplier is estimated without any
plateau or reselected PDO certificate. Consumer: the endpoint/algebraic `hstep`
of the original complete finite residual alphabet.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology JanetCartan.RegularSector.Realization
namespace JanetCartan.PhysicalEllipticWords
open Pseudodifferential FourierIntegral FourierIntegral.LowBounds
open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.RetainedFactors
open ResponseTransfer.DirectEvolution.CompactTransfer
open ResponseTransfer.RetainedCharacteristicEnvelopes
open RegularSector.Realization RegularSector.NormalizedSolver RegularSector.FiniteEvolution
open RegularSector.Characteristic.ResidualCoordinates RegularSector.FiniteAssembly
open ArbitraryAccuracy.SelectedLocalization

variable {d : ℕ} {I : Type}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d + 1))
local notation "H" => Lp F 2 (volume : Measure E)

/-- The exact original source in the selected physical coordinates. -/
def pairedChartSource (index : Fin (d + 1)) (a : E × Par → F) : E × Par → F :=
  fun q ↦ a (physicalCoordinates index q.1, q.2)

/-- The original coordinate permutation preserves the full smooth source. -/
theorem pairedChartSource_smooth (index : Fin (d + 1)) (a : E × Par → F)
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (pairedChartSource index a) :=
  ha.comp (((physicalCoordinates index).contDiff.comp contDiff_fst).prodMk contDiff_snd)

/-- Actual source support, with no enlargement of the phase domain. -/
theorem pairedChartSource_supported (index : Fin (d + 1)) (a : E × Par → F)
    (S : Set E) (has : ∀ q, q.1 ∉ S → a q = 0) :
    ∀ q, q.1 ∉ physicalCoordinates index ⁻¹' S → pairedChartSource index a q = 0 :=
  fun q hq ↦ has (physicalCoordinates index q.1, q.2) hq

/-- The literal test representative is the original physical L² pullback. -/
theorem pairedChartSource_test_eq (index : Fin (d + 1)) (a : E × Par → F)
    (ha : ContDiff ℝ ∞ a) (S : Set E) (hS : IsCompact S)
    (has : ∀ q, q.1 ∉ S → a q = 0) (c : Par) :
    graphTestToLp (vectorOriginalDatumTest (pairedChartSource index a)
      (pairedChartSource_smooth index a ha)
      ((physicalCoordinates index).toHomeomorph.isCompact_preimage.mpr hS)
      (pairedChartSource_supported index a S has) [] c) =
    physicalPullbackL2 index (graphTestToLp (vectorOriginalDatumTest a ha hS has [] c)) := by
  apply Lp.ext
  have he := (measurePreserving_physicalCoordinates index).quasiMeasurePreserving.ae_eq_comp
    (vectorOriginalDatumTest_toLp_ae a ha hS has [] c)
  filter_upwards [physicalPullbackL2_coeFn index _, he,
    vectorOriginalDatumTest_toLp_ae (pairedChartSource index a)
      (pairedChartSource_smooth index a ha)
      ((physicalCoordinates index).toHomeomorph.isCompact_preimage.mpr hS)
      (pairedChartSource_supported index a S has) [] c] with y hy hp ha'
  simpa only [Function.comp_apply, originalDatumDerivative, orderedTransferAction, pairedChartSource]
    using (hy.trans (hp.trans ha'.symm)).symm

/-- Every source Fourier jet is transported with constant one and the exact
natural reserve (`app:ch_response:eq:response-graded-reduced`). -/
theorem pairedChartSource_fourier (index : Fin (d + 1))
    (a : I → E × Par → F) (A K : I → ℝ) (reserve : ℕ) (V : Set Par)
    (Csource : ℕ → ℕ → ℝ)
    (hsource : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y, q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * A i * K i ^ (s + l - reserve)) :
    ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ pairedChartSource index (a i) (y, q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * A i * K i ^ (s + l - reserve) := by
  intro i c hc l w hw s
  obtain ⟨hm, hmem, hb⟩ := hsource i c hc l w hw s
  obtain ⟨hmc, _he, hmemc, hnorm⟩ :=
    fullSource_parameterWord_fourier_physicalPullback index (a i) c l w hm (s : ℝ)
  exact ⟨hmc, hmemc.mpr hmem, hnorm.trans_le hb⟩

/-- Pulling back the actual source ball preserves its radius and center. -/
theorem pairedChartSource_ball (index : Fin (d + 1)) {S : Set E} {x : E} {r : ℝ}
    (hS : S ⊆ ball x r) :
    physicalCoordinates index ⁻¹' S ⊆ ball ((physicalCoordinates index).symm x) r := by
  intro y hy
  have hd := (physicalCoordinateIsometry index).dist_map y ((physicalCoordinates index).symm x)
  change dist (physicalCoordinates index y)
    (physicalCoordinates index ((physicalCoordinates index).symm x)) =
    dist y ((physicalCoordinates index).symm x) at hd
  rw [ContinuousLinearEquiv.apply_symm_apply] at hd
  change dist y ((physicalCoordinates index).symm x) < r
  rw [← hd]
  exact hS hy

/-- Physical transport retains the whole normalized pair and its complex
scalar. Both halves remain external halves of the same original operator. -/
theorem physicalOperator_normalized_scalar_pair (index : Fin (d + 1))
    (T : H →L[ℂ] H) (z : ℂ) :
    physicalOperator index (normalizedPair (z • T)) =
      normalizedPair (z • physicalOperator index T) := by
  have hz : physicalOperator index (z • T) = z • physicalOperator index T := by
    ext1 u
    simp only [physicalOperator_apply, smul_apply, map_smul]
  rw [normalizedPair_eq, normalizedPair_eq]
  have hc := physicalOperator_boundedConjugate index (z • T)
  ext1 u
  change (physicalPullbackL2 index).symm
    ((1 / 2 : ℂ) • ((z • T) (physicalPullbackL2 index u) +
      boundedConjugate (z • T) (physicalPullbackL2 index u))) = _
  rw [map_smul, map_add]
  change (1 / 2 : ℂ) • (physicalOperator index (z • T) u +
    physicalOperator index (boundedConjugate (z • T)) u) = _
  rw [hz, hc, hz]
  rfl

private theorem paired_sourceCut_carrier_commute
    (μ : E → ℝ) (hμ : Continuous μ) (hμb : ∀ y, ‖μ y‖ ≤ 1)
    (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    sourceCutMultiplier μ hμ hμb (carrierMultiplication lam φ hφ u) =
      carrierMultiplication lam φ hφ (sourceCutMultiplier μ hμ hμb u) := by
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn μ hμ hμb (carrierMultiplication lam φ hφ u),
    carrierMultiplication_ae lam φ hφ u,
    carrierMultiplication_ae lam φ hφ (sourceCutMultiplier μ hμ hμb u),
    sourceCutMultiplier_coeFn μ hμ hμb u] with y h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  exact smul_comm _ _ _

private theorem paired_input_plateau (ν : E → ℝ) (hν : Continuous ν)
    (hνb : ∀ y, ‖ν y‖ ≤ 1) (S : Set E) (hS : IsCompact S)
    (hin : ∀ y ∈ S, ν y = 1) (a : E × Par → F) (ha : ContDiff ℝ ∞ a)
    (has : ∀ q, q.1 ∉ S → a q = 0) (c : Par) (lam : ℝ)
    (φ : E → ℝ) (hφ : Continuous φ) :
    sourceCutMultiplier ν hν hνb
      (carrierMultiplication lam φ hφ (graphTestToLp (vectorOriginalDatumTest a ha hS has [] c))) =
      carrierMultiplication lam φ hφ (graphTestToLp (vectorOriginalDatumTest a ha hS has [] c)) := by
  let u := graphTestToLp (vectorOriginalDatumTest a ha hS has [] c)
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn ν hν hνb (carrierMultiplication lam φ hφ u),
    carrierMultiplication_ae lam φ hφ u, vectorOriginalDatumTest_toLp_ae a ha hS has [] c]
    with y h₁ h₂ h₃
  rw [h₁, h₂]
  by_cases hy : y ∈ S
  · rw [hin y hy, Complex.ofReal_one, one_smul]
  · rw [show u y = a (y, c) from h₃, has (y, c) hy, smul_zero, smul_zero]

/-- The precise measurement step on the actual physical source. The only
response input is the complete chart estimate, supplied by the actual endpoint,
algebraic or retarded constructor. No bound for a recut response is assumed. -/
theorem measured_physical_reserved_bounds
    {V : Set Par} (hV : IsOpen V) (index : Fin (d + 1))
    (T : I → H →L[ℂ] H) (lam A K : I → ℝ) (reserve : ℕ)
    (φ : I → E → Par → ℝ) (hφ : ∀ i c, Continuous (fun y ↦ φ i y c))
    (S : Set E) (hS : IsCompact S) (a : I → E × Par → F)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (has : ∀ i q, q.1 ∉ S → a i q = 0)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hν : Continuous ν) (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (hin : ∀ y ∈ S, ν y = 1)
    (hchart : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i)
        (fun y ↦ φ i (physicalCoordinates index y) c)
        ((hφ i c).comp (physicalCoordinates index).continuous) (T i)
        (physicalPullbackL2 index
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))) A K reserve) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        (measuredOperator μ ν hμ.continuous hν hμb hνb (physicalOperator index (T i)))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) A K reserve := by
  let u := fun i c ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)
  have hp := hchart.physical hV index
  have hphys : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        (physicalOperator index (T i)) (u i c)) A K reserve := by
    simpa only [demodulatedL2Operator_physicalOperator, physicalOperator_apply, u,
      Function.comp_def] using hp
  have hc := hphys.cut hV μ hμ hμc hμb
  have he : (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
      (measuredOperator μ ν hμ.continuous hν hμb hνb (physicalOperator index (T i))) (u i c)) =
      (fun i c ↦ sourceCutMultiplier μ hμ.continuous hμb
        (demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
          (physicalOperator index (T i)) (u i c))) := by
    funext i c
    have hi := paired_input_plateau ν hν hνb S hS hin (a i) (ha i) (has i) c
      (lam i) (fun y ↦ φ i y c) (hφ i c)
    simp only [demodulatedL2Operator, measuredOperator, ContinuousLinearMap.comp_apply]
    rw [show sourceCutMultiplier ν hν hνb
      (carrierMultiplication (lam i) (fun y ↦ φ i y c) (hφ i c) (u i c)) =
        carrierMultiplication (lam i) (fun y ↦ φ i y c) (hφ i c) (u i c) from hi]
    exact (paired_sourceCut_carrier_commute μ hμ.continuous hμb
      (-(lam i)) (fun y ↦ φ i y c) (hφ i c) _).symm
  change ReservedLetterBounds V
    (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
      (measuredOperator μ ν hμ.continuous hν hμb hνb (physicalOperator index (T i))) (u i c)) A K reserve
  rw [he]
  exact hc

end JanetCartan.PhysicalEllipticWords
