module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredPlateau

/-!
# The original real source in the complex chronological chain

The original inner cutoff supplies physical support, and the original outer
cutoff supplies its plateau. These deductions provide the support and low norm
inputs of `normalizedSource_alternatingChain_observation_rapidDecayAt` on the
same zero-extended real source. No source is selected at a new proof depth.
Source: `app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:source-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped NNReal ENNReal
namespace JanetCartan.RegularSector.NormalizedResidualWords.ObservedChains
open Realization Characteristic.RetardedLocalization Characteristic.EvolutionIntegral
open FourierIntegral.LowBounds LocalSobolev SmallSupport
open ArbitraryAccuracy.SelectedLocalization
variable {d : ℕ} {x : Euclidean (d+1)}
local notation "E" => Euclidean (d+1)
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The literal inner-cut source of `NormalizedCorrectedExpansion` has the
physical support used by `measuredResidual_hchain_of_individual_estimates`.
This includes the unchanged depth-zero source (`app:ch_regular:thm:exact-correction`). -/
theorem cut_source_ae_zero_off_support {D : Set E} (χ₂ : ContDiffBump x)
    (u : LocalL2 D RF) :
    ∀ᵐ y ∂volume.restrict D, y ∉ tsupport (χ₂ : E → ℝ) →
      bumpL2 (p := 2) le_rfl χ₂ u y = 0 := by
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₂ u] with y hy
  intro hs
  rw [hy, image_eq_zero_of_notMem_tsupport hs, zero_smul]

/-- The original physical support proves the complex source plateau after
its literal zero extension and whole-space restriction
(`app:ch_regular:lem:finite-chain`). -/
theorem complex_source_plateau_of_support {D : Set E} (hD : MeasurableSet D)
    (χ₂ χ₃ : ContDiffBump x)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) (u : LocalL2 D RF)
    (hsupport : ∀ᵐ y ∂volume.restrict D, y ∉ tsupport (χ₂ : E → ℝ) → u y = 0) :
    let source := restrictL2 univ (l2ComplexInclusion volume (zeroExtend hD u))
    sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
      (zeroExtend MeasurableSet.univ source) = zeroExtend MeasurableSet.univ source := by
  intro source
  dsimp only [source]
  rw [zeroExtend_restrictL2_univ]
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn χ₃ χ₃.continuous (bump_norm_le_one χ₃)
      (l2ComplexInclusion volume (zeroExtend hD u)),
    euclideanComplexInclusion.coeFn_compLpL (zeroExtend hD u),
    zeroExtend_coeFn hD u, (ae_restrict_iff' hD).mp hsupport] with y hm hi hz hs
  change l2ComplexInclusion volume (zeroExtend hD u) y =
    euclideanComplexInclusion (zeroExtend hD u y) at hi
  rw [hm, hi, hz]
  by_cases hyD : y ∈ D
  · rw [indicator_of_mem hyD]
    by_cases hyS : y ∈ tsupport (χ₂ : E → ℝ)
    · rw [hnest y hyS, Complex.ofReal_one, one_smul]
    · rw [hs hyD hyS, map_zero, smul_zero]
  · rw [indicator_of_notMem hyD, map_zero, smul_zero]

/-- The fixed source's inclusion, zero extension and whole-space restriction
are contractions, supplying the chronological source low norm without any
new frequency or history dependence (`app:ch_regular:lem:finite-chain`). -/
theorem complex_source_norm_le {D : Set E} (hD : MeasurableSet D) (u : LocalL2 D RF) :
    ‖restrictL2 univ (l2ComplexInclusion volume (zeroExtend hD u))‖ ≤ ‖u‖ := by
  calc
    _ ≤ ‖l2ComplexInclusion volume (zeroExtend hD u)‖ := by
      simpa only [one_mul] using (restrictL2 (d := d) (q := d+1) univ).le_of_opNorm_le
        (norm_restrictL2_le univ) (l2ComplexInclusion volume (zeroExtend hD u))
    _ ≤ ‖zeroExtend hD u‖ := by
      simpa only [one_mul] using (l2ComplexInclusion (ι := Fin (d+1)) volume).le_of_opNorm_le
        (l2ComplexInclusion_norm_le volume) (zeroExtend hD u)
    _ = ‖u‖ := LinearIsometry.norm_map _ _

end JanetCartan.RegularSector.NormalizedResidualWords.ObservedChains
