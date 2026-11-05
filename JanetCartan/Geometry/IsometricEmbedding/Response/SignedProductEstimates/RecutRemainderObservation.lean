module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedCorrectedExpansion
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.Normalized.Real

/-!
# Angular observation of the same normalized inverse remainder

The outer inverse bump fixes every finite inverse remainder on the actual
inner-cut datum, including depth zero. Its complex zero extension therefore
has exactly the input plateau needed by the existing normalized source cost.
Apply that cost to the complete source minus one identity, retaining the
physical output measurement and both inverse masks. The source operator has
order zero; all decay comes from the signed inverse remainder estimate.

Consumers: the remainder in `normalized_correctedSource_angular_finite_expansion`
and `UniformStep.SampledProduct`. Sources: `app:ch_regular:eq:finite-observation`
and `app:ch_pairs:eq:pairs-lag-one-error`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization LocalSobolev FixedDomainInverse SmallSupport
open FourierIntegral.LowBounds
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The output bump of the literal measured residual gives the original
outer plateau on its real compression (`app:ch_regular:thm:exact-correction`). -/
private theorem recut_real_measured_plateau {U : Set E} (hU : MeasurableSet U)
    (χ₂ χ₃ : ContDiffBump center)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1)
    (T : H →L[ℂ] H) (u : LocalL2 U E) :
    let R := localRealCompression hU U (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃) T)
    bumpL2 (p := 2) le_rfl χ₃ (R u) = R u := by
  intro R
  let z := T (sourceCutMultiplier χ₃ χ₃.continuous (bump_norm_le_one χ₃)
    (zeroExtend hU (l2ComplexInclusion (volume.restrict U) u)))
  change bumpL2 (p := 2) le_rfl χ₃ (l2RealPart (volume.restrict U)
    (restrictL2 U (sourceCutMultiplier χ₂ χ₂.continuous (bump_norm_le_one χ₂) z))) = _
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₃ (R u),
    euclideanRealPart.coeFn_compLpL
      (restrictL2 U (sourceCutMultiplier χ₂ χ₂.continuous (bump_norm_le_one χ₂) z)),
    restrictL2_coeFn U (sourceCutMultiplier χ₂ χ₂.continuous (bump_norm_le_one χ₂) z),
    ae_restrict_of_ae (sourceCutMultiplier_coeFn χ₂ χ₂.continuous (bump_norm_le_one χ₂) z)]
    with y hb hr hl hm
  change (R u) y = _ at hr
  change (bumpL2 (p := 2) le_rfl χ₃ (R u)) y = _
  rw [hb]
  by_cases hy : y ∈ tsupport (χ₂ : E → ℝ)
  · rw [hnest y hy, one_smul]
  · rw [hr, hl, hm, image_eq_zero_of_notMem_tsupport hy]
    simp

/-- The outer inverse bump fixes every finite normalized inverse remainder
on the actual inner-cut datum (`app:ch_regular:eq:inverse-remainder`). -/
theorem normalized_inverse_remainder_source_plateau
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : H →L[ℂ] H)
    {U : Set E} (hU : MeasurableSet U) (χ₂ χ₃ : ContDiffBump center)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1)
    (j : ℕ) (u : LocalL2 U E) :
    let R := localRealCompression hU U (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
      (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
      (pairedResidual f hK L₀ Q B output ho hob W₁ retarded))
    ‖R‖ < 1 →
    let v := neumannInverse R ((R^j) (bumpL2 (p := 2) le_rfl χ₂ u))
    bumpL2 (p := 2) le_rfl χ₃ v = v := by
  intro R hR v
  let P := bumpL2 (p := 2) (F := E) (μ := volume.restrict U) le_rfl χ₃
  have hfixR (z : LocalL2 U E) : P (R z) = R z :=
    recut_real_measured_plateau hU χ₂ χ₃ hnest _ z
  have hfix₀ : P (bumpL2 (p := 2) le_rfl χ₂ u) = bumpL2 (p := 2) le_rfl χ₂ u := by
    apply Lp.ext
    filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₃ (bumpL2 (p := 2) le_rfl χ₂ u),
      bumpL2_coeFn (p := 2) le_rfl χ₂ u] with y h₃ h₂
    rw [h₃]
    by_cases hy : y ∈ tsupport (χ₂ : E → ℝ)
    · rw [hnest y hy, one_smul]
    · rw [h₂, image_eq_zero_of_notMem_tsupport hy]
      simp
  have hfixj : P ((R^j) (bumpL2 (p := 2) le_rfl χ₂ u)) =
      (R^j) (bumpL2 (p := 2) le_rfl χ₂ u) := by
    cases j with
    | zero => exact hfix₀
    | succ j =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        hfixR ((R^j) (bumpL2 (p := 2) le_rfl χ₂ u))
  change P v = v
  calc
    P v = P (((R^j) (bumpL2 (p := 2) le_rfl χ₂ u)) - R v) :=
      congrArg P (neumannInverse_eq_sub R hR _)
    _ = ((R^j) (bumpL2 (p := 2) le_rfl χ₂ u)) - R v :=
      (P.map_sub _ _).trans (congrArg₂ (fun a b : LocalL2 U E ↦ a - b) hfixj (hfixR v))
    _ = v := (neumannInverse_eq_sub R hR _).symm

/-- The complex zero extension of a locally fixed real datum is fixed by
that same original mask (`app:ch_regular:eq:inverse-remainder`). -/
private theorem recut_complex_source_plateau {U : Set E} (hU : MeasurableSet U)
    (χ : ContDiffBump center) (u : LocalL2 U E)
    (hfix : bumpL2 (p := 2) le_rfl χ u = u) :
    sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ)
      (zeroExtend hU (l2ComplexInclusion (volume.restrict U) u)) =
        zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) := by
  have hp : ∀ᵐ y ∂volume.restrict U, χ y • u y = u y := by
    have hh := bumpL2_coeFn (p := 2) le_rfl χ u
    rw [hfix] at hh
    exact hh.symm
  have hc : bumpL2 (p := 2) le_rfl χ (l2ComplexInclusion (volume.restrict U) u) =
      l2ComplexInclusion (volume.restrict U) u := by
    apply Lp.ext
    filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ (l2ComplexInclusion (volume.restrict U) u),
      euclideanComplexInclusion.coeFn_compLpL u, hp] with y hb hi hy
    change (l2ComplexInclusion (volume.restrict U) u) y = _ at hi
    rw [hb, hi, ← map_smul, hy]
  rw [sourceCutMultiplier_zeroExtend_bump, hc]

/-- The actual normalized source discrepancy observes the finite inverse
remainder with order zero, using the SAME outer-bump plateau. Its constants
precede the final radial threshold, coefficients, residual, depth and source.
Only the supplied compact measurement masks enter this cost. Decay comes from
`exists_normalized_innerCut_product_inverse_remainder_constants`, not from a
gain assigned to the angular source (`app:ch_regular:eq:finite-observation`,
`app:ch_pairs:eq:pairs-lag-one-error`). -/
theorem exists_normalized_inverse_remainder_observation_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (χ₂ χ₃ : ContDiffBump center)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1)
    (μ : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ L₀ : ℝ, f.radialThreshold ≤ L₀ →
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
        (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : H →L[ℂ] H)
        (U Vout : Set E) (hU : MeasurableSet U) (_hV : MeasurableSet Vout),
        tsupport (χ₃ : E → ℝ) ⊆ U → tsupport μ ⊆ Vout →
      let R := localRealCompression hU U
        (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
          (pairedResidual f hK L₀ Q B output ho.continuous hob W₁ retarded))
      ∀ (j : ℕ) (u : LocalL2 U E), ‖R‖ < 1 →
      let v := neumannInverse R ((R^j) (bumpL2 (p := 2) le_rfl χ₂ u))
      ∀ s, MemRestrictionSobolev U s v →
      let A := localRealCompression hU Vout
        ((sourceCutMultiplier μ hμ.continuous hμb).comp
          (pairedSource f hK L₀ output ho.continuous hob - 1))
      MemRestrictionSobolev Vout s (A v) ∧
        restrictionSobolevNorm Vout s (A v) ≤ C s * restrictionSobolevNorm U s v := by
  obtain ⟨C, hC, hcost⟩ := exists_normalizedRealSource_measured_discrepancy_signed_constants
    f hK output ho hoc hob μ χ₃ hμ χ₃.contDiff hμc χ₃.hasCompactSupport
    hμb (bump_norm_le_one χ₃)
  refine ⟨C, hC, ?_⟩
  intro L₀ hL Q B W₁ retarded U Vout hU hV hχ₃U hμV R j u hR v s hv A
  have hfix := normalized_inverse_remainder_source_plateau f hK L₀ Q B output
    ho.continuous hob W₁ retarded hU χ₂ χ₃ hnest j u hR
  have hz := recut_complex_source_plateau hU χ₃ v hfix
  let D := pairedSource f hK L₀ output ho.continuous hob - 1
  have he : localRealCompression hU Vout
      (measuredOperator μ χ₃ hμ.continuous χ₃.continuous hμb (bump_norm_le_one χ₃) D) v = A v := by
    exact congrArg (fun z : H ↦ l2RealPart (volume.restrict Vout)
      (restrictL2 Vout (sourceCutMultiplier μ hμ.continuous hμb (D z)))) hz
  exact he ▸ (hcost L₀ hL U Vout hU hV hχ₃U hμV s).1 v hv

end JanetCartan.SignedProductEstimates
