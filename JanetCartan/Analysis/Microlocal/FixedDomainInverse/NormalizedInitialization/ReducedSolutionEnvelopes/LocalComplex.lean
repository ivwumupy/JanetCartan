module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ComplexInverse
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Physical

/-!
# The original localized operator as a complex linear map

The normalized inverse records its local operator using the underlying real
Hilbert space. Restriction and zero extension also commute with complex
scalars. This file bundles that SAME formula over `ℂ`, so the original real
contraction applies to the complex Neumann series in
`app:ch_response:eq:response-graded-reduced`. No local operator is chosen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped JanetCartan.RegularSector.Realization
open scoped ENNReal NNReal

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport RegularSector RegularSector.Realization
open RegularSector.Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem bumpL2_complex_smul {U : Set E} {x : E} (χ : ContDiffBump x)
    (c : ℂ) (u : LocalL2 U F) :
    bumpL2 (p := 2) le_rfl χ (c • u) = c • bumpL2 (p := 2) le_rfl χ u := by
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ (c • u),
    Lp.coeFn_smul c u, Lp.coeFn_smul c (bumpL2 (p := 2) le_rfl χ u),
    bumpL2_coeFn (p := 2) le_rfl χ u] with y hb hs hc hu
  rw [hb, hs, hc, Pi.smul_apply, Pi.smul_apply, hu]
  exact smul_comm _ _ _

private theorem bumpL2_complex_inclusion {U : Set E} {x : E} (χ : ContDiffBump x)
    (u : LocalL2 U (EuclideanSpace ℝ (Fin q))) :
    bumpL2 (p := 2) le_rfl χ (l2ComplexInclusion (volume.restrict U) u) =
      l2ComplexInclusion (volume.restrict U) (bumpL2 (p := 2) le_rfl χ u) := by
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ (l2ComplexInclusion (volume.restrict U) u),
    euclideanComplexInclusion.coeFn_compLpL u,
    euclideanComplexInclusion.coeFn_compLpL (bumpL2 (p := 2) le_rfl χ u),
    bumpL2_coeFn (p := 2) le_rfl χ u] with y hb hi hc hu
  change (l2ComplexInclusion (volume.restrict U) u : E → F) y = _ at hi
  change (l2ComplexInclusion (volume.restrict U) (bumpL2 (p := 2) le_rfl χ u) : E → F) y = _ at hc
  rw [hb, hi, hc, hu]
  exact (euclideanComplexInclusion.map_smul (χ y) (u y)).symm

/-- The original real bump acts on both quadratures before they are combined.
This identifies the inner recut source and the outer plateau of the SAME
complex inverse (`app:ch_response:eq:response-actual-solver-formula`). -/
theorem bumpL2_complex_quadratures {U : Set E} {x : E} (χ : ContDiffBump x)
    (u v : LocalL2 U (EuclideanSpace ℝ (Fin q))) :
    bumpL2 (p := 2) le_rfl χ
        (l2ComplexInclusion (volume.restrict U) u +
          Complex.I • l2ComplexInclusion (volume.restrict U) v) =
      l2ComplexInclusion (volume.restrict U) (bumpL2 (p := 2) le_rfl χ u) +
        Complex.I • l2ComplexInclusion (volume.restrict U) (bumpL2 (p := 2) le_rfl χ v) := by
  rw [map_add, bumpL2_complex_smul, bumpL2_complex_inclusion, bumpL2_complex_inclusion]

private theorem zeroExtend_complex_smul {U : Set E} (hU : MeasurableSet U)
    (c : ℂ) (u : LocalL2 U F) :
    zeroExtend hU (c • u) = c • zeroExtend hU u := by
  apply Lp.ext
  filter_upwards [zeroExtend_coeFn hU (c • u),
    zeroExtend_coeFn hU u, Lp.coeFn_smul c (zeroExtend hU u),
    (ae_restrict_iff' hU).mp (Lp.coeFn_smul c u)] with x hx hu hc hs
  rw [hx, hc, Pi.smul_apply, hu]
  by_cases hi : x ∈ U
  · simp only [indicator_of_mem hi, hs hi, Pi.smul_apply]
  · simp only [indicator_of_notMem hi, smul_zero]

private theorem restrictL2_complex_smul (U : Set E) (c : ℂ) (u : H) :
    restrictL2 U (c • u) = c • restrictL2 U u := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn U (c • u),
    ae_restrict_of_ae (Lp.coeFn_smul c u), Lp.coeFn_smul c (restrictL2 U u),
    restrictL2_coeFn U u] with x hx hs hc hu
  rw [hx, hs, hc, Pi.smul_apply, Pi.smul_apply, hu]

/-- The two original real quadratures combine before zero extension, with
the original restriction measure unchanged. This identifies the complex
Neumann output with the SAME globally represented smooth solver
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem zeroExtend_complex_quadratures {U : Set E} (hU : MeasurableSet U)
    (u v : LocalL2 U (EuclideanSpace ℝ (Fin q))) :
    zeroExtend hU (l2ComplexInclusion (volume.restrict U) u +
        Complex.I • l2ComplexInclusion (volume.restrict U) v) =
      l2ComplexInclusion volume (zeroExtend hU u) +
        Complex.I • l2ComplexInclusion volume (zeroExtend hU v) := by
  rw [map_add, zeroExtend_complex_smul]
  have hu := compLp_zeroExtend (euclideanComplexInclusion (ι := Fin q)) hU u
  have hv := compLp_zeroExtend (euclideanComplexInclusion (ι := Fin q)) hU v
  change l2ComplexInclusion volume (zeroExtend hU u) =
    zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) at hu
  change l2ComplexInclusion volume (zeroExtend hU v) =
    zeroExtend hU (l2ComplexInclusion (volume.restrict U) v) at hv
  exact congrArg₂ (· + ·) hu.symm (congrArg (Complex.I • ·) hv.symm)

/-- The actual zero-extension/operator/restriction formula is complex-linear.
Restricting scalars recovers the existing local operator definitionally.
Consumer: the SAME normalized measured residual's complex Neumann series
(`app:ch_regular:eq:neumann-series`,
`app:ch_response:eq:response-actual-solver-formula`). -/
def complexLocalRetardedOperator {U : Set E} (hU : MeasurableSet U) (V : Set E)
    (T : H →L[ℂ] H) : LocalL2 U F →L[ℂ] LocalL2 V F where
  toFun := localRetardedOperator hU V T
  map_add' := map_add _
  map_smul' c u := by
    change restrictL2 V (T (zeroExtend hU (c • u))) =
      c • restrictL2 V (T (zeroExtend hU u))
    rw [zeroExtend_complex_smul, map_smul, restrictL2_complex_smul]
  cont := (localRetardedOperator hU V T).continuous

/-- The complex bundle has the SAME underlying local real operator
(`app:ch_regular:eq:neumann-series`). -/
@[simp] theorem complexLocalRetardedOperator_restrictScalars
    {U : Set E} (hU : MeasurableSet U) (V : Set E) (T : H →L[ℂ] H) :
    (complexLocalRetardedOperator hU V T).restrictScalars ℝ =
      localRetardedOperator hU V T := rfl

/-- Its real compression is exactly the existing normalized local compression,
on the original source and target measures
(`app:ch_response:eq:response-actual-solver-formula`). -/
@[simp] theorem realCompression_complexLocalRetardedOperator
    {U : Set E} (hU : MeasurableSet U) (V : Set E) (T : H →L[ℂ] H) :
    realCompression (complexLocalRetardedOperator hU V T) =
      localRealCompression hU V T := rfl

/-- Observe an already recut global source through the SAME local inverse
and full solver. The original source already contains `χ₂`, so this formula
has only the original final `χ₃` before zero extension. It supplies the graph
realization for the literal normalized inverse
(`app:ch_response:eq:response-actual-solver-formula`). -/
def complexLocalSolverObservation {U : Set E} (hU : MeasurableSet U)
    {center : E} (χ₃ : ContDiffBump center)
    (S : H →L[ℂ] H) (T : LocalL2 U F →L[ℂ] LocalL2 U F) : H →L[ℂ] H where
  toFun u := S (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃ (T (restrictL2 U u))))
  map_add' u v := by simp only [map_add]
  map_smul' c u := by
    have h₁ := (congrArg T (restrictL2_complex_smul U c u)).trans
      (T.map_smul c (restrictL2 U u))
    have h₂ := (congrArg (bumpL2 (p := 2) le_rfl χ₃) h₁).trans
      (bumpL2_complex_smul χ₃ c (T (restrictL2 U u)))
    have h₃ := (congrArg (zeroExtend hU) h₂).trans
      (zeroExtend_complex_smul hU c (bumpL2 (p := 2) le_rfl χ₃ (T (restrictL2 U u))))
    exact (congrArg S h₃).trans (S.map_smul c _)
  cont := S.continuous.comp ((zeroExtend hU).continuous.comp
    ((bumpL2 (p := 2) le_rfl χ₃).continuous.comp (T.continuous.comp (restrictL2 U).continuous)))

/-- Bundle the SAME inner recut, local inverse, outer plateau, zero extension
and full solver as one complex-linear map on global L². Taking the local
operator to be `complexNeumannInverse R` gives the original complete solver
whose smooth representative is used by joint reconstruction
(`app:ch_response:eq:response-actual-solver-formula`). -/
def complexBumpedLocalObservation {U : Set E} (hU : MeasurableSet U)
    {center : E} (χ₂ χ₃ : ContDiffBump center)
    (S : H →L[ℂ] H) (T : LocalL2 U F →L[ℂ] LocalL2 U F) : H →L[ℂ] H where
  toFun u := S (zeroExtend hU (bumpL2 (p := 2) le_rfl χ₃
    (T (bumpL2 (p := 2) le_rfl χ₂ (restrictL2 U u)))))
  map_add' u v := by simp only [map_add]
  map_smul' c u := by
    let v := bumpL2 (p := 2) le_rfl χ₂ (restrictL2 U u)
    have h₁ := (congrArg (bumpL2 (p := 2) le_rfl χ₂)
      (restrictL2_complex_smul U c u)).trans
        (bumpL2_complex_smul χ₂ c (restrictL2 U u))
    have h₂ := (congrArg T h₁).trans (T.map_smul c v)
    have h₃ := (congrArg (bumpL2 (p := 2) le_rfl χ₃) h₂).trans
      (bumpL2_complex_smul χ₃ c (T v))
    have h₄ := (congrArg (zeroExtend hU) h₃).trans
      (zeroExtend_complex_smul hU c (bumpL2 (p := 2) le_rfl χ₃ (T v)))
    exact (congrArg S h₄).trans (S.map_smul c _)
  cont := S.continuous.comp ((zeroExtend hU).continuous.comp
    ((bumpL2 (p := 2) le_rfl χ₃).continuous.comp
      (T.continuous.comp ((bumpL2 (p := 2) le_rfl χ₂).continuous.comp (restrictL2 U).continuous))))

private theorem star_zeroExtend {U : Set E} (hU : MeasurableSet U)
    (u : LocalL2 U F) :
    star (zeroExtend hU u) = zeroExtend hU (star u) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (zeroExtend hU u), zeroExtend_coeFn hU u,
    zeroExtend_coeFn hU (star u),
    (ae_restrict_iff' hU).mp (Lp.coeFn_star u)] with x hs hu hx hi
  rw [hs, Pi.star_apply, hu, hx]
  by_cases h : x ∈ U
  · simp only [indicator_of_mem h, hi h, Pi.star_apply]
  · simp only [indicator_of_notMem h, star_zero]

private theorem star_restrictL2 (U : Set E) (u : H) :
    star (restrictL2 U u) = restrictL2 U (star u) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (restrictL2 U u), restrictL2_coeFn U u,
    restrictL2_coeFn U (star u), ae_restrict_of_ae (Lp.coeFn_star u)] with x hs hu hx hi
  rw [hs, Pi.star_apply, hu, hx, hi, Pi.star_apply]

/-- Whole-operator reality passes through the original localization formula.
Together with `realCompression_norm_eq_of_conjugation`, this derives the
complex contraction from the original real one without changing its constant
(`real-sector-normalization`, `app:ch_regular:eq:neumann-series`). -/
theorem complexLocalRetardedOperator_conjugation
    {U : Set E} (hU : MeasurableSet U) (V : Set E) (T : H →L[ℂ] H)
    (hT : conjugateOperator T.toLinearMap = T.toLinearMap) :
    conjugateOperator (complexLocalRetardedOperator hU V T).toLinearMap =
      (complexLocalRetardedOperator hU V T).toLinearMap := by
  have hstar (u : H) : T (star u) = star (T u) := by
    simpa only [conjugateOperator_apply, star_star, ContinuousLinearMap.coe_coe]
      using (LinearMap.congr_fun hT (star u)).symm
  apply LinearMap.ext
  intro u
  change star (restrictL2 V (T (zeroExtend hU (star u)))) =
    restrictL2 V (T (zeroExtend hU u))
  rw [← star_zeroExtend, hstar, star_restrictL2, star_star]

end JanetCartan.FixedDomainInverse
