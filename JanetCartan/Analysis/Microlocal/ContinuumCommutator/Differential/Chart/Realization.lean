module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Localization
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.SourceBounds

/-!
# Realization on smooth periodic tests

For `app:ch_background:eq:bg-commutator`, the bounded chart operator agrees
with the literal source-first Lebesgue kernel on a compact extension of a
smooth periodic test. The L² extension norm is at most the periodic input norm.
All constants in this module are independent of the high amplitude budget.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "L²" => EuclideanL2 d ℂ

namespace SourceCutoff
variable {r : ℝ} (χ : SourceCutoff d r) {u : Torus d → ℂ}

/-- The compact source extension as a Lebesgue L² class
(`app:ch_background:eq:bg-commutator`). -/
def extendL2 (hu : IsSmoothPeriodic u) : L² :=
  ((χ.smooth_extend hu).continuous.memLp_of_hasCompactSupport (χ.compact_extend u)).toLp _

/-- The L² class has the actual smooth compact representative
(`app:ch_background:eq:bg-commutator`). -/
theorem extendL2_coe (hu : IsSmoothPeriodic u) :
    χ.extendL2 hu =ᵐ[volume] χ.extend u := MemLp.coeFn_toLp _

/-- The extension norm is at most the input norm, by exact unit-cell measure
comparison and `0 ≤ χ ≤ 1` (`app:ch_background:eq:bg-commutator`). -/
theorem norm_extendL2_le (hu : IsSmoothPeriodic u) (hm : MemLp u 2) :
    ‖χ.extendL2 hu‖ ≤ ‖hm.toLp u‖ := by
  rw [← (toEuclidean (𝕜 := ℂ)).norm_map (hm.toLp u)]
  apply Lp.norm_le_norm_of_ae_le
  have hlift := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp)
  filter_upwards [χ.extendL2_coe hu, toEuclidean_coe (𝕜 := ℂ) (hm.toLp u), hlift]
    with x hx hx' hux
  rw [hx, hx']
  by_cases hc : x ∈ halfOpenCell d
  · rw [indicator_of_mem hc, show periodicLift (hm.toLp u) x = periodicLift u x from hux hc]
    simp only [extend, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (χ.range x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.range x).2
  · have hz : χ.toFun x = 0 := by
      by_contra h
      exact hc (subset_halfOpenCell_of_strict (fun y hy ↦ hy)
        (χ.support_cell (subset_tsupport _ h)))
    simp [extend, hz, hc]

end SourceCutoff

section
variable (hd : 0 < d) {r : ℝ} (hr : r < 1 / 2)
  (b : (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (A : ℝ)
  (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)

include hr

/-- The actual Euclidean operator agrees on the unit-cell lift and on any fixed
compact smooth extension (`app:ch_background:eq:bg-commutator`). -/
theorem twoPositionL2Operator_cellLift_eq_extension (χ : SourceCutoff d r)
    {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) (hm : MemLp u 2) :
    twoPositionL2Operator hd r b hb hs A hA (toEuclidean (𝕜 := ℂ) (hm.toLp u)) =
      twoPositionL2Operator hd r b hb hs A hA (χ.extendL2 hu) := by
  apply twoPositionL2Operator_congr_on_source
  have hlift := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp)
  filter_upwards [toEuclidean_coe (𝕜 := ℂ) (hm.toLp u), χ.extendL2_coe hu, hlift]
    with y hy hy' huy hbox
  rw [hy, hy', indicator_of_mem (chartBox_subset_cell hr hbox)]
  exact (huy (chartBox_subset_cell hr hbox)).trans
    (χ.extend_eventuallyEq u hbox).self_of_nhds.symm

/-- On periodic tests, the bounded chart operator is precisely the
periodization of the compact-test Euclidean operator
(`app:ch_background:eq:bg-commutator`). -/
theorem torusL2Operator_eq_extension (χ : SourceCutoff d r)
    {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) (hm : MemLp u 2) :
    torusL2Operator hd r b hb hs A hA (hm.toLp u) =
      toTorus (𝕜 := ℂ) (twoPositionL2Operator hd r b hb hs A hA (χ.extendL2 hu)) := by
  change toTorus (𝕜 := ℂ)
    (twoPositionL2Operator hd r b hb hs A hA (toEuclidean (𝕜 := ℂ) (hm.toLp u))) = _
  rw [twoPositionL2Operator_cellLift_eq_extension hd hr b hb hs A hA χ hu hm]

/-- Exact normalized-torus realization of the literal full-amplitude kernel.
The compact source extension is constructed, and its source-derivative
integrability follows from the primitive physical budget
(`app:ch_background:eq:bg-commutator`). -/
theorem torusL2Operator_ae_kernel {u : Torus d → ℂ}
    (hu : IsSmoothPeriodic u) (hm : MemLp u 2) :
    torusL2Operator hd r b hb hs A hA (hm.toLp u) =ᵐ[volume] torusKernelOperator b u := by
  obtain ⟨χ⟩ := nonempty_sourceCutoff (d := d) hr
  rw [torusL2Operator_eq_extension hd hr b hb hs A hA χ hu hm,
    χ.torusKernelOperator_eq_extend hr b hs u]
  apply (toTorus_coe (𝕜 := ℂ) _).trans
  apply measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
  exact (twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget
    hd r b hb hs A hA (χ.extend u)
    ((χ.smooth_extend hu).continuous.memLp_of_hasCompactSupport (χ.compact_extend u))
    ((χ.smooth_extend hu).of_le (by simp)) (χ.compact_extend u)).restrict

/-- The compact output and the chart output have identical L² norm on smooth
periodic tests (`app:ch_background:eq:bg-commutator`). -/
theorem norm_torusL2Operator_eq_extension (χ : SourceCutoff d r)
    {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) (hm : MemLp u 2) :
    ‖torusL2Operator hd r b hb hs A hA (hm.toLp u)‖ =
      ‖twoPositionL2Operator hd r b hb hs A hA (χ.extendL2 hu)‖ := by
  rw [norm_torusL2Operator_apply hd r b hb hs A hA hr,
    twoPositionL2Operator_cellLift_eq_extension hd hr b hb hs A hA χ hu hm]

/-- Lifting the actual chart output recovers the full compact-test Euclidean
output, including its zero exterior (`app:ch_background:eq:bg-commutator`). -/
theorem toEuclidean_torusL2Operator_eq_extension (χ : SourceCutoff d r)
    {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) (hm : MemLp u 2) :
    toEuclidean (𝕜 := ℂ) (torusL2Operator hd r b hb hs A hA (hm.toLp u)) =
      twoPositionL2Operator hd r b hb hs A hA (χ.extendL2 hu) := by
  rw [torusL2Operator_eq_extension hd hr b hb hs A hA χ hu hm]
  apply toEuclidean_toTorus
  filter_upwards [twoPositionL2Operator_supported hd r b hb hs A hA (χ.extendL2 hu)]
    with x hx hc
  exact hx (fun h ↦ hc (chartBox_subset_cell hr h))

end
end JanetCartan.Pseudodifferential.DifferentialChart
