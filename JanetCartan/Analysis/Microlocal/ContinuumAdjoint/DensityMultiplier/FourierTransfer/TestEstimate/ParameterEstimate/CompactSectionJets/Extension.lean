module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.CompactSection
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Extension from compact transverse support into L²

The bounded extension map consumed by `contDiff_carrierTestSlice` for
`app:ch_background:eq:bg-density-adjoint`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier.CompactSectionJets

variable {n : ℕ} {K : Set (Euclidean (n - 1))}
variable (hK : IsCompact K)
variable [CompactSpace K]

/-- Extend a continuous function on the compact spatial set by zero, for
`app:ch_background:eq:bg-density-adjoint`. -/
def extendZero (f : C(K, ℂ)) : (Euclidean (n - 1)) → ℂ :=
  Function.extend Subtype.val f 0

omit [CompactSpace K] in
/-- The extension retains the original values on the compact set
(`app:ch_background:eq:bg-density-adjoint`). -/
lemma extendZero_mem (f : C(K, ℂ)) {x : Euclidean (n - 1)} (hx : x ∈ K) :
    extendZero f x = f ⟨x, hx⟩ := by
  exact Subtype.coe_injective.extend_apply _ _ ⟨x, hx⟩

omit [CompactSpace K] in
/-- The extension vanishes off the compact set
(`app:ch_background:eq:bg-density-adjoint`). -/
lemma extendZero_notMem (f : C(K, ℂ)) {x : Euclidean (n - 1)} (hx : x ∉ K) :
    extendZero f x = 0 := by
  exact Function.extend_apply' _ _ _ (by simpa using hx)

include hK in
/-- The extension is in actual Lebesgue L2, by compact support and boundedness
(`app:ch_background:eq:bg-density-adjoint`). -/
lemma extendZero_memLp (f : C(K, ℂ)) : MemLp (extendZero f) 2 volume := by
  have hm : StronglyMeasurable (extendZero f) :=
    (MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet).stronglyMeasurable_extend
      f.continuous.stronglyMeasurable stronglyMeasurable_zero
  have hs : HasCompactSupport (extendZero f) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (extendZero_notMem f hn)
  apply hs.memLp_of_bound hm.aestronglyMeasurable ‖f‖
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [extendZero_mem f hx]
    exact f.norm_coe_le_norm _
  · rw [extendZero_notMem f hx, norm_zero]
    exact norm_nonneg _

/-- Zero extension from the uniform norm to actual Lebesgue L2 is bounded
linear. This transfers the carrier compact-family derivatives in
`app:ch_background:eq:bg-density-adjoint`. -/
def compactToL2 : C(K, ℂ) →L[ℝ] Lp ℂ 2 (volume : Measure (Euclidean (n - 1))) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (extendZero_memLp hK f).toLp (extendZero f)
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [extendZero_mem _ hx]
        · simp [extendZero_notMem _ hx]
      map_smul' := by
        intro a f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [extendZero_mem _ hx]
        · simp [extendZero_notMem _ hx] }
    ‖indicatorConstLp (μ := (volume : Measure (Euclidean (n - 1)))) 2
      hK.isClosed.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖
    (fun f ↦ by
      rw [mul_comm]
      change ‖(extendZero_memLp hK f).toLp (extendZero f)‖ ≤ _
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(extendZero_memLp hK f).coeFn_toLp,
        indicatorConstLp_coeFn (μ := (volume : Measure (Euclidean (n - 1)))) (p := 2)
          (hs := hK.isClosed.measurableSet)
          (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hx hy
      rw [hx, hy]
      by_cases hxK : x ∈ K
      · simp only [extendZero_mem _ hxK, indicator_of_mem hxK, norm_one, mul_one]
        exact f.norm_coe_le_norm _
      · simp [extendZero_notMem _ hxK, indicator_of_notMem hxK])

end JanetCartan.ContinuumAdjoint.DensityMultiplier.CompactSectionJets
