module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compact physical tensors in Lebesgue L2

The bounded zero extension for `app:ch_waves:eq:background-quadrature`.
The physical measure is volume on `Euclidean n`; matrix norms are Frobenius.
This is the real tensor counterpart of the scalar response extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground.CompactTensor

variable {n : ℕ} {K : Set (Euclidean n)}
variable (hK : IsCompact K)
variable [CompactSpace K]

/-- Extend a continuous function on the compact spatial set by zero, for
`app:ch_waves:eq:background-quadrature`. -/
def extendZero (f : C(K, Matrix (Fin n) (Fin n) ℝ)) : (Euclidean n) → Matrix (Fin n) (Fin n) ℝ :=
  Function.extend Subtype.val f 0

omit [CompactSpace K] in
/-- The extension retains the original values on the compact set
(`app:ch_waves:eq:background-quadrature`). -/
lemma extendZero_mem (f : C(K, Matrix (Fin n) (Fin n) ℝ)) {x : Euclidean n} (hx : x ∈ K) :
    extendZero f x = f ⟨x, hx⟩ := by
  exact Subtype.coe_injective.extend_apply _ _ ⟨x, hx⟩

omit [CompactSpace K] in
/-- The extension vanishes off the compact set
(`app:ch_waves:eq:background-quadrature`). -/
lemma extendZero_notMem (f : C(K, Matrix (Fin n) (Fin n) ℝ)) {x : Euclidean n} (hx : x ∉ K) :
    extendZero f x = 0 := by
  exact Function.extend_apply' _ _ _ (by simpa using hx)

/-- The square root of the compact physical volume, expressed as the norm of
its indicator. It is fixed before frequencies, labels and sampling parameters
(`app:ch_waves:eq:background-quadrature`). -/
def physicalL2Constant : ℝ :=
  ‖indicatorConstLp (μ := (volume : Measure (Euclidean n))) 2
    hK.isClosed.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖

omit [CompactSpace K] in
/-- Nonnegativity of the physical L2 conversion factor
(`app:ch_waves:eq:background-quadrature`). -/
lemma physicalL2Constant_nonneg : 0 ≤ physicalL2Constant hK := norm_nonneg _

include hK in
/-- The extension is in actual Lebesgue L2, by compact support and boundedness
(`app:ch_waves:eq:background-quadrature`). -/
lemma extendZero_memLp (f : C(K, Matrix (Fin n) (Fin n) ℝ)) : MemLp (extendZero f) 2 volume := by
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
linear. This transfers the compact-family derivatives in
`app:ch_waves:eq:background-quadrature`. -/
def compactToL2 : C(K, Matrix (Fin n) (Fin n) ℝ) →L[ℝ] Lp (Matrix (Fin n) (Fin n) ℝ) 2 (volume : Measure (Euclidean n)) :=
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
    (physicalL2Constant hK)
    (fun f ↦ by
      rw [mul_comm]
      unfold physicalL2Constant
      change ‖(extendZero_memLp hK f).toLp (extendZero f)‖ ≤ _
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(extendZero_memLp hK f).coeFn_toLp,
        indicatorConstLp_coeFn (μ := (volume : Measure (Euclidean n))) (p := 2)
          (hs := hK.isClosed.measurableSet)
          (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hx hy
      rw [hx, hy]
      by_cases hxK : x ∈ K
      · simp only [extendZero_mem _ hxK, indicator_of_mem hxK, norm_one, mul_one]
        exact f.norm_coe_le_norm _
      · simp [extendZero_notMem _ hxK, indicator_of_notMem hxK])

omit [CompactSpace K] in
/-- A pointwise uniform estimate on the common physical support becomes an
L2 estimate. This also applies to the parent's tensor transport differences
(`app:ch_waves:eq:background-quadrature`). -/
lemma norm_toLp_le {f : Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    (hf : MemLp f 2 volume) (hs : ∀ x ∉ K, f x = 0)
    {B : ℝ} (_hB : 0 ≤ B) (hb : ∀ x ∈ K, ‖f x‖ ≤ B) :
    ‖hf.toLp f‖ ≤ physicalL2Constant hK * B := by
  rw [mul_comm]
  unfold physicalL2Constant
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hf.coeFn_toLp,
    indicatorConstLp_coeFn (μ := (volume : Measure (Euclidean n))) (p := 2)
      (hs := hK.isClosed.measurableSet)
      (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hx hy
  rw [hx, hy]
  by_cases hxK : x ∈ K
  · simpa only [indicator_of_mem hxK, norm_one, mul_one] using hb x hxK
  · simp [hs x hxK, indicator_of_notMem hxK]

/-- The zero-extension operator has the physical-volume bound
(`app:ch_waves:eq:background-quadrature`). -/
lemma norm_compactToL2_le : ‖compactToL2 hK‖ ≤ physicalL2Constant hK := by
  apply ContinuousLinearMap.opNorm_le_bound _ (physicalL2Constant_nonneg hK)
  intro f
  exact norm_toLp_le hK (extendZero_memLp hK f)
    (fun x hx ↦ extendZero_notMem f hx) (norm_nonneg f)
    (fun x hx ↦ by rw [extendZero_mem f hx]; exact f.norm_coe_le_norm _)

end JanetCartan.Sampling.RetainedBackground.CompactTensor
