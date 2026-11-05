module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.Extension
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.TensorFrame
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteHistoryBounds

/-!
# Small-input estimates for the fixed defect smoothing

`main:eq:smoothing-low` and `main:eq:smoothing-small` are proved for the actual
extension and multiplier. Only local smoothness and the zeroth core bound are
inputs. No high defect profile or tail estimate is assumed here.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.DefectSmoothing

variable {n : ℕ}

/-- The zeroth extension constant is fixed before the domain, input and scale
(`main:eq:smoothing-low`). -/
def extensionZeroConstant : ℝ := max 1 (∑' j, |Seeley.coeff j|)

/-- Positivity of the fixed extension constant (`main:eq:smoothing-low`). -/
theorem extensionZeroConstant_pos : 0 < extensionZeroConstant :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- The actual extension has a uniform Frobenius bound from its core data,
with no positivity assumption on the tensor (`main:eq:smoothing-low`). -/
theorem norm_extendToTorus_le (D : LocalDomain) {f : MetricField n} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ x ∈ D.core n, ‖f x‖ ≤ M) (z : Torus n) :
    ‖extendToTorus D f z‖ ≤ extensionZeroConstant * M := by
  apply (extensionParameters D).norm_extend_le Seeley.coeff _ f hM hf
  simpa using Seeley.summable_abs_coeff_moment 0

private theorem norm_le_core_cNorm (D : LocalDomain) {f : MetricField n}
    (hf : ContDiffOn ℝ ∞ f (D.chart n)) {x : Euclidean n} (hx : x ∈ D.core n) :
    ‖f x‖ ≤ cNorm (D.core n) 0 f := by
  have hsub : D.core n ⊆ D.chart n :=
    Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt (s := D.core n) (f := f) (r := 0) (j := 0)
      (isCompact_closedBall _ _) (fun y hy ↦
        (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hsub hy))).of_le (by simp)) hx le_rfl

/-- The zeroth norm of the actual torus extension from the genuine core
seminorm, with local boundedness justified (`main:eq:smoothing-small`). -/
theorem cNorm_zero_extendToTorus_le (D : LocalDomain) {f : MetricField n}
    (hf : ContDiffOn ℝ ∞ f (D.chart n)) :
    cNorm (fundamentalCell n) 0 (periodicLift (extendToTorus D f)) ≤
      extensionZeroConstant * cNorm (D.core n) 0 f := by
  rw [cNorm_order_zero]
  apply Real.sSup_le _ (mul_nonneg extensionZeroConstant_pos.le (cNorm_nonneg _ _ _))
  rintro _ ⟨x, _, rfl⟩
  exact norm_extendToTorus_le D (cNorm_nonneg _ _ _) (fun y hy ↦
    norm_le_core_cNorm D hf hy) (torusQuotient x)

/-- The literal Fourier smoothing of the fixed extension (`main:lem:smoothing`). -/
def smoothTensor (D : LocalDomain) (R : ℝ) (f : MetricField n) : Torus n → MetricTensor n :=
  periodicCutoff R (extendToTorus D f)

/-- The actual cutoff output is smooth (`main:lem:smoothing`). -/
theorem isSmoothPeriodic_smoothTensor (D : LocalDomain) (R : ℝ) (f : MetricField n) :
    IsSmoothPeriodic (smoothTensor D R f) := isSmoothPeriodic_periodicCutoff _ _

/-- Exact support at `2R` for the same smooth tensor (`main:lem:smoothing`). -/
theorem hasFourierSupport_smoothTensor (D : LocalDomain) {R : ℝ} (hR : 0 < R)
    {f : MetricField n} (hf : ContDiffOn ℝ ∞ f (D.core n)) :
    HasFourierSupport (2 * R) (smoothTensor D R f) :=
  hasFourierSupport_periodicCutoff (isSmoothPeriodic_extendToTorus D hf).1 hR

/-- Both norms of the actual smoothed tensor follow from its small input.
The constant precedes the scale, target, history and physical measurement set
(`main:eq:smoothing-low`). -/
theorem exists_smoothTensor_low_bound (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (f : MetricField n),
      ContDiffOn ℝ ∞ f (D.chart n) → ∀ δ : ℝ,
      cNorm (D.core n) 0 f ≤ δ ^ 2 → ∀ s : Set (Euclidean n),
      cNorm s r (periodicLift (smoothTensor D R f)) +
        periodicSobolevNorm (r : ℝ) (smoothTensor D R f) ≤ C * δ ^ 2 * R ^ r := by
  obtain ⟨C, hC, hb⟩ := exists_periodicCutoff_smoothing_bound n r
  refine ⟨C * extensionZeroConstant, mul_nonneg hC extensionZeroConstant_pos.le, ?_⟩
  intro R hR f hf δ hδ s
  have hsmooth := isSmoothPeriodic_extendToTorus D
    (hf.mono (Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius))
  calc
    _ ≤ cNorm (fundamentalCell n) r (periodicLift (smoothTensor D R f)) +
        periodicSobolevNorm (r : ℝ) (smoothTensor D R f) :=
      add_le_add (BandHistory.cNorm_periodicLift_le_cell s r
        (isSmoothPeriodic_smoothTensor D R f)) le_rfl
    _ ≤ C * R ^ r * cNorm (fundamentalCell n) 0 (periodicLift (extendToTorus D f)) :=
      hb hR hsmooth
    _ ≤ C * R ^ r * (extensionZeroConstant * δ ^ 2) :=
      mul_le_mul_of_nonneg_left ((cNorm_zero_extendToTorus_le D hf).trans
        (mul_le_mul_of_nonneg_left hδ extensionZeroConstant_pos.le))
        (mul_nonneg hC (pow_nonneg (by linarith) _))
    _ = _ := by ring

/-- The small tail is derived from the actual cutoff's order-zero tail and
exact extension agreement, independently of any high profile
(`main:eq:smoothing-small`). -/
theorem exists_smoothTensor_small_tail_bound (D : LocalDomain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (f : MetricField n),
      ContDiffOn ℝ ∞ f (D.chart n) → ∀ δ : ℝ,
      cNorm (D.core n) 0 f ≤ δ ^ 2 →
      cNorm (D.core n) 0 (f - periodicLift (smoothTensor D R f)) ≤ C * δ ^ 2 := by
  refine ⟨periodicCutoffApproximationConstant n 0 * extensionZeroConstant,
    mul_nonneg (periodicCutoffApproximationConstant_nonneg _ _) extensionZeroConstant_pos.le, ?_⟩
  intro R hR f hf δ hδ
  have hsmooth := isSmoothPeriodic_extendToTorus D
    (hf.mono (Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius))
  rw [cNorm_order_zero]
  apply Real.sSup_le _ (mul_nonneg
    (mul_nonneg (periodicCutoffApproximationConstant_nonneg _ _) extensionZeroConstant_pos.le)
    (sq_nonneg δ))
  rintro _ ⟨x, hx, rfl⟩
  have he := periodicLift_extendToTorus_eqOn D f hx
  change ‖f x - periodicLift (smoothTensor D R f) x‖ ≤ _
  rw [← he]
  have ht := norm_periodicLift_sub_periodicCutoff_le hsmooth 0
    (lt_of_lt_of_le zero_lt_one hR) x
  simp only [pow_zero, inv_one, mul_one] at ht
  exact ht.trans (by
    calc
      _ ≤ periodicCutoffApproximationConstant n 0 * (extensionZeroConstant * δ ^ 2) :=
        mul_le_mul_of_nonneg_left ((cNorm_zero_extendToTorus_le D hf).trans
          (mul_le_mul_of_nonneg_left hδ extensionZeroConstant_pos.le))
          (periodicCutoffApproximationConstant_nonneg _ _)
      _ = _ := by ring)

/-- The Fourier multiplier preserves real symmetric tensors, without a sign
restriction (`main:lem:smoothing`). -/
theorem smoothTensor_isSymm (D : LocalDomain) {R : ℝ} {f : MetricField n}
    (hf : ContDiffOn ℝ ∞ f (D.core n)) (hs : ∀ x ∈ D.core n, (f x).IsSymm)
    (z : Torus n) : (smoothTensor D R f z).IsSymm := by
  let A : MetricTensor n →L[ℝ] MetricTensor n :=
    LinearMap.toContinuousLinearMap
      { toFun := Matrix.transpose, map_add' := Matrix.transpose_add, map_smul' := by intros; rfl }
  have he : A ∘ extendToTorus D f = extendToTorus D f :=
    funext (extendToTorus_isSymm D hs)
  have h := periodicCutoff_comp_clm A (isSmoothPeriodic_extendToTorus D hf).1 R
  rw [he] at h
  exact (congrFun h z).symm

end JanetCartan.DefectSmoothing
