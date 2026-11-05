module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Synthesis
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Cutoffs
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Norms
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Scale
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Spectral

/-!
# The compact positive-background source in the actual Sobolev scale

For `app:ch_background:eq:bg-current-raising`, the smooth compact physical
source is periodized on the unit torus and placed in the SAME real L² space
as the uncorrected continuum row. Its Sobolev membership and bounds follow
from its physical jets. No inverse regularity or density smallness is assumed
in this construction. The consumer is the original inverse in
`PositiveBackground.Synthesis`, before the corrected positive row is fixed.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PositiveBackground
open ContinuumRow UniformStep.Periodization

variable {n : ℕ}

/-- The actual L² class of the smooth, periodized physical source
(`app:ch_background:eq:bg-current-raising`). This single class is used at
every Sobolev order. -/
def sourceToL2 (e : Euclidean n → Euclidean n)
    (he : IsSmoothPeriodic (vectorPeriodization e)) : OutputL2 n :=
  (he.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp _

/-- The source class has the literal centered physical representative
(`app:ch_background:eq:bg-current-raising`). -/
theorem sourceToL2_coeFn (e : Euclidean n → Euclidean n)
    (he : IsSmoothPeriodic (vectorPeriodization e)) :
    sourceToL2 e he =ᵐ[volume] vectorPeriodization e :=
  MemLp.coeFn_toLp _

/-- Smooth compact sources belong to every level of the actual continuum
Sobolev scale, with summability proved (`app:ch_background:prop:bg-inverse`). -/
theorem sourceToL2_mem (e : Euclidean n → Euclidean n)
    (he : IsSmoothPeriodic (vectorPeriodization e)) (s : ℕ) :
    sourceToL2 e he ∈ periodicSobolevLevel n (Euclidean n) s :=
  he.toLp_mem_periodicSobolevLevel s _

/-- The source's graded norm is exactly the shared Fourier Sobolev norm,
including the original unit-torus normalization
(`app:ch_background:eq:bg-current-raising`). -/
theorem sourceToL2_gradeNorm (e : Euclidean n → Euclidean n)
    (he : IsSmoothPeriodic (vectorPeriodization e)) (s : ℕ) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s (sourceToL2 e he) =
      periodicSobolevNorm s (vectorPeriodization e) := he.gradeNorm_toLp s _

private theorem source_sobolev_le_cNorm {r : ℝ} (hr : r < 1 / 2)
    {e : Euclidean n → Euclidean n} (he : ContDiff ℝ ∞ e)
    (hs : tsupport e ⊆ closedBall 0 r) (s : ℕ) :
    periodicSobolevNorm s (vectorPeriodization e) ≤
      (Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card) *
        cNorm (closedBall 0 r) s e := by
  have hsbox : tsupport e ⊆ {x | ∀ i, |x i| ≤ r} := by
    intro x hx i
    exact (PiLp.norm_apply_le x i).trans (mem_closedBall_zero_iff.mp (hs hx))
  have hjet (j : ℕ) (hj : j ≤ s) (x : Euclidean n) :
      ‖iteratedFDeriv ℝ j e x‖ ≤ cNorm (closedBall 0 r) s e := by
    by_cases hx : x ∈ closedBall 0 r
    · exact norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        (he.of_le (by simp)) hx hj
    · have hz : iteratedFDeriv ℝ j e x = 0 := by
        by_contra h
        exact hx (hs (support_iteratedFDeriv_subset j h))
      rw [hz, norm_zero]
      exact cNorm_nonneg _ _ _
  have hderiv (α : Option (Fin n) → ℕ) (hα : α ∈ sobolevMultiindices n s) :
      periodicL2Norm (periodicMultiindexDeriv (fun i ↦ α (some i))
        (vectorPeriodization e)) ≤ cNorm (closedBall 0 r) s e := by
    apply periodicL2Norm_le_of_bound _ (cNorm_nonneg _ _ _)
    intro z
    rw [multiindexDeriv_vectorPeriodization hr hsbox he]
    apply (LocalSobolev.norm_cartesianJetDerivative_le _ _ _).trans
    apply hjet
    have := mem_sobolevMultiindices.mp hα
    omega
  have hsum : periodicDerivativeL2Norm s (vectorPeriodization e) ≤
      Real.sqrt (sobolevMultiindices n s).card * cNorm (closedBall 0 r) s e := by
    unfold periodicDerivativeL2Norm
    calc
      _ ≤ Real.sqrt (∑ _α ∈ sobolevMultiindices n s,
          (cNorm (closedBall 0 r) s e) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun α hα ↦
          pow_le_pow_left₀ (Real.sqrt_nonneg _) (hderiv α hα) 2
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (cNorm_nonneg _ _ _)]
  exact (periodicSobolevNorm_le_factorial_mul_derivativeL2Norm
    (isSmoothPeriodic_vectorPeriodization hr hsbox he) s).trans
      ((mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

/-- Physical source jets bound its genuine Sobolev norm with an explicit
order-dependent constant and no derivative loss
(`app:ch_background:eq:bg-positive-profile`). -/
theorem sourceToL2_gradeNorm_le {r : ℝ} (hr : r < 1 / 2)
    {e : Euclidean n → Euclidean n} (he : ContDiff ℝ ∞ e)
    (hs : tsupport e ⊆ closedBall 0 r)
    (hep : IsSmoothPeriodic (vectorPeriodization e)) (s : ℕ) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s (sourceToL2 e hep) ≤
      (Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card) *
        cNorm (closedBall 0 r) s e := by
  rw [sourceToL2_gradeNorm]
  exact source_sobolev_le_cNorm hr he hs s

/-- The physical compact source and the source passed to the original inverse
are the SAME L² element. Only the uncut reduced residual needs an L²
representative; no smoothness or bound for that representative is assumed
(`app:ch_background:eq:bg-current-raising`). -/
theorem sourceToL2_cutReducedSource_eq_inverseSource
    {r : ℝ} (hr : r < 1 / 2) (θ : Euclidean n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hs : tsupport θ ⊆ closedBall 0 r)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (he : IsSmoothPeriodic (vectorPeriodization (cutReducedSource θ Q R)))
    (residual : OutputL2 n)
    (hres : residual =ᵐ[volume] vectorPeriodization
      (fun x ↦ WithLp.toLp 2 (CubeKernel.tensorContraction (Q x) (R x)))) :
    sourceToL2 (cutReducedSource θ Q R) he =
      inverseSource (ImageGeometry.periodizedImageCutoff hr θ hθ hs) residual := by
  apply Lp.ext
  filter_upwards [sourceToL2_coeFn (cutReducedSource θ Q R) he,
    inverseSource_coeFn (ImageGeometry.periodizedImageCutoff hr θ hθ hs) residual,
    hres] with z hz hi hrz
  rw [hz, hi, hrz]
  rfl

/-- The larger fixed cutoff supplies a genuine L² residual representative.
Its values outside the source support do not affect the original inverse
source. This closes the representative input without assuming that the
uncut geometric residual has a global torus realization
(`app:ch_background:eq:bg-current-raising`). -/
theorem inverseSource_bufferedResidual
    {r : ℝ} (hr : r < 1 / 2) (θ κ : Euclidean n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hs : tsupport θ ⊆ closedBall 0 r)
    (hplateau : ∀ x, θ x ≠ 0 → κ x = 1)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (he : IsSmoothPeriodic (vectorPeriodization (cutReducedSource θ Q R)))
    (hbuffer : IsSmoothPeriodic (vectorPeriodization (cutReducedSource κ Q R))) :
    inverseSource (ImageGeometry.periodizedImageCutoff hr θ hθ hs)
      ((-2 : ℝ) • sourceToL2 (cutReducedSource κ Q R) hbuffer) =
        sourceToL2 (cutReducedSource θ Q R) he := by
  apply Lp.ext
  filter_upwards [inverseSource_coeFn (ImageGeometry.periodizedImageCutoff hr θ hθ hs)
      ((-2 : ℝ) • sourceToL2 (cutReducedSource κ Q R) hbuffer),
    Lp.coeFn_smul (-2 : ℝ) (sourceToL2 (cutReducedSource κ Q R) hbuffer),
    sourceToL2_coeFn (cutReducedSource κ Q R) hbuffer,
    sourceToL2_coeFn (cutReducedSource θ Q R) he] with z hi hsm hb hez
  rw [hi, hsm, Pi.smul_apply, hb, hez]
  let x := AmplitudeBound.centeredTorusRepresentative z
  change (- (1 / 2 : ℝ) * θ x) • ((-2 : ℝ) • cutReducedSource κ Q R x) =
    cutReducedSource θ Q R x
  by_cases hx : θ x = 0
  · simp [cutReducedSource, hx]
  · simp only [cutReducedSource, hplateau x hx, mul_one, smul_smul]
    congr 1
    ring

/-- A source cutoff lying in a measurement plateau gives an exactly fixed
L² source under the measurement multiplier, before inversion or synthesis
(`app:ch_background:eq:bg-density-twice`). -/
theorem cutoffMultiplier_sourceToL2
    (θ : Euclidean n → ℝ)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (he : IsSmoothPeriodic (vectorPeriodization (cutReducedSource θ Q R)))
    (χ : C(Torus n, ℝ))
    (hχ : ∀ z, θ (AmplitudeBound.centeredTorusRepresentative z) ≠ 0 → χ z = 1) :
    cutoffMultiplier χ (sourceToL2 (cutReducedSource θ Q R) he) =
      sourceToL2 (cutReducedSource θ Q R) he := by
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn χ (sourceToL2 (cutReducedSource θ Q R) he),
    sourceToL2_coeFn (cutReducedSource θ Q R) he] with z hc hz
  rw [hc, hz]
  by_cases h : θ (AmplitudeBound.centeredTorusRepresentative z) = 0
  · simp [vectorPeriodization, Function.comp_apply, cutReducedSource, h]
  · rw [hχ z h, one_smul]

end JanetCartan.PositiveBackground
