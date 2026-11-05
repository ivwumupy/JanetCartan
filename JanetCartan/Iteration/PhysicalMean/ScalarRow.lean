module

public import JanetCartan.Iteration.PhysicalMean.SamplingEvent
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawKernel

/-!
# The original scalar auxiliary kernel on the same sampled phase

For `new:eq:amplitude-test`, the scalar auxiliary row keeps the original full
phase difference, carrier shift, angular/high mask and radial input partition,
but uses a fixed physical cutoff instead of the measured stress amplitude.
It is embedded into one output coordinate ONLY to use the existing kernel
concentration machinery. The scalar projection is contractive; this is not a
comparison with the measured canonical row.

The scalar kernel's sharp single-band estimate and uniform continuum normal
bound must still be proved from the actual current phase geometry before the
common event in `SamplingEvent` is instantiated.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open Sampling Sampling.RawKernel SamplingKernelBounds RawInputPartition

variable {n J : ℕ} {P : Type*} [TopologicalSpace P]

/-- The scalar auxiliary amplitude contains no stress measurement or sampled
source.  It has the fixed physical support used by the amplitude test. -/
def scalarAuxiliaryAmplitude (hn : 1 ≤ n) (χ : ContDiffBump (0 : Euclidean n))
    (_p : P) (x : Euclidean n) (_η : Euclidean (n - 1)) : EuclideanSpace ℂ (Fin n) :=
  (χ x : ℂ) • PiLp.single 2 ⟨0, hn⟩ (1 : ℂ)

/-- Fixed-cutoff regularity is independent of the sampled parameters. -/
theorem continuous_scalarAuxiliaryAmplitude (hn : 1 ≤ n) (χ : ContDiffBump (0 : Euclidean n)) :
    Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      scalarAuxiliaryAmplitude hn χ q.1.1 q.1.2 q.2) := by
  unfold scalarAuxiliaryAmplitude
  exact (Complex.continuous_ofReal.comp
    (χ.continuous.comp (continuous_snd.comp continuous_fst))).smul continuous_const

omit [TopologicalSpace P] in
/-- The original scalar cutoff gives a uniform amplitude bound of one. -/
theorem norm_scalarAuxiliaryAmplitude_le (hn : 1 ≤ n) (χ : ContDiffBump (0 : Euclidean n))
    (p : P) (x : Euclidean n) (η : Euclidean (n - 1)) :
    ‖scalarAuxiliaryAmplitude hn χ p x η‖ ≤ 1 := by
  simp only [scalarAuxiliaryAmplitude, norm_smul, PiLp.norm_single, norm_one,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
  exact χ.le_one

/-- The scalar auxiliary kernel is constructed from the SAME full phase,
carrier shifts and original input mask as the measured wave kernel.  Only
its fixed output amplitude differs, exactly as required in Step 1 of
`app:ch_mean_pairs:prop:canonical-estimates`. -/
def scalarAuxiliaryKernel (hn : 1 ≤ n) (χ : ContDiffBump (0 : Euclidean n))
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ) (d : Euclidean (n - 1) → ℂ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦ S q.1.1 q.1.2 q.2))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous d) {B : ℝ} (hB : 0 ≤ B) (hdb : ∀ η, ‖d η‖ ≤ B) :
    BandKernelData (Fin J × P) n :=
  bandKernelData S (scalarAuxiliaryAmplitude hn χ) ζ τ d hS
    (continuous_scalarAuxiliaryAmplitude hn χ) hζ hτ hτ₀ hd
    (tsupport (χ : Euclidean n → ℝ)) χ.hasCompactSupport
    (fun p x η hx ↦ by
      have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [scalarAuxiliaryAmplitude, hz, Complex.ofReal_zero, zero_smul])
    1 B zero_le_one hB (norm_scalarAuxiliaryAmplitude_le hn χ) hdb

omit [TopologicalSpace P] in
/-- Coordinate extraction recovers the literal scalar amplitude, with no
inverse coefficient, weight, or rank factor. -/
theorem scalarAuxiliaryAmplitude_component (hn : 1 ≤ n) (χ : ContDiffBump (0 : Euclidean n))
    (p : P) (x : Euclidean n) (η : Euclidean (n - 1)) :
    (scalarAuxiliaryAmplitude hn χ p x η).ofLp ⟨0, hn⟩ = (χ x : ℂ) := by
  simp [scalarAuxiliaryAmplitude]

/-- The scalar projection on the original whole-space physical output. -/
def scalarOutputProjection (hn : 1 ≤ n) :
    Output n →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)) :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) ⟨0, hn⟩).compLpL 2 volume

/-- Projection does not enlarge the actual sampled auxiliary row norm. -/
theorem norm_scalarOutputProjection_le (hn : 1 ≤ n) : ‖scalarOutputProjection hn‖ ≤ 1 := by
  apply (ContinuousLinearMap.norm_compLpL_le _).trans
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [PiLp.proj_apply, one_mul] using PiLp.norm_apply_le v ⟨0, hn⟩

/-- Applying the scalar projection to any constructed auxiliary row keeps its
operator bound exactly.  The row here is the SCALAR kernel row, never the
measured canonical row (`new:eq:amplitude-test`). -/
theorem norm_scalarOutputProjection_comp_le (hn : 1 ≤ n) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] Output n) :
    ‖(scalarOutputProjection hn).comp T‖ ≤ ‖T‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_scalarOutputProjection_le hn) (norm_nonneg T)).trans_eq (one_mul _))

end JanetCartan.PhysicalMean
