module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SourceEstimates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SourceBounds
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The L² realization of a full two-position operator

For `app:ch_regular_base:thm:actual-calculus` and
`app:ch_regular_base:eq:fio-input`, reuse the amplitude-bound construction and
identify its strong limit with the source-first `fullAmplitudeOperator`.
All physical masks remain in the amplitude and the phase has the project's
`2π` normalization. Positive Sobolev orders are not asserted in this module.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology FourierTransform RealInnerProductSpace
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}

/-- `app:ch_regular_base:thm:actual-calculus`: the compact-frequency kernel
is exactly the truncated source-first Fourier integral. -/
theorem boxScalarAmplitudeKernel_eq_sourceIntegral
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (ρ : ℝ) (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    boxScalarAmplitudeKernel b ρ f x =
      ∫ ξ in Metric.closedBall 0 ρ,
        Real.fourierChar ⟪ξ, x⟫ •
          sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) f x ξ := by
  unfold boxScalarAmplitudeKernel sourceAmplitudeTransform
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  simp_rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro ξ _
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  rw [Real.fourierChar_apply]
  rw [show ⟪ξ, x⟫ + -⟪y, ξ⟫ = ⟪x - y, ξ⟫ by
    simp only [inner_sub_left]
    rw [real_inner_comm ξ x]
    ring]
  ring

/-- `app:ch_regular_base:thm:actual-calculus`: expanding closed frequency
balls recover an absolutely convergent inverse Fourier integral. -/
theorem tendsto_frequencyBall_integral (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : Integrable g) :
    Tendsto (fun ρ : ℝ ↦ ∫ ξ in Metric.closedBall 0 ρ, g ξ) atTop (𝓝 (∫ ξ, g ξ)) := by
  have hexhaust : (⋃ ρ : ℝ, Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ) = Set.univ := by
    ext ξ
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨‖ξ‖, by simp⟩
  have h := tendsto_setIntegral_of_monotone (f := g)
    (fun ρ : ℝ ↦ measurableSet_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (ε := ρ))
    (fun _ _ h ↦ Metric.closedBall_subset_closedBall h)
    (hg.integrableOn (s := ⋃ ρ : ℝ, Metric.closedBall 0 ρ))
  simpa only [hexhaust, Measure.restrict_univ] using h

/-- `app:ch_regular_base:thm:actual-calculus`: the literal compact-frequency
kernels converge pointwise to the actual source-first operator when its source
transform is integrable. This is an integrability premise, not an operator
identification premise. -/
theorem tendsto_boxScalarAmplitudeKernel_fullAmplitudeOperator
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin d))
    (hi : Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ b ξ (pairedPosition x y)) f x)) :
    Tendsto (fun ρ : ℝ ↦ boxScalarAmplitudeKernel b ρ f x) atTop
      (𝓝 (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) f x)) := by
  simp only [boxScalarAmplitudeKernel_eq_sourceIntegral, fullAmplitudeOperator,
    Real.fourierInv_eq]
  apply tendsto_frequencyBall_integral
  have hp : Continuous (fun ξ ↦ Real.fourierChar ⟪ξ, x⟫) := by fun_prop
  exact hi.norm.mono' (hp.aestronglyMeasurable.smul hi.aestronglyMeasurable)
    (Eventually.of_forall (fun ξ ↦ by simp))

/-- `app:ch_regular_base:thm:actual-calculus`: source integration respects
almost-everywhere equality of the datum. -/
theorem sourceAmplitudeTransform_congr_ae_input
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) → ℂ)
    {u v : EuclideanSpace ℝ (Fin d) → ℂ} (huv : u =ᵐ[volume] v)
    (x ξ : EuclideanSpace ℝ (Fin d)) :
    sourceAmplitudeTransform c u x ξ = sourceAmplitudeTransform c v x ξ := by
  simp only [sourceAmplitudeTransform, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [huv] with y hy
  rw [hy]

/-- `app:ch_regular_base:thm:actual-calculus`: the full operator respects
almost-everywhere equality of the datum even before integrability is known. -/
theorem fullAmplitudeOperator_congr_ae_input
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) → ℂ)
    {u v : EuclideanSpace ℝ (Fin d) → ℂ} (huv : u =ᵐ[volume] v) :
    fullAmplitudeOperator c u = fullAmplitudeOperator c v := by
  funext x
  unfold fullAmplitudeOperator
  rw [show sourceAmplitudeTransform c u x = sourceAmplitudeTransform c v x from
    funext (fun ξ ↦ sourceAmplitudeTransform_congr_ae_input c huv x ξ)]

/-- `app:ch_regular_base:thm:actual-calculus`: the physical pairing used by the
amplitude-bound construction is smooth in both positions. -/
theorem contDiff_pairedPosition :
    ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      pairedPosition p.1 p.2) := by
  apply (contDiff_piLp 2).mpr
  intro i
  dsimp only [pairedPosition, PiLp.toLp_apply]
  split_ifs <;> fun_prop

section Realization

variable (hd : 0 < d) (R : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
  (hbound : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)

/-- `app:ch_regular_base:eq:fio-input`: the low L² realization, reusing the
completed two-position amplitude construction. This is not a new series or an
assumed bounded extension of the desired integral. -/
def twoPositionL2Operator :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  boxScalarAmplitudeOperator b hb.continuous.stronglyMeasurable hd
    (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) A hbound.norm_le hbound.pure_le

/-- `app:ch_regular_base:eq:fio-input`, index zero: the constant uses only the
fixed box and the fixed low physical derivative budget. -/
theorem norm_twoPositionL2Operator_le :
    ‖twoPositionL2Operator hd R b hb hs A hbound‖ ≤ fixedBoxAmplitudeConstant d R * A :=
  norm_boxScalarAmplitudeOperator_le ..

/-- `app:ch_regular_base:eq:fio-input`, index zero on actual L² data. -/
theorem norm_twoPositionL2Operator_apply_le
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    ‖twoPositionL2Operator hd R b hb hs A hbound f‖ ≤
      (fixedBoxAmplitudeConstant d R * A) * ‖f‖ :=
  (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right (norm_twoPositionL2Operator_le hd R b hb hs A hbound)
      (norm_nonneg f))

/-- `app:ch_regular_base:eq:fio-input`, index zero for the actual Hilbert
adjoint of the bounded realization. Kernel reversal is a separate assertion. -/
theorem norm_twoPositionL2Operator_adjoint_apply_le
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    ‖(twoPositionL2Operator hd R b hb hs A hbound).adjoint f‖ ≤
      (fixedBoxAmplitudeConstant d R * A) * ‖f‖ := by
  apply (ContinuousLinearMap.le_opNorm _ f).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  simpa only [LinearIsometryEquiv.norm_map] using
    norm_twoPositionL2Operator_le hd R b hb hs A hbound

/-- `app:ch_regular_base:thm:actual-calculus`: the bounded realization equals
`fullAmplitudeOperator` almost everywhere on data with an integrable source
transform. Strong convergence supplies an almost-everywhere subsequence and
uniqueness of its pointwise limit proves the identification. -/
theorem twoPositionL2Operator_ae_fullAmplitudeOperator
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (hi : ∀ᵐ x, Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ b ξ (pairedPosition x y)) f x)) :
    twoPositionL2Operator hd R b hb hs A hbound f =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) f := by
  let Bρ := boxCompactFrequencyAmplitudeOperator b hb.continuous.stronglyMeasurable hd
    (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) A hbound.norm_le hbound.pure_le
  have hlim : Tendsto (fun ρ : ℝ ↦ Bρ ρ f) atTop
      (𝓝 (twoPositionL2Operator hd R b hb hs A hbound f)) :=
    tendsto_boxCompactFrequencyAmplitudeOperator ..
  obtain ⟨s, hsexhaust, hsae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae'
  have heq : ∀ᵐ x, ∀ n : ℕ, Bρ (s n) f x = boxScalarAmplitudeKernel b (s n) f x :=
    ae_all_iff.mpr (fun n ↦ boxCompactFrequencyAmplitudeOperator_ae_kernel ..)
  filter_upwards [hsae, heq, hi] with x hx hx' hix
  exact tendsto_nhds_unique (hx.congr (fun n ↦ hx' n))
    ((tendsto_boxScalarAmplitudeKernel_fullAmplitudeOperator b f x hix).comp hsexhaust)

include hd R hb hs A hbound in
/-- `app:ch_regular_base:eq:fio-input`: the literal source-first output is in
L² whenever source integration converges. Its bounded realization is proved
by the preceding theorem, rather than assumed. -/
theorem memLp_fullAmplitudeOperator_of_integrable_source
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (hi : ∀ᵐ x, Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ b ξ (pairedPosition x y)) f x)) :
    MemLp (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) f) 2 :=
  (Lp.memLp _).ae_eq (twoPositionL2Operator_ae_fullAmplitudeOperator hd R b hb hs A hbound f hi)

/-- `app:ch_regular_base:thm:actual-calculus`: identification on actual test
functions, independently of the representative chosen by `Lp`. -/
theorem twoPositionL2Operator_toLp_ae_fullAmplitudeOperator
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (hu : MemLp u 2)
    (hi : ∀ᵐ x, Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ b ξ (pairedPosition x y)) u x)) :
    twoPositionL2Operator hd R b hb hs A hbound (hu.toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u := by
  have heq : ∀ x, sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y))
      (hu.toLp u) x = sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) u x :=
    fun x ↦ funext (fun ξ ↦ sourceAmplitudeTransform_congr_ae_input _ hu.coeFn_toLp x ξ)
  have h := twoPositionL2Operator_ae_fullAmplitudeOperator hd R b hb hs A hbound
    (hu.toLp u) (by simpa only [heq] using hi)
  rwa [fullAmplitudeOperator_congr_ae_input _ hu.coeFn_toLp] at h

/-- `app:ch_regular_base:thm:actual-calculus`: a finite source-derivative mass
bound discharges the integrability premise on compact test data. The derivative
reserve is `dim + 1`, independent of the requested Sobolev index. -/
theorem twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_derivativeMass
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (hu : MemLp u 2)
    (huc : Continuous u) (hus : HasCompactSupport u)
    (hsource : ∀ x ξ, ContDiff ℝ (d + 1)
      (fun y ↦ u y • b ξ (pairedPosition x y)))
    (M : EuclideanSpace ℝ (Fin d) → ℝ)
    (hM : ∀ x ξ, sourceDerivativeMass
      (fun y ↦ u y • b ξ (pairedPosition x y)) (d + 1) ≤ M x) :
    twoPositionL2Operator hd R b hb hs A hbound (hu.toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u := by
  apply twoPositionL2Operator_toLp_ae_fullAmplitudeOperator hd R b hb hs A hbound u hu
  apply Eventually.of_forall
  intro x
  refine integrable_sourceFourier_of_compact_derivativeMass
    (fun ξ y ↦ u y • b ξ (pairedPosition x y)) ?_ 0 (d + 1) ?_ (hsource x)
    (fun _ ↦ hus.smul_right) (M x) ?_
  · exact (huc.comp continuous_snd).smul
      (hb.continuous.comp (continuous_fst.prodMk
        (continuous_pairedPosition.comp (continuous_const.prodMk continuous_snd))))
  · simp
  · simpa using hM x

/-- `app:ch_regular_base:thm:actual-calculus`: primitive finite source symbol
bounds identify the realization on smooth compact tests. The product derivative
mass is derived by Leibniz's rule in `SourceBounds`, not taken as an input. -/
theorem twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_sourceBounds
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (hu : MemLp u 2)
    (huc : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u)
    (M : EuclideanSpace ℝ (Fin d) → ℕ → ℝ)
    (hM : ∀ x j, j ≤ d + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ b ξ (pairedPosition x z)) y‖ ≤ M x j) :
    twoPositionL2Operator hd R b hb hs A hbound (hu.toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u := by
  apply twoPositionL2Operator_toLp_ae_fullAmplitudeOperator hd R b hb hs A hbound u hu
  apply Eventually.of_forall
  intro x
  refine integrable_sourceAmplitudeTransform_of_sourceSymbolBounds
    (fun x y ξ ↦ b ξ (pairedPosition x y)) u x 0 ?_ ?_ hus ?_ (M x) ?_
  · exact hb.continuous.comp (continuous_fst.prodMk
      (continuous_pairedPosition.comp (continuous_const.prodMk continuous_snd)))
  · simpa using huc
  · intro ξ
    exact (hb.comp (contDiff_const.prodMk
      (contDiff_pairedPosition.comp (contDiff_const.prodMk contDiff_id)))).of_le (by simp)
  · simpa using hM x

include hd R hb hs A hbound in
/-- `app:ch_regular_base:eq:fio-input`, index zero for the literal integral:
both membership and its numerical L² bound follow from the proved realization.
The smooth compact datum and primitive source bounds ensure convergence. -/
theorem fullAmplitudeOperator_l2_bound_of_sourceBounds
    (u : EuclideanSpace ℝ (Fin d) → ℂ)
    (huc : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u)
    (M : EuclideanSpace ℝ (Fin d) → ℕ → ℝ)
    (hM : ∀ x j, j ≤ d + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ b ξ (pairedPosition x z)) y‖ ≤ M x j) :
    MemLp (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u) 2 ∧
      (eLpNorm (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u)
        2 volume).toReal ≤
      (fixedBoxAmplitudeConstant d R * A) * (eLpNorm u 2 volume).toReal := by
  have hu : MemLp u 2 := huc.continuous.memLp_of_hasCompactSupport hus
  have heq := twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_sourceBounds
    hd R b hb hs A hbound u hu huc hus M hM
  refine ⟨(Lp.memLp _).ae_eq heq, ?_⟩
  rw [← eLpNorm_congr_ae heq, ← Lp.norm_def]
  simpa only [Lp.norm_toLp] using
    norm_twoPositionL2Operator_apply_le hd R b hb hs A hbound (hu.toLp u)

end Realization
end JanetCartan.Pseudodifferential
