module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.PhysicalCutoffError
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SourceBounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointRemainder
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Exact diagonal reduction of the unregularized operator

For `app:ch_regular_base:eq:actual-pdo-remainder`, pass the literal kernel
identity to its physical source-tested limit. The hypotheses are explicit
integrability conditions on the source Fourier transforms, supplied in
`SourceDecay` by finite source-derivative budgets.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff FourierTransform Topology

namespace JanetCartan.Pseudodifferential
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the cutoff defect is jointly
integrable against a compact physical source test. -/
theorem integrable_frequencyCutoffError_test
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V → V → V →L[ℝ] F) (u : V → ℂ) (χ : V → ℝ) (x : V)
    (hB : Continuous (fun p : V × V ↦ B x p.2 p.1))
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    Integrable (fun p : V × V ↦ u p.2 • frequencyCutoffError b χ (B x p.2) p.1) := by
  have he : Continuous (fun p : V × V ↦ frequencyCutoffError b χ (B x p.2) p.1) := by
    apply Continuous.const_smul
    apply continuous_finsetSum
    intro j _
    exact (((hχ.continuous_fderiv (by simp)).comp continuous_fst).clm_apply
      continuous_const).smul (hB.clm_apply continuous_const)
  apply ((hu.comp continuous_snd).smul he).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro ((hχc.fderiv ℝ).isCompact.prod huc.isCompact)
  intro p hp
  by_cases hξ : p.1 ∈ tsupport (fderiv ℝ χ)
  · have hy : p.2 ∉ tsupport u := fun hy ↦ hp ⟨hξ, hy⟩
    simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [frequencyCutoffError, image_eq_zero_of_notMem_tsupport hξ]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the diagonal amplitude is
exactly the source-independent diagonal symbol applied after the source mask. -/
theorem fullAmplitudeOperator_diagonalAmplitude
    (c : V → V → V → F) (β : V → ℝ) (u : V → ℂ) (x : V) :
    fullAmplitudeOperator (diagonalAmplitude c β) u x =
      fullAmplitudeOperator (fun x _y ξ ↦ c x x ξ) (fun y ↦ β y • u y) x := by
  unfold fullAmplitudeOperator
  apply congrArg (fun f : V → F ↦ 𝓕⁻ f x)
  funext ξ
  unfold sourceAmplitudeTransform
  apply congrArg (fun f : V → F ↦ 𝓕 f ξ)
  funext y
  change u y • (β y • c x x ξ) = (β y • u y) • c x x ξ
  rw [smul_assoc, smul_comm]

variable [CompleteSpace F]

set_option maxHeartbeats 600000 in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the exact frequency-cutoff
identity for the actual operators, including the full source-tested defect. -/
theorem fullAmplitudeOperator_frequency_smul_eq_diagonal_add_remainder_add_error
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β χ : V → ℝ) (u : V → ℂ) (x : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hβc : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    fullAmplitudeOperator (fun x y ξ ↦ χ ξ • c x y ξ) u x =
      fullAmplitudeOperator (fun x y ξ ↦ χ ξ • diagonalAmplitude c β x y ξ) u x +
      fullAmplitudeOperator (fun x y ξ ↦ χ ξ • diagonalRemainderAmplitude b c β x y ξ) u x +
      fullAmplitudeOperator (fun x y ξ ↦ frequencyCutoffError b χ
        (fullTaylorCoefficient c β x y) ξ) u x := by
  have hc' : Continuous (fun p : V × V ↦ c x p.2 p.1) :=
    hc.continuous.comp (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop)
  have hd : Continuous (fun p : V × V ↦ diagonalAmplitude c β x p.2 p.1) :=
    (hβ.continuous.comp continuous_snd).smul
      (hc.continuous.comp (f := fun p : V × V ↦ (x, x, p.1)) (by fun_prop))
  have hr : Continuous (fun p : V × V ↦ diagonalRemainderAmplitude b c β x p.2 p.1) :=
    (contDiff_diagonalRemainderAmplitude_joint b c β hc hβ).continuous.comp
      (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop)
  have hB : Continuous (fun p : V × V ↦ fullTaylorCoefficient c β x p.2 p.1) :=
    (contDiff_fullTaylorCoefficient_joint c β hc hβ).continuous.comp
      (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop)
  have hi := integrable_frequency_cutoff_amplitude_test c u χ x hc' hu huc hχ.continuous hχc
  have hid := integrable_frequency_cutoff_amplitude_test (diagonalAmplitude c β) u χ x hd hu huc hχ.continuous hχc
  have hir := integrable_frequency_cutoff_amplitude_test (diagonalRemainderAmplitude b c β) u χ x hr hu huc hχ.continuous hχc
  have hie := integrable_frequencyCutoffError_test b (fullTaylorCoefficient c β) u χ x hB hu huc (hχ.of_le (by simp)) hχc
  rw [fullAmplitudeOperator_eq_integral_amplitudeKernel _ u x hi,
    fullAmplitudeOperator_eq_integral_amplitudeKernel _ u x hid,
    fullAmplitudeOperator_eq_integral_amplitudeKernel _ u x hir,
    fullAmplitudeOperator_eq_integral_amplitudeKernel _ u x hie]
  have hcs : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2) :=
    hc.comp (f := fun p : V × V ↦ (x, p)) (by fun_prop)
  have hkd := integrable_amplitudeKernel_test (fun x y ξ ↦ χ ξ • diagonalAmplitude c β x y ξ) u x hid
  have hkr := integrable_amplitudeKernel_test (fun x y ξ ↦ χ ξ • diagonalRemainderAmplitude b c β x y ξ) u x hir
  have hke := integrable_amplitudeKernel_test (fun x y ξ ↦ frequencyCutoffError b χ (fullTaylorCoefficient c β x y) ξ) u x hie
  have hsum := integral_add (hkd.add hkr) hke
  simp only [Pi.add_apply] at hsum
  rw [← integral_add hkd hkr, ← hsum]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [amplitudeKernel_frequency_smul_eq_diagonal_add_remainder_add_error b c β χ x y
    hcs hβc hχ hχc]
  simp only [smul_add]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: exact diagonal reduction of
the unregularized full operator on compact source tests. All convergence inputs
concern explicit source Fourier integrals; the identity follows from the actual
regularized kernels and the vanishing cutoff defect. -/
theorem fullAmplitudeOperator_eq_diagonal_add_remainder_of_cutoff
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (u : V → ℂ) (x : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hβc : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hi : Integrable (sourceAmplitudeTransform c u x))
    (hid : Integrable (sourceAmplitudeTransform (diagonalAmplitude c β) u x))
    (hir : Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude b c β) u x))
    (hiB : Integrable (sourceAmplitudeTransform (fullTaylorCoefficient c β) u x))
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1) (hχc : HasCompactSupport χ)
    (C D : ℝ) (hC : ∀ ξ, |χ ξ| ≤ C) (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D) :
    fullAmplitudeOperator c u x = fullAmplitudeOperator (diagonalAmplitude c β) u x +
      fullAmplitudeOperator (diagonalRemainderAmplitude b c β) u x := by
  have hl := tendsto_fullAmplitudeOperator_frequency_cutoff c u x hi χ hχ.continuous hχ0 C hC
  have hd := tendsto_fullAmplitudeOperator_frequency_cutoff (diagonalAmplitude c β) u x hid χ hχ.continuous hχ0 C hC
  have hr := tendsto_fullAmplitudeOperator_frequency_cutoff (diagonalRemainderAmplitude b c β) u x hir χ hχ.continuous hχ0 C hC
  have hsource : ∀ ξ, Integrable (fun y ↦ u y • fullTaylorCoefficient c β x y ξ) := by
    intro ξ
    apply Continuous.integrable_of_hasCompactSupport _ huc.smul_right
    exact hu.smul ((contDiff_fullTaylorCoefficient_joint c β hc hβ).continuous.comp
      (f := fun y : V ↦ (x, y, ξ)) (by fun_prop))
  have he := tendsto_fullAmplitudeOperator_frequencyCutoffError_rescaled b
    (fullTaylorCoefficient c β) u x hsource hiB χ (hχ.differentiable (by simp)) D hD
  have hh := (hd.add hr).add he
  rw [add_zero] at hh
  apply tendsto_nhds_unique hl (hh.congr' _)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (fullAmplitudeOperator_frequency_smul_eq_diagonal_add_remainder_add_error b c β
    (fun ξ ↦ χ (R⁻¹ • ξ)) u x hc hβ hβc hu huc
    (hχ.comp (contDiff_const.smul contDiff_id)) (hχc.comp_smul (inv_ne_zero hR.ne'))).symm


/-- `app:ch_regular_base:eq:actual-pdo-remainder`: diagonal reduction without
any auxiliary cutoff in the statement. A smooth compact cutoff is constructed
inside the proof, and its entire defect vanishes in the physical limit. -/
theorem fullAmplitudeOperator_eq_diagonal_add_remainder
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (u : V → ℂ) (x : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hβc : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hi : Integrable (sourceAmplitudeTransform c u x))
    (hid : Integrable (sourceAmplitudeTransform (diagonalAmplitude c β) u x))
    (hir : Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude b c β) u x))
    (hiB : Integrable (sourceAmplitudeTransform (fullTaylorCoefficient c β) u x)) :
    fullAmplitudeOperator c u x = fullAmplitudeOperator (diagonalAmplitude c β) u x +
      fullAmplitudeOperator (diagonalRemainderAmplitude b c β) u x := by
  let χ : ContDiffBump (0 : V) := default
  have hχ : ContDiff ℝ ∞ (χ : V → ℝ) := χ.contDiff
  obtain ⟨D, hD⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  exact fullAmplitudeOperator_eq_diagonal_add_remainder_of_cutoff b c β u x hc hβ hβc hu huc
    hi hid hir hiB χ hχ (χ.one_of_mem_closedBall (by simp [χ.rIn_pos.le]))
    χ.hasCompactSupport 1 D (fun ξ ↦ (abs_of_nonneg χ.nonneg).trans_le χ.le_one) hD

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: finite source-derivative
budgets suffice for the exact unregularized diagonal identity. The common
reserve is `m + dim V + 1`; no convergence or operator identity is assumed. -/
theorem fullAmplitudeOperator_eq_diagonal_add_remainder_of_derivativeMass
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (u : V → ℂ) (x : V) (m : ℕ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hβc : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hu : ContDiff ℝ (m + Module.finrank ℝ V + 1) u) (huc : HasCompactSupport u)
    (A Ad Ar AB : ℝ)
    (hA : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • c x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ A * (1 + ‖ξ‖) ^ m)
    (hAd : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • diagonalAmplitude c β x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ Ad * (1 + ‖ξ‖) ^ m)
    (hAr : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • diagonalRemainderAmplitude b c β x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ Ar * (1 + ‖ξ‖) ^ m)
    (hAB : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • fullTaylorCoefficient c β x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ AB * (1 + ‖ξ‖) ^ m) :
    fullAmplitudeOperator c u x = fullAmplitudeOperator (diagonalAmplitude c β) u x +
      fullAmplitudeOperator (diagonalRemainderAmplitude b c β) u x := by
  have hd : ContDiff ℝ ∞ (fun p : V × V × V ↦ diagonalAmplitude c β p.1 p.2.1 p.2.2) :=
    (hβ.comp contDiff_snd.fst).smul
      (hc.comp (f := fun p : V × V × V ↦ (p.1, p.1, p.2.2)) (by fun_prop))
  have hr := contDiff_diagonalRemainderAmplitude_joint b c β hc hβ
  have hB := contDiff_fullTaylorCoefficient_joint c β hc hβ
  apply fullAmplitudeOperator_eq_diagonal_add_remainder b c β u x hc hβ hβc hu.continuous huc
  · exact integrable_sourceAmplitudeTransform_of_joint_derivativeMass c u x m hc hu huc A hA
  · exact integrable_sourceAmplitudeTransform_of_joint_derivativeMass _ u x m hd hu huc Ad hAd
  · exact integrable_sourceAmplitudeTransform_of_joint_derivativeMass _ u x m hr hu huc Ar hAr
  · exact integrable_sourceAmplitudeTransform_of_joint_derivativeMass _ u x m hB hu huc AB hAB

end JanetCartan.Pseudodifferential
