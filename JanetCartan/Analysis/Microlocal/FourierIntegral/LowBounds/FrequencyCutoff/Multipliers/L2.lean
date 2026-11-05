module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Basic
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder

/-! # Actual vector L² frequency cutoffs

The multipliers for `app:ch_regular_base:thm:actual-calculus`, Step 1, on
exactly the Euclidean-fiber Lebesgue space used by `LowBounds.VectorGraph`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped Topology ComplexInnerProductSpace ENNReal

namespace JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff

variable {n r : ℕ}
local notation "ℰ" => Euclidean n
local notation "𝒱" => EuclideanSpace ℂ (Fin r)
local notation "ℋ" => Lp 𝒱 2 (volume : Measure ℰ)

/-- Bounded symbol in cycle frequency for the regularization in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def cycleCutoffLp (j : ℕ) : Lp ℂ ∞ (volume : Measure ℰ) :=
  (memLp_top_of_bound (cycleCutoff_contDiff j).continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (cycleCutoff_norm_le j))).toLp (cycleCutoff j)

/-- The bounded symbol is the actual cutoff almost everywhere (same Step 1). -/
theorem cycleCutoffLp_coeFn (j : ℕ) :
    cycleCutoffLp (n := n) j =ᵐ[volume] cycleCutoff j :=
  MemLp.coeFn_toLp _

/-- Actual pointwise multiplication in frequency, consumed by `multiplier`
for `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def frequencyMultiplication (j : ℕ) : ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := 𝒱)).holderL volume ∞ 2 2 (cycleCutoffLp j)

/-- Pointwise meaning of frequency multiplication (same Step 1). -/
theorem frequencyMultiplication_coeFn (j : ℕ) (f : ℋ) :
    frequencyMultiplication j f =ᵐ[volume] fun ξ ↦ cycleCutoff j ξ • f ξ := by
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ (E := 𝒱)).coeFn_holder
    (r := 2) (cycleCutoffLp j) f, cycleCutoffLp_coeFn (n := n) j] with ξ h hξ
  exact h.trans (by rw [hξ]; rfl)

/-- Pointwise domination makes frequency multiplication contractive (same Step 1). -/
theorem frequencyMultiplication_norm_le (j : ℕ) (f : ℋ) :
    ‖frequencyMultiplication j f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [frequencyMultiplication_coeFn j f] with ξ hξ
  rw [hξ, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (cycleCutoff_norm_le j ξ)

/-- The actual cutoff `P_j = 𝓕⁻ χ_j(2π·) 𝓕`, consumed by the parent graph
factorization and strong adjoint limit in `app:ch_regular_base:thm:actual-calculus`. -/
def multiplier (j : ℕ) : ℋ →L[ℂ] ℋ :=
  (fourierInvCLM ℂ ℋ).comp ((frequencyMultiplication j).comp (fourierCLM ℂ ℋ))

/-- Literal Fourier definition of the regularization (same Step 1). -/
theorem multiplier_apply (j : ℕ) (f : ℋ) :
    multiplier j f = 𝓕⁻ (frequencyMultiplication j (𝓕 f)) := rfl

/-- The constructed physical-frequency cutoffs are contractions (same Step 1). -/
theorem multiplier_norm_le (j : ℕ) (f : ℋ) : ‖multiplier j f‖ ≤ ‖f‖ := by
  change ‖(Lp.fourierTransformₗᵢ ℰ 𝒱).symm (frequencyMultiplication j (𝓕 f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, ← Lp.norm_fourier_eq f]
  exact frequencyMultiplication_norm_le j _

/-- Uniform operator norm bound for the parent strong limit (same Step 1). -/
theorem norm_multiplier_le (j : ℕ) : ‖multiplier (n := n) (r := r) j‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using multiplier_norm_le j)

/-- Reality of the cutoff gives symmetry of frequency multiplication (same Step 1). -/
theorem frequencyMultiplication_inner (j : ℕ) (f g : ℋ) :
    ⟪frequencyMultiplication j f, g⟫ = ⟪f, frequencyMultiplication j g⟫ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frequencyMultiplication_coeFn j f,
    frequencyMultiplication_coeFn j g] with ξ hf hg
  rw [hf, hg, inner_smul_left, inner_smul_right]
  change star (cycleCutoff j ξ) * _ = _
  rw [cycleCutoff_star]

/-- Self-adjointness of the actual L² cutoff, used to remove graph
regularization in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem multiplier_adjoint (j : ℕ) :
    (multiplier (n := n) (r := r) j).adjoint = multiplier j := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro f g
  change ⟪multiplier j f, g⟫ = ⟪f, multiplier j g⟫
  rw [← Lp.inner_fourier_eq (multiplier j f) g,
    ← Lp.inner_fourier_eq f (multiplier j g)]
  simp only [multiplier_apply, fourier_fourierInv_eq]
  exact frequencyMultiplication_inner j (𝓕 f) (𝓕 g)

end JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
