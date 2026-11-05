module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Euclidean kernel normals and Fubini

The common-kernel deduction for `app:ch_waves:eq:sampling-prefix-normal`.
A square-integrable kernel gives a Bochner integral of rank-one operators;
Fubini then identifies the full normal with the integral of slice normals.
The later compact-kernel application supplies square integrability from the
original cutoffs. No normal identity is an input.
-/

@[expose] public noncomputable section
open MeasureTheory InnerProductSpace
open scoped ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open SamplingKernelBounds AmplitudeBound

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {k : X → E}

omit [CompleteSpace E] in
/-- The full rank-one normal kernel is Bochner integrable in operator norm,
by its exact squared-column norm (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_rankOne_kernel (hk : MemLp k 2 μ) :
    Integrable (fun u ↦ rankOne ℂ (k u) (k u)) μ := by
  have hc : Continuous (fun v : E ↦ rankOne ℂ v v) :=
    ((ContinuousLinearMap.smulRightL ℂ E E).continuous.comp (innerSL ℂ).continuous).clm_apply
      continuous_id
  apply (hk.integrable_norm_pow (by decide : 2 ≠ 0)).mono'
    (hc.comp_aestronglyMeasurable hk.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun u ↦ by simp [sq]

/-- The normal of actual synthesis equals its operator-valued kernel
integral (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem kernelSynthesis_normal_eq_integral (hk : MemLp k 2 μ) :
    kernelSynthesis hk ∘L (kernelSynthesis hk).adjoint =
      ∫ u, rankOne ℂ (k u) (k u) ∂μ := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, kernelSynthesis_apply,
    ContinuousLinearMap.integral_apply (integrable_rankOne_kernel hk) f]
  apply integral_congr_ae
  filter_upwards [kernelSynthesis_hasAdjointKernel hk f] with u hu
  simp only [hu, rankOne_apply]

omit [CompleteSpace E] in
/-- A bounded input mask preserves Bochner integrability of the full normal
kernel (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem integrable_maskedRankOne_kernel (hk : MemLp k 2 μ) (g : Lp ℂ ∞ μ) :
    Integrable (fun u ↦ g u • rankOne ℂ (k u) (k u)) μ := by
  exact memLp_one_iff_integrable.mp
    ((Lp.memLp g).smul (memLp_one_iff_integrable.mpr (integrable_rankOne_kernel hk)))

/-- Literal masked normal from the common forward kernel. Both physical
positions belong to the same column and its adjoint; no normal equality or
integrability is assumed (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem kernelSynthesis_maskedNormal_eq_integral (hk : MemLp k 2 μ) (g : Lp ℂ ∞ μ) :
    kernelSynthesis hk ∘L multiplicationOperator g ∘L (kernelSynthesis hk).adjoint =
      ∫ u, g u • rankOne ℂ (k u) (k u) ∂μ := by
  ext1 f
  simp only [ContinuousLinearMap.comp_apply]
  rw [kernelSynthesis_apply,
    ContinuousLinearMap.integral_apply (integrable_maskedRankOne_kernel hk g) f]
  apply integral_congr_ae
  filter_upwards [multiplicationOperator_coeFn g ((kernelSynthesis hk).adjoint f),
    kernelSynthesis_hasAdjointKernel hk f] with u hu hv
  simp only [hu, hv, smul_apply, rankOne_apply, smul_smul]

variable {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]
  {ν : Measure S} {σ : Measure U} [SFinite ν] [SFinite σ]
  {a : S → U → E}

omit [SFinite ν] in
/-- Slice normals are genuinely Bochner integrable, as a consequence of the
common square-integrable kernel and Fubini
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_sliceSynthesis_normal
    (ha : MemLp a.uncurry 2 (ν.prod σ)) (hs : ∀ s, MemLp (a s) 2 σ) :
    Integrable (fun s ↦ kernelSynthesis (hs s) ∘L (kernelSynthesis (hs s)).adjoint) ν := by
  simp_rw [kernelSynthesis_normal_eq_integral]
  exact (integrable_rankOne_kernel ha).integral_prod_left

/-- The common forward synthesis kernel disintegrates exactly. This is
Fubini in the operator norm, not merely a weak pairing identity
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem kernelSynthesis_normal_eq_integral_slice
    (ha : MemLp a.uncurry 2 (ν.prod σ)) (hs : ∀ s, MemLp (a s) 2 σ) :
    kernelSynthesis ha ∘L (kernelSynthesis ha).adjoint =
      ∫ s, kernelSynthesis (hs s) ∘L (kernelSynthesis (hs s)).adjoint ∂ν := by
  simp_rw [kernelSynthesis_normal_eq_integral]
  exact integral_prod _ (integrable_rankOne_kernel ha)

/-- A nonnegative patch weight enters the common forward kernel by its
square root, including at its zero set. The normal identity never divides
by this weight (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normal_sqrt_weight {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] E) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((Real.sqrt ρ : ℂ) • T) ∘L ((Real.sqrt ρ : ℂ) • T).adjoint =
      (ρ : ℂ) • (T ∘L T.adjoint) := by
  rw [map_smulₛₗ]
  simp only [Complex.conj_ofReal, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt hρ]

omit [CompleteSpace E] in
private theorem rankOne_sqrt_weight (v : E) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    rankOne ℂ ((Real.sqrt ρ : ℂ) • v) ((Real.sqrt ρ : ℂ) • v) =
      (ρ : ℂ) • rankOne ℂ v v := by
  ext w
  simp only [rankOne_apply, inner_smul_left, Complex.conj_ofReal, smul_apply, smul_smul]
  rw [mul_comm _ (Real.sqrt ρ : ℂ), ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hρ]

/-- Weighted disintegration after a measure-preserving input identification.
Only forward column equalities and an exact input-mask representative are
inputs. The common kernel supplies both Fubini and operator integrability;
zero patch weights are allowed (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weighted_normal_disintegration_of_columns
    (e : X ≃ᵐ S × U) (he : MeasurePreserving e μ (ν.prod σ))
    (hk : MemLp k 2 μ) (hs : ∀ s, MemLp (a s) 2 σ)
    (ρ m : S → ℝ) (hρ : ∀ s, 0 ≤ ρ s)
    (hcol : ∀ᵐ q ∂ν.prod σ, k (e.symm q) = (Real.sqrt (ρ q.1) : ℂ) • a q.1 q.2)
    (g : Lp ℂ ∞ μ)
    (hg : g =ᵐ[μ] fun u ↦ (m (e u).1 : ℂ)) :
    Integrable (fun s ↦ ((m s * ρ s : ℝ) : ℂ) •
      (kernelSynthesis (hs s) ∘L (kernelSynthesis (hs s)).adjoint)) ν ∧
    kernelSynthesis hk ∘L multiplicationOperator g ∘L (kernelSynthesis hk).adjoint =
      ∫ s, ((m s * ρ s : ℝ) : ℂ) •
        (kernelSynthesis (hs s) ∘L (kernelSynthesis (hs s)).adjoint) ∂ν := by
  let H := fun q : S × U ↦ ((m q.1 * ρ q.1 : ℝ) : ℂ) •
    rankOne ℂ (a q.1 q.2) (a q.1 q.2)
  have heq : (fun q : S × U ↦ g (e.symm q) •
      rankOne ℂ (k (e.symm q)) (k (e.symm q))) =ᵐ[ν.prod σ] H := by
    filter_upwards [(he.symm e).quasiMeasurePreserving.ae hg, hcol] with q hq hc
    simp only [e.apply_symm_apply] at hq
    rw [hq, hc, rankOne_sqrt_weight _ (hρ q.1), smul_smul]
    simp only [H, Complex.ofReal_mul]
  have hi : Integrable H (ν.prod σ) :=
    ((he.symm e).integrable_comp_of_integrable (integrable_maskedRankOne_kernel hk g)).congr heq
  have hslice (s : S) : (∫ u, H (s, u) ∂σ) =
      ((m s * ρ s : ℝ) : ℂ) •
        (kernelSynthesis (hs s) ∘L (kernelSynthesis (hs s)).adjoint) := by
    rw [kernelSynthesis_normal_eq_integral, ← integral_smul]
  refine ⟨?_, ?_⟩
  · simpa only [hslice] using hi.integral_prod_left
  · rw [kernelSynthesis_maskedNormal_eq_integral,
      ← (he.symm e).integral_comp e.symm.measurableEmbedding,
      integral_congr_ae heq, integral_prod _ hi]
    simp only [hslice]

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
