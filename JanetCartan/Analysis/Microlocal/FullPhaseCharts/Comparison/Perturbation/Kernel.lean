module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Basic
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.PhaseJets
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Mixed Hessian kernel for phase perturbations

The physical derivative of the covector integrand in
`app:ch_seed:eq:seed-quotient-integral` is the Riesz representative of
`D²S(x, ξ)((v, 0), (0, η))`. This module supplies its bounded linear extraction
from the joint Hessian, its derivative in all joint phase variables, and the
phase `C⁴` bounds. The consumer is the double-integral representation of
`modulationChart` in the comparison paragraph of
`app:ch_seed:prop:seed-phase-charts`.

These are estimates for the integrand. Identification with the literal chart
and differentiation of the two integrals are separate obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.Comparison

variable {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedSpace ℝ X := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ (X × E) := Prod.normedSpace
local instance : NormedSpace ℝ ((X × E) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((X × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((X × E) →L[ℝ] (X × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((X × E) →L[ℝ] (X × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Extract the mixed physical/covector Hessian in
`app:ch_seed:eq:seed-quotient-integral`, using the physical Riesz isometry. -/
def mixedHessianMap (H : (X × E) →L[ℝ] (X × E) →L[ℝ] ℝ) : E →L[ℝ] X :=
  (InnerProductSpace.toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((H.comp (ContinuousLinearMap.inl ℝ X E)).flip.comp
      (ContinuousLinearMap.inr ℝ X E))

/-- Evaluation of the mixed kernel paired with a physical direction
(`app:ch_seed:eq:seed-quotient-integral`). -/
@[simp] theorem inner_mixedHessianMap
    (H : (X × E) →L[ℝ] (X × E) →L[ℝ] ℝ) (η : E) (v : X) :
    inner ℝ (mixedHessianMap H η) v = H (v, 0) (0, η) := by
  change (InnerProductSpace.toDual ℝ X) ((InnerProductSpace.toDual ℝ X).symm _) v = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The mixed extraction has norm at most one; no phase-dependent constant
is introduced in `app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_mixedHessianMap_le (H : (X × E) →L[ℝ] (X × E) →L[ℝ] ℝ) :
    ‖mixedHessianMap H‖ ≤ ‖H‖ := by
  refine (mixedHessianMap H).opNorm_le_bound (norm_nonneg H) ?_
  intro η
  change ‖(InnerProductSpace.toDual ℝ X).symm _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg H) (norm_nonneg η)) ?_
  intro v
  change ‖H (v, 0) (0, η)‖ ≤ _
  simpa only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg v),
    max_eq_right (norm_nonneg η), mul_right_comm] using H.le_opNorm₂ (v, 0) (0, η)

/-- The bounded linear map from joint Hessians to the physical mixed kernel.
It is used to pass derivatives and integrals through the Riesz identification
in `app:ch_seed:prop:seed-phase-charts`. -/
def mixedHessianExtraction :
    ((X × E) →L[ℝ] (X × E) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := mixedHessianMap (X := X) (E := E)
      map_add' := by
        intro H G
        ext η
        apply (InnerProductSpace.toDual ℝ X).injective
        ext v
        simp only [map_add, add_apply]
        change inner ℝ (mixedHessianMap (H + G) η) v =
          inner ℝ (mixedHessianMap H η) v + inner ℝ (mixedHessianMap G η) v
        simp
      map_smul' := by
        intro c H
        ext η
        apply (InnerProductSpace.toDual ℝ X).injective
        ext v
        simp only [map_smul, smul_apply]
        change inner ℝ (mixedHessianMap (c • H) η) v =
          c • inner ℝ (mixedHessianMap H η) v
        simp }
    1 (fun H ↦ by simpa using norm_mixedHessianMap_le H)

/-- The operator used inside the two integrals for the physical modulation
chart (`app:ch_seed:prop:seed-phase-charts`). -/
def phaseMixedKernel (S : X × E → ℝ) (q : X × E) : E →L[ℝ] X :=
  mixedHessianExtraction (fderiv ℝ (fderiv ℝ S) q)

/-- The kernel evaluates exactly the mixed phase Hessian of
`app:ch_seed:eq:seed-quotient-integral`. -/
@[simp] theorem inner_phaseMixedKernel (S : X × E → ℝ) (q : X × E) (η : E) (v : X) :
    inner ℝ (phaseMixedKernel S q η) v =
      fderiv ℝ (fderiv ℝ S) q (v, 0) (0, η) :=
  inner_mixedHessianMap _ _ _

/-- The mixed-kernel value costs only two of the four phase derivatives in
`app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_phaseMixedKernel_le_cNorm_four {K : Set (X × E)} {S : X × E → ℝ}
    (hK : IsCompact K) (hS : ∀ q ∈ K, ContDiffAt ℝ 4 S q)
    {q : X × E} (hq : q ∈ K) :
    ‖phaseMixedKernel S q‖ ≤ cNorm K 4 S := by
  apply (norm_mixedHessianMap_le _).trans
  simpa only [norm_iteratedFDeriv_zero] using
    norm_phaseHessian_jet_le_cNorm_four hK hS hq (j := 0) (by norm_num)

/-- The directional kernel bound used under both integrals in
`app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_phaseMixedKernel_apply_le_cNorm_four {K : Set (X × E)} {S : X × E → ℝ}
    (hK : IsCompact K) (hS : ∀ q ∈ K, ContDiffAt ℝ 4 S q)
    {q : X × E} (hq : q ∈ K) (η : E) :
    ‖phaseMixedKernel S q η‖ ≤ cNorm K 4 S * ‖η‖ :=
  ((phaseMixedKernel S q).le_opNorm η).trans
    (mul_le_mul_of_nonneg_right (norm_phaseMixedKernel_le_cNorm_four hK hS hq)
      (norm_nonneg η))

/-- Local smoothness of the mixed kernel follows from local phase smoothness,
without a global extension (`app:ch_seed:prop:seed-phase-charts`). -/
theorem contDiffAt_phaseMixedKernel {S : X × E → ℝ} {q : X × E}
    (hS : ContDiffAt ℝ ∞ S q) : ContDiffAt ℝ ∞ (phaseMixedKernel S) q := by
  have h₁ : ContDiffAt ℝ ∞ (fderiv ℝ S) q := hS.fderiv_right (by simp)
  have h₂ : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ S)) q := h₁.fderiv_right (by simp)
  exact mixedHessianExtraction.contDiff.contDiffAt.comp q h₂

/-- All physical and covector variables are retained when differentiating the
mixed kernel (`app:ch_seed:prop:seed-phase-charts`). -/
theorem hasFDerivAt_phaseMixedKernel {S : X × E → ℝ} {q : X × E}
    (hS : ContDiffAt ℝ 4 S q) :
    HasFDerivAt (phaseMixedKernel S)
      (mixedHessianExtraction.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ S)) q)) q := by
  have h₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ S)) q :=
    (hS.fderiv_right (show (3 : WithTop ℕ∞) + 1 ≤ 4 by norm_num)).fderiv_right
      (by norm_num)
  exact mixedHessianExtraction.hasFDerivAt.comp q (h₂.differentiableAt (by norm_num)).hasFDerivAt

omit [CompleteSpace X] in
private theorem norm_phaseHessian_derivative_apply
    {K : Set (X × E)} {f : X × E → ℝ} (hK : IsCompact K)
    (hf : ∀ q ∈ K, ContDiffAt ℝ 4 f q) {q : X × E} (hq : q ∈ K) (v : X × E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) q v‖ ≤ cNorm K 4 f * ‖v‖ := by
  have hb : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) q‖ ≤ cNorm K 4 f := by
    simpa only [norm_iteratedFDeriv_one] using
      norm_phaseHessian_jet_le_cNorm_four hK hf hq (j := 1) (by norm_num)
  exact ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) q).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg v))

/-- The full phase-variable derivative of the mixed kernel is bounded by the
original `C⁴` error budget (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_fderiv_phaseMixedKernel_le_cNorm_four {K : Set (X × E)} {S : X × E → ℝ}
    (hK : IsCompact K) (hS : ∀ q ∈ K, ContDiffAt ℝ 4 S q)
    {q : X × E} (hq : q ∈ K) :
    ‖fderiv ℝ (phaseMixedKernel S) q‖ ≤ cNorm K 4 S := by
  rw [(hasFDerivAt_phaseMixedKernel (hS q hq)).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (cNorm_nonneg _ _ _)
  intro v
  exact (norm_mixedHessianMap_le _).trans
    (norm_phaseHessian_derivative_apply hK hS hq v)


/-- Subtracting locally smooth phases subtracts their actual mixed kernels,
so the error estimates use `cNorm K 4 (S - S₀)`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem phaseMixedKernel_sub {S S₀ : X × E → ℝ} {q : X × E}
    (hS : ContDiffAt ℝ 4 S q) (hS₀ : ContDiffAt ℝ 4 S₀ q) :
    phaseMixedKernel (S - S₀) q = phaseMixedKernel S q - phaseMixedKernel S₀ q := by
  have he : fderiv ℝ (S - S₀) =ᶠ[𝓝 q] fderiv ℝ S - fderiv ℝ S₀ := by
    filter_upwards [hS.eventually (by norm_num), hS₀.eventually (by norm_num)] with y hy hy₀
    exact fderiv_sub (hy.differentiableAt (by norm_num)) (hy₀.differentiableAt (by norm_num))
  have hd : DifferentiableAt ℝ (fderiv ℝ S) q :=
    (hS.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 4 by norm_num)).differentiableAt one_ne_zero
  have hd₀ : DifferentiableAt ℝ (fderiv ℝ S₀) q :=
    (hS₀.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 4 by norm_num)).differentiableAt one_ne_zero
  ext η
  apply (InnerProductSpace.toDual ℝ X).injective
  ext v
  change inner ℝ (phaseMixedKernel (S - S₀) q η) v =
    inner ℝ ((phaseMixedKernel S q - phaseMixedKernel S₀ q) η) v
  simp only [sub_apply, inner_sub_left, inner_phaseMixedKernel,
    he.fderiv_eq, fderiv_sub hd hd₀]

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Chain rule for the mixed kernel with every data variable retained.
The two terms distinguish changes in `η` from movement in phase space,
as needed in `app:ch_seed:prop:seed-phase-charts`. -/
theorem hasFDerivAt_phaseMixedKernel_comp_apply
    {S : X × E → ℝ} {g : A → X × E} {v : A → E} {a : A}
    {g' : A →L[ℝ] X × E} {v' : A →L[ℝ] E}
    (hS : ContDiffAt ℝ 4 S (g a)) (hg : HasFDerivAt g g' a) (hv : HasFDerivAt v v' a) :
    HasFDerivAt (fun b ↦ phaseMixedKernel S (g b) (v b))
      ((phaseMixedKernel S (g a)).comp v' +
        ((fderiv ℝ (phaseMixedKernel S) (g a)).comp g').flip (v a)) a := by
  exact (((hasFDerivAt_phaseMixedKernel hS).differentiableAt.hasFDerivAt).comp a hg).clm_apply hv

/-- Quantitative full data derivative of the mixed integrand. The phase is
measured only on `K`; the other factors are geometric derivatives of the shifted
point and direction (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_fderiv_phaseMixedKernel_comp_apply_le_cNorm_four
    {K : Set (X × E)} {S : X × E → ℝ} {g : A → X × E} {v : A → E} {a : A}
    (hK : IsCompact K) (hS : ∀ q ∈ K, ContDiffAt ℝ 4 S q) (ha : g a ∈ K)
    (hg : DifferentiableAt ℝ g a) (hv : DifferentiableAt ℝ v a) :
    ‖fderiv ℝ (fun b ↦ phaseMixedKernel S (g b) (v b)) a‖ ≤
      cNorm K 4 S * (‖fderiv ℝ v a‖ + ‖fderiv ℝ g a‖ * ‖v a‖) := by
  rw [(hasFDerivAt_phaseMixedKernel_comp_apply (hS _ ha) hg.hasFDerivAt hv.hasFDerivAt).fderiv]
  have hb := norm_phaseMixedKernel_le_cNorm_four hK hS ha
  have hd := norm_fderiv_phaseMixedKernel_le_cNorm_four hK hS ha
  calc
    _ ≤ ‖phaseMixedKernel S (g a)‖ * ‖fderiv ℝ v a‖ +
        (‖fderiv ℝ (phaseMixedKernel S) (g a)‖ * ‖fderiv ℝ g a‖) * ‖v a‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
      exact (((fderiv ℝ (phaseMixedKernel S) (g a)).comp
        (fderiv ℝ g a)).flip.le_opNorm (v a)).trans (by
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ cNorm K 4 S * ‖fderiv ℝ v a‖ +
        (cNorm K 4 S * ‖fderiv ℝ g a‖) * ‖v a‖ := by gcongr
    _ = _ := by ring

end JanetCartan.FullPhaseCharts.Comparison
