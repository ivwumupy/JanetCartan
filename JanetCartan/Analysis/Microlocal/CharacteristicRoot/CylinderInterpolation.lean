module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.LocalInterpolation
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Interpolation on characteristic cylinders

The rectangular cylinder in `app:ch_regular_base:lem:buffered-interpolation` is
an affine image of the unit ball for the product norm. Comparing ambient
iterated derivative seminorms under this fixed change of coordinates transfers
`app:lem:elementary-interpolation-jets` from the ball to the cylinder.

The resulting uniform baseline-one profiles are the missing interpolation input
for `exists_root_cNorm_bound_of_equation_profile`. All comparison constants are
chosen before the equation; smoothness is required only on its given open
neighborhood of the cylinder.
-/

@[expose] public noncomputable section

open scoped ContDiff
open Set Metric

namespace JanetCartan.CharacteristicRoot

variable {D E F P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- `app:lem:elementary-interpolation-jets`: the affine pullback comparison used
in both directions by the cylinder interpolation theorem. The ambient derivatives
are computed using the open neighborhood, including at the compact set's boundary. -/
private theorem cNorm_preAffine_le {s : Set D} {t U : Set E} (ht : IsCompact t)
    (hU : IsOpen U) (htU : t ⊆ U) {n k : ℕ} (hkn : k ≤ n)
    (L : D →L[ℝ] E) (b : E) {C : ℝ} (hC : 1 ≤ C) (hLC : ‖L‖ ≤ C)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hst : MapsTo (fun x ↦ L x + b) s t) :
    cNorm s k (fun x ↦ f (L x + b)) ≤ C ^ n * cNorm t k f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hC) _)
      (sSup_norm_iteratedFDeriv_nonneg t j f))
  intro j hj x hx
  let V := (fun y : E ↦ y + b) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ ∞ (fun y ↦ f (y + b)) V :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hy ↦ hy)
  have hpre : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hxV : L x ∈ V := htU (hst hx)
  have heq := L.iteratedFDerivWithin_comp_right hg hV.uniqueDiffOn hpre.uniqueDiffOn
    hxV (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hxV,
    iteratedFDerivWithin_of_isOpen _ hV hxV, iteratedFDeriv_comp_add_right] at heq
  change ‖iteratedFDeriv ℝ j ((fun y ↦ f (y + b)) ∘ L) x‖ ≤ _
  rw [heq]
  apply ((iteratedFDeriv ℝ j f (L x + b)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hb := le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt ht
    (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (htU hy))).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) hj)
    (mem_image_of_mem _ (hst hx))
  have hc : ‖L‖ ^ j ≤ C ^ n := (pow_le_pow_left₀ (norm_nonneg _) hLC j).trans
    (pow_le_pow_right₀ hC (hj.trans hkn))
  exact (mul_le_mul hb hc (pow_nonneg (norm_nonneg _) _)
    (sSup_norm_iteratedFDeriv_nonneg t j f)).trans_eq (mul_comm _ _)

/-- `app:ch_regular_base:lem:buffered-interpolation`: the invertible linear part
of the fixed unit-ball parametrization of the characteristic cylinder. -/
private def cylinderScale (r a : ℝ) (hr : 0 < r) (ha : 0 < a) :
    (P × ℝ) ≃L[ℝ] P × ℝ :=
  ((Units.mk0 (2 * r) (by positivity)) • ContinuousLinearEquiv.refl ℝ P).prodCongr
    ((Units.mk0 a ha.ne') • ContinuousLinearEquiv.refl ℝ ℝ)

/-- `app:ch_regular_base:lem:buffered-interpolation`: the translated rescaling
identifies precisely the product-norm unit ball and the working cylinder. -/
private theorem cylinderScale_mem_iff (p₀ : P) (τ₀ : ℝ) {r a : ℝ}
    (hr : 0 < r) (ha : 0 < a) (x : P × ℝ) :
    cylinderScale r a hr ha x + (p₀, τ₀) ∈
      closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a) ↔ x ∈ closedBall 0 1 := by
  have hr' : 0 < 2 * r := by positivity
  simp only [cylinderScale, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.smul_apply, Units.val_mk0, ContinuousLinearEquiv.refl_apply,
    Prod.mk_add_mk, mem_prod, mem_closedBall, dist_eq_norm, add_sub_cancel_right,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr', mem_Icc, smul_eq_mul,
    sub_zero, Prod.norm_def, max_le_iff]
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    constructor
    · nlinarith
    · rw [abs_le]
      constructor <;> nlinarith
  · rintro ⟨hp, ht⟩
    rcases abs_le.mp ht with ⟨hlo, hhi⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩


/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:elementary-interpolation-jets`: baseline-one interpolation on the actual
rectangular characteristic cylinder. The constant is chosen before the function
and controls every order from one through `n`. This supplies the equation profiles
for `exists_root_cNorm_bound_of_equation_profile`. -/
theorem exists_uniform_cNorm_baseline_one_profile_cylinder_on
    [FiniteDimensional ℝ P] (p₀ : P) (τ₀ : ℝ) {r a : ℝ}
    (hr : 0 < r) (ha : 0 < a) {W : Set (P × ℝ)} (hW : IsOpen W)
    (hKW : closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a) ⊆ W)
    {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ f : P × ℝ → ℝ, ContDiffOn ℝ ∞ f W →
      cNorm (closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) 1 f ≤ M →
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
      cNorm (closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) j f ≤
        B * (1 + cNorm (closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) n f) ^
          (((j : ℝ) - 1) / ((n : ℝ) - 1)) := by
  let K := closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  let S : Set (P × ℝ) := closedBall 0 1
  let L : (P × ℝ) ≃L[ℝ] P × ℝ := cylinderScale r a hr ha
  let b : P × ℝ := (p₀, τ₀)
  let φ : P × ℝ → P × ℝ := fun x ↦ L x + b
  let ψ : P × ℝ → P × ℝ := fun y ↦ L.symm y + -(L.symm b)
  have hφψ (y : P × ℝ) : φ (ψ y) = y := by simp [φ, ψ]
  have hφ : ContDiff ℝ ∞ φ := L.contDiff.add contDiff_const
  have hφmem (x : P × ℝ) : φ x ∈ K ↔ x ∈ S :=
    cylinderScale_mem_iff p₀ τ₀ hr ha x
  have hφmap : MapsTo φ S K := fun x hx ↦ (hφmem x).mpr hx
  have hψmap : MapsTo ψ K S := by
    intro y hy
    apply (hφmem (ψ y)).mp
    simpa only [hφψ] using hy
  let U := φ ⁻¹' W
  have hU : IsOpen U := hW.preimage hφ.continuous
  have hSU : S ⊆ U := fun x hx ↦ hKW (hφmap hx)
  have hK : IsCompact K := (isCompact_closedBall p₀ (2 * r)).prod isCompact_Icc
  let C₀ : ℝ := max 1 ‖(L : (P × ℝ) →L[ℝ] P × ℝ)‖
  let D₀ : ℝ := max 1 ‖(L.symm : (P × ℝ) →L[ℝ] P × ℝ)‖
  let C := C₀ ^ n
  let D := D₀ ^ n
  have hC₀ : 1 ≤ C₀ := le_max_left _ _
  have hD₀ : 1 ≤ D₀ := le_max_left _ _
  have hC : 1 ≤ C := one_le_pow₀ hC₀
  have hD : 1 ≤ D := one_le_pow₀ hD₀
  obtain ⟨A, hA, hprofile⟩ :=
    FlowForcing.exists_uniform_cNorm_baseline_one_profile_closedBall_on
      (F := ℝ) (0 : P × ℝ) (by norm_num : (0 : ℝ) < 1) hU hSU hn
      (mul_nonneg (zero_le_one.trans hC) hM)
  refine ⟨D * A * C, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hD hA) hC
  intro f hf hfM j hj hjn
  let g := f ∘ φ
  have hg : ContDiffOn ℝ ∞ g U := hf.comp hφ.contDiffOn (fun _ hx ↦ hx)
  have hforward (k : ℕ) (hkn : k ≤ n) : cNorm S k g ≤ C * cNorm K k f :=
    cNorm_preAffine_le hK hW hKW hkn L.toContinuousLinearMap b hC₀ (le_max_right _ _)
      hf hφmap
  have hreverse (k : ℕ) (hkn : k ≤ n) : cNorm K k f ≤ D * cNorm S k g := by
    have h := cNorm_preAffine_le (isCompact_closedBall (0 : P × ℝ) 1) hU hSU hkn
      L.symm.toContinuousLinearMap (-(L.symm b)) hD₀ (le_max_right _ _) hg hψmap
    have heq : (fun y ↦ g (L.symm y + -(L.symm b))) = f := by
      funext y
      exact congrArg f (hφψ y)
    simpa only [ContinuousLinearEquiv.coe_coe, heq] using h
  have hgM : cNorm S 1 g ≤ C * M := (hforward 1 (by omega)).trans
    (mul_le_mul_of_nonneg_left hfM (zero_le_one.trans hC))
  have hi := hprofile g hg hgM j hj hjn
  have hn' : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let θ : ℝ := ((j : ℝ) - 1) / ((n : ℝ) - 1)
  have hθ0 : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (by exact_mod_cast hj)) hn'.le
  have hθ1 : θ ≤ 1 := (div_le_one hn').mpr
    (sub_le_sub_right (by exact_mod_cast hjn) 1)
  have hhigh : 1 + cNorm S n g ≤ C * (1 + cNorm K n f) := by
    have := hforward n le_rfl
    nlinarith
  have hpow : (1 + cNorm S n g) ^ θ ≤ C * (1 + cNorm K n f) ^ θ := by
    calc
      _ ≤ (C * (1 + cNorm K n f)) ^ θ :=
        Real.rpow_le_rpow (by linarith [cNorm_nonneg S n g]) hhigh hθ0
      _ = C ^ θ * (1 + cNorm K n f) ^ θ :=
        Real.mul_rpow (zero_le_one.trans hC) (by linarith [cNorm_nonneg K n f])
      _ ≤ C * (1 + cNorm K n f) ^ θ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg
          (by linarith [cNorm_nonneg K n f]) _)
        exact (Real.rpow_le_rpow_of_exponent_le hC hθ1).trans_eq (Real.rpow_one C)
  calc
    cNorm K j f ≤ D * cNorm S j g := hreverse j hjn
    _ ≤ D * (A * (1 + cNorm S n g) ^ θ) :=
      mul_le_mul_of_nonneg_left hi (zero_le_one.trans hD)
    _ ≤ D * (A * (C * (1 + cNorm K n f) ^ θ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hA))
        (zero_le_one.trans hD)
    _ = (D * A * C) * (1 + cNorm K n f) ^ θ := by ring

end JanetCartan.CharacteristicRoot
