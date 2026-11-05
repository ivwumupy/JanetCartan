module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol.Basic
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Flow
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Differentiating the normalized determinant

The differential and both gradients in Step 1 of
`app:ch_seed:prop:seed-actual-menu`. The gradients below are obtained from the
actual Fréchet derivative by the Riesz map, using the existing Euclidean space.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.NormalizedSymbol

variable {n : ℕ}

/-- Physical part of a scalar phase-space differential, used for the literal
Hamilton symbols in `app:ch_seed:prop:seed-actual-menu`, Step 1. -/
def physicalGradient (h : Euclidean n × Euclidean n → ℝ)
    (z : Euclidean n × Euclidean n) : Euclidean n :=
  (InnerProductSpace.toDual ℝ (Euclidean n)).symm
    ((fderiv ℝ h z).comp (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean n)))

/-- Covector part of a scalar phase-space differential, used for the literal
Hamilton symbols in `app:ch_seed:prop:seed-actual-menu`, Step 1. -/
def covectorGradient (h : Euclidean n × Euclidean n → ℝ)
    (z : Euclidean n × Euclidean n) : Euclidean n :=
  (InnerProductSpace.toDual ℝ (Euclidean n)).symm
    ((fderiv ℝ h z).comp (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n)))

/-- The physical component really is the gradient in physical variables
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem physicalGradient_eq_gradient {h : Euclidean n × Euclidean n → ℝ}
    {z : Euclidean n × Euclidean n} (hd : DifferentiableAt ℝ h z) :
    physicalGradient h z = gradient (fun x ↦ h (x, z.2)) z.1 := by
  have hh := hd.hasFDerivAt.comp z.1
    ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk (hasFDerivAt_const z.2 z.1))
  simp only [Function.comp_def, id_eq] at hh
  rw [gradient, hh.fderiv]
  rfl

/-- The covector component really is the gradient in covector variables
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem covectorGradient_eq_gradient {h : Euclidean n × Euclidean n → ℝ}
    {z : Euclidean n × Euclidean n} (hd : DifferentiableAt ℝ h z) :
    covectorGradient h z = gradient (fun ξ ↦ h (z.1, ξ)) z.2 := by
  have hh := hd.hasFDerivAt.comp z.2
    ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) z.2))
  simp only [Function.comp_def, id_eq] at hh
  rw [gradient, hh.fderiv]
  rfl

/-- Reassembling the two true gradients gives the full Hamilton differential
(`app:lem:common-hamilton-phase`). -/
theorem hamiltonDifferential_eq_fderiv (h : Euclidean n × Euclidean n → ℝ)
    (z : Euclidean n × Euclidean n) :
    HamiltonPhase.hamiltonDifferential (physicalGradient h z) (covectorGradient h z) =
      fderiv ℝ h z := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [HamiltonPhase.hamiltonDifferential_apply, physicalGradient, covectorGradient,
    ← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp

/-- Smoothness of the covector gradient follows by differentiating the scalar
symbol (`app:lem:common-hamilton-phase`); no gradient regularity is assumed. -/
theorem contDiffAt_covectorGradient {h : Euclidean n × Euclidean n → ℝ}
    {z : Euclidean n × Euclidean n} (hh : ContDiffAt ℝ ∞ h z) :
    ContDiffAt ℝ ∞ (covectorGradient h) z := by
  exact (InnerProductSpace.toDual ℝ (Euclidean n)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
    ((hh.fderiv_right (by simp)).clm_comp contDiffAt_const)

/-- On the characteristic set, the full differential is multiplied by the
normalization factor (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem fderiv_normalizedSymbol_of_determinant_eq_zero
    {Q : Euclidean n → Fin n → MetricTensor n} {z : Euclidean n × Euclidean n}
    (hQ : ContDiffAt ℝ ∞ Q z.1) (hξ : z.2 ≠ 0) (hp : determinant (Q z.1) z.2 = 0) :
    fderiv ℝ (normalizedSymbol Q) z = determinantNormalization z.2 •
      fderiv ℝ (fun w : Euclidean n × Euclidean n ↦ determinant (Q w.1) w.2) z := by
  have hd := (contDiff_determinant.contDiffAt.comp z
    ((hQ.comp z contDiffAt_fst).prodMk contDiffAt_snd)).differentiableAt (by simp)
  have hw := ((contDiffAt_determinantNormalization hξ).comp z contDiffAt_snd).differentiableAt
    (by simp)
  change fderiv ℝ ((fun w : Euclidean n × Euclidean n ↦ determinant (Q w.1) w.2) *
    (fun w ↦ determinantNormalization w.2)) z = _
  simp only [Function.comp_def] at hd hw
  rw [fderiv_mul hd hw]
  simp [hp]

/-- The exact physical-gradient identity on the characteristic set
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem physicalGradient_normalizedSymbol_of_determinant_eq_zero
    {Q : Euclidean n → Fin n → MetricTensor n} {z : Euclidean n × Euclidean n}
    (hQ : ContDiffAt ℝ ∞ Q z.1) (hξ : z.2 ≠ 0) (hp : determinant (Q z.1) z.2 = 0) :
    physicalGradient (normalizedSymbol Q) z = determinantNormalization z.2 •
      physicalGradient (fun w ↦ determinant (Q w.1) w.2) z := by
  simp [physicalGradient, fderiv_normalizedSymbol_of_determinant_eq_zero hQ hξ hp,
    ContinuousLinearMap.smul_comp]

/-- The exact covector-gradient identity on the characteristic set
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem covectorGradient_normalizedSymbol_of_determinant_eq_zero
    {Q : Euclidean n → Fin n → MetricTensor n} {z : Euclidean n × Euclidean n}
    (hQ : ContDiffAt ℝ ∞ Q z.1) (hξ : z.2 ≠ 0) (hp : determinant (Q z.1) z.2 = 0) :
    covectorGradient (normalizedSymbol Q) z = determinantNormalization z.2 •
      covectorGradient (fun w ↦ determinant (Q w.1) w.2) z := by
  simp [covectorGradient, fderiv_normalizedSymbol_of_determinant_eq_zero hQ hξ hp,
    ContinuousLinearMap.smul_comp]

end JanetCartan.ActualCarriers.NormalizedSymbol
