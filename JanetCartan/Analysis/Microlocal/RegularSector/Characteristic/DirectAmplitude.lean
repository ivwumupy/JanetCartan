module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Operator

/-!
# The direct characteristic correction amplitude

For `paper-v2.tex`, `app:ch_regular_base:eq:two-term-null-identity`, use the
physical first-order operator already defined in `WKB.Operator`. The correction
is literally `i b₋₁ P W₀`. The complement identity and the scalar transport
compatibility imply its cancellation; differentiability is obtained from the
primitive coefficients and two derivatives of the leading amplitude.

This is a pointwise differential identity, before retarded integration. The
actual two-time phase, normalized nullvectors, signed transported row and
complement symbol must still instantiate the stated primitive hypotheses.
In particular, this lemma does not assert the complete operator residual or
its Sobolev bounds and does not remove the upper retarded endpoint.
-/

@[expose] public noncomputable section

open scoped ContDiff
open JanetCartan.WKB

namespace JanetCartan.RegularSector.Characteristic

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The direct correction `W₁ = i b₋₁ P W₀` in
`app:ch_regular_base:lem:characteristic-kernel`. The map `b` is the full
complement symbol, including its oblique source projection. -/
def directCorrection (C : Euclidean n → Fin n → F →L[ℂ] F)
    (D b : Euclidean n → F →L[ℂ] F) (a : Euclidean n → F)
    (x : Euclidean n) : F :=
  Complex.I • b x (firstOrderApply (fun y j ↦ (C y j).toLinearMap)
    (fun y ↦ (D y).toLinearMap) a x)

/-- Primitive differentiability of the coefficients and two derivatives of
`W₀` give differentiability of its physical first-order image. This supplies
the regularity needed to differentiate the explicit correction in
`app:ch_regular_base:eq:two-term-null-identity`. -/
theorem differentiableAt_firstOrderApply
    {C : Euclidean n → Fin n → F →L[ℂ] F} {D : Euclidean n → F →L[ℂ] F}
    {a : Euclidean n → F} {x : Euclidean n}
    (hC : ∀ j, DifferentiableAt ℝ (fun y ↦ C y j) x)
    (hD : DifferentiableAt ℝ D x) (ha : ContDiffAt ℝ 2 a x) :
    DifferentiableAt ℝ
      (firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap) a) x := by
  have hd (j : Fin n) : DifferentiableAt ℝ (fun y ↦ partialDeriv a y j) x :=
    ((ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hCr (j : Fin n) : DifferentiableAt ℝ (fun y ↦ (C y j).restrictScalars ℝ) x :=
    (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).differentiableAt.comp x (hC j)
  have hDr : DifferentiableAt ℝ (fun y ↦ (D y).restrictScalars ℝ) x :=
    (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).differentiableAt.comp x hD
  have hh := (DifferentiableAt.sum (u := Finset.univ) fun j _ ↦
    (hCr j).clm_apply (hd j)).add (hDr.clm_apply (ha.differentiableAt (by norm_num)))
  convert hh using 1
  funext y
  simp [firstOrderApply]

/-- The actual correction is differentiable from primitive data, without a
regularity premise on the corrected amplitude
(`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem differentiableAt_directCorrection
    {C : Euclidean n → Fin n → F →L[ℂ] F} {D b : Euclidean n → F →L[ℂ] F}
    {a : Euclidean n → F} {x : Euclidean n}
    (hC : ∀ j, DifferentiableAt ℝ (fun y ↦ C y j) x)
    (hD : DifferentiableAt ℝ D x) (hb : DifferentiableAt ℝ b x)
    (ha : ContDiffAt ℝ 2 a x) :
    DifferentiableAt ℝ (directCorrection C D b a) x := by
  have hbr : DifferentiableAt ℝ (fun y ↦ (b y).restrictScalars ℝ) x :=
    (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).differentiableAt.comp x hb
  exact (hbr.clm_apply (differentiableAt_firstOrderApply hC hD ha)).const_smul Complex.I

omit [IsScalarTower ℝ ℂ F] in
/-- The complement equation implies the leading/correction cancellation.
The projection is allowed to be oblique; its value on `P W₀` vanishes by
the signed row transport equation
(`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem directCorrection_cancel
    (C : Euclidean n → Fin n → F →L[ℂ] F) (D b : Euclidean n → F →L[ℂ] F)
    (φ : Euclidean n → ℝ) (a : Euclidean n → F) (x : Euclidean n)
    (proj : F →ₗ[ℂ] F)
    (hcomplement : ∀ v, principalSymbol (fun y j ↦ (C y j).toLinearMap) φ x (b x v) =
      v - proj v)
    (hrow : proj (firstOrderApply (fun y j ↦ (C y j).toLinearMap)
      (fun y ↦ (D y).toLinearMap) a x) = 0) :
    Complex.I • principalSymbol (fun y j ↦ (C y j).toLinearMap) φ x
      (directCorrection C D b a x) +
      firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap) a x = 0 := by
  simp only [directCorrection, map_smul, hcomplement, hrow, sub_zero, smul_smul,
    Complex.I_mul_I, neg_one_smul, neg_add_cancel]

/-- The exact physical identity
`P (exp(i φ) (W₀ + i b₋₁ P W₀)) = exp(i φ) P (i b₋₁ P W₀)`.
This reuses the checked wave product rule at unit physical frequency. It is
the differential cancellation in `app:ch_regular_base:eq:two-term-null-identity`,
not a graph-conjugation or bounded-operator assertion. -/
theorem firstOrder_directCorrection_identity
    {C : Euclidean n → Fin n → F →L[ℂ] F} {D b : Euclidean n → F →L[ℂ] F}
    {φ : Euclidean n → ℝ} {a : Euclidean n → F} {x : Euclidean n}
    (hC : ∀ j, DifferentiableAt ℝ (fun y ↦ C y j) x)
    (hD : DifferentiableAt ℝ D x) (hb : DifferentiableAt ℝ b x)
    (hφ : DifferentiableAt ℝ φ x) (ha : ContDiffAt ℝ 2 a x)
    (proj : F →ₗ[ℂ] F)
    (hnull : principalSymbol (fun y j ↦ (C y j).toLinearMap) φ x (a x) = 0)
    (hcomplement : ∀ v, principalSymbol (fun y j ↦ (C y j).toLinearMap) φ x (b x v) =
      v - proj v)
    (hrow : proj (firstOrderApply (fun y j ↦ (C y j).toLinearMap)
      (fun y ↦ (D y).toLinearMap) a x) = 0) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) •
        (a y + directCorrection C D b a y)) x =
      Complex.exp (Complex.I * (φ x : ℂ)) •
        firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
          (directCorrection C D b a) x := by
  have h := firstOrder_twoTermWave_residual
    (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
    (lam := 1) one_ne_zero hφ (ha.differentiableAt (by norm_num))
    (differentiableAt_directCorrection hC hD hb ha) hnull
    (directCorrection_cancel C D b φ a x proj hcomplement hrow)
  have he : twoTermWave 1 φ a (directCorrection C D b a) =
      fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) •
        (a y + directCorrection C D b a y) := by
    funext y
    simp [twoTermWave, modulatedWave, waveCarrier]
  rw [he] at h
  simpa [waveCarrier] using h

end JanetCartan.RegularSector.Characteristic
