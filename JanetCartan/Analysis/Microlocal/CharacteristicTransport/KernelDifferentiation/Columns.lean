module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.CompactOperator

/-!
# Columnwise cancellation for an oscillatory matrix kernel

The input weights are fixed while differentiating the output in
`app:ch_regular_base:eq:two-term-null-identity`. Each column identity is
supplied by `RegularSector.Characteristic.firstOrder_directCorrection_identity`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open WKB
variable {n q : ℕ}
local notation "FV" => Fin q → ℂ

/-- Pointwise column cancellations imply cancellation on the original matrix
input, with its unchanged spectral weights. This is the finite sum used before
frequency integration in `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem firstOrderApply_oscillatory_mulVec_of_columns (C : Euclidean n → Fin n → FV →ₗ[ℂ] FV)
    (D : Euclidean n → FV →ₗ[ℂ] FV) {φ : Euclidean n → ℝ}
    {b : Euclidean n → Matrix (Fin q) (Fin q) ℂ} (r : Matrix (Fin q) (Fin q) ℂ)
    {x : Euclidean n} (hφ : DifferentiableAt ℝ φ x)
    (hb : ∀ j, DifferentiableAt ℝ (fun y i ↦ b y i j) x)
    (hcancel : ∀ j, firstOrderApply C D
      (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) • (fun i ↦ b y i j)) x =
        Complex.exp (Complex.I * (φ x : ℂ)) • (fun i ↦ r i j)) (u : FV) :
    firstOrderApply C D (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) • (b y).mulVec u) x =
      Complex.exp (Complex.I * (φ x : ℂ)) • r.mulVec u := by
  have hd (j) : DifferentiableAt ℝ
      (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) • (fun i ↦ b y i j)) x :=
    ((differentiableAt_const Complex.I).mul
      (Complex.ofRealCLM.differentiableAt.comp x hφ)).cexp.smul (hb j)
  have he : (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) • (b y).mulVec u) =
      fun y ↦ ∑ j, u j • (Complex.exp (Complex.I * (φ y : ℂ)) • (fun i ↦ b y i j)) := by
    funext y i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.sum_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hsum := firstOrderApply_sum_columns C D (fun j ↦ (hd j).const_smul (u j))
  simp only [Pi.smul_apply] at hsum
  rw [hsum]
  have hc (j : Fin q) : firstOrderApply C D
      (fun y ↦ u j • (Complex.exp (Complex.I * (φ y : ℂ)) • (fun i ↦ b y i j))) x =
      u j • (Complex.exp (Complex.I * (φ x : ℂ)) • (fun i ↦ r i j)) := by
    exact (firstOrderApply_const_smul C D (hd j) (u j)).trans (congrArg (u j • ·) (hcancel j))
  trans ∑ j, u j • (Complex.exp (Complex.I * (φ x : ℂ)) • (fun i ↦ r i j))
  · apply Finset.sum_congr rfl
    intro j _
    exact hc j
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.sum_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
open RegularSector.Characteristic

/-- The actual direct-correction producer gives the matrix identity before
integration. Freeze source time and covector when instantiating `φ` and `a`.
The right side is literally the matrix with columns `P W₁`, with no integrated
cancellation premise (`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem firstOrderApply_directCorrection_mulVec {C : Euclidean n → Fin n → FV →L[ℂ] FV}
    {D B : Euclidean n → FV →L[ℂ] FV} {φ : Euclidean n → ℝ}
    {a : Fin q → Euclidean n → FV} {x : Euclidean n}
    (hC : ∀ i, DifferentiableAt ℝ (fun y ↦ C y i) x)
    (hD : DifferentiableAt ℝ D x) (hB : DifferentiableAt ℝ B x)
    (hφ : DifferentiableAt ℝ φ x) (ha : ∀ j, ContDiffAt ℝ 2 (a j) x)
    (proj : FV →ₗ[ℂ] FV)
    (hnull : ∀ j, principalSymbol (fun y i ↦ (C y i).toLinearMap) φ x (a j x) = 0)
    (hcomplement : ∀ v, principalSymbol (fun y i ↦ (C y i).toLinearMap) φ x (B x v) =
      v - proj v)
    (hrow : ∀ j, proj (firstOrderApply (fun y i ↦ (C y i).toLinearMap)
      (fun y ↦ (D y).toLinearMap) (a j) x) = 0) (u : FV) :
    firstOrderApply (fun y i ↦ (C y i).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) •
        Matrix.mulVec (fun i j ↦ (a j y + directCorrection C D B (a j) y) i) u) x =
      Complex.exp (Complex.I * (φ x : ℂ)) •
        Matrix.mulVec (fun i j ↦ (firstOrderApply (fun y k ↦ (C y k).toLinearMap)
          (fun y ↦ (D y).toLinearMap) (directCorrection C D B (a j)) x) i) u := by
  apply firstOrderApply_oscillatory_mulVec_of_columns _ _ _ hφ
  · intro j
    exact ((ha j).differentiableAt (by norm_num)).add
      (differentiableAt_directCorrection hC hD hB (ha j))
  · intro j
    exact firstOrder_directCorrection_identity hC hD hB hφ (ha j) proj
      (hnull j) hcomplement (hrow j)

end JanetCartan.CharacteristicTransport.KernelDifferentiation
