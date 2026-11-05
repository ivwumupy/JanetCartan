module

public import JanetCartan.Analysis.Microlocal.SingleChannel
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex Frobenius components of the physical raw slice

Upgrade the existing `matrixChannelComponents` and its exact norm identity to
complex linear isometry equivalences, pointwise and in L². The consumer is the
physical matrix-valued output of `app:ch_waves:eq:individual-raw-slice` obtained
from `exists_rawSliceBandOperator`. Both real quadratures are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.SingleChannel

/-- The existing Frobenius flattening is a complex linear isometry equivalence,
including its actual inverse (`app:ch_waves:setup:oscillatory`). -/
def matrixChannelEquiv (m n : ℕ) :
    Matrix (Fin m) (Fin n) ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m * n)) where
  toFun := matrixChannelComponents
  invFun v i j := v (finProdFinEquiv (i, j))
  left_inv A := by
    ext i j
    change A (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = A i j
    rw [Equiv.symm_apply_apply]
  right_inv v := by
    apply PiLp.ext
    intro k
    change v (finProdFinEquiv (finProdFinEquiv.symm k)) = v k
    rw [Equiv.apply_symm_apply]
  map_add' A B := by ext k; rfl
  map_smul' c A := by ext k; rfl
  norm_map' := norm_matrixChannelComponents

/-- The equivalence uses precisely the previously published components
(`app:ch_waves:setup:oscillatory`). -/
@[simp] theorem matrixChannelEquiv_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    matrixChannelEquiv m n A = matrixChannelComponents A := rfl

/-- Reassembling a component restores the original complex matrix entry,
with both its real and imaginary parts (`app:ch_waves:setup:oscillatory`). -/
@[simp] theorem matrixChannelEquiv_symm_apply {m n : ℕ}
    (v : EuclideanSpace ℂ (Fin (m * n))) (i : Fin m) (j : Fin n) :
    (matrixChannelEquiv m n).symm v i j = v (finProdFinEquiv (i, j)) := rfl

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Actual L² realization of Frobenius flattening on the given measure,
for `app:ch_waves:eq:individual-raw-slice`. -/
def matrixChannelL2Equiv (m n : ℕ) :
    Lp (Matrix (Fin m) (Fin n) ℂ) 2 μ ≃ₗᵢ[ℂ]
      Lp (EuclideanSpace ℂ (Fin (m * n))) 2 μ where
  __ := (matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ 2 μ
  invFun := (matrixChannelEquiv m n).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
  left_inv f := by
    apply Lp.ext
    filter_upwards [
      (matrixChannelEquiv m n).symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
        ((matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
      (matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f]
      with x hx hy
    dsimp only [ContinuousLinearMap.compLpₗ] at *
    simp only [hx, hy, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  right_inv f := by
    apply Lp.ext
    filter_upwards [
      (matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
        ((matrixChannelEquiv m n).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f),
      (matrixChannelEquiv m n).symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f]
      with x hx hy
    dsimp only [ContinuousLinearMap.compLpₗ] at *
    simp only [hx, hy, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
  norm_map' f := by
    change ‖(matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.compLp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable f)
    filter_upwards [
      (matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f]
      with x hx
    rw [hx]
    exact (matrixChannelEquiv m n).norm_map _

/-- Forward L² representative, on the original measure
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem matrixChannelL2Equiv_coeFn {m n : ℕ} (f : Lp (Matrix (Fin m) (Fin n) ℂ) 2 μ) :
    matrixChannelL2Equiv μ m n f =ᵐ[μ] fun x ↦ matrixChannelComponents (f x) :=
  (matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

/-- Reverse L² representative, retaining all complex entries
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem matrixChannelL2Equiv_symm_coeFn {m n : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin (m * n))) 2 μ) :
    (matrixChannelL2Equiv μ m n).symm f =ᵐ[μ]
      fun x ↦ (matrixChannelEquiv m n).symm (f x) :=
  (matrixChannelEquiv m n).symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

/-- Flattening commutes with the literal Bochner integral, including its
nonintegrable convention (`app:ch_waves:setup:oscillatory`). -/
theorem integral_matrixChannelComponents {m n : ℕ} (f : α → Matrix (Fin m) (Fin n) ℂ) :
    ∫ x, matrixChannelComponents (f x) ∂μ = matrixChannelComponents (∫ x, f x ∂μ) :=
  (matrixChannelEquiv m n).toLinearIsometry.integral_comp_comm f

/-- Reassembly commutes with the same integral; the oscillatory integral in
`app:ch_waves:eq:individual-raw-slice` is unchanged. -/
theorem integral_matrixChannelEquiv_symm {m n : ℕ}
    (f : α → EuclideanSpace ℂ (Fin (m * n))) :
    ∫ x, (matrixChannelEquiv m n).symm (f x) ∂μ =
      (matrixChannelEquiv m n).symm (∫ x, f x ∂μ) :=
  (matrixChannelEquiv m n).symm.toLinearIsometry.integral_comp_comm f

end JanetCartan.SingleChannel
