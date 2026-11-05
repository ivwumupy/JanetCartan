module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Factorization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.KernelBound
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.Real

/-!
# Bounded realization of the fixed source-square kernel

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the published real
tail operator realizes the exact fixed source-square kernel. Its quadratic
form is the double integral on every real L² input. The separate compact-test
energy identity must still identify this form with the channel energy defect.
Consumer: `fixedEuclideanChannel_energy_defect_eq_kernel`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- The actual bounded real tail, with the original source square and auxiliary
endpoint cutoff (`app:ch_background:prop:bg-frame`). Its realization is supplied
by the already proved separated Bessel kernel calculus. -/
def fixedSourceTailOperator (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : R² →L[ℝ] R² :=
  realCoefficientSourceCommutatorTailOperator
    (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
    (FixedCutoffs.physical hR 0) (fixedSourceSquare hR)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport
    (FixedCutoffs.physical hR 0).contDiff (contDiff_fixedSourceSquare hR)
    (hasCompactSupport_fixedSourceSquare hR) hR (fixedSourceSquare_plateau hR)

/-- Coordinate action of the fixed source-square matrix kernel
(`app:ch_background:prop:bg-frame`). -/
theorem fixedSourceTailKernel_apply (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (p : E × E) (v : E) (i : Fin n) :
    fixedSourceTailKernel hR A p v i =
      ∑ j, frozenSourceTailMatrixKernel A (FixedCutoffs.physical hR 0)
        (FixedCutoffs.physical hR 0) (fixedSourceSquare hR) p i j * v j := rfl

private theorem integrable_fixedSourceTailEntry_mul_coordinate (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (x : E) (i j : Fin n) :
    Integrable (fun y ↦ frozenSourceTailMatrixKernel A (FixedCutoffs.physical hR 0)
      (FixedCutoffs.physical hR 0) (fixedSourceSquare hR) (x, y) i j * u y j) := by
  let K : E × E → ℝ := fun p ↦ frozenSourceTailMatrixKernel A
    (FixedCutoffs.physical hR 0) (FixedCutoffs.physical hR 0) (fixedSourceSquare hR) p i j
  have hc : Continuous K :=
    (contDiff_coefficientSourceCommutatorTailKernel
      (fun _ ↦ A) (fun _ ↦ 0) _ _ _
      (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
      (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport
      (FixedCutoffs.physical hR 0).contDiff (contDiff_fixedSourceSquare hR)
      (hasCompactSupport_fixedSourceSquare hR) hR (fixedSourceSquare_plateau hR) i j).continuous
  have hs : HasCompactSupport K :=
    hasCompactSupport_coefficientSourceCommutatorTailKernel
      (fun _ ↦ A) (fun _ ↦ 0) _ _ _
      (FixedCutoffs.physical hR 0).hasCompactSupport
      (hasCompactSupport_fixedSourceSquare hR) i j
  have hsection : HasCompactSupport (fun y ↦ K (x, y)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_snd)
    intro y hy
    exact ⟨(x, y), subset_tsupport K hy, rfl⟩
  exact ((Lp.memLp u).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
    |>.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (hc.comp (continuous_const.prodMk continuous_id)) hsection

/-- Absolute convergence of each vector section against arbitrary real L²
data, needed to identify the source-tail quadratic form
(`app:ch_background:prop:bg-frame`). -/
theorem integrable_fixedSourceTailKernel_apply (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) (x : E) :
    Integrable (fun y ↦ fixedSourceTailKernel hR A (x, y) (u y)) := by
  apply integrable_piLp_iff.mpr
  intro i
  change Integrable (fun y ↦ fixedSourceTailKernel hR A (x, y) (u y) i)
  simp only [fixedSourceTailKernel_apply]
  exact integrable_finsetSum Finset.univ fun j _ ↦
    integrable_fixedSourceTailEntry_mul_coordinate hR A u x i j

/-- Literal Bochner kernel action of the fixed tail on every real L² input
(`app:ch_background:prop:bg-frame`). -/
theorem fixedSourceTailOperator_ae_integral (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    fixedSourceTailOperator hR A u =ᵐ[volume]
      fun x ↦ ∫ y, fixedSourceTailKernel hR A (x, y) (u y) := by
  filter_upwards [realCoefficientSourceCommutatorTailOperator_ae_integral
    (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
    (FixedCutoffs.physical hR 0) (fixedSourceSquare hR)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport
    (FixedCutoffs.physical hR 0).contDiff (contDiff_fixedSourceSquare hR)
    (hasCompactSupport_fixedSourceSquare hR) hR (fixedSourceSquare_plateau hR) u]
      with x hx
  change fixedSourceTailOperator hR A u x = _ at hx
  rw [hx]
  ext i
  have he := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (integrable_fixedSourceTailKernel_apply hR A u x)
  change (∫ y, fixedSourceTailKernel hR A (x, y) (u y) i) =
    (∫ y, fixedSourceTailKernel hR A (x, y) (u y)) i at he
  rw [← he]
  simp only [fixedSourceTailKernel_apply]
  exact (integral_finsetSum Finset.univ fun j _ ↦
    integrable_fixedSourceTailEntry_mul_coordinate hR A u x i j).symm

/-- The source-tail quadratic form equals its literal double-kernel energy.
The channel-energy identification remains the separate compact-test and
density obligation (`app:ch_background:prop:bg-frame`). -/
theorem fixedSourceTailOperator_inner_eq_integral (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    ⟪u, fixedSourceTailOperator hR A u⟫ =
      ∫ x, ∫ y, ⟪u x, fixedSourceTailKernel hR A (x, y) (u y)⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fixedSourceTailOperator_ae_integral hR A u] with x hx
  rw [hx]
  exact (integral_inner (integrable_fixedSourceTailKernel_apply hR A u x) (u x)).symm

end JanetCartan.ContinuumNormal.FrozenImageComparison
