module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Hermitian
public import JanetCartan.Iteration.PhysicalSmoothing.Basic

/-!
# The fixed-sample real source iteration of paper-v2

This is the literal recurrence `app:ch_mean_pairs:eq:single-iteration`, not
`MeanRecurrence.run`: its sample, derivative operator, input cutoff and inverse
are fixed before the number of Picard steps.  The quadratic map is constructed
from the complete weighted Hermitian tensor.  The exact residual identity is
consumed by the physical normal completion and `RevisedStage`.

This algebraic construction does not assert the original-data bounds for the
sampled normal operator or canonical derivative operator.  Those must still be
proved for the same prescribed inverse and the same sampled physical waves.
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalMean

open CurrentMean

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

/-- `app:ch_mean_pairs:eq:single-iteration`: a single fixed-source Picard run.
Neither the sample nor its cutoff or normal inverse depends on the step. -/
def sourceIterate (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y) (g : Y) : ℕ → Y
  | 0 => 0
  | j + 1 => g + (sourceIterate E Q g j - E (sourceIterate E Q g j)) -
      Q (sourceIterate E Q g j) (sourceIterate E Q g j)

/-- `main:eq:full-recursion`: the literal quadratic equation residual. -/
def sourceResidual (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y) (g r : Y) : Y :=
  g - E r - Q r r

/-- The residual is the next Picard difference, so no successful source is
postulated (`new:eq:difference-equation`). -/
theorem sourceResidual_eq_difference
    (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y) (g : Y) (j : ℕ) :
    sourceResidual E Q g (sourceIterate E Q g j) =
      sourceIterate E Q g (j + 1) - sourceIterate E Q g j := by
  simp only [sourceResidual, sourceIterate]
  abel

/-- `new:eq:Q-difference`: the symmetric quadratic difference identity. -/
theorem symmetric_quadratic_difference
    (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y) (hQ : ∀ u v, Q u v = Q v u) (u v : Y) :
    Q u u - Q v v = Q (u - v) (u + v) := by
  simp only [map_sub, map_add, LinearMap.sub_apply]
  rw [hQ v u]
  abel

/-- `new:eq:difference-equation`: the exact difference recurrence for the
same fixed sampled operators; no estimate or contraction is assumed. -/
theorem sourceIterate_difference_succ
    (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y)
    (hQ : ∀ u v, Q u v = Q v u) (g : Y) (j : ℕ) :
    sourceIterate E Q g (j + 2) - sourceIterate E Q g (j + 1) =
      (sourceIterate E Q g (j + 1) - sourceIterate E Q g j) -
        E (sourceIterate E Q g (j + 1) - sourceIterate E Q g j) -
      Q (sourceIterate E Q g (j + 1) - sourceIterate E Q g j)
        (sourceIterate E Q g (j + 1) + sourceIterate E Q g j) := by
  rw [← symmetric_quadratic_difference Q hQ, map_sub]
  conv_lhs => lhs; rw [show j + 2 = (j + 1) + 1 by omega, sourceIterate]
  conv_lhs => rhs; rw [sourceIterate]
  abel

variable {Ω ι m n : Type*} [Fintype ι] [Fintype m]

/-- `new:eq:mean-operators`: the actual complete Hermitian bilinear source,
formed with the fixed sample weights, fixed measurement and fixed canonical
derivative map.  No principal approximation or inverse sample weight occurs. -/
def sampledSourceQuadratic (μ : ι → ℝ)
    (C : (Ω → Matrix n n ℝ) →ₗ[ℝ] Y)
    (D : Y →ₗ[ℝ] (Ω → ι → Matrix m n ℂ)) : Y →ₗ[ℝ] Y →ₗ[ℝ] Y :=
  LinearMap.mk₂ ℝ (fun u v ↦ C (weightedHermitianBilinear μ (D u) (D v)))
    (fun u v w ↦ by simp only [map_add, LinearMap.add_apply])
    (fun c u v ↦ by simp only [map_smul, LinearMap.smul_apply])
    (fun u v w ↦ by simp only [map_add])
    (fun c u v ↦ by simp only [map_smul])

/-- The same physical Hermitian polarization is symmetric
(`new:eq:Q-difference`). -/
theorem sampledSourceQuadratic_comm (μ : ι → ℝ)
    (C : (Ω → Matrix n n ℝ) →ₗ[ℝ] Y)
    (D : Y →ₗ[ℝ] (Ω → ι → Matrix m n ℂ)) (u v : Y) :
    sampledSourceQuadratic μ C D u v = sampledSourceQuadratic μ C D v u := by
  change C (weightedHermitianBilinear μ (D u) (D v)) =
    C (weightedHermitianBilinear μ (D v) (D u))
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T ↦ μ i • T) (mixedHermitianTensor_comm (D u x i) (D v x i))

/-- The diagonal is exactly the complete self tensor of the corrected
canonical derivative family (`new:eq:mean-operators`). -/
theorem sampledSourceQuadratic_self (μ : ι → ℝ)
    (C : (Ω → Matrix n n ℝ) →ₗ[ℝ] Y)
    (D : Y →ₗ[ℝ] (Ω → ι → Matrix m n ℂ)) (u : Y) :
    sampledSourceQuadratic μ C D u u = C (weightedHermitianTensor μ (D u)) := by
  change C (weightedHermitianBilinear μ (D u) (D u)) = _
  rw [weightedHermitianBilinear_self]

/-- `new:eq:reduced-mean-identity`: exact source algebra for ONE canonical
input.  The linear-response identity must be instantiated by the same sampled
normal operator and prescribed inverse.  It is not a final mean estimate. -/
theorem sourceResidual_eq_weightedHermitian_defect
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (μ : ι → ℝ) (C : (Ω → Matrix n n ℝ) →ₗ[ℝ] Y)
    (L : V →ₗ[ℝ] (Ω → Matrix n n ℝ)) (A : Y →ₗ[ℝ] V)
    (D : Y →ₗ[ℝ] (Ω → ι → Matrix m n ℂ)) (E : Y →ₗ[ℝ] Y)
    (base : Ω → ι → Matrix m n ℂ) (Vbase : V) (target : Ω → Matrix n n ℝ)
    (hlinear : ∀ r, E r = C (L (A r) +
      (2 : ℝ) • weightedHermitianBilinear μ base (D r))) (r : Y) :
    sourceResidual E (sampledSourceQuadratic μ C D)
      (C (target - L Vbase - weightedHermitianTensor μ base)) r =
      C (target - L (Vbase + A r) - weightedHermitianTensor μ (base + D r)) := by
  have hself := weightedHermitianTensor_add_sub μ base (D r)
  rw [sourceResidual, hlinear, sampledSourceQuadratic_self]
  rw [show weightedHermitianTensor μ (base + D r) =
      weightedHermitianTensor μ base + (2 : ℝ) • weightedHermitianBilinear μ base (D r) +
        weightedHermitianTensor μ (D r) by
      have he := (sub_eq_iff_eq_add).mp hself
      rw [he]
      abel]
  simp only [map_add, map_sub]
  abel

/-- The actual augmented source equation is compared with physical strain
ONLY after the original plateau restriction. In particular this does not
identify the exterior-augmented global operator with physical strain away
from the source/core plateau (`new:eq:reduced-mean-identity`). The linear,
quadratic and background identities are supplied by the SAME original
sampled correction and current uncut inverse. -/
theorem sourceResidual_localized_eq_weightedHermitian_defect
    {Z V : Type*} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup V] [Module ℝ V]
    (loc : Y →ₗ[ℝ] Z) (μ : ι → ℝ) (C : (Ω → Matrix n n ℝ) →ₗ[ℝ] Z)
    (L : V →ₗ[ℝ] (Ω → Matrix n n ℝ)) (A : Y →ₗ[ℝ] V)
    (D : Y →ₗ[ℝ] (Ω → ι → Matrix m n ℂ))
    (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y)
    (base : Ω → ι → Matrix m n ℂ) (Vbase : V) (target : Ω → Matrix n n ℝ)
    (g : Y)
    (hlinear : ∀ r, loc (E r) = C (L (A r) +
      (2 : ℝ) • weightedHermitianBilinear μ base (D r)))
    (hquadratic : ∀ r, loc (Q r r) = C (weightedHermitianTensor μ (D r)))
    (hsource : loc g = C (target - L Vbase - weightedHermitianTensor μ base)) (r : Y) :
    loc (sourceResidual E Q g r) =
      C (target - L (Vbase + A r) - weightedHermitianTensor μ (base + D r)) := by
  have hself := weightedHermitianTensor_add_sub μ base (D r)
  rw [sourceResidual, map_sub, map_sub, hsource, hlinear, hquadratic]
  rw [show weightedHermitianTensor μ (base + D r) =
      weightedHermitianTensor μ base + (2 : ℝ) • weightedHermitianBilinear μ base (D r) +
        weightedHermitianTensor μ (D r) by
    have he := (sub_eq_iff_eq_add).mp hself
    rw [he]
    abel]
  simp only [map_add, map_sub]
  abel

end JanetCartan.PhysicalMean
