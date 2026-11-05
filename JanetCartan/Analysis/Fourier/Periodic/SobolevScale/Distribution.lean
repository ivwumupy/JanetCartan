module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.NegativeDual

/-!
# Distributional derivatives as negative Sobolev elements

For the H⁻¹ uniqueness step in `app:ch_background:prop:bg-inverse`, transpose
the bounded derivative H¹ → L² to construct the distributional derivative
L² → H⁻¹. Smooth density identifies its L² representatives with the actual
weak derivatives defined by integration against all smooth periodic tests.
Thus negative-order equations can be used with the integer Sobolev
characterization without assuming distributional representability.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.PeriodicSobolevNegativeOne

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The distributional derivative of an L² field as a bounded H⁻¹ functional
(`app:ch_background:prop:bg-inverse`). -/
def coordinateDerivative (i : Fin n) :
    PeriodicL2 n F →L[ℝ] PeriodicSobolevNegativeOne n F :=
  -(((ContinuousLinearMap.compL ℝ (PeriodicSobolevSpace n F 1) (PeriodicL2 n F) ℝ).flip
    ((PeriodicSobolevSpace.toL2 0).comp (PeriodicSobolevSpace.coordinateDerivative 0 i))).comp
      (innerSL ℝ))

/-- The negative-order derivative is the negative transpose of differentiation
on H¹ (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem coordinateDerivative_apply (i : Fin n) (u : PeriodicL2 n F)
    (φ : PeriodicSobolevSpace n F 1) :
    coordinateDerivative i u φ =
      -inner ℝ u (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.coordinateDerivative 0 i φ)) :=
  rfl

/-- One distributional derivative maps L² boundedly to H⁻¹ with constant one
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_coordinateDerivative_le (i : Fin n) (u : PeriodicL2 n F) :
    ‖coordinateDerivative i u‖ ≤ ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro φ
  rw [coordinateDerivative_apply, norm_neg]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul_of_nonneg_left
    ((PeriodicSobolevSpace.norm_toL2_le 0 _).trans
      (PeriodicSobolevSpace.norm_coordinateDerivative_le 0 i φ)) (norm_nonneg _))

/-- The distributional derivative has operator norm at most one
(`app:ch_background:prop:bg-inverse`). -/
theorem opNorm_coordinateDerivative_le (i : Fin n) :
    ‖coordinateDerivative (F := F) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_coordinateDerivative_le i u

/-- Evaluation on every smooth test is the usual distributional integral
(`app:ch_background:prop:bg-inverse`). -/
theorem coordinateDerivative_ofSmooth (i : Fin n) (u : PeriodicL2 n F)
    (φ : Torus n → F) (hφ : IsSmoothPeriodic φ) :
    coordinateDerivative i u (PeriodicSobolevSpace.ofSmooth 1 φ hφ) =
      -(∫ x, inner ℝ (u x) (periodicCoordinateDeriv i φ x)) := by
  rw [coordinateDerivative_apply, PeriodicSobolevSpace.coordinateDerivative_ofSmooth,
    inner_periodicL2_ofSmooth]

/-- An H⁻¹ derivative is represented by an L² field exactly when that field
is the weak derivative against all smooth tests. Smooth density extends the
identity to every H¹ test (`app:ch_background:prop:bg-inverse`). -/
theorem coordinateDerivative_eq_ofL2_iff (i : Fin n) (u v : PeriodicL2 n F) :
    coordinateDerivative i u = ofL2 v ↔ HasPeriodicWeakDerivative i u v := by
  constructor
  · intro h φ hφ
    have heq := DFunLike.congr_fun h (PeriodicSobolevSpace.ofSmooth 1 φ hφ)
    rw [coordinateDerivative_ofSmooth, ofL2_apply, inner_periodicL2_ofSmooth] at heq
    exact heq.symm
  · intro h
    apply DFunLike.coe_injective
    apply (PeriodicSobolevSpace.denseRange_ofSmooth 1).equalizer
      (coordinateDerivative i u).continuous (ofL2 v).continuous
    funext φ
    rw [Function.comp_apply, Function.comp_apply, coordinateDerivative_ofSmooth,
      ofL2_apply, inner_periodicL2_ofSmooth]
    exact (h φ.1 φ.2).symm

/-- On H¹ the negative-order derivative agrees with the L² derivative under
the canonical inclusion (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem coordinateDerivative_toL2 (i : Fin n) (u : PeriodicSobolevSpace n F 1) :
    coordinateDerivative i (PeriodicSobolevSpace.toL2 1 u) =
      ofL2 (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.coordinateDerivative 0 i u)) :=
  (coordinateDerivative_eq_ofL2_iff _ _ _).mpr
    (PeriodicSobolevSpace.hasPeriodicWeakDerivative_coordinateDerivative 0 i u)

end JanetCartan.PeriodicSobolevNegativeOne

namespace JanetCartan
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- H¹ is precisely the set of L² fields whose H⁻¹ coordinate derivatives all
have L² representatives (`app:ch_background:prop:bg-inverse`). -/
theorem mem_periodicSobolevLevel_one_iff_negativeDerivatives (u : PeriodicL2 n F) :
    u ∈ periodicSobolevLevel n F 1 ↔
      ∀ i : Fin n, ∃ v : PeriodicL2 n F,
        PeriodicSobolevNegativeOne.coordinateDerivative i u = PeriodicSobolevNegativeOne.ofL2 v := by
  simp only [mem_periodicSobolevLevel_one_iff_weakDerivatives,
    PeriodicSobolevNegativeOne.coordinateDerivative_eq_ofL2_iff]

end JanetCartan
