module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.CoefficientDecay

/-!
# Fixed finite matrix amplitudes

The entrywise extension in `app:ch_osc:lem:osc-amplitude`, on finite Hilbert
direct sums of scalar `L²` spaces. All norms on these sums are the `ℓ²` norms.
The scalar entries remain the operator series; integral-kernel identification is
not asserted by this module.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound

variable {I H : Type*} [Fintype I] [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Isometric coordinate inclusion for the matrix step of
`app:ch_osc:lem:osc-amplitude`. -/
def coordinateInjection (i : I) : H →ₗᵢ[ℂ] PiLp 2 (fun _ : I ↦ H) := by
  classical
  refine { toFun := fun x : H ↦ (PiLp.single 2 i x : PiLp 2 (fun _ : I ↦ H))
           map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }
  · intro x y
    exact PiLp.single_add 2 i
  · intro c x
    apply PiLp.ext
    intro j
    by_cases hj : j = i
    · subst j; simp
    · simp
  · intro x
    exact PiLp.norm_single 2 (fun _ : I ↦ H) i x

variable {J K : Type*} [Fintype J]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- A finite matrix of operators acting between `ℓ²` direct sums, as in the
fixed-matrix extension of `app:ch_osc:lem:osc-amplitude`. -/
def matrixOperator (B : I → J → H →L[ℂ] K) :
    PiLp 2 (fun _ : J ↦ H) →L[ℂ] PiLp 2 (fun _ : I ↦ K) :=
  ∑ i, ∑ j, (coordinateInjection i).toContinuousLinearMap.comp
    ((B i j).comp (PiLp.proj 2 (fun _ : J ↦ H) j))

/-- The block operator acts by ordinary matrix multiplication, with operator
entries (`app:ch_osc:lem:osc-amplitude`). -/
theorem matrixOperator_apply (B : I → J → H →L[ℂ] K)
    (f : PiLp 2 (fun _ : J ↦ H)) (i : I) :
    matrixOperator B f i = ∑ j, B i j (f j) := by
  classical
  simp [matrixOperator, coordinateInjection, Pi.single_apply]

/-- The entrywise bound in `app:ch_osc:lem:osc-amplitude`: the matrix operator
norm is bounded by the sum of the scalar operator norms. -/
theorem norm_matrixOperator_le (B : I → J → H →L[ℂ] K) :
    ‖matrixOperator B‖ ≤ ∑ i, ∑ j, ‖B i j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  calc
    ‖matrixOperator B f‖ ≤ ∑ i, ∑ j, ‖B i j (f j)‖ := by
      simp only [matrixOperator, sum_apply, ContinuousLinearMap.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ (coordinateInjection i).norm_map _ |>.le))
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * ‖f‖ := by
      gcongr with i _ j _
      exact ((B i j).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (PiLp.norm_apply_le f j) (norm_nonneg _))
    _ = (∑ i, ∑ j, ‖B i j‖) * ‖f‖ := by simp_rw [Finset.sum_mul]

/-- A common scalar bound gives a bound depending only on the fixed matrix
dimensions, as required in `app:ch_osc:lem:osc-amplitude`. -/
theorem norm_matrixOperator_le_of_entry_bound (B : I → J → H →L[ℂ] K) (A : ℝ)
    (hB : ∀ i j, ‖B i j‖ ≤ A) :
    ‖matrixOperator B‖ ≤ (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * A := by
  calc
    _ ≤ ∑ i, ∑ j, ‖B i j‖ := norm_matrixOperator_le B
    _ ≤ ∑ _ : I, ∑ _ : J, A :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hB i j
    _ = _ := by simp [mul_assoc]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The fixed-matrix operator-series conclusion of `app:ch_osc:lem:osc-amplitude`,
conditional on the physical Fourier coefficient decay entrywise. -/
theorem norm_matrixAmplitudeOperator_fourierMultiplier_le_of_decay (d : ℕ)
    (L R : (Fin (2 * d) → ℤ) → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : I → J → (Fin (2 * d) → ℤ) → Lp (α := E) ℂ ∞) (A : ℝ)
    (hL : ∀ k, ‖L k‖ ≤ 1) (hR : ∀ k, ‖R k‖ ≤ 1)
    (ha : ∀ i j k, ‖a i j k‖ ≤ A * twoPositionWeight d k) :
    ‖matrixOperator (H := Lp (α := E) ℂ 2) (K := Lp (α := E) ℂ 2)
      (fun i j ↦ amplitudeOperator L R
        (fun k ↦ fourierMultiplier (a i j k)))‖ ≤
      (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * (coefficientSumConstant d * A) :=
  norm_matrixOperator_le_of_entry_bound _ _ fun i j ↦
    norm_amplitudeOperator_fourierMultiplier_le_of_decay d L R (a i j) A hL hR (ha i j)

end JanetCartan.AmplitudeBound

