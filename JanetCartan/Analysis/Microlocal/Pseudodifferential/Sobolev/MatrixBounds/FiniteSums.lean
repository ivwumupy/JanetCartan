module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Matrices

/-!
# Finite Hilbert sums of scalar Sobolev estimates

The finite matrix step of `app:ch_regular_base:eq:fio-input`. The norm is the
Hilbert sum of the scalar Fourier Sobolev norms, not the supremum norm on a
function type. This leaf is consumed by the literal two-position matrix bounds.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ} {I J : Type*} [Fintype I] [Fintype J]
local notation "L²" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Coordinatewise membership in the finite Hilbert Sobolev sum of
`app:ch_regular_base:eq:fio-input`. -/
def MemMatrixFourierSobolev (s : ℝ) (f : PiLp 2 (fun _ : I ↦ L²)) : Prop :=
  ∀ i, MemFourierSobolev s (f i)

/-- The Hilbert, rather than supremum, Sobolev norm for the matrix step of
`app:ch_regular_base:eq:fio-input`. Use with `MemMatrixFourierSobolev`. -/
def matrixFourierSobolevNorm (s : ℝ) (f : PiLp 2 (fun _ : I ↦ L²)) : ℝ :=
  ‖(WithLp.toLp 2 (fun i ↦ fourierSobolevNorm s (f i)) : EuclideanSpace ℝ I)‖

/-- Squared Hilbert norm for `app:ch_regular_base:eq:fio-input`. -/
theorem matrixFourierSobolevNorm_sq (s : ℝ) (f : PiLp 2 (fun _ : I ↦ L²)) :
    matrixFourierSobolevNorm s f ^ 2 = ∑ i, fourierSobolevNorm s (f i) ^ 2 := by
  simp [matrixFourierSobolevNorm, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

/-- Exact L² normalization of the matrix norm in `app:ch_regular_base:eq:fio-input`. -/
@[simp] theorem matrixFourierSobolevNorm_zero (f : PiLp 2 (fun _ : I ↦ L²)) :
    matrixFourierSobolevNorm 0 f = ‖f‖ := by
  have h := matrixFourierSobolevNorm_sq 0 f
  simp only [fourierSobolevNorm_zero, ← PiLp.norm_sq_eq_of_L2] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- A scalar coordinate is bounded by the Hilbert Sobolev norm in
`app:ch_regular_base:eq:fio-input`. -/
theorem fourierSobolevNorm_coordinate_le (s : ℝ)
    (f : PiLp 2 (fun _ : I ↦ L²)) (i : I) :
    fourierSobolevNorm s (f i) ≤ matrixFourierSobolevNorm s f := by
  simpa only [matrixFourierSobolevNorm, PiLp.toLp_apply, Real.norm_eq_abs,
    abs_of_nonneg (fourierSobolevNorm_nonneg _ _)] using
    PiLp.norm_apply_le (WithLp.toLp 2 (fun i ↦ fourierSobolevNorm s (f i))) i

/-- The Hilbert norm is bounded by the sum of coordinate norms, used only for
an explicit (non-sharp) dimension factor in `app:ch_regular_base:eq:fio-input`. -/
theorem matrixFourierSobolevNorm_le_sum (s : ℝ)
    (f : PiLp 2 (fun _ : I ↦ L²)) :
    matrixFourierSobolevNorm s f ≤ ∑ i, fourierSobolevNorm s (f i) := by
  classical
  have he : (WithLp.toLp 2 (fun i ↦ fourierSobolevNorm s (f i)) : EuclideanSpace ℝ I) =
      ∑ i, PiLp.single 2 i (fourierSobolevNorm s (f i)) := by
    ext i
    simp [Pi.single_apply]
  unfold matrixFourierSobolevNorm
  rw [he]
  simpa only [PiLp.norm_single, Real.norm_eq_abs,
    abs_of_nonneg (fourierSobolevNorm_nonneg _ _)] using norm_sum_le Finset.univ (fun i ↦ (PiLp.single 2 i (fourierSobolevNorm s (f i)) : EuclideanSpace ℝ I))

omit [Fintype J] in
/-- Finite sums retain scalar Sobolev membership and their triangle bound,
for the row sums in `app:ch_regular_base:eq:fio-input`. -/
theorem fourierSobolev_finsetSum {s : ℝ} (S : Finset J) (f : J → L²)
    (hf : ∀ j ∈ S, MemFourierSobolev s (f j)) :
    MemFourierSobolev s (∑ j ∈ S, f j) ∧
      fourierSobolevNorm s (∑ j ∈ S, f j) ≤ ∑ j ∈ S, fourierSobolevNorm s (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, MemFourierSobolev, fourierSobolevNorm]
    have h : weightedL2Fourier (d := d) s 0 = 0 := by
      funext x
      simp [weightedL2Fourier]
    rw [h]
    simp
  | @insert j S hj ih =>
    obtain ⟨hm, hn⟩ := ih (fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))
    have h := hf j (Finset.mem_insert_self _ _)
    simp only [Finset.sum_insert hj]
    exact ⟨h.add hm, (fourierSobolevNorm_add_le h hm).trans (add_le_add_right hn _)⟩

/-- Entrywise scalar tame estimates imply the finite Hilbert matrix estimate
of `app:ch_regular_base:eq:fio-input`, with explicit dimension factor. This
lemma does not supply its scalar analytic premises. -/
theorem matrixOperator_fourierSobolev_bound
    (B : I → J → L² →L[ℂ] L²) (s t C H : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hB : ∀ i j f, MemFourierSobolev s f →
      MemFourierSobolev t (B i j f) ∧
        fourierSobolevNorm t (B i j f) ≤ C * (fourierSobolevNorm s f + H * ‖f‖))
    (f : PiLp 2 (fun _ : J ↦ L²)) (hf : MemMatrixFourierSobolev s f) :
    MemMatrixFourierSobolev t (matrixOperator B f) ∧
      matrixFourierSobolevNorm t (matrixOperator B f) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
          (matrixFourierSobolevNorm s f + H * ‖f‖) := by
  have hr (i : I) := fourierSobolev_finsetSum Finset.univ (fun j ↦ B i j (f j))
    (fun j _ ↦ (hB i j (f j) (hf j)).1)
  constructor
  · intro i
    simpa only [matrixOperator_apply] using (hr i).1
  calc
    _ ≤ ∑ i, fourierSobolevNorm t (matrixOperator B f i) :=
      matrixFourierSobolevNorm_le_sum _ _
    _ ≤ ∑ i : I, ∑ j : J, fourierSobolevNorm t (B i j (f j)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [matrixOperator_apply] using (hr i).2
    _ ≤ ∑ _ : I, ∑ _ : J, C * (matrixFourierSobolevNorm s f + H * ‖f‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (hB i j (f j) (hf j)).2.trans (mul_le_mul_of_nonneg_left
        (add_le_add (fourierSobolevNorm_coordinate_le s f j)
          (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le f j) hH)) hC)
    _ = _ := by simp [mul_assoc]

/-- The actual Hilbert adjoint reverses the finite channel indices, for
`app:ch_regular_base:eq:fio-input`. -/
theorem matrixOperator_adjoint (B : I → J → L² →L[ℂ] L²) :
    (matrixOperator B).adjoint = matrixOperator (fun j i ↦ (B i j).adjoint) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [matrixOperator_apply, sum_inner, inner_sum, ContinuousLinearMap.adjoint_inner_right]
  exact Finset.sum_comm

end JanetCartan.Pseudodifferential
