module

public import JanetCartan.Analysis.Operator.NormalPerturbation.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite weighted rows

For a finite family of operators between complete real or complex Hilbert spaces,
`weightedRow w A` sends `x` to `∑ i, √(w i) • A i (x i)`. Its input has the
Hilbert direct-sum norm, and its normal is the sum of the weighted atom normals.
The input spaces may vary with the atom.

These are the algebraic estimates used to pass to the corrected atomic family
in `app:ch_response:cor:current-atoms` and to transfer the gap after
`app:ch_waves:eq:colored-normal-comparison`. Nonnegative weights and atomic
operator bounds are explicit inputs. In particular, this module does not prove
the analytic estimates on the corrected amplitudes or their operator realizations.
-/

@[expose] public noncomputable section

open scoped InnerProduct
open ContinuousLinearMap

namespace JanetCartan.NormalPerturbation

variable {𝕜 ι F : Type*} [RCLike 𝕜] [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  [∀ i, CompleteSpace (E i)]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The column of weighted adjoints for the finite row in
`app:ch_response:cor:current-atoms`. -/
def weightedColumn (w : ι → ℝ) (A : ∀ i, E i →L[𝕜] F) : F →L[𝕜] PiLp 2 E :=
  (PiLp.continuousLinearEquiv 2 𝕜 E).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i ↦ (Real.sqrt (w i) : 𝕜) • (A i)†)

/-- The finite row with square-root sampling weights, on the Hilbert direct sum
(`app:ch_waves:eq:colored-normal-comparison`). Its concrete sum formula is
`weightedRow_apply`. -/
def weightedRow (w : ι → ℝ) (A : ∀ i, E i →L[𝕜] F) : PiLp 2 E →L[𝕜] F :=
  (weightedColumn w A)†

omit [Fintype ι] in
/-- Coordinate formula for the weighted adjoint column
(`app:ch_response:cor:current-atoms`). -/
@[simp] theorem weightedColumn_apply (w : ι → ℝ) (A : ∀ i, E i →L[𝕜] F)
    (x : F) (i : ι) : weightedColumn w A x i = (Real.sqrt (w i) : 𝕜) • ((A i)†) x := rfl

/-- The adjoint of the sampled row is its column of weighted adjoints
(`app:ch_waves:eq:colored-normal-comparison`). -/
@[simp] theorem weightedRow_adjoint (w : ι → ℝ) (A : ∀ i, E i →L[𝕜] F) :
    (weightedRow w A)† = weightedColumn w A := adjoint_adjoint _

/-- The actual sum defining the finite sampled row
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem weightedRow_apply (w : ι → ℝ) (A : ∀ i, E i →L[𝕜] F) (x : PiLp 2 E) :
    weightedRow w A x = ∑ i, (Real.sqrt (w i) : 𝕜) • A i (x i) := by
  apply ext_inner_right 𝕜
  intro y
  rw [weightedRow, adjoint_inner_left, PiLp.inner_apply, sum_inner]
  simp only [weightedColumn_apply, inner_smul_real_right, inner_smul_real_left,
    adjoint_inner_right]

/-- Exact weighted row-normal identity for nonnegative sampling weights
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem normal_weightedRow (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : ∀ i, E i →L[𝕜] F) :
    normal (weightedRow w A) = ∑ i, (w i : 𝕜) • normal (A i) := by
  ext x
  simp only [normal, comp_apply, weightedRow_adjoint, weightedRow_apply,
    weightedColumn_apply, map_smul, smul_smul, sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hw i)]

/-- Correcting each atom adds the row of corrections
(`app:ch_response:cor:current-atoms`). -/
theorem weightedRow_add (w : ι → ℝ) (A D : ∀ i, E i →L[𝕜] F) :
    weightedRow w (fun i ↦ A i + D i) = weightedRow w A + weightedRow w D := by
  ext x
  simp [weightedRow_apply, smul_add, Finset.sum_add_distrib]

/-- The row norm is bounded by the weighted square sum of atom norms
(`app:ch_response:cor:current-atoms`). No orthogonality between atom images is
required; orthogonality comes from the Hilbert direct-sum input. -/
theorem norm_weightedRow_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : ∀ i, E i →L[𝕜] F) :
    ‖weightedRow w A‖ ≤ Real.sqrt (∑ i, w i * ‖A i‖ ^ 2) := by
  rw [weightedRow, LinearIsometryEquiv.norm_map]
  refine (weightedColumn w A).opNorm_le_bound (Real.sqrt_nonneg _) fun x ↦ ?_
  have hs : 0 ≤ ∑ i, w i * ‖A i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _)
  have hsq : ‖weightedColumn w A x‖ ^ 2 ≤ (∑ i, w i * ‖A i‖ ^ 2) * ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    change ‖(Real.sqrt (w i) : 𝕜) • ((A i)†) x‖ ^ 2 ≤ _
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hw i)]
    have h := ((A i)†).le_opNorm x
    rw [LinearIsometryEquiv.norm_map] at h
    simpa [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) (hw i)
  have hsq' : ‖weightedColumn w A x‖ ^ 2 ≤
      (Real.sqrt (∑ i, w i * ‖A i‖ ^ 2) * ‖x‖) ^ 2 := by
    simpa [mul_pow, Real.sq_sqrt hs] using hsq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq'

/-- The row normal is bounded by the weighted square sum of atom norms
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_normal_weightedRow_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : ∀ i, E i →L[𝕜] F) :
    ‖normal (weightedRow w A)‖ ≤ ∑ i, w i * ‖A i‖ ^ 2 := by
  rw [norm_normal]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_weightedRow_le w hw A) 2
  rwa [Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _))] at h

/-- Assemble supplied atomic estimates into a finite row estimate
(`app:ch_response:cor:current-atoms`). -/
theorem norm_weightedRow_le_of_bounds (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : ∀ i, E i →L[𝕜] F) {a : ι → ℝ} (hA : ∀ i, ‖A i‖ ≤ a i) :
    ‖weightedRow w A‖ ≤ Real.sqrt (∑ i, w i * a i ^ 2) := by
  refine (norm_weightedRow_le w hw A).trans (Real.sqrt_le_sqrt ?_)
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hA i) 2) (hw i)

/-- A finite weighted atomic budget gives the row bound used in
`norm_normal_add_sub_le_of_bounds` (`app:ch_response:cor:current-atoms`). -/
theorem norm_weightedRow_le_of_sum_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : ∀ i, E i →L[𝕜] F) {a : ι → ℝ} {b : ℝ}
    (hA : ∀ i, ‖A i‖ ≤ a i) (hb : 0 ≤ b)
    (hsum : ∑ i, w i * a i ^ 2 ≤ b ^ 2) : ‖weightedRow w A‖ ≤ b := by
  exact (norm_weightedRow_le_of_bounds w hw A hA).trans
    ((Real.sqrt_le_sqrt hsum).trans_eq (Real.sqrt_sq hb))

/-- Row bound under finite weighted perturbations, with the atomic bounds
as inputs (`app:ch_response:cor:current-atoms`). -/
theorem norm_weightedRow_add_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A D : ∀ i, E i →L[𝕜] F) {a d : ι → ℝ}
    (hA : ∀ i, ‖A i‖ ≤ a i) (hD : ∀ i, ‖D i‖ ≤ d i) :
    ‖weightedRow w (fun i ↦ A i + D i)‖ ≤
      Real.sqrt (∑ i, w i * a i ^ 2) + Real.sqrt (∑ i, w i * d i ^ 2) := by
  rw [weightedRow_add]
  exact norm_row_add_le _ _ (norm_weightedRow_le_of_bounds w hw A hA)
    (norm_weightedRow_le_of_bounds w hw D hD)

/-- Normal comparison under finite weighted perturbations, conditional on
atomic operator estimates (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_normal_weightedRow_add_sub_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A D : ∀ i, E i →L[𝕜] F) {a d : ι → ℝ}
    (hA : ∀ i, ‖A i‖ ≤ a i) (hD : ∀ i, ‖D i‖ ≤ d i) :
    ‖normal (weightedRow w (fun i ↦ A i + D i)) - normal (weightedRow w A)‖ ≤
      2 * Real.sqrt (∑ i, w i * a i ^ 2) * Real.sqrt (∑ i, w i * d i ^ 2) +
        ∑ i, w i * d i ^ 2 := by
  rw [weightedRow_add]
  have h := norm_normal_add_sub_le_of_bounds _ _
    (norm_weightedRow_le_of_bounds w hw A hA) (norm_weightedRow_le_of_bounds w hw D hD)
  rwa [Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _))] at h

/-- Transfer a gap on a specified output class using finite weighted atom
bounds (`app:ch_waves:eq:colored-normal-comparison`). The original gap and the
atom bounds must be proved separately for the analytic family. -/
theorem normal_weightedRow_add_lower_bound (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A D : ∀ i, E i →L[𝕜] F) (s : Set F) {g : ℝ} {a d : ι → ℝ}
    (hgap : ∀ x ∈ s, g * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (normal (weightedRow w A) x) x))
    (hA : ∀ i, ‖A i‖ ≤ a i) (hD : ∀ i, ‖D i‖ ≤ d i) :
    ∀ x ∈ s, (g - (2 * Real.sqrt (∑ i, w i * a i ^ 2) *
      Real.sqrt (∑ i, w i * d i ^ 2) + ∑ i, w i * d i ^ 2)) * ‖x‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (normal (weightedRow w (fun i ↦ A i + D i)) x) x) :=
  quadratic_lower_bound_of_norm_sub_le _ _ s hgap
    (norm_normal_weightedRow_add_sub_le w hw A D hA hD)

end JanetCartan.NormalPerturbation
