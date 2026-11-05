module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.RawEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RecurrenceTail.Raw

/-!
# The original normal inverse and the constructed raw cutoff

Apply the actual grouped carrier multiplier and both auxiliary multipliers to
the SAME right inverse. The only remaining inputs are the continuum inverse's
regularity and quantitative adjoint estimates. In particular, weighted-domain
membership, its finite-energy comparison and the cutoff plateau are proved,
not supplied as new analytic hypotheses.
-/

@[expose] public noncomputable section
namespace JanetCartan.CanonicalTailRealization
open ContinuumRow RawCutoffBounds CarrierSobolev

variable {n : ℕ} {ι Y : Type*} [Fintype ι]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The actual fixed-inverse error at carrier plateau `c*K`, retaining both
auxiliary ceilings `K` (`main:eq:linear-two-errors`). The gap constant `γ` is
distinct from the geometric plateau constant `c`. -/
theorem reference_error_scaled_rounded_le_raw_norm
    (A : AugmentedInput n ι →L[ℝ] Y) {γ c K : ℝ} (hγ : 0 < γ)
    (hgap : ∀ v, γ * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    (hc : 0 < c) (hK : 1 ≤ K) (hcK : 1 ≤ c * K) {s : ℕ} (r : Y)
    (hmem : CoerciveInverse.rightInverse A r ∈ (augmentedInputSobolevScale n ι).level s) :
    ‖r - A (rawSquaredCutoff K (fun _ ↦ RawInputPartition.roundedCarrierMask n (c * K))
      (A.adjoint ((CoerciveInverse.normalOperator A).inverse r)))‖ ≤
      (‖A‖ * max 1 (c ^ (-(s : ℝ)))) * K ^ (-(s : ℝ)) *
        (augmentedInputSobolevScale n ι).gradeNorm s (CoerciveInverse.rightInverse A r) := by
  let u := CoerciveInverse.rightInverse A r
  change ‖r - A (rawSquaredCutoff K _ u)‖ ≤ _
  have hid : r - A (rawSquaredCutoff K
      (fun _ ↦ RawInputPartition.roundedCarrierMask n (c * K)) u) =
      A (u - rawSquaredCutoff K (fun _ ↦ RawInputPartition.roundedCarrierMask n (c * K)) u) := by
    rw [map_sub, CoerciveInverse.apply_rightInverse A hγ hgap r]
  rw [hid]
  calc
    _ ≤ ‖A‖ * ‖u - rawSquaredCutoff K
        (fun _ ↦ RawInputPartition.roundedCarrierMask n (c * K)) u‖ := A.le_opNorm _
    _ ≤ ‖A‖ * ((max 1 (c ^ (-(s : ℝ))) * K ^ (-(s : ℝ))) *
        (augmentedInputSobolevScale n ι).gradeNorm s u) :=
      mul_le_mul_of_nonneg_left
        (rawSquaredCutoff_scaled_rounded_tail_of_augmentedInputLevel hc hK hcK hmem)
        (norm_nonneg _)
    _ = _ := by ring

/-- One-high tail bound with the exact carrier plateau loss. The inverse and
raw estimates are the quantitative inputs of `ContinuumInverse`; all cutoff,
weighted-membership and finite-sum obligations are discharged here
(`main:lem:mean-recurrence`). -/
theorem reference_error_scaled_rounded_le_one_high
    (G : GradedScale Y) (A : AugmentedInput n ι →L[ℝ] Y)
    {γ c K : ℝ} (hγ : 0 < γ)
    (hgap : ∀ v, γ * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    (hc : 0 < c) (hK : 1 ≤ K) (hcK : 1 ≤ c * K) {s : ℕ} (r : Y)
    {d k T : ℝ} (hk : 0 ≤ k) (hT : 0 ≤ T)
    (hinvmem : (CoerciveInverse.normalOperator A).inverse r ∈ G.level s)
    (hinv : G.gradeNorm s ((CoerciveInverse.normalOperator A).inverse r) ≤
      d * (G.gradeNorm s r + T ^ s * ‖r‖))
    (hraw : ∀ v, v ∈ G.level s →
      A.adjoint v ∈ (augmentedInputSobolevScale n ι).level s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint v) ≤
        k * (G.gradeNorm s v + T ^ s * ‖v‖)) :
    ‖r - A (rawSquaredCutoff K (fun _ ↦ RawInputPartition.roundedCarrierMask n (c * K))
      (A.adjoint ((CoerciveInverse.normalOperator A).inverse r)))‖ ≤
      (‖A‖ * max 1 (c ^ (-(s : ℝ))) * (k * (d + γ⁻¹))) * K ^ (-(s : ℝ)) *
        (G.gradeNorm s r + T ^ s * ‖r‖) := by
  have hm := ContinuumInverse.rightInverse_mem G (augmentedInputSobolevScale n ι) A
    hinvmem (fun v hv ↦ (hraw v hv).1)
  have hb := ContinuumInverse.rightInverse_gradeNorm_le G (augmentedInputSobolevScale n ι)
    A hγ hgap hk (pow_nonneg hT s) hinvmem hinv (fun v hv ↦ (hraw v hv).2)
  calc
    _ ≤ (‖A‖ * max 1 (c ^ (-(s : ℝ)))) * K ^ (-(s : ℝ)) *
        (augmentedInputSobolevScale n ι).gradeNorm s (CoerciveInverse.rightInverse A r) :=
      reference_error_scaled_rounded_le_raw_norm A hγ hgap hc hK hcK r hm
    _ ≤ (‖A‖ * max 1 (c ^ (-(s : ℝ)))) * K ^ (-(s : ℝ)) *
        (k * (d + γ⁻¹) * (G.gradeNorm s r + T ^ s * ‖r‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- With the constructed plateau `c=1`, the coefficient is exactly the one
used by `RecurrenceTail.run_inductive_raw_tail_le`, without an additional
mask or energy premise (`main:lem:mean-recurrence`). -/
theorem reference_error_rounded_le_one_high
    (G : GradedScale Y) (A : AugmentedInput n ι →L[ℝ] Y)
    {γ K : ℝ} (hγ : 0 < γ) (hgap : ∀ v, γ * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    (hK : 1 ≤ K) {s : ℕ} (r : Y) {d k T : ℝ} (hk : 0 ≤ k) (hT : 0 ≤ T)
    (hinvmem : (CoerciveInverse.normalOperator A).inverse r ∈ G.level s)
    (hinv : G.gradeNorm s ((CoerciveInverse.normalOperator A).inverse r) ≤
      d * (G.gradeNorm s r + T ^ s * ‖r‖))
    (hraw : ∀ v, v ∈ G.level s →
      A.adjoint v ∈ (augmentedInputSobolevScale n ι).level s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint v) ≤
        k * (G.gradeNorm s v + T ^ s * ‖v‖)) :
    ‖r - A (rawSquaredCutoff K (fun _ ↦ RawInputPartition.roundedCarrierMask n K)
      (A.adjoint ((CoerciveInverse.normalOperator A).inverse r)))‖ ≤
      (‖A‖ * (k * (d + γ⁻¹))) * K ^ (-(s : ℝ)) *
        (G.gradeNorm s r + T ^ s * ‖r‖) := by
  simpa only [one_mul, Real.one_rpow, max_self, mul_one] using
    reference_error_scaled_rounded_le_one_high G A hγ hgap (c := 1) zero_lt_one hK
      (by simpa only [one_mul] using hK) r hk hT hinvmem hinv hraw

end JanetCartan.CanonicalTailRealization
