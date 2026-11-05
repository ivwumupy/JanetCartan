module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverResidual
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.CompactRange
public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# Full reconstruction of the complete angular residual

The same stress row and its inverse Gram matrix reconstruct every component
of the reduced residual in `app:ch_response:eq:response-full-identity`.
The explicit Leibniz bound keeps the entire high coefficient seminorm visible;
actual history profiles and restriction Sobolev residual estimates are applied
in the subsequent leaves. Consumers are corrected-atom arbitrary precision
and the actual `UniformHistoryCorrection` construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms

/-- The literal full-tensor multiplier of the complete reduced residual,
including the factor two in `app:ch_response:eq:response-full-identity`.
It is constructed from the supplied row and its own inverse Gram matrix. -/
def fullStressResidualReconstruction {n : ℕ} (Q : Fin n → MetricTensor n) :
    Euclidean n →L[ℝ] MetricTensor n :=
  (2 : ℝ) • ∑ i, ∑ j, (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
    ((stressGram Q)⁻¹ i j • Q i)

/-- Exact agreement with the original double sum; all residual components
remain present (`app:ch_response:eq:response-full-identity`). -/
theorem fullStressResidualReconstruction_apply {n : ℕ}
    (Q : Fin n → MetricTensor n) (v : Euclidean n) :
    fullStressResidualReconstruction Q v =
      (2 : ℝ) • ∑ i, ∑ j, ((stressGram Q)⁻¹ i j * v j) • Q i := by
  simp [fullStressResidualReconstruction, smul_smul, mul_comm]

/-- Linear independence of the original row proves smoothness of its
inverse-Gram multiplier (`app:ch_response:prop:response-ambient`). No
regularity of an inverse matrix or full residual is assumed. -/
theorem contDiffAt_fullStressResidualReconstruction {n : ℕ}
    {Q : Fin n → MetricTensor n} (hQ : LinearIndependent ℝ Q) :
    ContDiffAt ℝ ∞ (@fullStressResidualReconstruction n) Q := by
  have hunit : IsUnit (stressGram Q) := (Matrix.posDef_gram_of_linearIndependent hQ).isUnit
  have hinv : ContDiffAt ℝ ∞ (fun R : Fin n → MetricTensor n ↦ (stressGram R)⁻¹) Q :=
    (contDiffAt_matrix_inv hunit).comp Q
      RawPrimary.AmbientStrain.contDiff_stressGram.contDiffAt
  unfold fullStressResidualReconstruction
  apply ContDiffAt.const_smul
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  apply contDiffAt_const.smulRight
  exact ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.contDiffAt.comp Q hinv).smul
    (contDiffAt_pi.mp contDiffAt_id i)

/-- Smoothness of the SAME inverse-Gram multiplier on a smooth independent
row (`app:ch_response:prop:response-ambient`). -/
theorem contDiffOn_fullStressResidualReconstruction {n : ℕ}
    {Q : Euclidean n → Fin n → MetricTensor n} {U : Set (Euclidean n)}
    (hQ : ContDiffOn ℝ ∞ Q U) (hlin : ∀ x ∈ U, LinearIndependent ℝ (Q x)) :
    ContDiffOn ℝ ∞ (fun x ↦ fullStressResidualReconstruction (Q x)) U :=
  fun x hx ↦ (contDiffAt_fullStressResidualReconstruction (hlin x hx)).comp_contDiffWithinAt x (hQ x hx)

/-- Explicit Leibniz transfer from the complete smooth reduced residual to
its full-tensor reconstruction. The high coefficient seminorm remains visible;
it is not absorbed into a purported uniform history constant
(`app:ch_response:eq:response-full-identity`, `app:ch_response:cor:current-atoms`). -/
theorem cNorm_fullStressResidualReconstruction_le {n : ℕ}
    {K U : Set (Euclidean n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlin : ∀ x ∈ U, LinearIndependent ℝ (Q x))
    (v : Euclidean n → Euclidean n) (hv : ContDiffOn ℝ ∞ v U) (s : ℕ) :
    cNorm K s (fun x ↦ fullStressResidualReconstruction (Q x) (v x)) ≤
      ((s + 1 : ℝ) * (2 : ℝ)^s) *
        cNorm K s (fun x ↦ fullStressResidualReconstruction (Q x)) * cNorm K s v := by
  let A := fun x ↦ fullStressResidualReconstruction (Q x)
  have hA := contDiffOn_fullStressResidualReconstruction hQ hlin
  have hAj (j : ℕ) (hj : j ≤ s) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ j A x‖ ≤ cNorm K s A :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hA.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp)) hx hj
  have hvj (j : ℕ) (hj : j ≤ s) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ j v x‖ ≤ cNorm K s v :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hv.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp)) hx hj
  let B := ContinuousLinearMap.id ℝ (Euclidean n →L[ℝ] MetricTensor n)
  have hjet (q : ℕ) (hq : q ≤ s) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ q (fun x ↦ A x (v x)) x‖ ≤
        (2 : ℝ)^s * cNorm K s A * cNorm K s v := by
    have hh := B.norm_iteratedFDerivWithin_le_of_bilinear hA hv hU.uniqueDiffOn
      (hKU hx) (n := q) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)] at hh
    change ‖iteratedFDeriv ℝ q (fun x ↦ A x (v x)) x‖ ≤ _ at hh
    have hsum : ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) = (2 : ℝ)^q := by
      exact_mod_cast Nat.sum_range_choose q
    apply hh.trans
    calc
      _ ≤ 1 * ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) * cNorm K s A * cNorm K s v := by
        apply mul_le_mul ContinuousLinearMap.norm_id_le
        · apply Finset.sum_le_sum
          intro i hi
          have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hAj i (hiq.trans hq) x hx) (Nat.cast_nonneg _))
            (hvj (q-i) ((Nat.sub_le _ _).trans hq) x hx) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
        · positivity
        · norm_num
      _ = (2 : ℝ)^q * cNorm K s A * cNorm K s v := by
        rw [one_mul, ← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hq) (cNorm_nonneg _ _ _))
        (cNorm_nonneg _ _ _)
  have hh := cNorm_le_sum_of_bounds (s := K) (r := s)
    (fun _ _ ↦ mul_nonneg (mul_nonneg (by positivity) (cNorm_nonneg K s A)) (cNorm_nonneg K s v))
    hjet
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_assoc] using hh

end JanetCartan.CorrectedAtoms
