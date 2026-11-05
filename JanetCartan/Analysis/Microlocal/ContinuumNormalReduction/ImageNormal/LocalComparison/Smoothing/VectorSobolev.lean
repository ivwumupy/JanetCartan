module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.ScalarSobolev

/-!
# Vector Sobolev gain for the differentiated Bessel remainder

The concrete matrix entries in `app:ch_background:prop:bg-frame`, Step 1,
are smooth and compactly supported. Their proved scalar derivative bounds
give a common finite bound for the vector operator and its Hilbert adjoint.
The constant depends on the fixed masks and coefficients; this is not a
uniform tame estimate over a family of geometric data.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
open Pseudodifferential
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The actual two-factor Bessel remainder and its Hilbert adjoint map
complex vector L² into H¹, as required in
`app:ch_background:prop:bg-frame`, Step 1. All scalar smoothing inputs are
discharged by smoothness and compact support of the displayed matrix kernel.
The bound is for these fixed coefficients and masks. -/
theorem localizedImageNormalRemainderOperator_sobolev_one_bounds
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E),
      MemVectorFourierSobolev 1
        (localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ f) ∧
      vectorFourierSobolevNorm 1
        (localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ f) ≤ C * ‖f‖ ∧
      MemVectorFourierSobolev 1
        ((localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ).adjoint f) ∧
      vectorFourierSobolevNorm 1
        ((localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ).adjoint f) ≤
          C * ‖f‖ := by
  classical
  let B := localizedImageNormalRemainderEntryOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ
  have hentry (i k : I) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L²,
      MemFourierSobolev 1 (B i k f) ∧ fourierSobolevNorm 1 (B i k f) ≤ C * ‖f‖ ∧
      MemFourierSobolev 1 ((B i k).adjoint f) ∧
        fourierSobolevNorm 1 ((B i k).adjoint f) ≤ C * ‖f‖ :=
    imageNormalRealKernelOperator_sobolev_one_bounds
      (localizedImageNormalRemainderKernel χ ψ A Z i k)
      (contDiff_localizedImageNormalRemainderKernel hr χ ψ hχ hψ hχs hψs A Z hA hZ i k)
      (hasCompactSupport_localizedImageNormalRemainderKernel χ ψ hχs hψs A Z i k)
  choose C hC hentry using hentry
  let D : ℝ := ∑ i, ∑ k, C i k
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦ hC i k
  have hCD (i k : I) : C i k ≤ D :=
    (Finset.single_le_sum (fun j _ ↦ hC i j) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun j _ ↦ Finset.sum_nonneg fun l _ ↦ hC j l)
        (Finset.mem_univ i))
  have hforward : ∀ i k f, MemFourierSobolev 0 f →
      MemFourierSobolev 1 (B i k f) ∧
        fourierSobolevNorm 1 (B i k f) ≤ D * (fourierSobolevNorm 0 f + 0 * ‖f‖) := by
    intro i k f _
    exact ⟨(hentry i k f).1, by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        (hentry i k f).2.1.trans
          (mul_le_mul_of_nonneg_right (hCD i k) (norm_nonneg f))⟩
  have hreverse : ∀ k i f, MemFourierSobolev 0 f →
      MemFourierSobolev 1 ((B i k).adjoint f) ∧
        fourierSobolevNorm 1 ((B i k).adjoint f) ≤
          D * (fourierSobolevNorm 0 f + 0 * ‖f‖) := by
    intro k i f _
    exact ⟨(hentry i k f).2.2.1, by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        (hentry i k f).2.2.2.trans
          (mul_le_mul_of_nonneg_right (hCD i k) (norm_nonneg f))⟩
  refine ⟨(Fintype.card I : ℝ) * (Fintype.card I : ℝ) * D, by positivity, fun f ↦ ?_⟩
  have hf : MemVectorFourierSobolev 0 f := fun i ↦ memFourierSobolev_zero _
  have hF := vectorMatrixL2Operator_fourierSobolev_bound B 0 1 D 0 hD le_rfl hforward f hf
  have hR := vectorMatrixL2Operator_fourierSobolev_bound
    (fun k i ↦ (B i k).adjoint) 0 1 D 0 hD le_rfl hreverse f hf
  rw [localizedImageNormalRemainderOperator_adjoint]
  simpa only [B, localizedImageNormalRemainderOperator,
    vectorFourierSobolevNorm_zero, zero_mul, add_zero] using
    And.intro hF.1 (And.intro hF.2 hR)

end JanetCartan.ContinuumNormalReduction.ImageNormal
