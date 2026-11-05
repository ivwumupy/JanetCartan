module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.ScalarSobolev

/-!
# Complex realization of the one-factor remainder

The concrete kernel of `app:ch_background:prop:bg-frame`, Step 1, gives the
integral action of the one-factor remainder and its literal Hilbert adjoint.
The scalar compact-kernel estimates supply the paired H¹ bounds consumed by
the real realization and `normalCrossTerms_sobolev_one_bounds`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin d)) 2 (volume : Measure E)

private theorem matrixKernelOperator_ae_integral
    (B : Fin d → Fin d → L² →L[ℂ] L²) (kernel : Fin d → Fin d → E × E → ℝ)
    (hB : ∀ i j f, B i j f =ᵐ[volume] fun x ↦ ∫ y, (kernel i j (x, y) : ℂ) * f y)
    (f : C²) :
    vectorMatrixL2Operator B f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y, (kernel i j (x, y) : ℂ) * f y j) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  simp only [finiteL2CoordinateIsometry_vectorMatrixL2Operator, AmplitudeBound.matrixOperator_apply]
  have he (j : Fin d) := hB i j (finiteL2CoordinateIsometry volume f j)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun j ↦ B i j (finiteL2CoordinateIsometry volume f j)), ae_all_iff.mpr he] with x hx he
  simp only [Finset.sum_apply] at hx
  rw [hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j]
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume f j] with y hy
  exact congrArg (fun z : ℂ ↦ (kernel i j (x, y) : ℂ) * z) hy

variable {r : ℝ} (hr : r < 1 / 2) (ρ χ μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hμs : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : EuclideanSpace ℝ (Fin d) → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))

local notation "K" => oneFactorRemainderKernel (d := d) ρ χ μ A Z
local notation "hK" => contDiff_oneFactorRemainderKernel (d := d) (r := r) hr ρ χ μ hρ hχ hμ hρs hχs A Z hA hZ
local notation "hKs" => hasCompactSupport_oneFactorRemainderKernel (d := d) (r := r) ρ χ μ hχs hμs A Z
local notation "T" => complexOneFactorRemainderOperator (d := d) (r := r) hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ

/-- The complex one-factor remainder integrates the actual differentiated
kernel on every L² input (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexOneFactorRemainderOperator_ae_integral (f : C²) :
    T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ j, ∫ y, (K i j (x, y) : ℂ) * f y j) := by
  apply matrixKernelOperator_ae_integral
  intro i j g
  exact compactKernelOperator_ae_integral _ _ g

/-- The literal complex adjoint reverses the spatial arguments and transposes
the matrix entries (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexOneFactorRemainderOperator_adjoint_ae_integral (f : C²) :
    (T).adjoint f =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (fun j ↦ ∑ i, ∫ x, (K i j (x, y) : ℂ) * f x i) := by
  rw [complexOneFactorRemainderOperator, vectorMatrixL2Operator_adjoint]
  apply matrixKernelOperator_ae_integral (kernel := fun j i p ↦ K i j p.swap)
  intro j i g
  simpa only [imageNormalRealKernelOperator, Complex.star_def, Complex.conj_ofReal,
    Prod.swap_prod_mk] using
    compactKernelOperator_adjoint_ae_integral (μ := volume) (ν := volume)
      (t := fun x y ↦ (K i j (x, y) : ℂ))
      (Complex.continuous_ofReal.comp (hK i j).continuous)
      ((hKs i j).comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl) g

/-- Both the concrete complex one-factor remainder and its literal adjoint
gain one Sobolev derivative, with one finite constant for the fixed data
(`app:ch_background:prop:bg-frame`, Step 1). This supplies the real estimate
used by `normalCrossTerms_sobolev_one_bounds`. -/
theorem complexOneFactorRemainderOperator_sobolev_one_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : C²,
      MemVectorFourierSobolev 1 (T f) ∧
      vectorFourierSobolevNorm 1 (T f) ≤ C * ‖f‖ ∧
      MemVectorFourierSobolev 1 ((T).adjoint f) ∧
      vectorFourierSobolevNorm 1 ((T).adjoint f) ≤ C * ‖f‖ := by
  classical
  let B := fun i j ↦ imageNormalRealKernelOperator (K i j) (hK i j).continuous (hKs i j)
  have hentry (i j : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L²,
      MemFourierSobolev 1 (B i j f) ∧ fourierSobolevNorm 1 (B i j f) ≤ C * ‖f‖ ∧
      MemFourierSobolev 1 ((B i j).adjoint f) ∧
        fourierSobolevNorm 1 ((B i j).adjoint f) ≤ C * ‖f‖ :=
    imageNormalRealKernelOperator_sobolev_one_bounds (K i j) (hK i j) (hKs i j)
  choose C hC hentry using hentry
  let C₀ : ℝ := ∑ i, ∑ j, C i j
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hC i j
  have hCC₀ (i j : Fin d) : C i j ≤ C₀ :=
    (Finset.single_le_sum (fun k _ ↦ hC i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg fun l _ ↦ hC k l)
        (Finset.mem_univ i))
  have hforward : ∀ i j f, MemFourierSobolev 0 f →
      MemFourierSobolev 1 (B i j f) ∧
        fourierSobolevNorm 1 (B i j f) ≤ C₀ * (fourierSobolevNorm 0 f + 0 * ‖f‖) := by
    intro i j f _
    exact ⟨(hentry i j f).1, by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        (hentry i j f).2.1.trans
          (mul_le_mul_of_nonneg_right (hCC₀ i j) (norm_nonneg f))⟩
  have hreverse : ∀ j i f, MemFourierSobolev 0 f →
      MemFourierSobolev 1 ((B i j).adjoint f) ∧
        fourierSobolevNorm 1 ((B i j).adjoint f) ≤
          C₀ * (fourierSobolevNorm 0 f + 0 * ‖f‖) := by
    intro j i f _
    exact ⟨(hentry i j f).2.2.1, by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        (hentry i j f).2.2.2.trans
          (mul_le_mul_of_nonneg_right (hCC₀ i j) (norm_nonneg f))⟩
  refine ⟨(Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) * C₀,
    by positivity, fun f ↦ ?_⟩
  have hf : MemVectorFourierSobolev 0 f := fun i ↦ memFourierSobolev_zero _
  have hF := vectorMatrixL2Operator_fourierSobolev_bound B 0 1 C₀ 0 hC₀ le_rfl hforward f hf
  have hR := vectorMatrixL2Operator_fourierSobolev_bound
    (fun j i ↦ (B i j).adjoint) 0 1 C₀ 0 hC₀ le_rfl hreverse f hf
  rw [complexOneFactorRemainderOperator, vectorMatrixL2Operator_adjoint]
  simpa only [B, complexOneFactorRemainderOperator,
    vectorFourierSobolevNorm_zero, zero_mul, add_zero] using
    And.intro hF.1 (And.intro hF.2 hR)

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
