module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.FirstJet
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Vector Fourier regularity gives a genuine first weak derivative

The order-one conversion required by
`app:ch_regular_base:eq:sector-theorem-residual`. The coordinate isometry retains
literal L² classes, and coordinate synthesis bounds the Fréchet operator norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped ContDiff

namespace JanetCartan.LocalSobolev

open Pseudodifferential
variable {n r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Actual scalar distributional identities in each fiber coordinate give
the vector compact-test identity used in `app:not:fourier`. -/
theorem vector_integral_test_of_coordinateDerivatives
    (u v : Lp F 2 (volume : Measure E)) (i : Fin n)
    (h : ∀ a, HasEuclideanL2CoordinateDerivative i
      (finiteL2CoordinateIsometry volume u a) (finiteL2CoordinateIsometry volume v a))
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ψ x • v x) =
      - ∫ x, fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • u x := by
  have hi : Integrable (fun x ↦ ψ x • v x) :=
    ((Lp.memLp v).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hψ.continuous hc
  have hd : Integrable
      (fun x ↦ fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • u x) := by
    apply ((Lp.memLp u).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hc.fderiv ℝ).comp_left
        (g := fun L : E →L[ℝ] ℝ ↦ L (EuclideanSpace.basisFun (Fin n) ℝ i)) rfl
  apply PiLp.ext
  intro a
  change (∫ x, ψ x • v x) a = -(∫ x,
    fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • u x) a
  rw [eval_integral_piLp (fun b ↦ hi.eval_piLp b),
    eval_integral_piLp (fun b ↦ hd.eval_piLp b)]
  calc
    _ = ∫ x, ψ x • (finiteL2CoordinateIsometry volume v a) x := by
      apply integral_congr_ae
      filter_upwards [finiteL2Coordinates_apply_ae volume v a] with x hx
      exact congrArg (ψ x • ·) hx.symm
    _ = _ := (h a).integral_test ψ hψ hc
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [finiteL2Coordinates_apply_ae volume u a] with x hx
      exact congrArg (fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) • ·) hx

/-- Fourier H¹ membership alone constructs a genuine L² weak Fréchet
derivative. The quantitative bound retains the scalar `2π` factor and costs
only a finite fiber factor, for `app:ch_regular_base:eq:sector-theorem-residual`. -/
theorem exists_vector_firstWeakDerivative
    (u : Lp F 2 (volume : Measure E)) (hu : MemVectorFourierSobolev 1 u) :
    ∃ D : E → E →L[ℝ] F,
      Mollification.HasWeakFDerivOn volume u D univ ∧ MemLp D 2 volume ∧
      ‖u‖ + (eLpNorm D 2 volume).toReal ≤
        (((r : ℝ) + 1) * (1 + 2 * Real.pi * n)) * vectorFourierSobolevNorm 1 u := by
  have hu' (a : Fin r) : MemFourierSobolev ((0 : ℝ) + 1)
      (finiteL2CoordinateIsometry volume u a) := by simpa only [zero_add] using hu a
  choose w hw hn₁ hn₂ using fun a ↦
    ((hu' a).exists_coordinateDerivatives_norm_bounds (s := 0) (by norm_num)).2
  let v (i : Fin n) : Lp F 2 (volume : Measure E) :=
    (finiteL2CoordinateIsometry volume).symm (WithLp.toLp 2 (fun a ↦ w a i))
  have hv (i : Fin n) (a : Fin r) : finiteL2CoordinateIsometry volume (v i) a = w a i := by
    simp [v]
  have htest := fun ψ hψ hc i ↦ vector_integral_test_of_coordinateDerivatives u (v i) i
    (fun a ↦ by rw [hv]; exact (hw a i).1) ψ hψ hc
  refine ⟨coordinateFDeriv (fun i ↦ v i),
    hasWeakFDerivOn_coordinateFDeriv (Lp.memLp u) (fun i ↦ Lp.memLp (v i)) htest,
    memLp_coordinateFDeriv (fun i ↦ Lp.memLp (v i)), ?_⟩
  have hvnorm (i : Fin n) : ‖v i‖ ≤ ∑ a, ‖w a i‖ := by
    have h := matrixFourierSobolevNorm_le_sum (d := n) 0
      (WithLp.toLp 2 (fun a ↦ w a i))
    simpa [v] using h
  have hunorm : ‖u‖ ≤ ∑ a, ‖finiteL2CoordinateIsometry volume u a‖ := by
    simpa using matrixFourierSobolevNorm_le_sum (d := n) 0 (finiteL2CoordinateIsometry volume u)
  have hnonneg : 0 ≤ vectorFourierSobolevNorm 1 u := norm_nonneg _
  calc
    _ ≤ ‖u‖ + ∑ i, ‖v i‖ := by
      simpa only [← Lp.norm_def] using add_le_add (le_refl ‖u‖)
        (l2Norm_coordinateFDeriv_le (fun i ↦ Lp.memLp (v i)))
    _ ≤ (∑ a, ‖finiteL2CoordinateIsometry volume u a‖) + ∑ i, ∑ a, ‖w a i‖ :=
      add_le_add hunorm (Finset.sum_le_sum fun i _ ↦ hvnorm i)
    _ = ∑ a, (‖finiteL2CoordinateIsometry volume u a‖ + ∑ i, ‖w a i‖) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ _a : Fin r, (1 + 2 * Real.pi * n) * vectorFourierSobolevNorm 1 u := by
      apply Finset.sum_le_sum
      intro a _
      have h := hn₂ a
      simp only [zero_add, fourierSobolevNorm_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (fourierSobolevNorm_coordinate_le 1 (finiteL2CoordinateIsometry volume u) a)
        (by positivity))
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      nlinarith [mul_nonneg (show 0 ≤ 1 + 2 * Real.pi * n by positivity) hnonneg]

end JanetCartan.LocalSobolev
