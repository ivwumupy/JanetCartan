module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The fixed dilation of finite Sobolev row data

The row estimate in Section 7, `app:ch_osc:eq:amplitude-row`, first places the fixed
physical box strictly inside the normalized torus cell.  This leaf performs
that dilation on actual L² classes and their distributional derivatives.  It
does not assume classical derivatives of the row.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform LineDeriv
open scoped ENNReal SchwartzMap
open JanetCartan.Pseudodifferential

namespace JanetCartan.AmplitudeBound.RowCoefficients

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Fixed nonzero physical dilation preserves L²; the input is the original
row class in `app:ch_osc:eq:amplitude-row`. -/
theorem memLp_dilate {L : ℝ} (hL : L ≠ 0) (u : L²) :
    MemLp (fun x ↦ u (L • x)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume hL))).mpr
  exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp
    (Lp.memLp u)).comp_smul hL

/-- The literal dilated row, before taking its torus Fourier coefficients
in `app:ch_osc:eq:amplitude-row`. -/
def dilateL2 (L : ℝ) (hL : L ≠ 0) (u : L²) : L² :=
  (memLp_dilate hL u).toLp _

/-- The dilation represents the pointwise change of variables used in the
Section 7 row Fourier series. -/
theorem dilateL2_coe (L : ℝ) (hL : L ≠ 0) (u : L²) :
    dilateL2 L hL u =ᵐ[volume] fun x ↦ u (L • x) :=
  (memLp_dilate hL u).coeFn_toLp

private theorem norm_sq_eq_integral (u : L²) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The fixed enlargement of the box contracts the underlying L² norm;
all derivative powers are kept separately in `app:ch_osc:eq:amplitude-row`. -/
theorem norm_dilateL2_le {L : ℝ} (hL : 1 ≤ L) (u : L²) :
    ‖dilateL2 L (ne_of_gt (lt_of_lt_of_le zero_lt_one hL)) u‖ ≤ ‖u‖ := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have he : ‖dilateL2 L hL0.ne' u‖ ^ 2 = (L ^ d)⁻¹ * ‖u‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    calc
      _ = ∫ x, ‖u (L • x)‖ ^ 2 := integral_congr_ae
        ((dilateL2_coe L hL0.ne' u).mono (fun _ h ↦ by rw [h]))
      _ = (L ^ d)⁻¹ * ‖u‖ ^ 2 := by
        rw [Measure.integral_comp_smul_of_nonneg volume (fun x : E ↦ ‖u x‖ ^ 2) L (hR := hL0.le),
          finrank_euclideanSpace_fin, ← norm_sq_eq_integral]
        rfl
  have hp : (L ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have hb := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖u‖)
  nlinarith [norm_nonneg (dilateL2 L hL0.ne' u), norm_nonneg u]

private def inverseDilation (L : ℝ) (hL : L ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 L⁻¹ (inv_ne_zero hL))

private theorem inverseDilation_apply (L : ℝ) (hL : L ≠ 0) (x : E) :
    inverseDilation L hL x = L⁻¹ • x := rfl

private theorem dilateL2_pairing {L : ℝ} (hL : 0 < L) (u : L²)
    (ψ : 𝓢(E, ℂ)) :
    (dilateL2 L hL.ne' u : 𝓢'(E, ℂ)) ψ =
      (L ^ d)⁻¹ • (u : 𝓢'(E, ℂ))
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (inverseDilation L hL.ne') ψ) := by
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]
  calc
    _ = ∫ x, ψ x * u (L • x) := integral_congr_ae
      ((dilateL2_coe L hL.ne' u).mono (fun _ h ↦ by rw [h]))
    _ = ∫ x, (fun y : E ↦ ψ (L⁻¹ • y) * u y) (L • x) := by
      simp only [inv_smul_smul₀ hL.ne']
    _ = _ := by
      rw [Measure.integral_comp_smul_of_nonneg volume
        (fun y : E ↦ ψ (L⁻¹ • y) * u y) L (hR := hL.le),
        finrank_euclideanSpace_fin]
      rfl

/-- The actual weak derivative obeys the dilation chain rule.  In particular
the fixed rescaling in `app:ch_osc:eq:amplitude-row` uses no classical derivative
or additional regularity of the original row. -/
theorem hasEuclideanL2CoordinateDerivative_dilate {L : ℝ} (hL : 0 < L)
    {u v : L²} {i : Fin d} (h : HasEuclideanL2CoordinateDerivative i u v) :
    HasEuclideanL2CoordinateDerivative i (dilateL2 L hL.ne' u)
      ((L : ℂ) • dilateL2 L hL.ne' v) := by
  let e : E ≃L[ℝ] E := inverseDilation L hL.ne'
  let P : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  have hP (ψ : 𝓢(E, ℂ)) :
      lineDerivOp (EuclideanSpace.basisFun (Fin d) ℝ i) (P ψ) =
        L⁻¹ • P (lineDerivOp (EuclideanSpace.basisFun (Fin d) ℝ i) ψ) := by
    rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
    change P (lineDerivOp (L⁻¹ • EuclideanSpace.basisFun (Fin d) ℝ i) ψ) = _
    rw [lineDerivOp_left_smul, P.map_smul_of_tower]
  have hψ (ψ : 𝓢(E, ℂ)) :
      (v : 𝓢'(E, ℂ)) (P ψ) =
        -(L⁻¹ • (u : 𝓢'(E, ℂ))
          (P (lineDerivOp (EuclideanSpace.basisFun (Fin d) ℝ i) ψ))) := by
    rw [← h]
    simp only [euclideanCoordinateDerivative, TemperedDistribution.lineDerivOp_apply_apply,
      hP, map_neg]
    congr 1
    exact (u : 𝓢'(E, ℂ)).map_smul_of_tower L⁻¹ _
  unfold HasEuclideanL2CoordinateDerivative euclideanCoordinateDerivative
  ext ψ
  have hsmul : (((L : ℂ) • dilateL2 L hL.ne' v : L²) : 𝓢'(E, ℂ)) =
      (L : ℂ) • (dilateL2 L hL.ne' v : 𝓢'(E, ℂ)) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).map_smul _ _
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg, hsmul]
  simp only [smul_apply]
  rw [dilateL2_pairing hL, dilateL2_pairing hL]
  change -((L ^ d)⁻¹ • (u : 𝓢'(E, ℂ))
      (P (lineDerivOp (EuclideanSpace.basisFun (Fin d) ℝ i) ψ))) =
    (L : ℂ) • ((L ^ d)⁻¹ • (v : 𝓢'(E, ℂ)) (P ψ))
  rw [hψ]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  field_simp

private theorem weighted_smul_ae (s : ℝ) (c : ℂ) (u : L²) :
    weightedL2Fourier s (c • u) =ᵐ[volume] c • weightedL2Fourier s u := by
  have he : 𝓕 (c • u) = c • 𝓕 u := (fourierCLM ℂ L²).map_smul c u
  filter_upwards [Lp.coeFn_smul c (𝓕 u)] with x hx
  simp only [weightedL2Fourier, he, hx, Pi.smul_apply]
  exact smul_comm _ _ _

private theorem mem_smul {s : ℝ} {u : L²} (h : MemFourierSobolev s u) (c : ℂ) :
    MemFourierSobolev s (c • u) :=
  (h.const_smul c).ae_eq (weighted_smul_ae s c u).symm

private theorem norm_smul (s : ℝ) (c : ℂ) (u : L²) :
    fourierSobolevNorm s (c • u) = ‖c‖ * fourierSobolevNorm s u := by
  rw [fourierSobolevNorm, eLpNorm_congr_ae (weighted_smul_ae s c u),
    eLpNorm_const_smul, ENNReal.toReal_mul]
  simp [fourierSobolevNorm]

/-- Fixed physical dilation is bounded at every natural Fourier Sobolev
order, with that same order on the original row.  This supplies both the
single-row and the combined-position uses of
`app:ch_osc:lem:osc-amplitude`. -/
theorem fourierSobolev_dilate_nat {L : ℝ} (hL : 1 ≤ L) (s : ℕ)
    (u : L²) (hu : MemFourierSobolev (s : ℝ) u) :
    MemFourierSobolev (s : ℝ) (dilateL2 L (ne_of_gt (lt_of_lt_of_le zero_lt_one hL)) u) ∧
      fourierSobolevNorm (s : ℝ)
          (dilateL2 L (ne_of_gt (lt_of_lt_of_le zero_lt_one hL)) u) ≤
        (L * (1 + 2 * Real.pi * d)) ^ s * fourierSobolevNorm (s : ℝ) u := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  induction s generalizing u with
  | zero =>
    simpa only [Nat.cast_zero, memFourierSobolev_zero, fourierSobolevNorm_zero,
      pow_zero, one_mul, true_and] using norm_dilateL2_le hL u
  | succ s ih =>
    have hu' : MemFourierSobolev ((s : ℝ) + 1) u := by
      simpa only [Nat.cast_add, Nat.cast_one] using hu
    have hu0 : MemFourierSobolev (s : ℝ) u := hu'.mono (by linarith)
    obtain ⟨v, hv⟩ := hu'.exists_coordinateDerivatives (by positivity)
    obtain ⟨huD, hnuD⟩ := ih u hu0
    have hvD := fun i ↦ ih (v i) (hv i).2
    let w : Fin d → L² := fun i ↦ (L : ℂ) • dilateL2 L hL0.ne' (v i)
    have hw (i : Fin d) : HasEuclideanL2CoordinateDerivative i
        (dilateL2 L hL0.ne' u) (w i) :=
      hasEuclideanL2CoordinateDerivative_dilate hL0 (hv i).1
    have hwH (i : Fin d) : MemFourierSobolev (s : ℝ) (w i) :=
      mem_smul (hvD i).1 (L : ℂ)
    rw [Nat.cast_add, Nat.cast_one]
    refine ⟨huD.of_coordinateDerivatives (by positivity) hwH hw, ?_⟩
    let C : ℝ := L * (1 + 2 * Real.pi * d)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hwN (i : Fin d) : fourierSobolevNorm (s : ℝ) (w i) ≤
        L * (C ^ s * fourierSobolevNorm (s : ℝ) (v i)) := by
      calc
        _ = L * fourierSobolevNorm (s : ℝ) (dilateL2 L hL0.ne' (v i)) := by
          simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
            using norm_smul (s : ℝ) (L : ℂ) (dilateL2 L hL0.ne' (v i))
        _ ≤ _ := mul_le_mul_of_nonneg_left (hvD i).2 hL0.le
    have hbase : C ^ s * fourierSobolevNorm (s : ℝ) u ≤
        L * (C ^ s * fourierSobolevNorm (s : ℝ) u) :=
      le_mul_of_one_le_left (mul_nonneg (pow_nonneg hC _) (fourierSobolevNorm_nonneg _ _)) hL
    calc
      _ ≤ fourierSobolevNorm (s : ℝ) (dilateL2 L hL0.ne' u) +
          ∑ i, fourierSobolevNorm (s : ℝ) (w i) :=
        fourierSobolevNorm_le_coordinateDerivatives (by positivity) huD hwH hw
      _ ≤ C ^ s * fourierSobolevNorm (s : ℝ) u +
          ∑ i, L * (C ^ s * fourierSobolevNorm (s : ℝ) (v i)) :=
        add_le_add hnuD (Finset.sum_le_sum (fun i _ ↦ hwN i))
      _ ≤ L * (C ^ s * fourierSobolevNorm (s : ℝ) u) +
          ∑ i, L * (C ^ s * fourierSobolevNorm (s : ℝ) (v i)) :=
        add_le_add hbase le_rfl
      _ = L * C ^ s * (fourierSobolevNorm (s : ℝ) u +
          ∑ i, fourierSobolevNorm (s : ℝ) (v i)) := by
        simp only [mul_assoc, Finset.mul_sum, mul_add]
      _ ≤ L * C ^ s * ((1 + 2 * Real.pi * d) *
          fourierSobolevNorm ((s : ℝ) + 1) u) :=
        mul_le_mul_of_nonneg_left
          (fourierSobolevNorm_coordinateDerivatives_le (by positivity) hu' (fun i ↦ (hv i).1))
          (mul_nonneg hL0.le (pow_nonneg hC _))
      _ = _ := by dsimp [C]; rw [pow_succ]; ring

end JanetCartan.AmplitudeBound.RowCoefficients
