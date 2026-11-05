module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.ReverseFrequency

/-!
# Fourier test pairings of the literal reversed triangle

Physical Fourier duality and Schwartz decay identify the uncut reversed
triangle in all test pairings. The conjugate multiplier stays outside the
time triangle and the source mask stays outside the multiplier. Source:
`app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

private theorem physicalFourier_pairing (f : SchwartzMap E V) (W : E → V)
    (hW : Continuous W) (hWi : Integrable W) :
    (∫ x, inner ℂ (WithLp.toLp 2 (f x)) (WithLp.toLp 2
      (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • W ξ))) =
      ∫ ξ, inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform f ξ))
        (WithLp.toLp 2 (W ξ)) := by
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)).symm
  let K := fun x ξ ↦ inner ℂ (L (f x))
    (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • L (W ξ))
  have hfi : Integrable (fun x ↦ L (f x)) := L.toContinuousLinearMap.integrable_comp f.integrable
  have hwi : Integrable (fun x ↦ L (W x)) := L.toContinuousLinearMap.integrable_comp hWi
  have hmod (x : E) : Integrable (fun ξ ↦
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • L (W ξ)) := by
    apply hwi.norm.mono' (by fun_prop : Continuous _).aestronglyMeasurable
    filter_upwards [] with ξ
    simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hK : Integrable (Function.uncurry K) := by
    apply (hfi.norm.mul_prod hwi.norm).mono' (by fun_prop : Continuous _).aestronglyMeasurable
    filter_upwards [] with p
    exact (norm_inner_le_norm _ _).trans_eq (by
      simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul])
  calc
    _ = ∫ x, ∫ ξ, K x ξ := by
      apply integral_congr_ae
      filter_upwards [] with x
      have he := L.integral_comp_comm (μ := volume)
        (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • W ξ)
      simp only [map_smul] at he
      change inner ℂ (L (f x)) (L _) = _
      rw [← he, ← integral_inner (hmod x)]
    _ = ∫ ξ, ∫ x, K x ξ := integral_integral_swap hK
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      have hi : Integrable (fun x ↦ Complex.exp (Complex.I * (-(inner ℝ x ξ) : ℝ)) • L (f x)) := by
        apply hfi.norm.mono' (by fun_prop : Continuous _).aestronglyMeasurable
        filter_upwards [] with x
        simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
      have he := ((innerSL ℂ).flip (L (W ξ))).integral_comp_commSL RCLike.conj_smul hi
      change (∫ x, inner ℂ (Complex.exp (Complex.I * (-(inner ℝ x ξ) : ℝ)) • L (f x))
        (L (W ξ))) = inner ℂ (∫ x, Complex.exp (Complex.I * (-(inner ℝ x ξ) : ℝ)) • L (f x))
          (L (W ξ)) at he
      have hphase (x : E) : (starRingEnd ℂ)
          (Complex.exp (Complex.I * (-(inner ℝ x ξ) : ℝ))) =
          Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) := by
        rw [← Complex.exp_conj]
        congr 1
        simp
      simp only [inner_smul_left, hphase] at he
      change (∫ x, K x ξ) = inner ℂ (L (sourceInputFourierTransform f ξ)) (L (W ξ))
      rw [sourceInputFourierTransform_eq_integral, ← L.integral_comp_comm]
      simpa only [K, inner_smul_right, map_smul] using he

/-- Fourier duality for the actual compact reversed triangle. Its physical
normalization is retained; `hW` is supplied by
`continuous_reverseRetardedFrequency`. Consumer: cutoff removal for the
Hilbert-adjoint pairing in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem cutReverseRetardedFourier_pairing
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hθ : Continuous θ) (hθcs : HasCompactSupport θ)
    (a c : ℝ) (u v : graphTestSpace (d + 1) q)
    (hW : Continuous (reverseRetardedFrequency Ψ b χout β (fun x ↦ (u.val x).ofLp) a c)) :
    (∫ x, inner ℂ (v.val x) (WithLp.toLp 2
      (cutReverseRetardedFourier Ψ b χout χsource β θ
        (fun x ↦ (u.val x).ofLp) a c x))) =
      ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ * ∫ ξ,
        inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
          (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
          (WithLp.toLp 2 (star (θ ξ) •
            reverseRetardedFrequency Ψ b χout β (fun x ↦ (u.val x).ofLp) a c ξ)) := by
  let W := fun ξ ↦ star (θ ξ) •
    reverseRetardedFrequency Ψ b χout β (fun x ↦ (u.val x).ofLp) a c ξ
  have hWc : Continuous W := hθ.star.smul hW
  have hWi : Integrable W := hWc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hθcs (fun ξ hξ ↦ by
      simp [W, image_eq_zero_of_notMem_tsupport hξ]))
  have he (x : E) : cutReverseRetardedFourier Ψ b χout χsource β θ
      (fun x ↦ (u.val x).ofLp) a c x = star (χsource x) •
        (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
          ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • W ξ) := by
    unfold cutReverseRetardedFourier
    congr 2
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [W, reverseRetardedFrequency, star_mul, smul_smul]
    congr 1
    ring
  simp_rw [he, WithLp.toLp_smul, inner_smul_right]
  let f := graphTestToSchwartz (complexSourceMaskTest χsource hs v)
  have hf (x : E) : WithLp.toLp 2 (f x) = χsource x • v.val x := by
    simp [f, complexSourceMaskTest]
  calc
    _ = ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ *
        ∫ x, inner ℂ (WithLp.toLp 2 (f x))
          (WithLp.toLp 2 (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • W ξ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hf, inner_smul_left]
      change star (χsource x) * (_ * _) = _ * (star (χsource x) * _)
      ring
    _ = _ := by
      simpa only [f, W, WithLp.toLp_smul, inner_smul_right] using
        congrArg (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ * ·)
          (physicalFourier_pairing f W hWc hWi)

/-- A continuous bounded reversed frequency datum has absolutely integrable
Schwartz test pairings, and the physical cutoffs can be removed in those
pairings. The exact producers of `hW` and `hbound` are
`continuous_reverseRetardedFrequency` and `exists_bound_reverseRetardedFrequency`.
Consumer: the original Hilbert adjoint in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem integrable_and_tendsto_reverseFrequency_pairing
    (f : SchwartzMap E V) (W : E → V) (hW : Continuous W)
    (B : ℝ) (hbound : ∀ ξ, ‖W ξ‖ ≤ B) :
    Integrable (fun ξ ↦ inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform f ξ))
      (WithLp.toLp 2 (W ξ))) ∧
    Tendsto (fun j ↦ ∫ ξ, inner ℂ
      (WithLp.toLp 2 (sourceInputFourierTransform f ξ))
      (WithLp.toLp 2 (star (complexPhysicalCutoff j ξ) • W ξ))) atTop
      (𝓝 (∫ ξ, inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform f ξ))
        (WithLp.toLp 2 (W ξ)))) := by
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)).symm.toContinuousLinearMap
  let g := fun ξ ↦ inner ℂ (L (sourceInputFourierTransform f ξ)) (L (W ξ))
  have hfi : Integrable (fun ξ ↦ L (sourceInputFourierTransform f ξ)) :=
    L.integrable_comp (sourceInputFourierTransform f).integrable
  have hg : Integrable g := by
    apply (hfi.norm.mul_const (‖L‖ * B)).mono' (by fun_prop : Continuous g).aestronglyMeasurable
    filter_upwards [] with ξ
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound ξ) (norm_nonneg _)))
      (norm_nonneg _))
  refine ⟨hg, ?_⟩
  simp only [WithLp.toLp_smul, inner_smul_right]
  change Tendsto (fun j ↦ ∫ ξ, star (complexPhysicalCutoff j ξ) * g ξ) atTop (𝓝 (∫ ξ, g ξ))
  apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖g ξ‖)
  · intro j
    exact ((complexPhysicalCutoff_contDiff j).continuous.star.mul
      (by fun_prop : Continuous g)).aestronglyMeasurable
  · exact hg.norm
  · intro j
    filter_upwards [] with ξ
    simpa only [norm_mul, norm_star, one_mul] using
      mul_le_mul_of_nonneg_right (complexPhysicalCutoff_norm_le j ξ) (norm_nonneg (g ξ))
  · filter_upwards [] with ξ
    simpa only [star_one, one_mul] using
      (complexPhysicalCutoff_tendsto ξ).star.mul_const (g ξ)

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
