module

public import JanetCartan.Analysis.PhysicalCutoff.Tail
public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised
import JanetCartan.Analysis.Fourier.Conventions.PhysicalSobolev
import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.EnvelopeJets.InverseJets
import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.EnvelopeJets.Moments

/-!
# The physical Sobolev bound at the revised baseline order

Paper-v2, §15, `new:lem:bernstein`(i) and Steps 5–6 of `main:thm:step` use
`m₀ = ⌊n/2⌋+2`, not the larger envelope reserve `n+1`. For one derivative,
`⟨ξ⟩^{1-m₀}` is genuinely in physical frequency L² since `2(m₀-1)>n`.
Cauchy–Schwarz and Fourier inversion give the pointwise estimate on the
original real vector-valued field. The high norm is the *actual* radian
weighted norm used by `PhysicalCutoff`, not a parameter or an assumed bound
for the derivatives. The constants depend only on the source dimension.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalSobolev

open PhysicalCutoff Pseudodifferential RevisedScales

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "F" => EuclideanSpace ℂ (Fin N)

/-- A fixed dimension-only constant for the first two pointwise jets in
`new:lem:bernstein`(i). The inverse Fourier derivative costs at most `2π`;
the reciprocal Bessel weight is in genuine L² at precisely the revised order. -/
def embeddingConstant (n : ℕ) : ℝ :=
  (2 * Real.pi) * (eLpNorm (euclideanSobolevWeight (d := n) (1 - (baselineOrder n : ℝ)))
    2 volume).toReal

/-- Nonnegativity of the constant consumed by the physical cutoff step. -/
theorem embeddingConstant_nonneg (n : ℕ) : 0 ≤ embeddingConstant n :=
  mul_nonneg (by positivity) ENNReal.toReal_nonneg

private theorem reciprocal_memLp (n : ℕ) :
    MemLp (euclideanSobolevWeight (d := n) (1 - (baselineOrder n : ℝ))) 2 volume := by
  apply (memLp_two_iff_integrable_sq (continuous_euclideanSobolevWeight _).aestronglyMeasurable).mpr
  have hn : n + 2 < 2 * baselineOrder n := by unfold baselineOrder; omega
  have hn' : (n : ℝ) + 2 < 2 * (baselineOrder n : ℝ) := by exact_mod_cast hn
  have hi := integrable_rpow_neg_one_add_norm_sq («E» := EuclideanSpace ℝ (Fin n)) (μ := volume)
    (r := 2 * ((baselineOrder n : ℝ) - 1)) (by rw [finrank_euclideanSpace_fin]; linarith)
  convert hi using 1
  funext ξ
  unfold euclideanSobolevWeight
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

-- For r=0,1, use the SAME radian m₀ norm. The auxiliary reciprocal weight
-- is taken at ξ (unit frequency), which only enlarges the final constant.
private theorem moment_le (u : 𝓢(E, V)) (r : ℕ) (hr : r ≤ 1) :
    (∫ ξ : E, ‖ξ‖ ^ r * ‖𝓕 (complexify u) ξ‖) ≤
      (eLpNorm (euclideanSobolevWeight (d := n) (1 - (baselineOrder n : ℝ))) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
  let m : ℝ := baselineOrder n
  let w := euclideanSobolevWeight (d := n) (1 - m)
  let g : 𝓢(E, F) := 𝓕 (complexify u)
  let v (ξ : E) := euclideanSobolevWeight m ((2 * Real.pi) • ξ) • g ξ
  have hw : MemLp w 2 volume := reciprocal_memLp n
  have hv : MemLp v 2 volume := memLp_physicalWeightedFourier m u
  have hp : MemLp (w • v) 1 volume := hw.smul hv
  have hpow (ξ : E) : ‖ξ‖ ^ r ≤ w ξ * euclideanSobolevWeight m ((2 * Real.pi) • ξ) := by
    calc
      ‖ξ‖ ^ r ≤ euclideanSobolevWeight (r : ℝ) ξ :=
        ResponseTransfer.SourceNegative.envelope_norm_pow_le_weight r ξ
      _ ≤ euclideanSobolevWeight 1 ξ := euclideanSobolevWeight_mono (by exact_mod_cast hr) ξ
      _ = w ξ * euclideanSobolevWeight m ξ := by
        rw [show (1 : ℝ) = (1 - m) + m by ring, euclideanSobolevWeight_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (FourierConventions.euclideanSobolevWeight_le_physical (baselineOrder n) ξ)
        (euclideanSobolevWeight_pos _ _).le
  calc
    _ ≤ ∫ ξ : E, ‖(w • v) ξ‖ := by
      apply integral_mono (g.integrable_pow_mul volume r) (memLp_one_iff_integrable.mp hp).norm
      intro ξ
      change ‖ξ‖ ^ r * ‖g ξ‖ ≤ ‖w ξ • (euclideanSobolevWeight m ((2 * Real.pi) • ξ) • g ξ)‖
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le,
        Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hpow ξ) (norm_nonneg _)
    _ = (eLpNorm (w • v) 1 volume).toReal := by
      rw [integral_norm_eq_lintegral_enorm hp.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm hp.aestronglyMeasurable]
    _ ≤ (eLpNorm w 2 volume * eLpNorm v 2 volume).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hw.eLpNorm_ne_top hv.eLpNorm_ne_top)
        (eLpNorm_smul_le_mul_eLpNorm hw.aestronglyMeasurable hv.aestronglyMeasurable)
    _ = _ := ENNReal.toReal_mul

private theorem jet_le (u : 𝓢(E, V)) (r : ℕ) (hr : r ≤ 1) (x : E) :
    ‖iteratedFDeriv ℝ r (u : E → V) x‖ ≤ embeddingConstant n *
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
  let g : 𝓢(E, F) := 𝓕 (complexify u)
  have hinv : 𝓕⁻ (g : E → F) = (complexify u : E → F) := by
    rw [← SchwartzMap.fourierInv_coe]
    exact congrArg (fun f : 𝓢(E, F) ↦ (f : E → F)) (fourierInv_fourier_eq (complexify u))
  let L : V →ₗᵢ[ℝ] F := ⟨euclideanComplexInclusion.toLinearMap, euclideanComplexInclusion_norm⟩
  have hiso : ‖iteratedFDeriv ℝ r (complexify u : E → F) x‖ = ‖iteratedFDeriv ℝ r (u : E → V) x‖ :=
    L.norm_iteratedFDeriv_comp_left (u.smooth ⊤).contDiffAt (by simp)
  have hjet := ResponseTransfer.SourceNegative.norm_iteratedFDeriv_fourierInv_le_moment
    (g : E → F) r g.continuous.aestronglyMeasurable (fun d _ ↦ g.integrable_pow_mul volume d) x
  rw [hinv, hiso] at hjet
  have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hp : (2 * Real.pi) ^ r ≤ 2 * Real.pi := by simpa only [pow_one] using pow_le_pow_right₀ hπ hr
  refine hjet.trans ((mul_le_mul_of_nonneg_left (moment_le u r hr) (by positivity)).trans ?_)
  rw [← mul_assoc, embeddingConstant]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg

/-- Pointwise order zero of the physical `H^{m₀} → C¹` estimate, on the
original real global Schwartz representative (`new:lem:bernstein`(i)). -/
theorem norm_le (u : 𝓢(E, V)) (x : E) :
    ‖u x‖ ≤ embeddingConstant n *
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
  simpa only [norm_iteratedFDeriv_zero] using jet_le u 0 (by decide) x

/-- The actual global derivative in `new:lem:bernstein`(i) is bounded by the
original physical `H^{⌊n/2⌋+2}` norm, before choosing any accuracy or cutoff.
There is no output-dimension, derivative-tail, or band-support hypothesis. -/
theorem norm_fderiv_le (u : 𝓢(E, V)) (x : E) :
    ‖fderiv ℝ (u : E → V) x‖ ≤ embeddingConstant n *
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
  simpa only [norm_iteratedFDeriv_one] using jet_le u 1 le_rfl x

end JanetCartan.PhysicalSobolev
