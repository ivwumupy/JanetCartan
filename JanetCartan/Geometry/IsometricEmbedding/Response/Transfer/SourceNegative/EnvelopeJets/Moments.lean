module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic

/-!
# Integrable Fourier moments of the source envelope

The Sobolev profile in `app:ch_response:eq:response-graded-source` controls the
absolute Fourier moments with the fixed loss `n + 1`. These are the inputs to
Fourier inversion and differentiation for the envelope jets used in the original
source estimate preceding `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.ResponseTransfer.SourceNegative

open Pseudodifferential

variable {n : ℕ}

/-- The fixed Cauchy–Schwarz constant for the Euclidean envelope embedding in
`app:ch_response:eq:response-graded-source`. -/
def envelopeMomentConstant (n : ℕ) : ℝ :=
  (eLpNorm (euclideanSobolevWeight (d := n) (-(n + 1 : ℕ) : ℝ)) 2 volume).toReal

/-- Nonnegativity of the constant used to extract Fourier moments from
`app:ch_response:eq:response-graded-source`. -/
theorem envelopeMomentConstant_nonneg (n : ℕ) : 0 ≤ envelopeMomentConstant n :=
  ENNReal.toReal_nonneg

/-- The reciprocal weight for the loss `n + 1` is genuinely in Lebesgue L²;
this is the integrability input to the envelope embedding in
`app:ch_response:eq:response-graded-source`. -/
theorem envelope_reciprocal_weight_memLp (n : ℕ) :
    MemLp (euclideanSobolevWeight (d := n) (-(n + 1 : ℕ) : ℝ)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (continuous_euclideanSobolevWeight _).aestronglyMeasurable).mpr
  have hi := integrable_rpow_neg_one_add_norm_sq
    (E := Euclidean n) (μ := volume) (r := 2 * (n + 1 : ℕ)) (by
      simp only [Euclidean, finrank_euclideanSpace_fin]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n])
  convert hi using 1
  funext ξ
  unfold euclideanSobolevWeight
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

/-- Polynomial moments are bounded by the Bessel weight with the same order,
retaining the Euclidean convention in `app:ch_response:eq:response-graded-source`. -/
theorem envelope_norm_pow_le_weight (r : ℕ) (ξ : Euclidean n) :
    ‖ξ‖ ^ r ≤ euclideanSobolevWeight (r : ℝ) ξ := by
  calc
    ‖ξ‖ ^ r = (‖ξ‖ ^ 2) ^ ((r : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

/-- The weighted pointwise majorant for extracting the `r`-th Fourier moment
from the single Sobolev order `r + n + 1` in
`app:ch_response:eq:response-graded-source`. -/
theorem envelope_moment_weight_le (r : ℕ) (ξ : Euclidean n) :
    ‖ξ‖ ^ r ≤ euclideanSobolevWeight (-(n + 1 : ℕ) : ℝ) ξ *
      euclideanSobolevWeight ((r + (n + 1) : ℕ) : ℝ) ξ := by
  rw [← euclideanSobolevWeight_add]
  have he : (-(n + 1 : ℕ) : ℝ) + ((r + (n + 1) : ℕ) : ℝ) = (r : ℝ) := by
    push_cast
    ring
  rw [he]
  exact envelope_norm_pow_le_weight r ξ

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cauchy–Schwarz extracts an actual absolute Fourier moment from one weighted
L² bound. The consumer is the envelope jet estimate for the original source
preceding `app:ch_response:eq:response-graded-reduced`. -/
theorem envelope_moment_integrable_and_le {g : Euclidean n → F}
    (hg : AEStronglyMeasurable g volume) (r : ℕ)
    (hw : MemLp (fun ξ ↦ euclideanSobolevWeight ((r + (n + 1) : ℕ) : ℝ) ξ • g ξ)
      2 volume) :
    Integrable (fun ξ ↦ ‖ξ‖ ^ r * ‖g ξ‖) volume ∧
      (∫ ξ, ‖ξ‖ ^ r * ‖g ξ‖) ≤ envelopeMomentConstant n *
        (eLpNorm (fun ξ ↦ euclideanSobolevWeight ((r + (n + 1) : ℕ) : ℝ) ξ • g ξ)
          2 volume).toReal := by
  let w := euclideanSobolevWeight (d := n) (-(n + 1 : ℕ) : ℝ)
  let v := fun ξ ↦ ‖euclideanSobolevWeight ((r + (n + 1) : ℕ) : ℝ) ξ • g ξ‖
  have hwm : MemLp w 2 volume := envelope_reciprocal_weight_memLp n
  have hvm : MemLp v 2 volume := hw.norm
  have hp : MemLp (w • v) 1 volume := hwm.smul hvm
  have hpi : Integrable (w • v) volume := memLp_one_iff_integrable.mp hp
  have hpnonneg (ξ : Euclidean n) : 0 ≤ (w • v) ξ := by
    exact mul_nonneg (euclideanSobolevWeight_pos _ _).le (norm_nonneg _)
  have hmajor (ξ : Euclidean n) : ‖ξ‖ ^ r * ‖g ξ‖ ≤ (w • v) ξ := by
    dsimp [w, v]
    rw [norm_smul, Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le]
    simpa only [smul_eq_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right (envelope_moment_weight_le r ξ) (norm_nonneg (g ξ))
  have hm : AEStronglyMeasurable (fun ξ ↦ ‖ξ‖ ^ r * ‖g ξ‖) volume :=
    ((continuous_norm.pow r).aestronglyMeasurable).mul hg.norm
  have hi : Integrable (fun ξ ↦ ‖ξ‖ ^ r * ‖g ξ‖) volume :=
    hpi.mono' hm (Filter.Eventually.of_forall fun ξ ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hmajor ξ)
  refine ⟨hi, ?_⟩
  calc
    (∫ ξ, ‖ξ‖ ^ r * ‖g ξ‖) ≤ ∫ ξ, ‖(w • v) ξ‖ := by
      apply integral_mono hi hpi.norm
      intro ξ
      dsimp only
      rw [Real.norm_of_nonneg (hpnonneg ξ)]
      exact hmajor ξ
    _ = (eLpNorm (w • v) 1 volume).toReal := by
      rw [integral_norm_eq_lintegral_enorm hp.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm hp.aestronglyMeasurable]
    _ ≤ (eLpNorm w 2 volume * eLpNorm v 2 volume).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hwm.eLpNorm_ne_top hvm.eLpNorm_ne_top)
        (eLpNorm_smul_le_mul_eLpNorm hwm.aestronglyMeasurable hvm.aestronglyMeasurable)
    _ = _ := by
      rw [ENNReal.toReal_mul, eLpNorm_norm _ hw.aestronglyMeasurable]
      rfl

end Normed

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {f : Euclidean n → F} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}

/-- Each absolute Fourier moment of the envelope is integrable, using only
Sobolev order `r + n + 1` from `app:ch_response:eq:response-graded-source`. -/
theorem SobolevEnvelopeBounds.fourier_moment_integrable
    (h : SobolevEnvelopeBounds f hf A K C) (r : ℕ) :
    Integrable (fun ξ ↦ ‖ξ‖ ^ r *
      ‖(𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) ξ‖) volume :=
  (envelope_moment_integrable_and_le (Lp.aestronglyMeasurable _) r
    (h.fourier_memLp (r + (n + 1)))).1

/-- The Fourier moment bound with a fixed loss, for the pointwise envelope jets
used before `app:ch_response:eq:response-graded-reduced`. -/
theorem SobolevEnvelopeBounds.fourier_moment_le
    (h : SobolevEnvelopeBounds f hf A K C) (r : ℕ) :
    (∫ ξ, ‖ξ‖ ^ r * ‖(𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) ξ‖) ≤
      envelopeMomentConstant n * C (r + (n + 1)) * A * K ^ (r + (n + 1)) := by
  have hb := (envelope_moment_integrable_and_le (Lp.aestronglyMeasurable _) r
    (h.fourier_memLp (r + (n + 1)))).2
  exact hb.trans ((mul_le_mul_of_nonneg_left (h.fourier_bound (r + (n + 1)))
    (envelopeMomentConstant_nonneg n)).trans_eq (by ring))

/-- The actual L² Fourier representative is in L¹ even when the envelope is
not, allowing inversion in `app:ch_response:eq:response-graded-source`. -/
theorem SobolevEnvelopeBounds.fourier_integrable
    (h : SobolevEnvelopeBounds f hf A K C) :
    Integrable (𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) volume := by
  apply (integrable_norm_iff (Lp.aestronglyMeasurable _)).mp
  simpa only [pow_zero, one_mul] using h.fourier_moment_integrable 0

end JanetCartan.ResponseTransfer.SourceNegative
