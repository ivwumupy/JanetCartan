module

public import JanetCartan.Probability.OperatorCompression.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Variance under orthogonal compression

Quadratic-form versions of the variance comparison in
`app:ch_waves:thm:sampling` of `paper.tex`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace JanetCartan.OperatorCompression

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Compression preserves self-adjointness (`app:ch_waves:thm:sampling`). -/
theorem isSelfAdjoint_compress (P T : H →L[𝕜] H)
    (hP : IsSelfAdjoint P) (hT : IsSelfAdjoint T) : IsSelfAdjoint (compress P T) := by
  simpa only [compress, hP.adjoint_eq] using hT.conj_adjoint P

omit [CompleteSpace H] in
/-- Compression by a contraction decreases the operator norm
(`app:ch_waves:thm:sampling`). -/
theorem norm_compress_le (P T : H →L[𝕜] H) (hP : ‖P‖ ≤ 1) :
    ‖compress P T‖ ≤ ‖T‖ := by
  calc
    ‖compress P T‖ ≤ ‖P‖ * ‖T ∘L P‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T ∘L P‖ := mul_le_of_le_one_left (norm_nonneg _) hP
    _ ≤ ‖T‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ := mul_le_of_le_one_right (norm_nonneg _) hP

/-- The quadratic form of `PTP` is the quadratic form of `T` at `Px`
(`app:ch_waves:thm:sampling`). -/
theorem inner_compress (P T : H →L[𝕜] H) (hP : IsSelfAdjoint P) (x : H) :
    ⟪x, compress P T x⟫_𝕜 = ⟪P x, T (P x)⟫_𝕜 := by
  change ⟪x, P (T (P x))⟫_𝕜 = _
  rw [← hP.adjoint_eq, ContinuousLinearMap.adjoint_inner_right, hP.adjoint_eq]

/-- A self-adjoint square has quadratic form equal to a squared norm
(`app:ch_waves:thm:sampling`). -/
theorem re_inner_square (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) (x : H) :
    RCLike.re ⟪x, (T ∘L T) x⟫_𝕜 = ‖T x‖ ^ 2 := by
  simpa only [hT.adjoint_eq] using (T.apply_norm_sq_eq_inner_adjoint_right x).symm

/-- The pointwise variance inequality `(PYP)² ≤ PY²P`, in quadratic-form order.
It is the algebraic compression step in `app:ch_waves:thm:sampling`. -/
theorem re_inner_compress_square_le (P Y : H →L[𝕜] H)
    (hP : IsSelfAdjoint P) (hPn : ‖P‖ ≤ 1) (hY : IsSelfAdjoint Y) (x : H) :
    RCLike.re ⟪x, (compress P Y ∘L compress P Y) x⟫_𝕜 ≤
      RCLike.re ⟪x, compress P (Y ∘L Y) x⟫_𝕜 := by
  rw [re_inner_square _ (isSelfAdjoint_compress P Y hP hY), inner_compress P _ hP,
    re_inner_square Y hY]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (P.le_opNorm (Y (P x))).trans
    (mul_le_of_le_one_left (norm_nonneg _) hPn)

/-- Variance domination survives compression, expressed as scalar second moments.
This is exactly the quadratic-form meaning of `V_compressed ≤ PVP` in
`app:ch_waves:thm:sampling`. Only the uncompressed scalar second moments need
integrability for this inequality. -/
theorem sum_integral_compress_variance_le
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι)
    (Y : ι → Ω → H →L[𝕜] H) (P V : H →L[𝕜] H)
    (hP : IsSelfAdjoint P) (hPn : ‖P‖ ≤ 1)
    (hint : ∀ i ∈ s, ∀ x, Integrable (fun ω ↦ ‖Y i ω x‖ ^ 2) μ)
    (hV : ∀ x, ∑ i ∈ s, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ ≤ RCLike.re ⟪x, V x⟫_𝕜)
    (x : H) :
    ∑ i ∈ s, ∫ ω, ‖compress P (Y i ω) x‖ ^ 2 ∂μ ≤
      RCLike.re ⟪x, compress P V x⟫_𝕜 := by
  rw [inner_compress P V hP]
  refine (Finset.sum_le_sum (fun i hi ↦ ?_)).trans (hV (P x))
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (hint i hi (P x))
  apply Filter.Eventually.of_forall
  intro ω
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (P.le_opNorm (Y i ω (P x))).trans
    (mul_le_of_le_one_left (norm_nonneg _) hPn)

end JanetCartan.OperatorCompression
