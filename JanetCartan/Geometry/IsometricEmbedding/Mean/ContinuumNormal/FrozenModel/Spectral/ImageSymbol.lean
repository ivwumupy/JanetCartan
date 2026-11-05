module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Detection

/-!
# The image summand in the frozen spectral gap

The literal image symbol of `app:ch_background:prop:bg-frame` is continuous,
uniformly bounded, and its quadratic form is the squared actual image channel
divided by `1 + |k|²`. Its radial monotonicity is the image part of extending
the compact-sphere gap to all sufficiently large frequencies.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers

variable {n : ℕ} (Q₀ : Fin n → MetricTensor n)

/-- Continuity of the actual image multiplier, including the origin
(`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem frozenImageSymbol_continuous : Continuous (frozenImageSymbol Q₀) := by
  have hp : Continuous (pencil Q₀) := (pencilContinuousLinearMap Q₀).continuous
  exact (((continuous_const (y := (1 : ℝ))).add (continuous_norm.pow 2)).inv₀
    (fun k ↦ by change (1 + ‖k‖ ^ 2 : ℝ) ≠ 0; positivity)).smul (hp.mul hp.matrix_transpose)

/-- A global frequency bound for the literal image multiplier follows from
linearity of the pencil and its Frobenius norm. This is the image input to
the finite frozen symbol bound (`app:ch_background:prop:bg-frame`). -/
theorem frozenImageSymbol_norm_le (k : Euclidean n) :
    ‖frozenImageSymbol Q₀ k‖ ≤ ‖pencilContinuousLinearMap Q₀‖ ^ 2 := by
  have hd : 0 < 1 + ‖k‖ ^ 2 := by positivity
  have hp := (pencilContinuousLinearMap Q₀).le_opNorm k
  change ‖pencil Q₀ k‖ ≤ ‖pencilContinuousLinearMap Q₀‖ * ‖k‖ at hp
  have hs : ‖pencil Q₀ k‖ ^ 2 ≤ ‖pencilContinuousLinearMap Q₀‖ ^ 2 * ‖k‖ ^ 2 := by
    nlinarith [norm_nonneg (pencil Q₀ k), norm_nonneg (pencilContinuousLinearMap Q₀),
      norm_nonneg k]
  rw [frozenImageSymbol, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hd.le)]
  calc
    _ ≤ (1 + ‖k‖ ^ 2)⁻¹ * (‖pencil Q₀ k‖ * ‖(pencil Q₀ k).transpose‖) :=
      mul_le_mul_of_nonneg_left (frobenius_norm_mul _ _) (inv_nonneg.mpr hd.le)
    _ = ‖pencil Q₀ k‖ ^ 2 / (1 + ‖k‖ ^ 2) := by
      rw [frobenius_norm_transpose]; ring
    _ ≤ ‖pencilContinuousLinearMap Q₀‖ ^ 2 := (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg ‖pencilContinuousLinearMap Q₀‖])

/-- The quadratic form of the image summand is exactly the original image
detector energy with its Bessel denominator
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`). -/
theorem frozenImageSymbol_quadratic (k s : Euclidean n) :
    dotProduct (fun i ↦ s i) (frozenImageSymbol Q₀ k *ᵥ (fun i ↦ s i)) =
      ‖ActualCarriers.imageChannel (pencil Q₀ k) s‖ ^ 2 / (1 + ‖k‖ ^ 2) := by
  simp only [frozenImageSymbol, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [← mulVec_mulVec, dotProduct_mulVec]
  have he : (fun i ↦ s i) ᵥ* pencil Q₀ k = (pencil Q₀ k).transpose *ᵥ (fun i ↦ s i) := by
    rw [← vecMul_transpose, transpose_transpose]
  rw [he, EuclideanSpace.real_norm_sq_eq (ActualCarriers.imageChannel (pencil Q₀ k) s)]
  simp only [ActualCarriers.imageChannel, PiLp.toLp_apply, dotProduct, pow_two]
  ring

/-- Zero image energy annihilates the actual image detector; the denominator
is strictly positive at every frequency (`app:ch_background:prop:bg-frame`). -/
theorem frozenImageSymbol_quadratic_eq_zero_iff (k s : Euclidean n) :
    dotProduct (fun i ↦ s i) (frozenImageSymbol Q₀ k *ᵥ (fun i ↦ s i)) = 0 ↔
      ActualCarriers.imageChannel (pencil Q₀ k) s = 0 := by
  rw [frozenImageSymbol_quadratic, div_eq_zero_iff]
  have hd : (1 + ‖k‖ ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [hd, or_false, sq_eq_zero_iff, norm_eq_zero]

/-- Radially increasing frequency cannot decrease the image energy. This
preserves the exact Bessel factor when extending the compact-sphere gap
(`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem frozenImageSymbol_quadratic_smul_mono {t : ℝ} (ht : 1 ≤ t) (k s : Euclidean n) :
    dotProduct (fun i ↦ s i) (frozenImageSymbol Q₀ k *ᵥ (fun i ↦ s i)) ≤
      dotProduct (fun i ↦ s i) (frozenImageSymbol Q₀ (t • k) *ᵥ (fun i ↦ s i)) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hp : pencil Q₀ (t • k) = t • pencil Q₀ k :=
    (pencilContinuousLinearMap Q₀).map_smul t k
  have hi : ActualCarriers.imageChannel (pencil Q₀ (t • k)) s =
      t • ActualCarriers.imageChannel (pencil Q₀ k) s := by
    ext i
    simp [ActualCarriers.imageChannel, hp, Matrix.smul_mulVec]
  rw [frozenImageSymbol_quadratic, frozenImageSymbol_quadratic, hi]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, mul_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hs := sq_nonneg ‖ActualCarriers.imageChannel (pencil Q₀ k) s‖
  nlinarith [mul_nonneg (show 0 ≤ t ^ 2 - 1 by nlinarith) hs]

end JanetCartan.ContinuumNormal.FrozenModel
