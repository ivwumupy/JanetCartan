module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Dilation.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CompactFamily
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Star.Real

/-!
# Weighted carrier means under dilation

The finite sum of carrier integrals in `app:ch_background:prop:bg-normalized`,
its positivity, and its exact dilation identity. The `C^s` estimate is conditional
on smoothness of the unscaled mean. This file does not construct the actual
Hamilton phases or null transports, or prove their analytic estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {n : ℕ}

/-- Integrating an integrable positive semidefinite matrix field preserves
positivity, as used for `H₀` in `app:ch_background:prop:bg-normalized`.
The integral is expressed entrywise, independently of any matrix norm. -/
theorem posSemidef_integral_entries {f : Z → MetricTensor n}
    (hf : ∀ i j, Integrable (fun z ↦ f z i j) μ)
    (hpos : ∀ z, (f z).PosSemidef) :
    Matrix.PosSemidef (fun i j ↦ ∫ z, f z i j ∂μ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ by simpa using (hpos z).isHermitian.apply i j
  · intro v
    have hint (i j : Fin n) : Integrable (fun z ↦ v i * (f z i j * v j)) μ :=
      ((hf i j).mul_const _).const_mul _
    have hsum (i : Fin n) : Integrable (fun z ↦ ∑ j, v i * (f z i j * v j)) μ :=
      integrable_finsetSum _ (fun j _ ↦ hint i j)
    have heq : v ⬝ᵥ ((fun i j ↦ ∫ z, f z i j ∂μ) *ᵥ v) =
        ∫ z, v ⬝ᵥ (f z *ᵥ v) ∂μ := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ ↦ hsum i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
      simp only [integral_const_mul, integral_mul_const]
    simp only [star_trivial]
    rw [heq]
    exact integral_nonneg fun z ↦ by simpa using (hpos z).dotProduct_mulVec_nonneg v

variable {A E F : Type*} [Fintype A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- The fixed-weight carrier mean `∑ₐ ∫ wₐ |νₐ|² ξₐ ⊗ ξₐ`
of `app:ch_background:prop:bg-normalized`. Each carrier chart may have its own
measure. Spatial and carrier arguments are kept separate. -/
def carrierMean (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n) (x : E) : MetricTensor n :=
  ∑ a, fun i j ↦ ∫ z, w a z * ‖ν a (x, z)‖ ^ 2 *
    (ξ a (x, z) i * ξ a (x, z) j) ∂μ a

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Positivity of the actual weighted integral expression, requiring only
nonnegative weights and integrable entries
(`app:ch_background:prop:bg-normalized`). -/
theorem carrierMean_posSemidef (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n) (x : E)
    (hw : ∀ a z, 0 ≤ w a z)
    (hi : ∀ a i j, Integrable (fun z ↦ w a z * ‖ν a (x, z)‖ ^ 2 *
      (ξ a (x, z) i * ξ a (x, z) j)) (μ a)) :
    (carrierMean μ w ν ξ x).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro a _
  apply posSemidef_integral_entries (hi a)
  intro z
  have hξ := Matrix.posSemidef_vecMulVec_self_star (fun i ↦ ξ a (x, z) i)
  convert! hξ.smul (mul_nonneg (hw a z) (sq_nonneg ‖ν a (x, z)‖)) using 1

/-- The normalized mean, computed using the regular coefficient pullbacks in
`app:ch_background:eq:bg-Nsigma`. Its value at zero is algebraic. -/
def normalizedCarrierMean (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n) (σ : ℝ) (x : E) :
    MetricTensor n :=
  carrierMean μ w (fun a p ↦ normalizedPullback (ν a) (σ, p))
    (fun a p ↦ normalizedPullback (ξ a) (σ, p)) x

/-- Exact identity `Hσ(x) = Ĥ(σx)` for the integral mean
(`app:ch_background:eq:bg-Hsigma`). No change of the carrier measure occurs. -/
theorem normalizedCarrierMean_eq_dilation (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n) (σ : ℝ) (x : E) :
    normalizedCarrierMean μ w ν ξ σ x = carrierMean μ w ν ξ (σ • x) := rfl

/-- The algebraic limiting mean is constant in space
(`app:ch_background:prop:bg-normalized`). -/
@[simp] theorem normalizedCarrierMean_zero (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n) (x : E) :
    normalizedCarrierMean μ w ν ξ 0 x = carrierMean μ w ν ξ 0 := by
  simp [normalizedCarrierMean_eq_dilation]

/-- Nonnegativity of the constant algebraic limit
(`app:ch_background:prop:bg-normalized`). This says nothing about the normal
rank of an immersion at zero scale. -/
theorem normalizedCarrierMean_zero_posSemidef (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n) (x : E)
    (hw : ∀ a z, 0 ≤ w a z)
    (hi : ∀ a i j, Integrable (fun z ↦ w a z * ‖ν a (0, z)‖ ^ 2 *
      (ξ a (0, z) i * ξ a (0, z) j)) (μ a)) :
    (normalizedCarrierMean μ w ν ξ 0 x).PosSemidef := by
  rw [normalizedCarrierMean_zero]
  exact carrierMean_posSemidef μ w ν ξ 0 hw hi

/-- Conditional analytic step of `app:ch_background:eq:bg-Hsigma`: smoothness
of the unscaled mean implies the `O(σ)` estimate at every fixed spatial order,
with the project's `cNorm` and Frobenius matrix norm. Smoothness of the actual
transported mean must be supplied by the carrier construction. -/
theorem exists_cNorm_normalizedCarrierMean_sub_zero_bound
    (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n)
    {K : Set E} (hK : IsCompact K) (hH : ContDiff ℝ ∞ (carrierMean μ w ν ξ)) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (0 : ℝ) 1,
      cNorm K s (fun x ↦ normalizedCarrierMean μ w ν ξ σ x -
        normalizedCarrierMean μ w ν ξ 0 x) ≤ C * σ := by
  simpa only [normalizedCarrierMean_eq_dilation, zero_smul] using
    exists_cNorm_dilation_sub_const_bound hK hH s

end JanetCartan.NormalizedBackground
