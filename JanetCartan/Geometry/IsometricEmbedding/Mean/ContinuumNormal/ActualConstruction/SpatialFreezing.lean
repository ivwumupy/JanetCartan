module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.SpatialFreezing.Scalar

/-!
# Matrix and real-torus full-amplitude freezing

The checked scalar estimate supplies the literal matrix PDO and then its real
periodic compression. The origin-vanishing condition concerns BOTH physical
positions. All measures, Fourier conventions and real quadratures remain those
of the existing operators. `DensityFreezing` instantiates this condition on the
actual divided-footpoint density and the frozen-label reference; uniform
primitive bounds and same-row carrier realizations remain producer obligations.
Sources: `app:ch_background:prop:bg-frame`, Step 3; `bg-local-bound`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace NNReal Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.ActualConstruction
open Pseudodifferential AmplitudeBound
variable {n : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (2 * n)

/-- The two-position spatial freezing estimate for the literal matrix PDO.
Its constant precedes the full amplitude and support radius. Finite-coordinate
isometries preserve the Euclidean Lebesgue L² pairing and contribute only the
fixed matrix-size factor. Consumer: the real normalized normal comparison
(`app:ch_background:prop:bg-frame`, Step 3; `bg-local-bound`). -/
theorem exists_matrix_fullAmplitude_small_support_constant
    (hn : 0 < n) (R : ℝ) (θ : P → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθs : HasCompactSupport θ) (hθbox : ∀ z, θ z ≠ 0 → ∀ j, |z j| ≤ R)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχθ : ∀ x y, θ (pairedPosition x y) ≠ 0 → χ x = 1 ∧ χ y = 1) :
    ∃ C > 0, ∀ (b : E → P → Matrix (Fin n) (Fin n) ℂ)
      (hb : ContDiff ℝ ∞ (Function.uncurry b))
      (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (A : ℝ≥0)
      (hA : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
        (2 * (n + 1) + 1) A),
      (∀ ξ, b ξ 0 = 0) → (∀ ξ z, b ξ z ≠ 0 → θ z = 1) →
      ∀ r : ℝ, 0 ≤ r → (∀ x ∈ Metric.closedBall (0 : E) r, χ x = 1) →
      ∀ f : Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure E),
      (∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → f x = 0) →
      |inner ℝ (vectorTwoPositionL2Operator hn R b hb hs A
        (fun i j ξ is his ↦ hA i j ξ is (by omega)) f) f| ≤ C * A * r * ‖f‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_scalar_fullAmplitude_small_support_constant
    hn R θ hθ hθs hθbox χ hχ hχs hχθ
  refine ⟨(n : ℝ) ^ 2 * C, by positivity, ?_⟩
  intro b hb hs A hA hzero hmask r hr hplateau f hf
  let fcoord := finiteL2CoordinateIsometry volume f
  let T := fun i j ↦ twoPositionL2Operator hn R (fun ξ z ↦ b ξ z i j)
    ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) A
      (fun ξ is his ↦ hA i j ξ is (by omega))
  have hsupport (i : Fin n) :
      ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → fcoord i x = 0 := by
    filter_upwards [finiteL2Coordinates_apply_ae volume f i, hf] with x hxi hfx
    intro hx
    change fcoord i x = f x i at hxi
    rw [hxi, hfx hx]
    rfl
  have hcoord (i : Fin n) : ‖fcoord i‖ ≤ ‖f‖ :=
    (PiLp.norm_apply_le fcoord i).trans_eq ((finiteL2CoordinateIsometry volume).norm_map f)
  have hentry (i j : Fin n) :
      |inner ℝ (T i j (fcoord j)) (fcoord i)| ≤ C * A * r * ‖f‖ ^ 2 := by
    have hz (ξ : E) : b ξ 0 i j = 0 := by rw [hzero]; rfl
    have hm (ξ : E) (z : P) (hij : b ξ z i j ≠ 0) : θ z = 1 :=
      hmask ξ z (fun he ↦ hij (by rw [he]; rfl))
    have hh := hbound (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) A (hA i j)
      hz hm r hr hplateau (fcoord j) (fcoord i) (hsupport j) (hsupport i)
    apply hh.trans
    rw [pow_two]
    calc
      _ ≤ C * A * r * ‖f‖ * ‖f‖ := by gcongr <;> exact hcoord _
      _ = _ := by ring
  have he : inner ℝ (vectorTwoPositionL2Operator hn R b hb hs A
      (fun i j ξ is his ↦ hA i j ξ is (by omega)) f) f =
      ∑ i, ∑ j, inner ℝ (T i j (fcoord j)) (fcoord i) := by
    rw [real_inner_eq_complex_re,
      ← (finiteL2CoordinateIsometry volume).inner_map_map]
    simp only [vectorTwoPositionL2Operator, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
      PiLp.inner_apply, matrixOperator_apply, sum_inner, Complex.re_sum,
      real_inner_eq_complex_re, fcoord, T]
  rw [he]
  calc
    _ ≤ ∑ i, ∑ j, |inner ℝ (T i j (fcoord j)) (fcoord i)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, C * A * r * ‖f‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hentry i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

open ContinuumRow PeriodicLocalL2 in
/-- Transfer the constructed matrix freezing estimate to the original real
torus output space. The real compression and cell zero extension introduce
no extra quadrature factor or changed measure. The constant precedes the
amplitude, density budget and support radius. Consumer: weighted-limit normal
comparison in `exists_sourceDensityLimit_frozen_error_constant`
(`app:ch_background:prop:bg-frame`, Step 3; `bg-realification`). -/
theorem exists_real_fullAmplitude_small_support_constant
    (hn : 0 < n) (R : ℝ) (θ : P → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθs : HasCompactSupport θ) (hθbox : ∀ z, θ z ≠ 0 → ∀ j, |z j| ≤ R)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχθ : ∀ x y, θ (pairedPosition x y) ≠ 0 → χ x = 1 ∧ χ y = 1) :
    ∃ C > 0, ∀ (b : E → P → Matrix (Fin n) (Fin n) ℂ)
      (hb : ContDiff ℝ ∞ (Function.uncurry b))
      (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (A : ℝ≥0)
      (hA : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
        (2 * (n + 1) + 1) A),
      (∀ ξ, b ξ 0 = 0) → (∀ ξ z, b ξ z ≠ 0 → θ z = 1) →
      ∀ r : ℝ, 0 ≤ r → (∀ x ∈ Metric.closedBall (0 : E) r, χ x = 1) →
      ∀ w : OutputL2 n,
      (∀ᵐ x ∂volume, x ∉ torusChart (Metric.closedBall (0 : E) r) → w x = 0) →
      |inner ℝ (realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R b hb hs A
          (fun i j ξ is his ↦ hA i j ξ is (by omega)))) w) w| ≤
        C * A * r * ‖w‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_matrix_fullAmplitude_small_support_constant
    hn R θ hθ hθs hθbox χ hχ hχs hχθ
  refine ⟨C, hC, ?_⟩
  intro b hb hs A hA hzero hmask r hr hplateau w hw
  let T := vectorTwoPositionL2Operator hn R b hb hs A
    (fun i j ξ is his ↦ hA i j ξ is (by omega))
  let wc := l2ComplexInclusion volume w
  let f := toEuclidean (𝕜 := ℂ) wc
  have hwc : ∀ᵐ x ∂volume, x ∉ torusChart (Metric.closedBall (0 : E) r) → wc x = 0 := by
    filter_upwards [(euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL w, hw]
      with x hx hw hxout
    change wc x = euclideanComplexInclusion (w x) at hx
    rw [hx, hw hxout, map_zero]
  have hf : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → f x = 0 :=
    toEuclidean_supported hwc
  have hnorm : ‖f‖ ≤ ‖w‖ := by
    rw [show ‖f‖ = ‖wc‖ from toEuclidean.norm_map _]
    exact ((l2ComplexInclusion volume).le_opNorm w).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (l2ComplexInclusion_norm_le volume) (norm_nonneg w))
  have he : inner ℝ (realOutputCompression (transferOperator T) w) w =
      inner ℝ (T f) f := by
    change inner ℝ (l2RealPart volume (transferOperator T wc)) w = _
    rw [l2RealPart_inner, real_inner_eq_complex_re, real_inner_eq_complex_re]
    change (inner ℂ (toTorus (𝕜 := ℂ) (T f)) wc).re = _
    rw [← ContinuousLinearMap.adjoint_inner_right, toTorus_adjoint]
    rfl
  change |inner ℝ (realOutputCompression (transferOperator T) w) w| ≤ _
  rw [he]
  exact (hbound b hb hs A hA hzero hmask r hr hplateau f hf).trans
    (by gcongr)

end JanetCartan.ContinuumNormal.ActualConstruction
