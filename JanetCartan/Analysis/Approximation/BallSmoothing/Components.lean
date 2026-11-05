module

public import JanetCartan.Analysis.Approximation.BallSmoothing.NormConventions
public import JanetCartan.Analysis.Fourier.Conventions.NormComparison.Components
public import Mathlib.Analysis.Complex.Basic

/-!
# Real, vector, and tensor action of the same smoother

The operator in `app:ch_regular_base:lem:ball-extension` is literally the
same scalar real operator in every fixed coordinate. The estimates below
also use the manuscript's maximum over the ORIGINAL input coordinates,
with only fixed dimension-and-order constants from Section 3.1. The output
norms retain the stronger Euclidean or Frobenius Fréchet bounds.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.BallSmoothing

open FourierConventions LocalSobolev

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Literal coordinatewise action on real Euclidean vector fields
(`app:ch_regular_base:lem:ball-extension`). -/
theorem affineSmoothing_vector_apply {I : Type*} [Fintype I]
    (c : E) {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : (2 : ℝ) * m ≤ R) {f : E → EuclideanSpace ℝ I}
    (hf : ContinuousOn f (closedBall c a)) (x : E) (i : I) :
    affineSmoothing c a R m f x i = affineSmoothing c a R m (fun y ↦ f y i) x := by
  exact (congrFun (affineSmoothing_map (PiLp.proj 2 (fun _ : I ↦ ℝ) i)
    c ha hm hR hf) x).symm

/-- Literal entrywise action on real tensor fields with their original
Frobenius topology (`app:ch_regular_base:lem:ball-extension`). -/
theorem affineSmoothing_matrix_apply {I J : Type*} [Fintype I] [Fintype J]
    (c : E) {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : (2 : ℝ) * m ≤ R) {f : E → Matrix I J ℝ}
    (hf : ContinuousOn f (closedBall c a)) (x : E) (i : I) (j : J) :
    affineSmoothing c a R m f x i j = affineSmoothing c a R m (fun y ↦ f y i j) x := by
  let P : Matrix I J ℝ →ₗ[ℝ] ℝ :=
    (LinearMap.proj j : (J → ℝ) →ₗ[ℝ] ℝ).comp (LinearMap.proj i)
  exact (congrFun (affineSmoothing_map P.toContinuousLinearMap c ha hm hR hf) x).symm

/-- A real input embedded in the complex fields remains exactly the
embedded real output, so smoothing preserves real fields
(`app:ch_regular_base:lem:ball-extension`). -/
theorem affineSmoothing_ofReal (c : E) {a : ℝ} (ha : 0 < a)
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    {f : E → ℝ} (hf : ContinuousOn f (closedBall c a)) :
    affineSmoothing c a R m (fun x ↦ (f x : ℂ)) =
      fun x ↦ (affineSmoothing (F := ℝ) c a R m f x : ℂ) :=
  affineSmoothing_map Complex.ofRealCLM c ha hm hR hf

private theorem exists_component_source_bounds
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (c : E) {a : ℝ} (ha : 0 < a) {V : Set E} (hV : IsOpen V)
    (hball : closedBall c a ⊆ V) (m : ℕ) (hm : 1 ≤ m)
    (M : ℕ → (E → F) → ℝ) (D : ℕ → ℝ) (hD : ∀ r, 0 ≤ D r)
    (hcompare : ∀ (U : Set E) (f : E → F), IsOpen U → closedBall c a ⊆ U →
      ContDiffOn ℝ ∞ f U → ∀ r, cNorm (closedBall c a) r f ≤ D r * M r f) :
    ∃ (K : Set E) (R₀ : ℝ) (C : ℕ → ℝ) (A : ℝ),
      IsCompact K ∧ K ⊆ V ∧ 1 ≤ R₀ ∧ (2 : ℝ) * m ≤ R₀ ∧
      (∀ r, 0 ≤ C r) ∧ 0 ≤ A ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (U : Set E) (f : E → F), IsOpen U →
        closedBall c a ⊆ U → ContDiffOn ℝ ∞ f U →
        ContDiff ℝ ∞ (affineSmoothing c a R m f) ∧
        tsupport (affineSmoothing c a R m f) ⊆ K ∧
        (∀ r, cNorm univ r (affineSmoothing c a R m f) +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (affineSmoothing c a R m f)) ≤
            C r * R ^ r * M 0 f) ∧
        cNorm (closedBall c a) 0 (f - affineSmoothing c a R m f) ≤ A * (R⁻¹)^m * M m f := by
  obtain ⟨K, R₀, C, A, S, hK, hKV, hR1, hRm, hC, hA, hout, _⟩ :=
    exists_ballSmoothing (F := F) c ha hV hball m hm
  refine ⟨K, R₀, fun r ↦ C r * D 0, A * D m, hK, hKV, hR1, hRm,
    fun r ↦ mul_nonneg (hC r) (hD 0), mul_nonneg hA (hD m), ?_⟩
  intro R hR U f hU hDU hf
  let f₀ : smoothClosedBallData (F := F) c a :=
    ⟨f, fun x hx ↦ hf.contDiffAt (hU.mem_nhds (hDU hx))⟩
  obtain ⟨he, hu, hs, hb, heps⟩ := hout R hR f₀
  rw [he] at hu hs hb heps
  have hR0 : 0 ≤ R := zero_le_one.trans (hR1.trans hR)
  refine ⟨hu, hs, ?_, ?_⟩
  · intro r
    exact ((hb r).2.trans (mul_le_mul_of_nonneg_left (hcompare U f hU hDU hf 0)
      (mul_nonneg (hC r) (pow_nonneg hR0 _)))).trans_eq (by ring)
  · exact (heps.trans (mul_le_mul_of_nonneg_left (hcompare U f hU hDU hf m)
      (mul_nonneg hA (pow_nonneg (inv_nonneg.mpr hR0) _)))).trans_eq (by ring)

/-- The actual vector smoother has both norm bounds and the exact
approximation estimate with the ORIGINAL componentwise Cartesian source
maximum of `app:not:fourier`. The constants absorb only the checked fixed
norm-convention factors (`app:ch_regular_base:lem:ball-extension`). -/
theorem exists_ballSmoothing_vector_bounds {I : Type*} [Fintype I]
    (c : E) {a : ℝ} (ha : 0 < a) {V : Set E} (hV : IsOpen V)
    (hball : closedBall c a ⊆ V) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (K : Set E) (R₀ : ℝ) (C : ℕ → ℝ) (A : ℝ),
      IsCompact K ∧ K ⊆ V ∧ 1 ≤ R₀ ∧ (2 : ℝ) * m ≤ R₀ ∧
      (∀ r, 0 ≤ C r) ∧ 0 ≤ A ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (U : Set E) (f : E → EuclideanSpace ℝ I), IsOpen U →
        closedBall c a ⊆ U → ContDiffOn ℝ ∞ f U →
        ContDiff ℝ ∞ (affineSmoothing c a R m f) ∧
        tsupport (affineSmoothing c a R m f) ⊆ K ∧
        (∀ r, cNorm univ r (affineSmoothing c a R m f) +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (affineSmoothing c a R m f)) ≤
            C r * R ^ r * vectorCartesianCNorm (closedBall c a) 0 f) ∧
        cNorm (closedBall c a) 0 (f - affineSmoothing c a R m f) ≤
          A * (R⁻¹)^m * vectorCartesianCNorm (closedBall c a) m f :=
  exists_component_source_bounds c ha hV hball m hm
    (fun r f ↦ vectorCartesianCNorm (closedBall c a) r f)
    (fun r ↦ Fintype.card I * cartesianCNormComparisonConstant n r)
    (fun r ↦ mul_nonneg (Nat.cast_nonneg _) (cartesianCNormComparisonConstant_pos n r).le)
    (fun _ _ hU hDU hf r ↦
      (vectorCartesianCNorm_comparison (isCompact_closedBall _ _) hU hDU r hf).2.2)

/-- The actual tensor smoother retains the original Frobenius output
topology and has both estimates from the manuscript's entrywise Cartesian
input maximum. No false equality with an operator norm is used
(`app:ch_regular_base:lem:ball-extension`, `app:not:fourier`). -/
theorem exists_ballSmoothing_matrix_bounds {I J : Type*} [Fintype I] [Fintype J]
    (c : E) {a : ℝ} (ha : 0 < a) {V : Set E} (hV : IsOpen V)
    (hball : closedBall c a ⊆ V) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (K : Set E) (R₀ : ℝ) (C : ℕ → ℝ) (A : ℝ),
      IsCompact K ∧ K ⊆ V ∧ 1 ≤ R₀ ∧ (2 : ℝ) * m ≤ R₀ ∧
      (∀ r, 0 ≤ C r) ∧ 0 ≤ A ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (U : Set E) (f : E → Matrix I J ℝ), IsOpen U →
        closedBall c a ⊆ U → ContDiffOn ℝ ∞ f U →
        ContDiff ℝ ∞ (affineSmoothing c a R m f) ∧
        tsupport (affineSmoothing c a R m f) ⊆ K ∧
        (∀ r, cNorm univ r (affineSmoothing c a R m f) +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (affineSmoothing c a R m f)) ≤
            C r * R ^ r * matrixCartesianCNorm (closedBall c a) 0 f) ∧
        cNorm (closedBall c a) 0 (f - affineSmoothing c a R m f) ≤
          A * (R⁻¹)^m * matrixCartesianCNorm (closedBall c a) m f :=
  exists_component_source_bounds c ha hV hball m hm
    (fun r f ↦ matrixCartesianCNorm (closedBall c a) r f)
    (fun r ↦ ((Fintype.card I * Fintype.card J : ℕ) : ℝ) * cartesianCNormComparisonConstant n r)
    (fun r ↦ mul_nonneg (Nat.cast_nonneg _) (cartesianCNormComparisonConstant_pos n r).le)
    (fun _ _ hU hDU hf r ↦
      (matrixCartesianCNorm_comparison (isCompact_closedBall _ _) hU hDU r hf).2.2)

end JanetCartan.BallSmoothing
