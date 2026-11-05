module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Construction
public import JanetCartan.Analysis.Fourier.Conventions.NormComparison.Cartesian

/-!
# The manuscript's Cartesian maximum convention

The construction is quantitative in the project's sum of Fréchet operator
norms. For smooth-neighborhood representatives of `C^∞` closed-ball data,
the checked Section 3.1 comparison changes this to the manuscript's
Cartesian maximum on BOTH sides of the estimates. No norm equality is
claimed. Output compact support proves the boundedness required by the
real suprema on the whole space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

open FourierConventions LocalSobolev

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem cartesianCNorm_univ_le_cNorm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) (r : ℕ) :
    cartesianCNorm univ r u ≤ cNorm univ r u := by
  apply cartesianCNorm_le_of_bound (cNorm_nonneg _ _ _)
  intro α hα x _
  have horder : ∑ i, α (some i) ≤ r := by
    have := mem_sobolevMultiindices.mp hα
    omega
  apply (norm_cartesianJetDerivative_le _ _ _).trans
  apply norm_iteratedFDeriv_le_cNorm_of_bddAbove (x := x) _ (mem_univ x) horder
  simpa only [image_univ] using
    ((hu.continuous_iteratedFDeriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
      (hs.iteratedFDeriv _).norm)

/-- The SAME actual operators satisfy the manuscript's Cartesian-maximum
version of both estimates. The neighborhood hypothesis spells out the
usual smooth-up-to-boundary representative convention; only original
closed-ball norm values occur on the right hand sides. Constants precede
the scale, representative, and its neighborhood
(`app:ch_regular_base:lem:ball-extension`, `app:not:fourier`). -/
theorem exists_ballSmoothing_cartesian_bounds
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (c : E) {a : ℝ} (ha : 0 < a) {V : Set E} (hV : IsOpen V)
    (hball : closedBall c a ⊆ V) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (K : Set E) (R₀ : ℝ) (C : ℕ → ℝ) (A : ℝ),
      IsCompact K ∧ K ⊆ V ∧ 1 ≤ R₀ ∧ (2 : ℝ) * m ≤ R₀ ∧
      (∀ r, 0 ≤ C r) ∧ 0 ≤ A ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (U : Set E) (f : E → F), IsOpen U →
        closedBall c a ⊆ U → ContDiffOn ℝ ∞ f U →
        ContDiff ℝ ∞ (affineSmoothing c a R m f) ∧
        tsupport (affineSmoothing c a R m f) ⊆ K ∧
        (∀ r, cartesianCNorm univ r (affineSmoothing c a R m f) +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (affineSmoothing c a R m f)) ≤
            C r * R ^ r * cartesianCNorm (closedBall c a) 0 f) ∧
        cartesianCNorm (closedBall c a) 0 (f - affineSmoothing c a R m f) ≤
          A * (R⁻¹)^m * cartesianCNorm (closedBall c a) m f := by
  obtain ⟨K, R₀, C, A, S, hK, hKV, hR1, hRm, hC, hA, hout, _⟩ :=
    exists_ballSmoothing (F := F) c ha hV hball m hm
  let q r := cartesianCNormComparisonConstant n r
  have hq r : 0 ≤ q r := (cartesianCNormComparisonConstant_pos n r).le
  refine ⟨K, R₀, fun r ↦ C r * q 0, A * q m, hK, hKV, hR1, hRm,
    fun r ↦ mul_nonneg (hC r) (hq 0), mul_nonneg hA (hq m), ?_⟩
  intro R hR U f hU hDU hf
  let f₀ : smoothClosedBallData (F := F) c a :=
    ⟨f, fun x hx ↦ hf.contDiffAt (hU.mem_nhds (hDU hx))⟩
  obtain ⟨he, hu, hs, hb, heps⟩ := hout R hR f₀
  rw [he] at hu hs hb heps
  change ContDiff ℝ ∞ (affineSmoothing c a R m f) at hu
  change tsupport (affineSmoothing c a R m f) ⊆ K at hs
  have hcomp : HasCompactSupport (affineSmoothing c a R m f) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hs
  have hin r : cNorm (closedBall c a) r f ≤ q r * cartesianCNorm (closedBall c a) r f :=
    cNorm_le_cartesianCNorm (isCompact_closedBall _ _) hU hDU hf
  have hR0 : 0 ≤ R := zero_le_one.trans (hR1.trans hR)
  refine ⟨hu, hs, ?_, ?_⟩
  · intro r
    calc
      _ ≤ cNorm univ r (affineSmoothing c a R m f) +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (affineSmoothing c a R m f)) :=
        add_le_add (cartesianCNorm_univ_le_cNorm hu hcomp r) le_rfl
      _ ≤ C r * R ^ r * cNorm (closedBall c a) 0 f := (hb r).2
      _ ≤ C r * R ^ r * (q 0 * cartesianCNorm (closedBall c a) 0 f) :=
        mul_le_mul_of_nonneg_left (hin 0) (mul_nonneg (hC r) (pow_nonneg hR0 _))
      _ = _ := by ring
  · calc
      _ ≤ cNorm (closedBall c a) 0 (f - affineSmoothing c a R m f) :=
        cartesianCNorm_le_cNorm (isCompact_closedBall _ _)
          (fun x hx ↦ ((hf.contDiffAt (hU.mem_nhds (hDU hx))).sub hu.contDiffAt).of_le (by simp))
      _ ≤ A * (R⁻¹)^m * cNorm (closedBall c a) m f := heps
      _ ≤ A * (R⁻¹)^m * (q m * cartesianCNorm (closedBall c a) m f) :=
        mul_le_mul_of_nonneg_left (hin m) (mul_nonneg hA (pow_nonneg (inv_nonneg.mpr hR0) _))
      _ = _ := by ring

end JanetCartan.BallSmoothing
