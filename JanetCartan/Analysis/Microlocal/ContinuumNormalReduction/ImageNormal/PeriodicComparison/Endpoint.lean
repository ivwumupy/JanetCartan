module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Algebra
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint

/-!
# The endpoint of the complete normal-comparison error

The Euclidean channel constructor must supply H¹ preservation for `B`.
The differentiated one-factor lattice comparison must supply the L²-to-H¹
bounds for `D` and its literal adjoint. From these precise, independent inputs,
this file bounds all three cross terms and transfers their negative endpoint
as required by `app:ch_background:prop:bg-frame`, Step 1. The final periodic
comparison still has to instantiate these inputs for its concrete operators.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E
local notation "C²" => EuclideanL2 d (EuclideanSpace ℂ (Fin d))

private theorem vector_three_term_bound {f g h : C²}
    (hf : MemVectorFourierSobolev 1 f) (hg : MemVectorFourierSobolev 1 g)
    (hh : MemVectorFourierSobolev 1 h) :
    MemVectorFourierSobolev 1 (f + g + h) ∧
      vectorFourierSobolevNorm 1 (f + g + h) ≤
        (d : ℝ) * (vectorFourierSobolevNorm 1 f + vectorFourierSobolevNorm 1 g +
          vectorFourierSobolevNorm 1 h) := by
  have hc : finiteL2CoordinateIsometry volume (f + g + h) =
      finiteL2CoordinateIsometry volume f + finiteL2CoordinateIsometry volume g +
        finiteL2CoordinateIsometry volume h := by simp
  constructor
  · intro i
    rw [hc]
    exact ((hf i).add (hg i)).add (hh i)
  · calc
      _ ≤ ∑ i, fourierSobolevNorm 1 (finiteL2CoordinateIsometry volume (f + g + h) i) :=
        matrixFourierSobolevNorm_le_sum _ _
      _ ≤ ∑ _ : Fin d, (vectorFourierSobolevNorm 1 f + vectorFourierSobolevNorm 1 g +
          vectorFourierSobolevNorm 1 h) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hc]
        have hb₁ : fourierSobolevNorm 1 (finiteL2CoordinateIsometry volume f i) ≤
            vectorFourierSobolevNorm 1 f := fourierSobolevNorm_coordinate_le _ _ i
        have hb₂ : fourierSobolevNorm 1 (finiteL2CoordinateIsometry volume g i) ≤
            vectorFourierSobolevNorm 1 g := fourierSobolevNorm_coordinate_le _ _ i
        have hb₃ : fourierSobolevNorm 1 (finiteL2CoordinateIsometry volume h i) ≤
            vectorFourierSobolevNorm 1 h := fourierSobolevNorm_coordinate_le _ _ i
        exact (fourierSobolevNorm_add_le ((hf i).add (hg i)) (hh i)).trans
          (add_le_add ((fourierSobolevNorm_add_le (hf i) (hg i)).trans
            (add_le_add hb₁ hb₂)) hb₃)
      _ = _ := by simp [mul_add]

/-- H¹ preservation of the Euclidean channel and smoothing of the one-factor
remainder bound the complete normal error and its literal adjoint. In
particular, the mixed term with `B` on the left uses H¹ preservation, not just
L² boundedness (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem normalCrossTerms_sobolev_one_bounds
    (B D : R² →L[ℝ] R²) {CB CD : ℝ} (hCB : 0 ≤ CB) (hCD : 0 ≤ CD)
    (hB : ∀ f, MemVectorFourierSobolev 1 (l2ComplexInclusion volume f) →
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume (B f)) ∧
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (B f)) ≤
          CB * vectorFourierSobolevNorm 1 (l2ComplexInclusion volume f))
    (hD : ∀ f, MemVectorFourierSobolev 1 (l2ComplexInclusion volume (D f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (D f)) ≤ CD * ‖f‖ ∧
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume (D.adjoint f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (D.adjoint f)) ≤ CD * ‖f‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f,
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume (normalCrossTerms B D f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (normalCrossTerms B D f)) ≤
        C * ‖f‖ ∧
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume ((normalCrossTerms B D).adjoint f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume ((normalCrossTerms B D).adjoint f)) ≤
        C * ‖f‖ := by
  let C := (d : ℝ) * (CB * CD + CD * ‖B.adjoint‖ + CD * ‖D.adjoint‖)
  refine ⟨C, by dsimp [C]; positivity, fun f ↦ ?_⟩
  have h₁ := hB (D.adjoint f) (hD f).2.2.1
  have h₂ := hD (B.adjoint f)
  have h₃ := hD (D.adjoint f)
  have hb₁ := h₁.2.trans (mul_le_mul_of_nonneg_left (hD f).2.2.2 hCB)
  have hb₂ := h₂.2.1.trans (mul_le_mul_of_nonneg_left (B.adjoint.le_opNorm f) hCD)
  have hb₃ := h₃.2.1.trans (mul_le_mul_of_nonneg_left (D.adjoint.le_opNorm f) hCD)
  have hs := vector_three_term_bound h₁.1 h₂.1 h₃.1
  have he : l2ComplexInclusion volume (normalCrossTerms B D f) =
      l2ComplexInclusion volume (B (D.adjoint f)) +
        l2ComplexInclusion volume (D (B.adjoint f)) +
          l2ComplexInclusion volume (D (D.adjoint f)) := by
    simp only [normalCrossTerms, add_apply,
      ContinuousLinearMap.comp_apply, map_add]
  have hm : MemVectorFourierSobolev 1
      (l2ComplexInclusion volume (normalCrossTerms B D f)) := by rw [he]; exact hs.1
  have hn : vectorFourierSobolevNorm 1
      (l2ComplexInclusion volume (normalCrossTerms B D f)) ≤ C * ‖f‖ := by
    rw [he]
    exact hs.2.trans ((mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hb₁ hb₂) hb₃) (Nat.cast_nonneg d)).trans_eq (by dsimp [C]; ring))
  rw [normalCrossTerms_adjoint]
  exact ⟨hm, hn, hm, hn⟩

/-- All three cross terms have the actual transferred adjoint H¹ lift and
H⁻¹-to-L² estimate once the two independent channel constructions have supplied
their displayed support and endpoint properties
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem normalCrossTerms_periodic_endpoints
    {r : ℝ} (hr : r < 1 / 2) (B D : R² →L[ℝ] R²) (μ : E → ℝ)
    (hμs : tsupport μ ⊆ chartBox r)
    (hBs : ∀ f, ∀ᵐ x ∂volume, x ∉ tsupport μ → B f x = 0)
    (hDs : ∀ f, ∀ᵐ x ∂volume, x ∉ tsupport μ → D f x = 0)
    {CB CD : ℝ} (hCB : 0 ≤ CB) (hCD : 0 ≤ CD)
    (hB : ∀ f, MemVectorFourierSobolev 1 (l2ComplexInclusion volume f) →
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume (B f)) ∧
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (B f)) ≤
          CB * vectorFourierSobolevNorm 1 (l2ComplexInclusion volume f))
    (hD : ∀ f, MemVectorFourierSobolev 1 (l2ComplexInclusion volume (D f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (D f)) ≤ CD * ‖f‖ ∧
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume (D.adjoint f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (D.adjoint f)) ≤ CD * ‖f‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∃ H : PeriodicL2 d E →L[ℝ] PeriodicSobolevSpace d E 1,
        (PeriodicSobolevSpace.toL2 1).comp H =
          (transferOperator (normalCrossTerms B D)).adjoint ∧ ‖H‖ ≤ C) ∧
      ∀ f : PeriodicL2 d E,
        ‖transferOperator (normalCrossTerms B D) f‖ ≤
          C * ‖PeriodicSobolevNegativeOne.ofL2 f‖ := by
  obtain ⟨C, hC, hb⟩ := normalCrossTerms_sobolev_one_bounds B D hCB hCD hB hD
  have hs (f : R²) : ∀ᵐ x ∂volume, x ∉ chartBox r →
      (normalCrossTerms B D).adjoint f x = 0 := by
    filter_upwards [(normalCrossTerms_support B D μ hBs hDs f).2] with x hx hxr
    exact hx (fun hxm ↦ hxr (hμs hxm))
  refine ⟨((d : ℝ) * (1 + 2 * Real.pi * d)) * C, by positivity, ?_, ?_⟩
  · exact PeriodicEndpoint.exists_transferOperator_adjoint_h1 hr hC _ hs (fun f ↦ (hb f).2.2)
  · exact PeriodicEndpoint.transferOperator_negativeOne_bound hr hC _ hs (fun f ↦ (hb f).2.2)

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
