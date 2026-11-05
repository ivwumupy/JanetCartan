module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PhaseTrade
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Canonical source differentiation of the graph operator

The source integration by parts in
`app:ch_regular_base:eq:direct-graph-identity` gives `T_b D_j = T_{η_j b}`
for a source-independent matrix amplitude and a smooth compactly supported input.
The source derivative of the literal graph phase is already proved in
`SobolevBounds.PhaseTrade`; no spatial regularity of `S` is needed here.

Compact support supplies every integrability premise of integration by parts,
including the absence of a boundary contribution. The inner-integral equality
then lifts through the existing iterated Bochner integral with its exact
Euclidean normalization. As with `graphOperator` itself, interpreting the result
as an unregularized oscillatory operator requires a separate limiting argument.

The consumer is the two-term conjugation construction, which specializes the
coordinate to canonical time and the amplitude to `χg U`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.FourierIntegral

variable {n r : ℕ}

/-- Smoothness in the source variable of the literal graph phase, without any
regularity hypothesis on `S`. This supplies the integration-by-parts premise for
`integral_graphOscillation_mulVec_source_partialDeriv`, used in
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem contDiff_graphOscillation_source
    (S : Euclidean n → Euclidean n → ℝ) (x η : Euclidean n) :
    ContDiff ℝ ∞ (fun y ↦ graphOscillation S x y η) := by
  unfold graphOscillation
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.sub (contDiff_id.inner ℝ contDiff_const)))).cexp

/-- The source integral sends `-i ∂_j v` to multiplication of the matrix amplitude
by the physical covector `η_j`. All integrability and boundary cancellation
premises follow from smoothness and compact support of `v`.
Source: the assertion `T_U D_t = T_{eU}` following
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem integral_graphOscillation_mulVec_source_partialDeriv
    (S : Euclidean n → Euclidean n → ℝ) (M : Matrix (Fin r) (Fin r) ℂ)
    {v : Euclidean n → Fin r → ℂ} (hv : ContDiff ℝ ∞ v)
    (hs : HasCompactSupport v) (x η : Euclidean n) (j : Fin n) :
    (∫ y, graphOscillation S x y η • M.mulVec (-Complex.I • partialDeriv v y j)) =
      ∫ y, graphOscillation S x y η • ((η j : ℂ) • M).mulVec (v y) := by
  let L := M.mulVecLin.toContinuousLinearMap.restrictScalars ℝ
  have hg : ContDiff ℝ ∞ (fun y ↦ M.mulVec (v y)) := L.contDiff.comp hv
  have hgs : HasCompactSupport (fun y ↦ M.mulVec (v y)) := hs.comp_left (map_zero L)
  have hgd (y : Euclidean n) :
      partialDeriv (fun z ↦ M.mulVec (v z)) y j = M.mulVec (partialDeriv v y j) := by
    exact congrArg (fun A : Euclidean n →L[ℝ] (Fin r → ℂ) ↦
      A (EuclideanSpace.single j 1))
      (L.hasFDerivAt.comp y ((hv.differentiable (by simp) y).hasFDerivAt)).fderiv
  have hf := contDiff_graphOscillation_source S x η
  have hf' : Continuous (fun y ↦ partialDeriv (fun z ↦ graphOscillation S x z η) y j) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hg' : Continuous (fun y ↦ partialDeriv (fun z ↦ M.mulVec (v z)) y j) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hibp : (∫ y, graphOscillation S x y η • M.mulVec (partialDeriv v y j)) =
      -(∫ y, partialDeriv (fun z ↦ graphOscillation S x z η) y j • M.mulVec (v y)) := by
    simp_rw [← hgd]
    exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      ((hf'.smul hg.continuous).integrable_of_hasCompactSupport hgs.smul_left)
      ((hf.continuous.smul hg').integrable_of_hasCompactSupport
        (hgs.fderiv_apply ℝ (EuclideanSpace.single j 1)).smul_left)
      ((hf.continuous.smul hg.continuous).integrable_of_hasCompactSupport hgs.smul_left)
      (fun _ _ ↦ hf.differentiable (by simp) _)
      (fun _ _ ↦ hg.differentiable (by simp) _)
  calc
    _ = -Complex.I • ∫ y, graphOscillation S x y η • M.mulVec (partialDeriv v y j) := by
      simp_rw [Matrix.mulVec_smul, smul_comm (graphOscillation S x _ η) (-Complex.I)]
      exact integral_smul _ _
    _ = -Complex.I • -(∫ y,
        partialDeriv (fun z ↦ graphOscillation S x z η) y j • M.mulVec (v y)) := by
      rw [hibp]
    _ = _ := by
      rw [← integral_neg, ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      rw [partialDeriv_graphOscillation_right]
      simp only [neg_smul, neg_neg, Matrix.smul_mulVec, smul_smul]
      congr 1
      calc
        -Complex.I * (Complex.I * (η j : ℂ) * graphOscillation S x y η) =
            -(Complex.I * Complex.I) * (graphOscillation S x y η * (η j : ℂ)) := by ring
        _ = _ := by simp

/-- Canonical source integration by parts for a source-independent matrix
amplitude, with Euclidean Lebesgue measures and the exact `(2π)⁻ⁿ` factor from
`graphOperator`. Specializing `j` to canonical time and `b` to `χg U` supplies
`T_0 D_t = T_{χg eU}` in `app:ch_regular_base:eq:direct-graph-identity`.
No regularity of `S` or `b`, or frequency integrability premise, is needed to
lift the pointwise inner-integral equality through the iterated Bochner integral. -/
theorem graphOperator_source_partialDeriv
    (S : Euclidean n → Euclidean n → ℝ)
    (b : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    {v : Euclidean n → Fin r → ℂ} (hv : ContDiff ℝ ∞ v)
    (hs : HasCompactSupport v) (x : Euclidean n) (j : Fin n) :
    graphOperator S (fun x _ η ↦ b x η) (fun y ↦ -Complex.I • partialDeriv v y j) x =
      graphOperator S (fun x _ η ↦ (η j : ℂ) • b x η) v x := by
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards with η
  exact integral_graphOscillation_mulVec_source_partialDeriv S (b x η) hv hs x η j

end JanetCartan.FourierIntegral
