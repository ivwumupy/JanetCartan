module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Amplitude

/-!
# Source integration by parts for the forward selected graph

The source derivative in `app:ch_response:thm:response-literal-transfer`
transfers the physical covector to the datum or the full amplitude. All
integrals use Euclidean volume. Compact support eliminates the boundary term.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer
open FourierIntegral
variable {n r : ℕ}

/-- Integration by parts against the literal physical graph oscillation in
`app:ch_response:thm:response-literal-transfer`. The compactly supported vector
function may include every source weight and the full matrix amplitude. -/
theorem graphOscillation_source_integration_by_parts
    (Φ : Euclidean n → Euclidean n → ℝ) (x δ : Euclidean n) (l : Fin n)
    (g : Euclidean n → Fin r → ℂ) (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    (Complex.I * (δ l : ℂ)) • (∫ y, graphOscillation Φ x y δ • g y) =
      ∫ y, graphOscillation Φ x y δ • partialDeriv g y l := by
  let e := fun y ↦ graphOscillation Φ x y δ
  have he : Differentiable ℝ e := by
    intro y
    dsimp [e, graphOscillation]
    exact ((Complex.ofRealCLM.differentiableAt.comp y
      ((differentiableAt_const (Φ x δ)).sub
        (differentiableAt_id.inner ℝ (differentiableAt_const δ)))).const_mul _).cexp
  have hi : Integrable (fun y ↦ e y • g y) :=
    (he.continuous.smul hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hdg : Continuous (fun y ↦ partialDeriv g y l) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hid : Integrable (fun y ↦ e y • partialDeriv g y l) :=
    (he.continuous.smul hdg).integrable_of_hasCompactSupport
      (hgs.fderiv_apply ℝ (EuclideanSpace.single l 1)).smul_left
  have hie : Integrable (fun y ↦ partialDeriv e y l • g y) := by
    simp only [e, partialDeriv_graphOscillation_source, mul_smul]
    exact hi.smul (-(Complex.I * (δ l : ℂ)))
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    hie hid hi (fun y _ ↦ he y) (fun y _ ↦ hg.differentiable (by simp) y)
  change (∫ y, e y • partialDeriv g y l) = -(∫ y, partialDeriv e y l • g y) at h
  simpa only [e, partialDeriv_graphOscillation_source, mul_smul, integral_smul,
    neg_smul, integral_neg, neg_neg] using h.symm

/-- Compact source support gives integrability of the literal matrix kernel in
`app:ch_response:thm:response-literal-transfer`; no source weight is removed. -/
theorem integrable_graphOscillation_mulVec
    (Φ : Euclidean n → Euclidean n → ℝ) (x δ : Euclidean n)
    (a : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (u : Euclidean n → Fin r → ℂ)
    (ha : Continuous a) (hu : Continuous u) (hus : HasCompactSupport u) :
    Integrable (fun y ↦ graphOscillation Φ x y δ • (a y).mulVec (u y)) := by
  have hc : Continuous (fun y ↦ graphOscillation Φ x y δ • (a y).mulVec (u y)) := by
    unfold graphOscillation Matrix.mulVec dotProduct
    fun_prop
  apply hc.integrable_of_hasCompactSupport (hus.mono ?_)
  intro y hy
  contrapose! hy
  simp only [Function.mem_support, not_not] at hy ⊢
  simp [hy]

/-- The source covector transfers either to the full amplitude or to the actual
datum, in the forward paragraph of `app:ch_response:thm:response-literal-transfer`.
The compact support is that of the datum including its original source weights. -/
theorem graphOscillation_source_mulVec_integration_by_parts
    (Φ : Euclidean n → Euclidean n → ℝ) (x δ : Euclidean n) (l : Fin n)
    (a : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (u : Euclidean n → Fin r → ℂ)
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    (Complex.I * (δ l : ℂ)) • (∫ y, graphOscillation Φ x y δ • (a y).mulVec (u y)) =
      (∫ y, graphOscillation Φ x y δ • (partialDeriv a y l).mulVec (u y)) +
      ∫ y, graphOscillation Φ x y δ • (a y).mulVec (partialDeriv u y l) := by
  have hg : ContDiff ℝ ∞ (fun y ↦ (a y).mulVec (u y)) := by
    apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ ∞ (fun y ↦ ∑ k, a y i k * u y k)
    have ha' (k : Fin r) : ContDiff ℝ ∞ (fun y ↦ a y i k) := by
      let ev : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] ℂ :=
        { toFun := fun M ↦ M i k
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      exact ev.toContinuousLinearMap.contDiff.comp ha
    exact ContDiff.sum (fun k _ ↦ (ha' k).mul (contDiff_pi.mp hu k))
  have hgs : HasCompactSupport (fun y ↦ (a y).mulVec (u y)) := by
    apply hus.mono
    intro y hy
    contrapose! hy
    simp only [Function.mem_support, not_not] at hy ⊢
    simp [hy]
  rw [graphOscillation_source_integration_by_parts Φ x δ l _ hg hgs]
  simp_rw [partialDeriv_matrix_mulVec a u _ l
    (ha.differentiable (by simp) _) (hu.differentiable (by simp) _), smul_add]
  apply integral_add
  · exact integrable_graphOscillation_mulVec Φ x δ _ u
      ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) hu.continuous hus
  · exact integrable_graphOscillation_mulVec Φ x δ a _ ha.continuous
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hus.fderiv_apply ℝ (EuclideanSpace.single l 1))

end JanetCartan.ResponseTransfer
