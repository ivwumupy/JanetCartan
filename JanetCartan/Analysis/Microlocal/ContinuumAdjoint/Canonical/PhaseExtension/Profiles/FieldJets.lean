module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.ExtensionBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.Expressions

/-!
# Rational fields as functions of the actual first jet

This realizes both fields of `app:ch_background:eq:bg-derivative-trade` as
rational functions of the first derivative of the extended transported position.
The gap is an explicit input, whose actual producer is
`jc-adjoint-phase-extension-gap`. No field profile or operator bound is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow DerivativeKernels
variable {n : ℕ}

/-- Extract the spatial matrix from the full first jet, retaining the original
physical/carrier order (`app:ch_background:eq:bg-derivative-trade`). -/
def spatialFirstJet :
    ((Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1)) →L[ℝ] TransverseMatrix n :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) {
    toFun := fun J i k ↦ (J (EuclideanSpace.single i 1, 0)) k
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The branch coefficient as a function of the first jet. The carrier case
includes the full carrier derivative (`app:ch_background:eq:bg-derivative-trade`). -/
def firstJetBranch (e : InitialCarrierDerivative n) (j : Fin n)
    (J : (Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1)) : ℂ :=
  ((∑ k, transverseLeftInverse (spatialFirstJet J) k j *
    (match e with
    | .initial h => h k
    | .carrier h => (J (0,h)) k) : ℝ) : ℂ)

/-- The spatial slice derivative is exactly the fixed extraction of the full
first jet, used by the rational bounds (`app:ch_background:eq:bg-derivative-trade`). -/
theorem spatialFirstJet_fderiv
    {Y : Euclidean n × CarrierParameter → Euclidean (n-1)}
    {p : Euclidean n × CarrierParameter} (hY : DifferentiableAt ℝ Y p) :
    spatialFirstJet (fderiv ℝ Y p) = spatialMatrix Y p.2 p.1 := by
  have he := (hY.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)).fderiv
  simp only [Function.comp_def] at he
  ext i k
  change (fderiv ℝ Y p (EuclideanSpace.single i 1, 0)) k = _
  rw [spatialMatrix, he]
  rfl

/-- Exact identification with the existing `branchField`, before taking norms.
Consumer: the global field profiles in `app:ch_background:prop:bg-adjoint`. -/
theorem firstJetBranch_fderiv
    {Y : Euclidean n × CarrierParameter → Euclidean (n-1)}
    {p : Euclidean n × CarrierParameter} (hY : DifferentiableAt ℝ Y p)
    (e : InitialCarrierDerivative n) (j : Fin n) :
    firstJetBranch e j (fderiv ℝ Y p) =
      branchField (initialField Y) (carrierField Y) e j (p.2,p.1) := by
  have he := (hY.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
  simp only [Function.comp_def] at he
  cases e with
  | initial h =>
      simp only [firstJetBranch, spatialFirstJet_fderiv hY, branchField,
        initialField, Matrix.mulVec, dotProduct, transpose_apply]
  | carrier h =>
      simp only [firstJetBranch, spatialFirstJet_fderiv hY, branchField,
        carrierField, initialField, Matrix.mulVec, dotProduct, transpose_apply, he]
      rfl

private def matrixEntry (k : Fin (n-1)) (j : Fin n) :
    Matrix (Fin (n-1)) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) {
    toFun := fun B ↦ B k j
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- Rational smoothness follows from the Gram inverse and the transverse gap,
with no composite regularity premise (`app:ch_background:eq:bg-derivative-trade`). -/
theorem contDiffAt_firstJetBranch
    {J : (Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1)}
    {δ : ℝ} (hδ : 0 < δ) (hgap : TransverseGap δ (spatialFirstJet J))
    (e : InitialCarrierDerivative n) (j : Fin n) :
    ContDiffAt ℝ ∞ (firstJetBranch e j) J := by
  have hsum : ContDiffAt ℝ ∞
      (fun J : (Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1) ↦
        ∑ k, transverseLeftInverse (spatialFirstJet J) k j *
          (match e with
          | .initial h => h k
          | .carrier h => (J (0,h)) k)) J := by
    apply ContDiffAt.sum
    intro k _
    have hinv := (matrixEntry k j).contDiff.contDiffAt.comp J
      ((contDiffAt_transverseLeftInverse (N := ∞) hδ hgap).comp J spatialFirstJet.contDiff.contDiffAt)
    apply hinv.mul
    cases e with
    | initial h => exact contDiffAt_const
    | carrier h =>
        exact (EuclideanSpace.proj k).contDiff.contDiffAt.comp J
          (contDiffAt_id.clm_apply contDiffAt_const)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp J hsum

private theorem isCompact_firstJetGap (M δ : ℝ) :
    IsCompact {J : (Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1) |
      ‖J‖ ≤ M ∧ TransverseGap δ (spatialFirstJet J)} := by
  have hg : IsClosed {J : (Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1) |
      TransverseGap δ (spatialFirstJet J)} := by
    change IsClosed {J : (Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1) |
      ∀ v, δ * (v ⬝ᵥ v) ≤
        (spatialFirstJet J *ᵥ v) ⬝ᵥ (spatialFirstJet J *ᵥ v)}
    simp_rw [ofPred_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const
      ((spatialFirstJet.continuous.matrix_mulVec continuous_const).dotProduct
        (spatialFirstJet.continuous.matrix_mulVec continuous_const))
  exact (isCompact_closedBall (0 : (Euclidean n × CarrierParameter) →L[ℝ] Euclidean (n-1)) M).of_isClosed_subset ((isClosed_le continuous_norm continuous_const).inter hg)
      (fun J hJ ↦ by simpa using hJ.1)

/-- Uniform one-high bounds for the literal fields on a fixed ball. The only
varying analytic input is the primitive position: its first derivative has
bounded range and a fixed gap. The high loss is exactly one.
Consumer: field interpolation in `app:ch_background:prop:bg-adjoint`. -/
theorem exists_cNorm_branchField_le_firstJet
    (p₀ : Euclidean n × CarrierParameter) {R : ℝ} (hR : 0 < R)
    (M : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (e : InitialCarrierDerivative n) (j : Fin n) (m : ℕ) :
    ∃ C > 0, ∀ Y : Euclidean n × CarrierParameter → Euclidean (n-1),
      ContDiff ℝ ∞ Y →
      (∀ p ∈ closedBall p₀ R, ‖fderiv ℝ Y p‖ ≤ M ∧ TransverseGap δ (spatialMatrix Y p.2 p.1)) →
      cNorm (closedBall p₀ R) m
        (fun p : Euclidean n × CarrierParameter ↦
          branchField (initialField Y) (carrierField Y) e j (p.2,p.1)) ≤
        C * (1 + cNorm (closedBall p₀ R) (m+1) Y) := by
  obtain ⟨C, hC, hb⟩ := GeometricProfile.exists_cNorm_firstJet_comp_le_closedBall
    p₀ hR (isCompact_firstJetGap (n := n) M δ)
    (fun J hJ ↦ (contDiffAt_firstJetBranch hδ hJ.2 e j).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  refine ⟨C, hC, fun Y hY hg ↦ ?_⟩
  have he : (fun p : Euclidean n × CarrierParameter ↦
      branchField (initialField Y) (carrierField Y) e j (p.2,p.1)) =
      firstJetBranch e j ∘ fderiv ℝ Y := by
    funext p
    exact (firstJetBranch_fderiv (hY.differentiable (by simp)).differentiableAt e j).symm
  rw [he]
  apply hb Y hY
  intro p hp
  refine ⟨(hg p hp).1, ?_⟩
  rw [spatialFirstJet_fderiv (hY.differentiable (by simp)).differentiableAt]
  exact (hg p hp).2

/-- Smoothness of the literal branch in the endpoint's carrier/physical order,
from global smoothness of the position and its gap. This supplies the jet lift
used in `app:ch_background:prop:bg-adjoint`. -/
theorem branchField_contDiff_of_gap
    {Y : Euclidean n × CarrierParameter → Euclidean (n-1)}
    (hY : ContDiff ℝ ∞ Y) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ p : Euclidean n × CarrierParameter, TransverseGap δ (spatialMatrix Y p.2 p.1))
    (e : InitialCarrierDerivative n) (j : Fin n) :
    ContDiff ℝ ∞ (branchField (initialField Y) (carrierField Y) e j) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ Y) := hY.fderiv_right (by simp)
  have hb : ContDiff ℝ ∞ (firstJetBranch e j ∘ fderiv ℝ Y) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    apply (contDiffAt_firstJetBranch hδ ?_ e j).comp p hd.contDiffAt
    rw [spatialFirstJet_fderiv (hY.differentiable (by simp)).differentiableAt]
    exact hgap p
  have he : branchField (initialField Y) (carrierField Y) e j =
      (firstJetBranch e j ∘ fderiv ℝ Y) ∘ Prod.swap := by
    funext p
    exact (firstJetBranch_fderiv (Y := Y) (p := (p.2,p.1))
      (hY.differentiable (by simp)).differentiableAt e j).symm
  rw [he]
  exact hb.comp (contDiff_snd.prodMk contDiff_fst)

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
