module

public import JanetCartan.Analysis.Extension.Mollification.WeakDeriv
public import JanetCartan.Analysis.Extension.Mollification.WeakJet
public import JanetCartan.Analysis.Extension.Mollification.Contraction
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Contraction of weak derivatives and finite jets

Local weak identities for the contraction and zero-extension steps in the density
paragraph of Appendix B, `app:ch_regular_base:lem:ball-extension` of `paper.tex`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function Metric
open scoped Topology ContDiff

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E}

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: changing values outside
an open domain preserves the weak derivative identity on that domain. -/
theorem HasWeakFDerivOn.congr {f g : E → F} {f' g' : E → E →L[ℝ] F}
    {U : Set E} (hw : HasWeakFDerivOn μ f f' U) (hU : IsOpen U)
    (hf : EqOn f g U) (hf' : EqOn f' g' U) : HasWeakFDerivOn μ g g' U := by
  refine ⟨hw.1.congr ((ae_restrict_iff' hU.measurableSet).mpr (Filter.Eventually.of_forall hf)),
    hw.2.1.congr ((ae_restrict_iff' hU.measurableSet).mpr (Filter.Eventually.of_forall hf')), ?_⟩
  intro ψ hψ hc hs v
  have hleft : (fun x ↦ ψ x • g' x v) = (fun x ↦ ψ x • f' x v) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [hf' (hs hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright : (fun x ↦ fderiv ℝ ψ x v • g x) =
      (fun x ↦ fderiv ℝ ψ x v • f x) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [hf (hs hx)]
    · simp [fderiv_of_notMem_tsupport ℝ hx]
  rw [hleft, hright]
  exact hw.2.2 ψ hψ hc hs v

omit [BorelSpace E] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: multiplication of a weak
function and its weak derivative by the same real constant. -/
theorem HasWeakFDerivOn.smul {f : E → F} {f' : E → E →L[ℝ] F}
    {U : Set E} (hw : HasWeakFDerivOn μ f f' U) (b : ℝ) :
    HasWeakFDerivOn μ (fun x ↦ b • f x) (fun x ↦ b • f' x) U := by
  refine ⟨hw.1.smul b, hw.2.1.smul b, ?_⟩
  intro ψ hψ hc hs v
  simpa only [smul_apply, smul_comm (ψ _) b,
    smul_comm (fderiv ℝ ψ _ v) b, integral_smul, smul_neg] using
    congrArg (b • ·) (hw.2.2 ψ hψ hc hs v)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: zero extension from a
closed ball preserves the weak identity on its open interior only. -/
theorem HasWeakFDerivOn.indicator_closedBall {f : E → F} {f' : E → E →L[ℝ] F}
    {c : E} {R : ℝ} (hw : HasWeakFDerivOn μ f f' (ball c R)) :
    HasWeakFDerivOn μ ((closedBall c R).indicator f)
      ((closedBall c R).indicator f') (ball c R) := by
  apply hw.congr isOpen_ball
  · intro x hx
    simp [ball_subset_closedBall hx]
  · intro x hx
    simp [ball_subset_closedBall hx]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: changing a finite jet
outside the domain preserves its positive-order weak identities. The zeroth
component must still represent the new function, as required by `HasWeakJetOn`. -/
theorem HasWeakJetOn.congr {f g : E → F}
    {J K : (j : ℕ) → E → E [×j]→L[ℝ] F} {U : Set E} {m : ℕ}
    (hw : HasWeakJetOn μ f J U m) (hU : IsOpen U)
    (hzero : K 0 = iteratedFDeriv ℝ 0 g) (hJ : ∀ j, EqOn (J j) (K j) U) :
    HasWeakJetOn μ g K U m := by
  refine ⟨hzero, fun j hj ↦ (hw.2 j hj).congr hU (hJ j) ?_⟩
  intro x hx
  simp only [comp_apply, hJ (j + 1) hx]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: simultaneously extending
all components by zero preserves the finite weak jet on the open ball. -/
theorem HasWeakJetOn.indicator_closedBall {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {c : E} {R : ℝ} {m : ℕ}
    (hw : HasWeakJetOn μ f J (ball c R) m) :
    HasWeakJetOn μ ((closedBall c R).indicator f)
      (fun j ↦ (closedBall c R).indicator (J j)) (ball c R) m := by
  apply hw.congr isOpen_ball
  · rw [hw.1]
    ext x v
    by_cases hx : x ∈ closedBall c R <;> simp [hx, iteratedFDeriv_zero_apply]
  · intro j x hx
    simp [ball_subset_closedBall hx]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the inverse affine contraction cancels the
original contraction. -/
theorem contract_inv_contract (c x : E) {a : ℝ} (ha : a ≠ 0) :
    contract c a⁻¹ (contract c a x) = x := by
  simp [contract, inv_smul_smul₀ ha]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: a nonzero affine contraction is a
homeomorphism, whose inverse has reciprocal scale. -/
def contractHomeomorph (c : E) {a : ℝ} (ha : a ≠ 0) : E ≃ₜ E where
  toFun := contract c a
  invFun := contract c a⁻¹
  left_inv x := contract_inv_contract c x ha
  right_inv x := by simpa using contract_inv_contract c x (inv_ne_zero ha)
  continuous_toFun := (contDiff_contract c a 0).continuous
  continuous_invFun := (contDiff_contract c a⁻¹ 0).continuous

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: change of variables under affine
contraction has the Haar Jacobian factor a⁻ⁿ. -/
theorem integral_comp_contract (f : E → F) (c : E) {a : ℝ} (ha : 0 < a) :
    (∫ x, f (contract c a x) ∂μ) = (a ^ Module.finrank ℝ E)⁻¹ • ∫ x, f x ∂μ := by
  unfold contract
  rw [integral_sub_right_eq_self (fun y ↦ f (c + a • y)) c,
    Measure.integral_comp_smul_of_nonneg μ (fun y ↦ f (c + y)) a (hR := ha.le),
    integral_add_left_eq_self f c]

omit [NormedSpace ℝ F] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: integrability is preserved by pullback
through a nonzero affine contraction. -/
theorem integrable_comp_contract {f : E → F} (hf : Integrable f μ)
    (c : E) {a : ℝ} (ha : a ≠ 0) : Integrable (f ∘ contract c a) μ :=
  ((hf.comp_add_left c).comp_smul ha).comp_sub_right c

omit [NormedSpace ℝ F] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: integrability on a measurable domain
transports to its inverse image under contraction. -/
theorem integrableOn_comp_contract {f : E → F} {U : Set E}
    (hf : IntegrableOn f U μ) (hU : MeasurableSet U)
    (c : E) {a : ℝ} (ha : a ≠ 0) :
    IntegrableOn (f ∘ contract c a) ((contract c a) ⁻¹' U) μ := by
  rw [← integrable_indicator_iff (hU.preimage (contDiff_contract c a 0).continuous.measurable)]
  convert integrable_comp_contract ((integrable_indicator_iff hU).mpr hf) c ha using 1
  funext x
  exact indicator_comp_right (contract c a)

omit [NormedSpace ℝ F] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: local integrability on an open domain
transports under contraction, by testing compact subsets. -/
theorem locallyIntegrableOn_comp_contract {f : E → F} {U : Set E}
    (hf : LocallyIntegrableOn f U μ) (hU : IsOpen U)
    (c : E) {a : ℝ} (ha : a ≠ 0) :
    LocallyIntegrableOn (f ∘ contract c a) ((contract c a) ⁻¹' U) μ := by
  apply (locallyIntegrableOn_iff (hU.preimage
    (contDiff_contract c a 0).continuous).isLocallyClosed).mpr
  intro K hKU hK
  have hK' := hK.image (contDiff_contract c a 0).continuous
  have hi := hf.integrableOn_compact_subset (image_subset_iff.mpr hKU) hK'
  exact (integrableOn_comp_contract hi hK'.measurableSet c ha).mono_set
    (subset_preimage_image _ _)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the weak affine chain rule follows
directly from integration by parts using the inverse-contracted test function and Haar change of
variables. -/
theorem HasWeakFDerivOn.comp_contract {f : E → F} {f' : E → E →L[ℝ] F}
    {U : Set E} (hw : HasWeakFDerivOn μ f f' U) (hU : IsOpen U)
    (c : E) {a : ℝ} (ha : 0 < a) :
    HasWeakFDerivOn μ (f ∘ contract c a)
      (fun x ↦ a • f' (contract c a x)) ((contract c a) ⁻¹' U) := by
  refine ⟨locallyIntegrableOn_comp_contract hw.1 hU c ha.ne',
    (locallyIntegrableOn_comp_contract hw.2.1 hU c ha.ne').smul a, ?_⟩
  intro ψ hψ hc hs v
  let φ : E → ℝ := ψ ∘ contract c a⁻¹
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_contract c a⁻¹ ∞)
  have hφc : HasCompactSupport φ := hc.comp_homeomorph (contractHomeomorph c ha.ne').symm
  have hinv (y : E) : contract c a (contract c a⁻¹ y) = y := by
    simpa using contract_inv_contract c y (inv_ne_zero ha.ne')
  have hφs : tsupport φ ⊆ U := by
    change tsupport (ψ ∘ (contractHomeomorph c ha.ne').symm) ⊆ U
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have hm := hs hy
    change contract c a (contract c a⁻¹ y) ∈ U at hm
    simpa only [hinv] using hm
  have hφd (x : E) : fderiv ℝ φ (contract c a x) (a • v) = fderiv ℝ ψ x v := by
    have hd := ((hψ.differentiable (by simp)
      (contract c a⁻¹ (contract c a x))).hasFDerivAt.comp (contract c a x)
      (HasFDerivAt.const_add c
        (((hasFDerivAt_id (contract c a x)).sub_const c).const_smul a⁻¹))).fderiv
    change fderiv ℝ φ (contract c a x) =
      (fderiv ℝ ψ (contract c a⁻¹ (contract c a x))).comp
        (a⁻¹ • ContinuousLinearMap.id ℝ E) at hd
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      inv_smul_smul₀ ha.ne', contract_inv_contract c x ha.ne']
  calc
    (∫ x, ψ x • (a • f' (contract c a x)) v ∂μ) =
        ∫ x, φ (contract c a x) • f' (contract c a x) (a • v) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [φ, comp_apply, contract_inv_contract c x ha.ne', smul_apply, map_smul]
    _ = (a ^ Module.finrank ℝ E)⁻¹ • ∫ y, φ y • f' y (a • v) ∂μ :=
      integral_comp_contract (fun y ↦ φ y • f' y (a • v)) c ha
    _ = (a ^ Module.finrank ℝ E)⁻¹ • (- ∫ y, fderiv ℝ φ y (a • v) • f y ∂μ) := by
      rw [hw.2.2 φ hφ hφc hφs (a • v)]
    _ = - ∫ x, fderiv ℝ φ (contract c a x) (a • v) • f (contract c a x) ∂μ := by
      rw [integral_comp_contract (fun y ↦ fderiv ℝ φ y (a • v) • f y) c ha, smul_neg]
    _ = - ∫ x, fderiv ℝ ψ x v • (f ∘ contract c a) x ∂μ := by
      simp only [hφd, comp_apply]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: contraction transports a finite weak jet,
multiplying its component of order j by aʲ. -/
theorem HasWeakJetOn.comp_contract {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {U : Set E} {m : ℕ}
    (hw : HasWeakJetOn μ f J U m) (hU : IsOpen U)
    (c : E) {a : ℝ} (ha : 0 < a) :
    HasWeakJetOn μ (f ∘ contract c a)
      (fun j x ↦ a ^ j • J j (contract c a x)) ((contract c a) ⁻¹' U) m := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · ext x v
    simp [hw.1, iteratedFDeriv_zero_apply]
  · have hh := ((hw.2 j hj).comp_contract hU c ha).smul (a ^ j)
    simpa only [Function.comp_def, map_smul, smul_smul, pow_succ] using hh

end JanetCartan.Mollification
