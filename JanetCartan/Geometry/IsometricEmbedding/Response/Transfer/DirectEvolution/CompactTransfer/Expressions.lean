module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Iteration
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.TransferAmplitudes

/-!
# Literal amplitude expressions for compact carrier transfer

The coefficient and amplitude branches after `paper-v2.tex`, `new:eq:carrier-ibp`.
A pair `M × ℝ` embeds an arbitrary matrix amplitude and the real scalar transfer
coefficients in the same expression value space. The product below is scalar
multiplication, so it neither changes the matrix action nor requires an identity
matrix. All masks belong to the initial amplitude. No frequency occurs in the
coefficient construction. Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
open Pseudodifferential IsometricEmbedding.Response.NearCarrier

variable {n : ℕ} {E M V ι : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Scalar multiplication of the full amplitude, with the scalar in the
second component of its primitive leaf (`new:eq:carrier-ibp`). -/
def scalarAmplitudeProduct : (M × ℝ) →L[ℝ] (M × ℝ) →L[ℝ] (M × ℝ) :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (ContinuousLinearMap.snd ℝ M ℝ)

/-- The actual primitive fields: the full masked amplitude and the negative
components of the literal transfer vector field. The sign is the IBP sign.
Source: the four terms in `new:eq:carrier-ibp`. -/
def jointAmplitudeFields (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    (α : E → CarrierVariables n → M) :
    Option (E × ι) → (E × CarrierVariables n) → M × ℝ
  | none, p => (α p.1 p.2, 0)
  | some (e, i), p => (0, -inner ℝ (b i) (transferCoefficient f w₀ e p.1 p.2))

/-- Integration directions and their signed coefficients for the published
`divergenceTransfer` construction (`new:eq:carrier-ibp`). -/
def jointDivergenceTerms (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (e : E) :
    List ((E × CarrierVariables n) × Option (E × ι) ×
      ((M × ℝ) →L[ℝ] (M × ℝ) →L[ℝ] (M × ℝ))) :=
  (Finset.univ.toList : List ι).map fun i =>
    ((0, b i), some (e, i), scalarAmplitudeProduct)

/-- Local smoothness of the existing amplitude expressions on the same open
box. This is used to iterate the actual compact identity, not an operator
transfer hypothesis (`new:eq:carrier-ibp`). -/
theorem contDiffOn_amplitudeExpression {X Y J : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {S : Set X} (hS : IsOpen S) (a : J → X → Y)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) S) (v : AmplitudeExpression X Y J) :
    ContDiffOn ℝ ∞ (v.evaluate a) S := by
  induction v with
  | primitive i => exact ha i
  | add v w hv hw => exact hv.add hw
  | bilinear B v w hv hw => exact (B.contDiff.comp_contDiffOn hv).clm_apply hw
  | deriv u v hv => exact (hv.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

/-- Primitive smoothness is supplied by the full amplitude and the literal
coefficient jets, all on the original box (`new:eq:carrier-ibp`). -/
theorem contDiffOn_jointAmplitudeFields
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {α : E → CarrierVariables n → M} {U : Set E} {D : Set (CarrierVariables n)}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (i : Option (E × ι)) :
    ContDiffOn ℝ ∞ (jointAmplitudeFields b f w₀ α i) (U ×ˢ D) := by
  cases i with
  | none => exact hα.prodMk contDiffOn_const
  | some i => exact contDiffOn_const.prodMk ((contDiffOn_const.inner ℝ (hA i.1)).neg)

/-- Joint derivatives restrict to the external direction without losing any
mask derivative (`new:eq:carrier-ibp`). -/
theorem fderiv_joint_external {g : E × CarrierVariables n → V}
    {q : E} {w : CarrierVariables n} (hg : DifferentiableAt ℝ g (q, w)) (e : E) :
    fderiv ℝ (fun p => g (p, w)) q e = fderiv ℝ g (q, w) (e, 0) := by
  exact congrArg (fun L : E →L[ℝ] V => L e)
    (hg.hasFDerivAt.comp q ((hasFDerivAt_id q).prodMk (hasFDerivAt_const w q))).fderiv

/-- Joint derivatives restrict to the integration direction, including the
normalized covector direction (`new:eq:carrier-ibp`). -/
theorem fderiv_joint_integration {g : E × CarrierVariables n → V}
    {q : E} {w : CarrierVariables n} (hg : DifferentiableAt ℝ g (q, w))
    (v : CarrierVariables n) :
    fderiv ℝ (fun z => g (q, z)) w v = fderiv ℝ g (q, w) (0, v) := by
  exact congrArg (fun L : CarrierVariables n →L[ℝ] V => L v)
    (hg.hasFDerivAt.comp w ((hasFDerivAt_const q w).prodMk (hasFDerivAt_id w))).fderiv

/-- The evaluated coefficient product is the actual signed component times
the complete amplitude; it contains no factor of frequency (`new:eq:carrier-ibp`). -/
theorem evaluate_jointCoefficientProduct
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    (α : E → CarrierVariables n → M)
    (v : AmplitudeExpression (E × CarrierVariables n) (M × ℝ) (Option (E × ι)))
    (e : E) (i : ι) (p : E × CarrierVariables n) :
    (v.coefficientProduct scalarAmplitudeProduct (some (e, i))).evaluate
        (jointAmplitudeFields b f w₀ α) p =
      -inner ℝ (b i) (transferCoefficient f w₀ e p.1 p.2) •
        v.evaluate (jointAmplitudeFields b f w₀ α) p := rfl

/-- The published divergence expression evaluates to the complete transferred
amplitude. In particular, every derivative of each original mask is retained.
Source: the first and third terms of `new:eq:carrier-ibp`. -/
theorem evaluate_jointDivergenceTransfer
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {α : E → CarrierVariables n → M} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (v : AmplitudeExpression (E × CarrierVariables n) (M × ℝ) (Option (E × ι)))
    (e : E) {q : E} {w : CarrierVariables n} (hq : q ∈ U) (hw : w ∈ D) :
    (v.divergenceTransfer (e, 0) (jointDivergenceTerms b e)).evaluate
        (jointAmplitudeFields b f w₀ α) (q, w) =
      transferredIntegrand b f w₀ e
        (fun p z => v.evaluate (jointAmplitudeFields b f w₀ α) (p, z)) q w := by
  classical
  let fields := jointAmplitudeFields b f w₀ α
  have hv := contDiffOn_amplitudeExpression (hU.prod hD) fields
    (contDiffOn_jointAmplitudeFields b hα hA) v
  have hd := (hv.contDiffAt ((hU.prod hD).mem_nhds (show (q, w) ∈ U ×ˢ D from ⟨hq, hw⟩))).differentiableAt (by simp)
  rw [AmplitudeExpression.evaluate_divergenceTransfer]
  simp only [jointDivergenceTerms, List.map_map, Function.comp_def]
  have hi (i : ι) :
      fderiv ℝ (fun p => scalarAmplitudeProduct (fields (some (e, i)) p)
        (v.evaluate fields p)) (q, w) (0, b i) =
      -fderiv ℝ (fun z => inner ℝ (b i) (transferCoefficient f w₀ e q z) •
        v.evaluate fields (q, z)) w (b i) := by
    have hc := contDiffOn_amplitudeExpression (hU.prod hD) fields
      (contDiffOn_jointAmplitudeFields b hα hA)
      (v.coefficientProduct scalarAmplitudeProduct (some (e, i)))
    change fderiv ℝ ((v.coefficientProduct scalarAmplitudeProduct (some (e, i))).evaluate fields) (q, w) (0, b i) = _
    rw [← fderiv_joint_integration
      ((hc.contDiffAt ((hU.prod hD).mem_nhds (show (q, w) ∈ U ×ˢ D from ⟨hq, hw⟩))).differentiableAt (by simp))]
    change fderiv ℝ (fun z => -inner ℝ (b i) (transferCoefficient f w₀ e q z) •
      v.evaluate fields (q, z)) w (b i) = _
    simp only [neg_smul, fderiv_fun_neg, neg_apply]
  change ((Finset.univ.toList.map fun i => fderiv ℝ (fun p =>
    scalarAmplitudeProduct (fields (some (e, i)) p) (v.evaluate fields p))
      (q, w) (0, b i)).sum + fderiv ℝ (v.evaluate fields) (q, w) (e, 0)) = _
  simp_rw [hi]
  rw [← fderiv_joint_external hd]
  simp only [Finset.sum_map_toList, Finset.sum_neg_distrib]
  simp only [transferredIntegrand, weightedDivergence, sub_eq_add_neg, add_comm]
  rfl

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
