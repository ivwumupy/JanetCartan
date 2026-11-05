module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Kernel

/-!
# Joint classical derivatives of the normalized annular integral

The exact finite expansion of `paper-v2.tex`, `new:eq:carrier-ibp`, with the
physical Fourier constant and both powers of frequency included. Primitive
smooth critical matching on the supported open convex domain supplies all
coefficient regularity and integrability. The consumer is weak transfer for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential FourierIntegral CompactTransfer BranchAmplitudes
variable {n r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "V" => Fin r → ℂ

omit [FiniteDimensional ℝ P] in
private theorem originalDatumDerivative_const_smul {R : Type}
    [DivisionRing R] [Module R V] [SMulCommClass ℝ R V] [ContinuousConstSMul R V]
    (c : R) (es : List (E × P)) (g : E × P → V) :
    originalDatumDerivative es (c • g) = c • originalDatumDerivative es g := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (fun q => fderiv ℝ (originalDatumDerivative es (c • g)) q e) = _
    rw [ih, fderiv_const_smul_field]
    rfl

/-- Absolute integrability for every enumerated branch follows from the same
compact support and primitive local jets. In particular the joint-to-iterated
kernel identities require no additional integrability hypothesis.
Source: the finite expansion after `new:eq:carrier-ibp`. -/
theorem integrable_jointBranch_of_primitive_geometry
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat} {a : E × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (lam : ℝ) (es : List (E × P)) (t : JointTransferTerm n P Mat ι)
    (ht : t ∈ jointTransferTerms b es) {q : E × P} (hq : q ∈ U) :
    Integrable (fun w => oscillation f lam q w •
      jointTransferTermValue b ReverseDerivative.matrixAction f w₀ α a t q w) := by
  exact integrable_oscillation_jointTransferTerm b ReverseDerivative.matrixAction
    hU hD hK hKD hf hα ha hs
    (contDiffOn_transferCoefficient hU hD hcD hf hw₀ h₀ hinv) lam es t ht hq

/-- The normalized branch output is smooth on the original output/parameter
open set. This is proved from local integrand smoothness and compact support,
without a global phase extension or output regularity premise.
Source: the differentiation in `new:eq:carrier-ibp`. -/
theorem contDiffOn_normalizedBranchIntegral
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat} {a : E × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (lam : ℝ) (p : ℤ) (es : List (E × P)) (t : JointTransferTerm n P Mat ι)
    (ht : t ∈ jointTransferTerms b es) :
    ContDiffOn ℝ ∞ (normalizedBranchIntegral b f w₀ α a t lam p) U := by
  let g := fun q w => oscillation f lam q w •
    jointTransferTermValue b ReverseDerivative.matrixAction f w₀ α a t q w
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ D) :=
    (contDiffOn_oscillation hf lam).smul
      (contDiffOn_jointTransferTermValue b ReverseDerivative.matrixAction hU hD hα
        (contDiffOn_transferCoefficient hU hD hcD hf hw₀ h₀ hinv) ha t)
  have hsg : ∀ q ∈ U, Function.support (g q) ⊆ K := fun q hq =>
    (Function.support_smul_subset_right (oscillation f lam q) _).trans
      (support_jointTransferTermValue b ReverseDerivative.matrixAction f w₀ a
        hU hK.isClosed hs es t ht q hq)
  let : IsFiniteMeasure ((volume : Measure (CarrierVariables n)).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hi := contDiffOn_compactParameterIntegral (μ := volume) hU hD hK hKD hg
  have he : EqOn (fun q => ∫ w, g q w) (fun q => ∫ w in K, g q w) U := by
    intro q hq
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    exact Function.notMem_support.mp (fun h => hw (hsg q hq h))
  exact (((hi.congr he).const_smul (lam ^ p)).const_smul (lam ^ n)).const_smul
    (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- Every ordered joint derivative of the actual normalized base integral is
exactly the finite sum of its normalized branch integrals. The physical
operator, elapsed time and frequency are fixed during parameter differentiation;
only the original datum and carrier family are differentiated. The shared
branch count remains `amplitude.derivativeCost + datumWord.length = es.length`.
Source: `new:eq:carrier-ibp` and `app:ch_response:lem:energy-carrier-jets`. -/
theorem originalDatumDerivative_normalizedIntegral_expansion
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat} {a : E × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (lam : ℝ) (p : ℤ) (es : List (E × P)) {q : E × P} (hq : q ∈ U) :
    originalDatumDerivative es
      (normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p) q =
      ((jointTransferTerms b es).map fun t =>
        normalizedBranchIntegral b f w₀ α a t lam p q).sum := by
  have he := (orderedTransferAction_integral_expansion b ReverseDerivative.matrixAction
    hU hD hcD hK hKD hf hα ha hs hw₀ hcritical hvalue h₀ hinv lam es hq).1
  change originalDatumDerivative es _ q = _ at he
  have hbase : jointTransferTermValue b ReverseDerivative.matrixAction f w₀ α a
      initialJointTransferTerm = fun q w => ReverseDerivative.matrixAction (α q w)
        (sourceDatum a q w) := rfl
  unfold normalizedBranchIntegral
  simp only [hbase]
  change originalDatumDerivative es
    (((2 * Real.pi) ^ n : ℂ)⁻¹ • (lam ^ n • (lam ^ p •
      (fun q => ∫ w, oscillation f lam q w •
        ReverseDerivative.matrixAction (α q w) (sourceDatum a q w))))) q = _
  rw [originalDatumDerivative_const_smul, originalDatumDerivative_const_smul,
    originalDatumDerivative_const_smul]
  simp only [Pi.smul_apply]
  rw [he]
  simp only [List.smul_sum, List.map_map, Function.comp_def]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
