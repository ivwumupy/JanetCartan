module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.SourceTests

/-!
# Supported smooth representatives of the actual annular branches

The output mask in `app:ch_response:eq:direct-envelope-profile` turns the
local compact expansion into a global smooth representative on each parameter
neighborhood. Only the original amplitude support is used; the phase and
critical geometry are never extended outside their original open set.
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
/-- Every literal branch vanishes outside the original output support.
This follows from the support theorem for the actual amplitude expressions,
including all parameter words (`new:eq:carrier-ibp`). -/
theorem normalizedBranchIntegral_zero_of_notMem_output
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (E × P) → CarrierVariables n → ℝ) (w₀ : E × P → CarrierVariables n)
    (α : (E × P) → CarrierVariables n → Mat) (a : E × P → V)
    (es : List (E × P)) (t : JointTransferTerm n P Mat ι)
    (ht : t ∈ jointTransferTerms b es) {X : Set E}
    (hs : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    (lam : ℝ) (p : ℤ) {q : E × P} (hq : q.1 ∉ X) :
    normalizedBranchIntegral b f w₀ α a t lam p q = 0 := by
  have hz (w : CarrierVariables n) :
      t.amplitude.evaluate (jointAmplitudeFields b f w₀ α) (q, w) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hq
      (hs (q, w) (tsupport_jointTransferTerm_subset b f w₀ α es t ht h)))
  simp [normalizedBranchIntegral, jointTransferTermValue, hz]

omit [FiniteDimensional ℝ P] in
/-- The same compact output mask supports every normalized integral slice.
Consumer: its Schwartz representative in the weak-derivative characterization
of `app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_normalizedBranchIntegral_slice
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (E × P) → CarrierVariables n → ℝ) (w₀ : E × P → CarrierVariables n)
    (α : (E × P) → CarrierVariables n → Mat) (a : E × P → V)
    (es : List (E × P)) (t : JointTransferTerm n P Mat ι)
    (ht : t ∈ jointTransferTerms b es) {X : Set E} (hX : IsClosed X)
    (hs : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    (lam : ℝ) (p : ℤ) (c : P) :
    tsupport (fun x => normalizedBranchIntegral b f w₀ α a t lam p (x, c)) ⊆ X := by
  apply closure_minimal _ hX
  intro x hx
  by_contra hn
  exact hx (normalizedBranchIntegral_zero_of_notMem_output b f w₀ α a es t ht hs lam p hn)

/-- Local primitive smoothness suffices for global spatial smoothness on the
original parameter neighborhood. The only extra geometry is containment of
the ORIGINAL compact output support in the original open domain. No global
extension of the phase is assumed (`new:eq:carrier-ibp`). -/
theorem contDiffOn_normalizedBranchIntegral_output_strip
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
    (ht : t ∈ jointTransferTerms b es) {X : Set E} (hX : IsClosed X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    {C : Set P} (hXU : X ×ˢ C ⊆ U) :
    ContDiffOn ℝ ∞ (normalizedBranchIntegral b f w₀ α a t lam p) (univ ×ˢ C) := by
  have hg := contDiffOn_normalizedBranchIntegral b hU hD hcD hK hKD hf hα ha hs hw₀ h₀
    hinv lam p es t ht
  intro q hq
  by_cases hx : q.1 ∈ X
  · exact (hg.contDiffAt (hU.mem_nhds (hXU ⟨hx, hq.2⟩))).contDiffWithinAt
  · have he : normalizedBranchIntegral b f w₀ α a t lam p =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [(hX.preimage continuous_fst).isOpen_compl.mem_nhds hx] with y hy
      exact normalizedBranchIntegral_zero_of_notMem_output b f w₀ α a es t ht houtput lam p hy
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

/-- The exact compact expansion holds at every output point once the original
amplitude has its supported output mask. Off that mask both sides vanish by
locality. This globalizes `new:eq:carrier-ibp` without extending the phase. -/
theorem originalDatumDerivative_normalizedIntegral_expansion_of_output_support
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
    (lam : ℝ) (p : ℤ) (es : List (E × P))
    {X : Set E} (hX : IsClosed X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    {C : Set P} (hXU : X ×ˢ C ⊆ U) {c : P} (hc : c ∈ C) (x : E) :
    originalDatumDerivative es
      (normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p) (x, c) =
      ((jointTransferTerms b es).map fun t =>
        normalizedBranchIntegral b f w₀ α a t lam p (x, c)).sum := by
  by_cases hx : x ∈ X
  · exact originalDatumDerivative_normalizedIntegral_expansion b hU hD hcD hK hKD hf hα ha
      hs hw₀ hcritical hvalue h₀ hinv lam p es (hXU ⟨hx, hc⟩)
  · have hbase (q : E × P) (hq : q.1 ∉ X) :
        normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p q = 0 :=
      normalizedBranchIntegral_zero_of_notMem_output b f w₀ α a [] _
        (by simp [jointTransferTerms, orderedTransferAction]) houtput lam p hq
    have hz : originalDatumDerivative es
        (normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p) (x, c) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx
        (tsupport_originalDatumDerivative_source hX hbase es h))
    rw [hz]
    symm
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    exact normalizedBranchIntegral_zero_of_notMem_output b f w₀ α a es t ht houtput lam p hx

/-- Global integrability follows from the original output mask and the local
primitive integrability theorem. Off the original supported chart the literal
integrand is zero, without any extension (`new:eq:carrier-ibp`). -/
theorem integrable_jointBranch_of_output_support
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
    (ht : t ∈ jointTransferTerms b es) {X : Set E}
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    (c : P) (hXU : ∀ x ∈ X, (x, c) ∈ U) (x : E) :
    Integrable (fun w => oscillation f lam (x, c) w •
      jointTransferTermValue b ReverseDerivative.matrixAction f w₀ α a t (x, c) w) := by
  by_cases hx : x ∈ X
  · exact integrable_jointBranch_of_primitive_geometry b hU hD hcD hK hKD hf hα ha hs hw₀ h₀
      hinv lam es t ht (hXU x hx)
  · have hz (w : CarrierVariables n) :
        t.amplitude.evaluate (jointAmplitudeFields b f w₀ α) ((x, c), w) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx
        (houtput ((x, c), w) (tsupport_jointTransferTerm_subset b f w₀ α es t ht h)))
    simp only [jointTransferTermValue, hz, Prod.fst_zero, map_zero, zero_apply, smul_zero]
    exact integrable_zero _ _ _

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
