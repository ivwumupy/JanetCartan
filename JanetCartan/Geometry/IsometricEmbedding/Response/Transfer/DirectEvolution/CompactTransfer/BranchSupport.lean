module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Terms

/-!
# The same compact support for every amplitude branch

All actual expressions after `paper-v2.tex`, `new:eq:carrier-ibp` retain the
original compact integration support, including differentiated masks. This
supplies the boundary and integrability conditions for finite iteration.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
open Pseudodifferential IsometricEmbedding.Response.NearCarrier

variable {n : ℕ} {E M J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup M] [NormedSpace ℝ M]

private theorem support_jointFDeriv_subset
    {U : Set E} {K : Set (CarrierVariables n)} (hU : IsOpen U) (hK : IsClosed K)
    {g : E × CarrierVariables n → M}
    (hs : ∀ q ∈ U, Function.support (fun w => g (q, w)) ⊆ K)
    (v : E × CarrierVariables n) :
    ∀ q ∈ U, Function.support (fun w => fderiv ℝ g (q, w) v) ⊆ K := by
  intro q hq w hw
  by_contra hn
  have heq : g =ᶠ[𝓝 (q, w)] (fun _ => 0) := by
    filter_upwards [(hU.prod hK.isOpen_compl).mem_nhds
      (show (q, w) ∈ U ×ˢ Kᶜ from ⟨hq, hn⟩)] with p hp
    exact Function.notMem_support.mp (fun h => hp.2 (hs p.1 hp.1 h))
  exact hw (by simp [heq.fderiv_eq])

/-- Coefficient multiplication preserves the actual integration support,
with no support restriction on the coefficient itself (`new:eq:carrier-ibp`). -/
theorem support_coefficientProduct_evaluate_subset
    {U : Set E} {K : Set (CarrierVariables n)}
    (fields : J → E × CarrierVariables n → M)
    (v : AmplitudeExpression (E × CarrierVariables n) M J)
    (hs : ∀ q ∈ U, Function.support (fun w => v.evaluate fields (q, w)) ⊆ K)
    (C : M →L[ℝ] M →L[ℝ] M) (i : J) :
    ∀ q ∈ U, Function.support
      (fun w => (v.coefficientProduct C i).evaluate fields (q, w)) ⊆ K := by
  intro q hq w hw
  by_contra hn
  have hz := Function.notMem_support.mp (fun h => hn (hs q hq h))
  exact hw (by simp [AmplitudeExpression.evaluate_coefficientProduct, hz])

/-- Every derivative in the full divergence expression retains the same
integration support, even with local coefficient geometry (`new:eq:carrier-ibp`). -/
theorem support_divergenceTransfer_evaluate_subset
    {U : Set E} {K : Set (CarrierVariables n)} (hU : IsOpen U) (hK : IsClosed K)
    (fields : J → E × CarrierVariables n → M)
    (v : AmplitudeExpression (E × CarrierVariables n) M J)
    (hs : ∀ q ∈ U, Function.support (fun w => v.evaluate fields (q, w)) ⊆ K)
    (e : E × CarrierVariables n)
    (qs : List ((E × CarrierVariables n) × J × (M →L[ℝ] M →L[ℝ] M))) :
    ∀ q ∈ U, Function.support
      (fun w => (v.divergenceTransfer e qs).evaluate fields (q, w)) ⊆ K := by
  induction qs with
  | nil => exact support_jointFDeriv_subset hU hK hs e
  | cons z zs ih =>
    intro q hq w hw
    by_contra hn
    have h₁ := Function.notMem_support.mp (fun h => hn
      (support_jointFDeriv_subset hU hK
        (support_coefficientProduct_evaluate_subset fields v hs z.2.2 z.2.1) z.1 q hq h))
    have h₂ := Function.notMem_support.mp (fun h => hn (ih q hq h))
    exact hw (by simp only [AmplitudeExpression.divergenceTransfer,
      AmplitudeExpression.evaluate, h₁, h₂, add_zero])

variable {P ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]

/-- Every enumerated actual amplitude has the original compact support.
This closes the support obligation for every finite IBP step, including all
mask derivatives. Source: iteration of `new:eq:carrier-ibp`. -/
theorem support_jointTransferTerms_amplitude
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (Euclidean n × P) → CarrierVariables n → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    {α : (Euclidean n × P) → CarrierVariables n → M}
    {U : Set (Euclidean n × P)} {K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hK : IsClosed K)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) :
    ∀ q ∈ U, Function.support
      (fun w => t.amplitude.evaluate (jointAmplitudeFields b f w₀ α) (q, w)) ⊆ K := by
  induction es generalizing t with
  | nil =>
    simp only [jointTransferTerms, orderedTransferAction, List.mem_singleton] at ht
    subst t
    intro q hq w hw
    by_contra hn
    have hz := Function.notMem_support.mp (fun h => hn (hs q hq h))
    exact hw (by simp [initialJointTransferTerm, AmplitudeExpression.evaluate,
      jointAmplitudeFields, hz])
  | cons e es ih =>
    change t ∈ (jointTransferTerms b es).flatMap (jointTransferChildren b e) at ht
    obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
    have hus := ih u hu
    simp only [jointTransferChildren, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | rfl | ⟨i, _, rfl⟩
    · exact support_divergenceTransfer_evaluate_subset hU hK _ _ hus _ _
    · exact hus
    · exact support_coefficientProduct_evaluate_subset _ _ hus _ _

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
