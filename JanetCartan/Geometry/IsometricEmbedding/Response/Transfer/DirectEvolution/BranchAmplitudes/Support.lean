module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Terms

/-!
# Full joint support of the actual IBP amplitudes

Every branch of `new:eq:carrier-ibp` retains the closed joint support of
the original full amplitude. This includes the output position and carrier
parameters, as well as source position and normalized covector. The result
discharges support and boundary smoothness for the low graph calculus in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
open IsometricEmbedding.Response.NearCarrier CompactTransfer

variable {X M J : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]

private theorem tsupport_coefficientProduct (a : J → X → M)
    (e : AmplitudeExpression X M J) (B : M →L[ℝ] M →L[ℝ] M) (i : J) :
    tsupport ((e.coefficientProduct B i).evaluate a) ⊆ tsupport (e.evaluate a) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  apply subset_tsupport
  intro h
  exact hx (by simp [AmplitudeExpression.evaluate_coefficientProduct, h])

private theorem tsupport_divergenceTransfer (a : J → X → M)
    (e : AmplitudeExpression X M J) (v : X)
    (qs : List (X × J × (M →L[ℝ] M →L[ℝ] M))) :
    tsupport ((e.divergenceTransfer v qs).evaluate a) ⊆ tsupport (e.evaluate a) := by
  induction qs with
  | nil => exact tsupport_fderiv_apply_subset ℝ v
  | cons q qs ih =>
    apply (tsupport_add _ _).trans
    exact union_subset
      ((tsupport_fderiv_apply_subset ℝ q.1).trans (tsupport_coefficientProduct a e q.2.2 q.2.1)) ih

variable {n : ℕ} {P ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]

/-- Every actual branch retains the full joint closed support of the original
amplitude, without any smoothness assumption outside the supported box.
Source: repeated `new:eq:carrier-ibp`. -/
theorem tsupport_jointTransferTerm_subset
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (Euclidean n × P) → CarrierVariables n → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    (α : (Euclidean n × P) → CarrierVariables n → M)
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) :
    tsupport (t.amplitude.evaluate (jointAmplitudeFields b f w₀ α)) ⊆
      tsupport (Function.uncurry α) := by
  induction es generalizing t with
  | nil =>
    simp only [jointTransferTerms, Pseudodifferential.orderedTransferAction,
      List.mem_singleton] at ht
    subst t
    exact tsupport_comp_subset (g := fun v : M => (v, (0 : ℝ))) rfl _
  | cons e es ih =>
    change t ∈ (jointTransferTerms b es).flatMap (jointTransferChildren b e) at ht
    obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
    have hus := ih u hu
    simp only [jointTransferChildren, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | rfl | ⟨i, _, rfl⟩
    · exact (tsupport_divergenceTransfer _ _ _ _).trans hus
    · exact hus
    · exact (tsupport_coefficientProduct _ _ _ _).trans hus

/-- Literal two-position normalized matrix amplitude for a compact IBP branch.
The same definition is used for the forward phase and the reversed adjoint
phase, with their corresponding original full amplitudes. -/
def normalizedTermAmplitude
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (Euclidean n × P) → CarrierVariables n → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    (α : (Euclidean n × P) → CarrierVariables n → M)
    (t : JointTransferTerm n P M ι) (c : P) :
    FourierIntegral.FullAmplitudePrimitiveBudget.Local.Point n → M :=
  matrixSlice c (t.amplitude.evaluate (jointAmplitudeFields b f w₀ α))

/-- The normalized matrix branch retains the closed original support at the
same parameter. Thus source/output masks and annular shoulders survive every
derivative. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_normalizedTermAmplitude_subset
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (Euclidean n × P) → CarrierVariables n → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    (α : (Euclidean n × P) → CarrierVariables n → M)
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) (c : P) :
    tsupport (normalizedTermAmplitude b f w₀ α t c) ⊆
      normalizedSlice c ⁻¹' tsupport (Function.uncurry α) := by
  apply (tsupport_comp_subset (g := Prod.fst) rfl _).trans
  apply (tsupport_comp_subset_preimage _ (contDiff_normalizedSlice c).continuous).trans
  exact preimage_mono (tsupport_jointTransferTerm_subset b f w₀ α es t ht)

/-- Primitive local smoothness and the original buffered support give global
smoothness of the actual matrix branch, with no extension of the physical
operator. The support premise concerns only the original amplitude.
Source: restoration of the carrier after `new:eq:carrier-ibp`. -/
theorem contDiff_normalizedTermAmplitude
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {α : (Euclidean n × P) → CarrierVariables n → M}
    {U : Set (Euclidean n × P)} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) (c : P)
    (hs : ∀ p, normalizedSlice c p ∈ tsupport (Function.uncurry α) →
      normalizedSlice c p ∈ U ×ˢ D) :
    ContDiff ℝ ∞ (normalizedTermAmplitude b f w₀ α t c) := by
  have hlocal := contDiffOn_matrixSlice
    (contDiffOn_amplitudeExpression (hU.prod hD) _
      (contDiffOn_jointAmplitudeFields b hα hA) t.amplitude) c
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport (normalizedTermAmplitude b f w₀ α t c)
  · exact hlocal.contDiffAt
      (((hU.prod hD).preimage (contDiff_normalizedSlice c).continuous).mem_nhds
        (hs p (tsupport_normalizedTermAmplitude_subset b f w₀ α es t ht c hp)))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hp)

end JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
