module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.BranchRealization.Basic

/-!
# Finite low budgets for all gain-one transfer branches

The original order-minus-one amplitude supplies the two first-output branch
families, retaining the original phase, supports and literal adjunction.
Consumer: the gain-one branch premises in
`SupportedSobolev.exists_graph_adjoint_integer_sobolev_constant`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.BranchRealization
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneProfiles SupportedSobolev
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n

/-- Every branch initialized at the forward or literal adjoint first-output
amplitude is admissible and has finite weighted low jets. The fixed reserve is
enlarged once for the first derivative, independently of the derivative word.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem gainOne_branch_budgets
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B c : ℝ) (hc : 1 ≤ c)
    {X₀ Y₀ F₀ : Set E} (hX₀ : IsCompact X₀) (hY₀ : IsCompact Y₀)
    (hF₀ : IsClosed F₀) (hF₀0 : (0 : E) ∉ F₀)
    {O : Set (Point n)} (hO : IsOpen O) (hcarrier : (X₀ ×ˢ Y₀) ×ˢ F₀ ⊆ O)
    (S : E → E → ℝ) (hS : SupportedPhaseRegularity S O)
    (hinv : SupportedMixedInvertibility S O)
    (hSchart : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hhomChart : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    (hinvChart : ∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det)
    (hgap : ∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B)
    (hlowS : ∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ + 3)
      (fun p : Point n ↦ S p.1.1 p.2) ≤ M)
    (A : FullAmplitude n r) (hA : ForwardAmplitudeAdmissible X₀ Y₀ F₀ A)
    (hbA : ∀ i j, BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A)
    (hlowA : ∀ i, orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ + 1) A ≤ M)
    (ρ : E → ℝ) (hρ : ∀ η, 1 ≤ ρ η) (hηρ : ∀ η, ‖η‖ ≤ ρ η)
    (hcover : ∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R ∧ R ≤ c * ρ p.2) :
    ∀ (i : Fin n) (is : List (Fin n)),
      (∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
        (graphTransferDatum S) (graphFirstOutputAmplitude S A i) is,
        ForwardAmplitudeAdmissible X₀ Y₀ F₀ p.1 ∧ ∃ L : ℝ, 0 ≤ L ∧
          ∀ w : List (Coordinate n), w.length ≤ μ → ∀ x y η,
            (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤ L) ∧
      (∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
        (adjointTransferDatum S) (adjointFirstOutputAmplitude A i) is,
        ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) p.1 ∧
          (∀ x y η, η ∉ F₀ → p.1 x y η = 0) ∧ ∃ L : ℝ, 0 ≤ L ∧
          ∀ w : List (Coordinate n), w.length ≤ μ → ∀ x y η,
            (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤ L) := by
  intro i is
  obtain ⟨P, C, hP, _hC, hprofiles⟩ := exists_finiteGainOne_primitive_inputs (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ hM B c hc is.length
  have hAc : ContDiffOn ℝ ∞ (uncurry A) V :=
    (hA.smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).contDiffOn
  obtain ⟨hH, hjets⟩ := hprofiles S A hSchart hhomChart hinvChart hgap hAc hbA hlowS hlowA
  obtain ⟨hAmp, hPhase, hScalar⟩ := hjets ((X₀ ×ˢ Y₀) ×ˢ F₀) ρ hρ hcover
  have hAr := reverseAdmissible_of_forward hA hX₀ hY₀ hF₀
  have hsupp : ∀ p : Point n, p ∉ (X₀ ×ˢ Y₀) ×ˢ F₀ → uncurry A p = 0 := by
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  let H := C * normalizedGainOneHigh z δ (is.length + 1 + (μ + 2)) S A
  have hbudget (p : FullAmplitude n r × List (Fin n)) :
      0 ≤ GainOneBranches.branchConstant n μ is.length P *
        H ^ (((is.length - p.2.length : ℕ) : ℝ) / is.length) :=
    mul_nonneg (GainOneBranches.branchConstant_nonneg _ _ _ hP)
      (Real.rpow_nonneg (zero_le_one.trans hH) _)
  constructor
  · intro p hp
    have hfirst := graphFirstOutput_admissible_of_supported hA hX₀ hY₀ hF₀ hF₀0 hO hcarrier hS i
    refine ⟨forward_branch_admissible hfirst hX₀ hY₀ hF₀ hF₀0 hcarrier hS is p hp,
      _, hbudget p, ?_⟩
    simpa only [Nat.add_sub_cancel] using
      (graph_branch_jet_norm_le_of_profiles μ (is.length + 1) (by omega)
        P hP H hH S A (hX₀.prod hY₀) hF₀ hF₀0 hO hcarrier hS hinv hAr.smooth hsupp
        ρ hρ hAmp hPhase hScalar i is (by omega) p hp)
  · intro p hp
    have hfirst : ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) (adjointFirstOutputAmplitude A i) :=
      hAr.conjTranspose.reverseFirstOutputAmplitude i
    have hfirstF : ∀ x y η, η ∉ F₀ → adjointFirstOutputAmplitude A i x y η = 0 :=
      (adjoint_branches_frequency_support (S := S)
        (fun x y η hη ↦ by
          simp only [hA.support x y η (Or.inr (Or.inr hη)), Matrix.conjTranspose_zero]) i).2.2
    have hpQ := reverse_branch_admissible hfirst hfirstF hF₀ hF₀0 hcarrier hS hinv is p hp
    refine ⟨hpQ.1, hpQ.2, _, hbudget p, ?_⟩
    simpa only [Nat.add_sub_cancel] using
      (adjoint_branch_jet_norm_le_of_profiles μ (is.length + 1) (by omega)
        P hP H hH S A (hX₀.prod hY₀) hF₀ hF₀0 hO hcarrier hS hinv hAr.smooth hsupp
        ρ hρ hηρ hAmp hScalar i is (by omega) p hp)

end JanetCartan.FourierIntegral.BranchRealization
