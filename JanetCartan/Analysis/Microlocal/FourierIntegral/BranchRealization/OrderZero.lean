module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.BranchRealization.Basic

/-!
# Finite low budgets for all order-zero transfer branches

The original normalized amplitude and phase data produce the weighted budgets
needed to apply the universal low realization, with no branch norm or realization
premise. Consumer: the two order-zero branch premises of
`SupportedSobolev.exists_graph_adjoint_integer_sobolev_constant`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.BranchRealization
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles SupportedSobolev
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n

/-- Every order-zero derivative branch is admissible and has a finite weighted
low-jet budget, in both directions. Reverse amplitudes are conjugated exactly
once. The reserve `μ` is fixed before the derivative word.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem orderZero_branch_budgets
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B : ℝ)
    {X₀ Y₀ F₀ : Set E} (hX₀ : IsCompact X₀) (hY₀ : IsCompact Y₀)
    (hF₀ : IsClosed F₀) (hF₀0 : (0 : E) ∉ F₀)
    {O : Set (Point n)} (hO : IsOpen O) (hcarrier : (X₀ ×ˢ Y₀) ×ˢ F₀ ⊆ O)
    (S : E → E → ℝ) (hS : SupportedPhaseRegularity S O)
    (hinv : SupportedMixedInvertibility S O)
    (hSchart : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hhomChart : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    (hinvChart : ∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det)
    (hgap : ∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B)
    (hlowS : ∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ + 2)
      (fun p : Point n ↦ S p.1.1 p.2) ≤ M)
    (A : FullAmplitude n r) (hA : ForwardAmplitudeAdmissible X₀ Y₀ F₀ A)
    (hbA : ∀ i j, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A))
    (hlowA : ∀ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ (uncurry A) ≤ M)
    (ρ : E → ℝ) (hρ : ∀ η, 0 ≤ ρ η)
    (hcover : ∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R) :
    ∀ is : List (Fin n),
      (∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
        (graphTransferDatum S) A is,
        ForwardAmplitudeAdmissible X₀ Y₀ F₀ p.1 ∧ ∃ L : ℝ, 0 ≤ L ∧
          ∀ w : List (Coordinate n), w.length ≤ μ → ∀ x y η,
            (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤ L) ∧
      (∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
        (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) is,
        ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) p.1 ∧
          (∀ x y η, η ∉ F₀ → p.1 x y η = 0) ∧ ∃ L : ℝ, 0 ≤ L ∧
          ∀ w : List (Coordinate n), w.length ≤ μ → ∀ x y η,
            (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤ L) := by
  obtain ⟨L, hL, hp⟩ := exists_finitePrimitiveProfile_inputs (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ hM B
  intro is
  obtain ⟨C, I, _hC, hI, hprofiles⟩ := hp is.length
  have hAc : ContDiffOn ℝ ∞ (uncurry A) V :=
    (hA.smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).contDiffOn
  obtain ⟨hq, hmono, hH, hlow, hhigh, hinterp, hjets⟩ :=
    hprofiles S A hSchart hhomChart hinvChart hgap hAc hbA hlowS hlowA
  obtain ⟨hAmp, hScalar⟩ := hjets ((X₀ ×ˢ Y₀) ×ˢ F₀) ρ hρ hcover
  have hAr := reverseAdmissible_of_forward hA hX₀ hY₀ hF₀
  have hsupp : ∀ p : Point n, p ∉ (X₀ ×ˢ Y₀) ×ˢ F₀ → uncurry A p = 0 := by
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  let H := C * normalizedGraphHigh z δ (is.length + (μ + 2)) S A
  have hbudget (p : FullAmplitude n r × List (Fin n)) :
      0 ≤ branchJetConstant n is.length μ L I * H ^ (((is.length - p.2.length : ℕ) : ℝ) / is.length) :=
    mul_nonneg (branchJetConstant_nonneg _ _ _ (zero_le_one.trans hL) (zero_le_one.trans hI))
      (Real.rpow_nonneg (zero_le_one.trans hH) _)
  constructor
  · intro p hp
    refine ⟨forward_branch_admissible hA hX₀ hY₀ hF₀ hF₀0 hcarrier hS is p hp,
      _, hbudget p, ?_⟩
    exact graph_branch_jet_norm_le_of_supported_geometry
      (hX₀.prod hY₀) hF₀ hF₀0 hO hcarrier hS hinv hAr.smooth hsupp
      ρ hρ (finitePrimitiveProfile z δ S A) hq hmono μ is.length
      L I H hL hI hH hlow hhigh hinterp hAmp hScalar is le_rfl p hp
  · intro p hp
    have hAc := hAr.conjTranspose
    have hAF : ∀ x y η, η ∉ F₀ → (A x y η).conjTranspose = 0 := by
      intro x y η hη
      simp only [hA.support x y η (Or.inr (Or.inr hη)), Matrix.conjTranspose_zero]
    have hpQ := reverse_branch_admissible hAc hAF hF₀ hF₀0 hcarrier hS hinv is p hp
    refine ⟨hpQ.1, hpQ.2, _, hbudget p, ?_⟩
    exact adjoint_branch_jet_norm_le_of_supported_geometry
      (A := fun x y η ↦ (A x y η).conjTranspose)
      (hX₀.prod hY₀) hF₀ hF₀0 hO hcarrier hS hinv hAc.smooth
      (fun p hp ↦ by
        change (uncurry A p).conjTranspose = 0
        rw [hsupp p hp, Matrix.conjTranspose_zero])
      ρ hρ (finitePrimitiveProfile z δ S A) hq hmono μ is.length
      L I H hL hI hH hlow hhigh hinterp
      (fun p hp w ↦ by simpa only [uncurry, norm_jet_conjTranspose] using hAmp p hp w)
      hScalar is le_rfl p hp

end JanetCartan.FourierIntegral.BranchRealization
