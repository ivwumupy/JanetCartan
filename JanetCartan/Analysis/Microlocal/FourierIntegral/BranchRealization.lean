module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.BranchRealization.OrderZero
public import JanetCartan.Analysis.Microlocal.FourierIntegral.BranchRealization.GainOne

/-!
# Supported derivative branches of the same full graph operators

`supported_graph_operator_inputs` eliminates all initial and derivative-branch
operator premises of `SupportedSobolev.exists_graph_adjoint_integer_sobolev_constant`
for `FullLowBounds.fullGraphOperator S` and `reverseFullGraphOperator S`.
Its only operator inputs are precisely the two universal weighted low clauses
produced by `exists_fullGraphFamily_of_wholeImage_phase` in
`PrimitiveRealization.Family`. The parent instantiates those clauses and performs
the Sobolev assembly. This deduction does not assert unconditional existence.

Every branch budget and admissibility statement is proved from the original
supported phase and normalized amplitude data. The cutoff sequence, phase, full
physical supports and once-conjugated reverse amplitude remain unchanged.
The low reserve is `fullLowReserve n = 3*n+4`, independent of output order;
the consumer's fixed high shift is therefore `3*n+6`.
Source: `app:ch_regular_base:eq:fio-input` and
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.BranchRealization
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneProfiles SupportedSobolev FullLowBounds
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The initial amplitude, its literal Hilbert adjoint and every actual transfer
branch satisfy the exact operator premises of the paired integer Sobolev theorem.
The common low constant is `C * (1 + M)`, depending only on declared low data.
The only operator hypotheses are the two universal weighted low clauses of
`exists_fullGraphFamily_of_wholeImage_phase`; no branch realization, branch
operator bound or high Sobolev estimate is assumed. The parent is responsible
for instantiating those two clauses from its concrete geometry.
Source: `app:ch_regular_base:eq:fio-input`, including the gain-one paragraph
after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem supported_graph_operator_inputs
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    {M : ℝ} (hM : 0 ≤ M) (B c C : ℝ) (hc : 1 ≤ c) (hC : 0 ≤ C)
    (d : ℕ) (hd : d = 0 ∨ d = 1)
    {X₀ Y₀ F₀ : Set E} (hX₀ : IsCompact X₀) (hY₀ : IsCompact Y₀)
    (hF₀ : IsClosed F₀) (hF₀0 : (0 : E) ∉ F₀)
    {O : Set (Point n)} (hO : IsOpen O) (hcarrier : (X₀ ×ˢ Y₀) ×ˢ F₀ ⊆ O)
    (S : E → E → ℝ) (hS : SupportedPhaseRegularity S O)
    (hinv : SupportedMixedInvertibility S O)
    (hSchart : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hhomChart : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    (hinvChart : ∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det)
    (hgap : ∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B)
    (hlowS : ∀ i, cNorm (Metric.closedBall (z i) (δ i)) (fullLowReserve n + d + 2)
      (fun p : Point n ↦ S p.1.1 p.2) ≤ M)
    (χ : ℕ → E → ℂ) (A : FullAmplitude n r)
    (hA : ForwardAmplitudeAdmissible X₀ Y₀ F₀ A)
    (hbA : ∀ i j, if d = 0 then
      BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)
      else BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A)
    (hlowA : ∀ i, (if d = 0 then
      normalizedSeminorm (Metric.closedBall (z i) (δ i)) (fullLowReserve n) (uncurry A)
      else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (fullLowReserve n + 1) A) ≤ M)
    (ρ : E → ℝ) (hρ : ∀ η, 1 ≤ ρ η) (hηρ : ∀ η, ‖η‖ ≤ ρ η)
    (hcover : ∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R ∧ R ≤ c * ρ p.2)
    (hforward : ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
      ∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ G →
      ∀ L : ℝ, 0 ≤ L →
      (∀ w : List (Coordinate n), w.length ≤ fullLowReserve n → ∀ x y η,
        (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) →
      ‖fullGraphOperator S G‖ ≤ C * L ∧
        GraphDistributionalRealization (graphOperator S) χ G (fullGraphOperator S G))
    (hreverse : ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
      ∀ (K₀ : Set (E × E)), K₀ ⊆ X₀ ×ˢ Y₀ →
      ∀ (G : FullAmplitude n r), ReverseAmplitudeAdmissible K₀ G →
      (∀ x y η, η ∉ F₀ → G x y η = 0) → ∀ L : ℝ, 0 ≤ L →
      (∀ w : List (Coordinate n), w.length ≤ fullLowReserve n → ∀ x y η,
        (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) →
      ‖reverseFullGraphOperator S G‖ ≤ C * L ∧
        GraphDistributionalRealization (reverseGraphOperator S) (fun j η ↦ star (χ j η))
          G (reverseFullGraphOperator S G)) :
    GraphDistributionalRealization (graphOperator S) χ A (fullGraphOperator S A) ∧
    ‖fullGraphOperator S A‖ ≤ C * (1 + M) ∧
    GraphDistributionalRealization (reverseGraphOperator S) (fun j η ↦ star (χ j η))
      (fun x y η ↦ (A x y η).conjTranspose) (fullGraphOperator S A).adjoint ∧
    (∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ G →
      GraphDistributionalRealization (graphOperator S) χ G (fullGraphOperator S G) →
      ∀ L : ℝ, 0 ≤ L →
      (∀ w : List (Coordinate n), w.length ≤ fullLowReserve n → ∀ x y η,
        (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) →
      ‖fullGraphOperator S G‖ ≤ (C * (1 + M)) * L) ∧
    (∀ (G : FullAmplitude n r), ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) G →
      (∀ x y η, η ∉ F₀ → G x y η = 0) →
      GraphDistributionalRealization (reverseGraphOperator S)
        (fun j η ↦ star (χ j η)) G (reverseFullGraphOperator S G) →
      ∀ L : ℝ, 0 ≤ L →
      (∀ w : List (Coordinate n), w.length ≤ fullLowReserve n → ∀ x y η,
        (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) →
      ‖reverseFullGraphOperator S G‖ ≤ (C * (1 + M)) * L) ∧
    ∀ s : ℕ,
      (if d = 0 then
        (∀ is : List (Fin n), is.length ≤ s →
          ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
            (graphTransferDatum S) A is,
            GraphDistributionalRealization (graphOperator S) χ p.1 (fullGraphOperator S p.1))
      else
        (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
          ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
            (graphTransferDatum S) (graphFirstOutputAmplitude S A i) is,
            GraphDistributionalRealization (graphOperator S) χ p.1 (fullGraphOperator S p.1))) ∧
      (if d = 0 then
        (∀ is : List (Fin n), is.length ≤ s →
          ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
            (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) is,
            GraphDistributionalRealization (reverseGraphOperator S)
              (fun j η ↦ star (χ j η)) p.1 (reverseFullGraphOperator S p.1))
      else
        (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
          ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
            (adjointTransferDatum S) (adjointFirstOutputAmplitude A i) is,
            GraphDistributionalRealization (reverseGraphOperator S)
              (fun j η ↦ star (χ j η)) p.1 (reverseFullGraphOperator S p.1))) := by
  have hcover' : ∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R := by
    intro p hp
    obtain ⟨i, R, hR, v, hv, he, hρR, _⟩ := hcover p hp
    exact ⟨i, R, hR, v, hv, he, hρR⟩
  have hbudget := initial_weighted_jets_le z δ U hU hV hball hrad hX₀ hY₀ hF₀
    (fullLowReserve n) d hM hA hbA hlowA ρ hρ hcover'
  obtain ⟨hlow, hreal⟩ := hforward ρ hρ hηρ A hA M hM hbudget
  have hAr := (reverseAdmissible_of_forward hA hX₀ hY₀ hF₀).conjTranspose
  have hAF : ∀ x y η, η ∉ F₀ → (A x y η).conjTranspose = 0 := by
    intro x y η hη
    simp only [hA.support x y η (Or.inr (Or.inr hη)), Matrix.conjTranspose_zero]
  have hadjoint := (hreverse ρ hρ hηρ (X₀ ×ˢ Y₀) Set.Subset.rfl
    (fun x y η ↦ (A x y η).conjTranspose) hAr hAF M hM
    (fun w hw x y η ↦ by simpa only [norm_jet_conjTranspose] using hbudget w hw x y η)).2
  rw [reverseFullGraphOperator_conjTranspose] at hadjoint
  have hCC : C ≤ C * (1 + M) := le_mul_of_one_le_right hC (by linarith)
  refine ⟨hreal, hlow.trans (mul_le_mul_of_nonneg_left (by linarith) hC), hadjoint,
    ?_, ?_, ?_⟩
  · intro G hG _ L hL hjets
    exact (hforward ρ hρ hηρ G hG L hL hjets).1.trans (mul_le_mul_of_nonneg_right hCC hL)
  · intro G hG hGF _ L hL hjets
    exact (hreverse ρ hρ hηρ (X₀ ×ˢ Y₀) Set.Subset.rfl G hG hGF L hL hjets).1.trans
      (mul_le_mul_of_nonneg_right hCC hL)
  · intro s
    rcases hd with rfl | rfl
    · simp only [↓reduceIte, Nat.add_zero] at hbA hlowA hlowS ⊢
      have hb := orderZero_branch_budgets z δ hδ U hU hV hball hrad hX hD hchart hcone
        (fullLowReserve n) hM B hX₀ hY₀ hF₀ hF₀0 hO hcarrier S hS hinv
        hSchart hhomChart hinvChart hgap hlowS A hA hbA hlowA
        ρ (fun η ↦ zero_le_one.trans (hρ η)) hcover'
      constructor
      · intro is _ p hp
        obtain ⟨hG, L, hL, hjets⟩ := (hb is).1 p hp
        exact (hforward ρ hρ hηρ p.1 hG L hL hjets).2
      · intro is _ p hp
        obtain ⟨hG, hGF, L, hL, hjets⟩ := (hb is).2 p hp
        exact (hreverse ρ hρ hηρ (X₀ ×ˢ Y₀) Set.Subset.rfl p.1 hG hGF L hL hjets).2
    · simp only [Nat.one_ne_zero, ↓reduceIte] at hbA hlowA ⊢
      have hlowS' : ∀ i, cNorm (Metric.closedBall (z i) (δ i)) (fullLowReserve n + 3)
          (fun p : Point n ↦ S p.1.1 p.2) ≤ M := by
        simpa only [Nat.add_assoc] using hlowS
      have hb := gainOne_branch_budgets z δ hδ U hU hV hball hrad hX hD hchart hcone
        (fullLowReserve n) hM B c hc hX₀ hY₀ hF₀ hF₀0 hO hcarrier S hS hinv
        hSchart hhomChart hinvChart hgap hlowS' A hA hbA hlowA ρ hρ hηρ hcover
      constructor
      · intro i is _ p hp
        obtain ⟨hG, L, hL, hjets⟩ := (hb i is).1 p hp
        exact (hforward ρ hρ hηρ p.1 hG L hL hjets).2
      · intro i is _ p hp
        obtain ⟨hG, hGF, L, hL, hjets⟩ := (hb i is).2 p hp
        exact (hreverse ρ hρ hηρ (X₀ ×ˢ Y₀) Set.Subset.rfl p.1 hG hGF L hL hjets).2

end JanetCartan.FourierIntegral.BranchRealization
