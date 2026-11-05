module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.IntegerBounds

/-!
# A common natural-order bound for one graph and its literal adjoint

The finite calculus consumes one forward realization and its actual Hilbert
adjoint. This theorem uses the same amplitude, cutoffs, order and high seminorm
in both estimates; the branch realizations may be chosen independently.
Source: `app:ch_regular_base:eq:fio-input` and `app:ch_regular_base:eq:actual-adjoint-trade`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneProfiles
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Both natural-order bounds for the same graph realization and its literal
Hilbert adjoint. The fixed reserve is `μ₀+2`, chosen before `s`. The low reserve
and distributional realizations are the only operator premises; weak transfer,
primitive interpolation, branch bounds and output membership are proved.
Source: `app:ch_regular_base:eq:fio-input`. -/
theorem exists_graph_adjoint_integer_sobolev_constant
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B c C₀ : ℝ) (hc : 1 ≤ c) (hC₀ : 0 ≤ C₀)
    (d : ℕ) (hd : d = 0 ∨ d = 1) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∀ (O : Set (Point n)), IsOpen O → (X₀ ×ˢ Y₀) ×ˢ F₀ ⊆ O →
      ∀ (S : E → E → ℝ), SupportedPhaseRegularity S O →
      SupportedMixedInvertibility S O → SupportedPhaseHomogeneity S O →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + d + 2)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) → (∀ j, (0 : E) ∉ tsupport (χ j)) →
      ∀ (T Tstar : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ForwardAmplitudeAdmissible X₀ Y₀ F₀ A →
      GraphDistributionalRealization (graphOperator S) χ A (T A) → ‖T A‖ ≤ C₀ →
      GraphDistributionalRealization (reverseGraphOperator S)
        (fun j η ↦ star (χ j η)) (fun x y η ↦ (A x y η).conjTranspose) (T A).adjoint →
      (∀ i j, if d = 0 then
        BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)
        else BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) →
      (∀ i, (if d = 0 then
        normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ₀ (uncurry A)
        else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ₀ + 1) A) ≤ M) →
      ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
      (∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R ∧ R ≤ c * ρ p.2) →
      (∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ G →
        GraphDistributionalRealization (graphOperator S) χ G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      (if d = 0 then
        (∀ is : List (Fin n), is.length ≤ s →
          ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
            (graphTransferDatum S) A is,
            GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1))
      else
        (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
          ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
            (graphTransferDatum S) (graphFirstOutputAmplitude S A i) is,
            GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1))) →
      (∀ (G : FullAmplitude n r), ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) G →
        (∀ x y η, η ∉ F₀ → G x y η = 0) →
        GraphDistributionalRealization (reverseGraphOperator S)
          (fun j η ↦ star (χ j η)) G (Tstar G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖Tstar G‖ ≤ C₀ * L) →
      (if d = 0 then
        (∀ is : List (Fin n), is.length ≤ s →
          ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
            (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) is,
            GraphDistributionalRealization (reverseGraphOperator S)
              (fun j η ↦ star (χ j η)) p.1 (Tstar p.1))
      else
        (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
          ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
            (adjointTransferDatum S) (adjointFirstOutputAmplitude A i) is,
            GraphDistributionalRealization (reverseGraphOperator S)
              (fun j η ↦ star (χ j η)) p.1 (Tstar p.1))) →
      ∀ W : H →L[ℂ] H, W = T A ∨ W = (T A).adjoint →
      ∀ u : H, MemVectorFourierSobolev ((s - d : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤ C *
            (vectorFourierSobolevNorm ((s - d : ℕ) : ℝ) u +
              normalizedGraphOrderHigh d z δ (s + (μ₀ + 2)) S A * ‖u‖) := by
  intro s
  obtain ⟨Cg, hCg, hg⟩ := exists_graph_integer_sobolev_constant (n := n) (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ₀ hM B c C₀ hc hC₀ d hd s
  obtain ⟨Ca, hCa, ha⟩ := exists_adjoint_integer_sobolev_constant (n := n) (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ₀ hM B c C₀ hc hC₀ d hd s
  refine ⟨max Cg Ca, lt_max_of_lt_left hCg, ?_⟩
  intro X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
    hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 T Tstar A hA hrealA hlow hadjoint
    hbA hlowA ρ hρ hηρ hcover hl2g hrealg hl2a hreala W hW u hu
  have hsupp : tsupport (uncurry A) ⊆ (X₀ ×ˢ Y₀) ×ˢ F₀ := by
    apply tsupport_subset_carrier (hX₀.prod hY₀) hF₀
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  have hAr : ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) A := by
    refine ⟨?_, fun _ hp ↦ (hsupp hp).1⟩
    intro p _
    exact hA.smooth.contDiffAt.comp p
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  have hAF : ∀ x y η, η ∉ F₀ → A x y η = 0 :=
    fun x y η hη ↦ hA.support x y η (Or.inr (Or.inr hη))
  have hAc : ContDiffOn ℝ ∞ (uncurry A) V :=
    (hA.smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).contDiffOn
  have hlowAdj : ‖(T A).adjoint‖ ≤ C₀ := by
    simpa only [LinearIsometryEquiv.norm_map] using hlow
  have hhigh : 0 ≤ normalizedGraphOrderHigh d z δ (s + (μ₀ + 2)) S A := by
    unfold normalizedGraphOrderHigh
    split
    · exact zero_le_one.trans (one_le_normalizedGraphHigh _ _ _ _ _)
    · exact zero_le_one.trans (one_le_normalizedGainOneHigh _ _ _ _ _)
  have hR : 0 ≤ vectorFourierSobolevNorm ((s - d : ℕ) : ℝ) u +
      normalizedGraphOrderHigh d z δ (s + (μ₀ + 2)) S A * ‖u‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg hhigh (norm_nonneg _))
  rcases hW with rfl | rfl
  · have hb := hg X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs T A hA hrealA hlow hbA hlowA
      ρ hρ hcover hl2g hrealg u hu
    exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR)⟩
  · have hb := ha (X₀ ×ˢ Y₀) F₀ (hX₀.prod hY₀) hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 Tstar A hAr hAF hAc hbA hlowA
      (T A) hadjoint hlowAdj ρ hρ hηρ hcover hl2a hreala u hu
    exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)⟩

end JanetCartan.FourierIntegral.SupportedSobolev
