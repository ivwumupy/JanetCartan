module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientJets

/-!
# Supports and initial low budgets for the fixed graph family

These deductions supply the initial operator and branch admissibility premises
of `SupportedSobolev.exists_graph_adjoint_integer_sobolev_constant`.
The original phase, both physical positions and every amplitude mask are retained.
Source: `app:ch_regular_base:eq:fio-input` and
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.BranchRealization
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneProfiles SupportedSobolev
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Full forward supports also give the reverse admissibility needed for the
literal adjoint in `app:ch_regular_base:eq:fio-input`. -/
theorem reverseAdmissible_of_forward {X Y F : Set E} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F) :
    ReverseAmplitudeAdmissible (X ×ˢ Y) A := by
  have hsupp : tsupport (uncurry A) ⊆ (X ×ˢ Y) ×ˢ F := by
    apply tsupport_subset_carrier (hX.prod hY) hF
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  refine ⟨?_, fun _ hp ↦ (hsupp hp).1⟩
  intro p _
  exact hA.smooth.contDiffAt.comp p
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))

/-- Every forward transfer branch preserves the full original carrier.
Consumer: branch realization in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem forward_branch_admissible {X Y F : Set E} {O : Set (Point n)}
    {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ O) (hS : SupportedPhaseRegularity S O)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is) : ForwardAmplitudeAdmissible X Y F p.1 := by
  exact fullAmplitudeDerivativeTerms_preserves_predicate _ _ (ForwardAmplitudeAdmissible X Y F)
    (fun i G hG ↦ hG.graphTransferRemainder_of_supported S hX.isClosed hY.isClosed
      hF hF0 hcarrier hS i)
    (fun i j G hG ↦ hG.graphTransferDatum_of_supported S hX.isClosed hY.isClosed
      hF hF0 hcarrier hS i j) A hA is p hp

/-- Every reverse transfer branch retains both physical and frequency supports.
The input is already conjugated once, as required by
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem reverse_branch_admissible {K : Set (E × E)} {F : Set E} {O : Set (Point n)}
    {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ReverseAmplitudeAdmissible K A)
    (hAF : ∀ x y η, η ∉ F → A x y η = 0)
    (hF : IsClosed F) (hF0 : (0 : E) ∉ F) (hcarrier : K ×ˢ F ⊆ O)
    (hS : SupportedPhaseRegularity S O) (hinv : SupportedMixedInvertibility S O)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is) :
    ReverseAmplitudeAdmissible K p.1 ∧ (∀ x y η, η ∉ F → p.1 x y η = 0) := by
  apply fullAmplitudeDerivativeTerms_preserves_predicate _ _
    (fun G ↦ ReverseAmplitudeAdmissible K G ∧ (∀ x y η, η ∉ F → G x y η = 0))
    _ _ _ ⟨hA, hAF⟩ is p hp
  · intro i G hG
    exact ⟨hG.1.adjointTransferRemainder_of_supported S hG.2 hF hF0 hcarrier hS hinv i,
      (adjoint_branches_frequency_support hG.2 i).1⟩
  · intro i j G hG
    exact ⟨hG.1.adjointTransferDatum_of_supported S hG.2 hF hF0 hcarrier hS hinv i j,
      (adjoint_branches_frequency_support hG.2 i).2.1 j⟩

/-- The original amplitude's weighted low jets are controlled by the declared
low amplitude bound alone, in either order. This supplies the initial low
operator bound in `app:ch_regular_base:eq:fio-input`, independently of output order. -/
theorem initial_weighted_jets_le {ι : Type*}
    (z : ι → Point n) (δ : ι → ℝ) (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F)
    (μ d : ℕ) {M : ℝ} (hM : 0 ≤ M) {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hbA : ∀ i j, if d = 0 then
      BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)
      else BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A)
    (hlowA : ∀ i, (if d = 0 then
      normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ (uncurry A)
      else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ + 1) A) ≤ M)
    (ρ : E → ℝ) (hρ : ∀ η, 1 ≤ ρ η)
    (hcover : ∀ p ∈ (X ×ˢ Y) ×ˢ F, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R) :
    ∀ w : List (Coordinate n), w.length ≤ μ → ∀ x y η,
      (ρ η) ^ frequencyOrder w * ‖jet w A x y η‖ ≤ M := by
  have hAc : ContDiffOn ℝ ∞ (uncurry A) V :=
    (hA.smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).contDiffOn
  have hsupp : tsupport (uncurry A) ⊆ (X ×ˢ Y) ×ˢ F := by
    apply tsupport_subset_carrier (hX.prod hY) hF
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  intro w hw x y η
  by_cases hz : jet w A x y η = 0
  · simpa only [hz, norm_zero, mul_zero] using hM
  have hc : ((x, y), η) ∈ (X ×ˢ Y) ×ˢ F :=
    hsupp (tsupport_jet_subset w A (subset_tsupport (uncurry (jet w A)) hz))
  obtain ⟨i, R, hR, v, hv, he, hρR⟩ := hcover ((x, y), η) hc
  change (ρ ((x, y), η).2) ^ frequencyOrder w * ‖uncurry (jet w A) ((x, y), η)‖ ≤ M
  rw [he] at hρR ⊢
  by_cases hd : d = 0
  · simp only [hd, ↓reduceIte] at hbA hlowA
    exact ((mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (zero_le_one.trans (hρ _)) hρR _) (norm_nonneg _)).trans
      (weighted_jet_le_normalizedSeminorm (z i) (hU i) hV (hball i) hAc
        (fun _ hR ↦ contDiffOn_normalizedField_of_dilations hAc (hrad i) hR)
        w (hbA i _) hR v hv (hrad i R hR v (hball i hv)))).trans
      ((normalizedSeminorm_mono (hbA i μ) hw).trans (hlowA i))
  · simp only [hd, ↓reduceIte] at hbA hlowA
    apply (weighted_amplitude_jet_le (z i) (hU i) hV (hball i) (hrad i)
      hAc hR (lt_of_lt_of_le zero_lt_one (hρ _)) hρR hv w).trans
    apply (div_le_self (cNorm_nonneg _ _ _) (hρ _)).trans
    exact (CNormInterpolation.cNorm_mono _ _ (show w.length ≤ μ + 1 by omega)).trans
      ((cNorm_orderMinusOneField_le (hbA i (μ + 1)) hR).trans (hlowA i))

end JanetCartan.FourierIntegral.BranchRealization
