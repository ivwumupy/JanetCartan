module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.WeightedGeometry
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.ForwardWeakTransfer
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.ReverseWeakTransfer
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds

/-!
# Strong graph estimates from weighted primitive inputs and a low L² reserve

This joins the actual weak expansions, weighted primitive budgets and Fourier
assembly for `app:ch_regular_base:eq:fio-input`. No high branch estimate or
operator derivative identity is assumed. Constants precede all high majorants,
phases, amplitudes and data. The L² premise is a fixed finite weighted jet
reserve, applied here to the complete modified amplitudes.

The primitive majorants and their interpolation still require construction from
the paper's normalized phase/amplitude seminorms and inverse gap. The exact
low L² estimate and distributional realizations are supplied analytic inputs
owed by the finite-calculus and graph-realization producers. These implications
do not finish that construction or identify the high majorant with the paper's
`1 + |A|_(s+μ) + |S|_(s+μ)`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter LineDeriv JanetCartan.Pseudodifferential
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The forward graph has the strong all-data integer Sobolev estimate from
weighted primitive bounds and the fixed low L² reserve. Weak differentiation,
branch norms and output membership are proved. Individual primitive interpolation
and endpoint comparison remain conditional; their producer is the normalized
phase/amplitude construction. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem exists_graph_sobolev_constant_of_weighted_primitives
    (μ s : ℕ) (L K C₀ : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X Y F : Set E), IsCompact X → IsCompact Y → IsClosed F → (0 : E) ∉ F →
      ∀ (O : Set (Point n)), IsOpen O → (X ×ˢ Y) ×ˢ F ⊆ O →
      ∀ (S : E → E → ℝ), SupportedPhaseRegularity S O →
      SupportedMixedInvertibility S O → SupportedPhaseHomogeneity S O →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ForwardAmplitudeAdmissible X Y F A →
      ∀ (ρ : E → ℝ), (∀ η, 0 ≤ ρ η) →
      (∀ (B : FullAmplitude n r), ForwardAmplitudeAdmissible X Y F B →
        GraphDistributionalRealization (graphOperator S) χ B (T B) → ∀ D : ℝ, 0 ≤ D →
        (∀ w : List (Coordinate n), w.length ≤ μ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w B x y η‖ ≤ D) → ‖T B‖ ≤ C₀ * D) →
      ∀ (q : Option (ScalarIndex n) → ℕ → ℝ) (Hhigh : ℝ),
      (∀ a j, 0 ≤ q a j) → (∀ a, Monotone (q a)) → 1 ≤ Hhigh →
      (∀ a, q a μ ≤ L) → (∀ a, q a (μ + s) ≤ Hhigh) →
      (∀ a j, μ < j → j < μ + s →
        q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
          q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s)) →
      (∀ p ∈ (X ×ˢ Y) ×ˢ F, ∀ w,
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤ q none w.length) →
      (∀ p ∈ (X ×ˢ Y) ×ˢ F, ∀ a w,
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
          q (some a) w.length) →
      (∀ is : List (Fin n), is.length ≤ s →
        ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
          (graphTransferDatum S) A is,
          GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T A u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T A u) ≤
            C * (vectorFourierSobolevNorm (s : ℝ) u + Hhigh * ‖u‖) := by
  obtain ⟨C, hC, hb⟩ := exists_graph_vector_sobolev_constant_all_data (n := n) (r := r) s
    (C₀ * branchJetConstant n s μ L K)
    (mul_nonneg hC₀ (branchJetConstant_nonneg n s μ (zero_le_one.trans hL) (zero_le_one.trans hK)))
  refine ⟨C, hC, ?_⟩
  intro X Y F hX hY hF hF0 O hO hcarrier S hS hinv hhom χ hχ hχs T A hA
    ρ hρ hl2 q Hhigh hq hmono hH hlow hhigh hinterp hAmp hScalar hreal u hu
  have hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p := by
    intro p _
    exact hA.smooth.contDiffAt.comp p
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  have hsupp : ∀ p : Point n, p ∉ (X ×ˢ Y) ×ˢ F → uncurry A p = 0 := by
    intro p hp
    apply hA.support
    simpa only [Set.mem_prod, not_and_or, or_assoc] using hp
  apply hb (graphTransferRemainder S) (graphTransferDatum S) A T
    (T A) Hhigh (zero_le_one.trans hH) ?_ ?_ u hu
  · intro v is his
    exact graph_realization_weak_derivative_expansion_of_supported hX hY hF hF0 hcarrier hS hhom
      χ hχ hχs T hA v is (fun js hjs p hp ↦ hreal js (hjs.trans his) p hp)
  · intro is his p hp
    have hpA : ForwardAmplitudeAdmissible X Y F p.1 :=
      fullAmplitudeDerivativeTerms_preserves_predicate _ _ (ForwardAmplitudeAdmissible X Y F)
        (fun i B hB ↦ hB.graphTransferRemainder_of_supported S hX.isClosed hY.isClosed hF hF0 hcarrier hS i)
        (fun i j B hB ↦ hB.graphTransferDatum_of_supported S hX.isClosed hY.isClosed hF hF0 hcarrier hS i j) A hA is p hp
    have hlen := (fullAmplitudeDerivativeTerms_datum_length_le
      (graphTransferRemainder S) (graphTransferDatum S) A is p hp).trans his
    have hj := graph_branch_jet_norm_le_of_supported_geometry
      (hX.prod hY) hF hF0 hO hcarrier hS hinv hsmooth hsupp
      ρ hρ q hq hmono μ s L K Hhigh hL hK hH hlow hhigh hinterp
      hAmp hScalar is his p hp
    have hn := hl2 p.1 hpA (hreal is his p hp) (branchJetConstant n s μ L K *
      Hhigh ^ (((s - p.2.length : ℕ) : ℝ) / s))
      (mul_nonneg (branchJetConstant_nonneg n s μ (zero_le_one.trans hL) (zero_le_one.trans hK))
        (Real.rpow_nonneg (zero_le_one.trans hH) _)) hj
    simpa only [Nat.cast_sub hlen, mul_assoc] using hn

/-- The literal Hilbert adjoint has the strong all-data integer Sobolev estimate from
weighted primitive bounds and the fixed low L² reserve. Weak differentiation,
branch norms and output membership are proved. Individual primitive interpolation
and endpoint comparison remain conditional; their producer is the normalized
phase/amplitude construction. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem exists_adjoint_sobolev_constant_of_weighted_primitives
    (μ s : ℕ) (L K C₀ : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K₀ : Set (E × E)) (F : Set E), IsCompact K₀ → IsClosed F → (0 : E) ∉ F →
      ∀ (O : Set (Point n)), IsOpen O → K₀ ×ˢ F ⊆ O →
      ∀ (S : E → E → ℝ), SupportedPhaseRegularity S O →
      SupportedMixedInvertibility S O → SupportedPhaseHomogeneity S O →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) →
      (∀ j, (0 : E) ∉ tsupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ReverseAmplitudeAdmissible K₀ A →
      (∀ x y η, η ∉ F → A x y η = 0) →
      ∀ U : H →L[ℂ] H,
      GraphDistributionalRealization (reverseGraphOperator S)
        (fun j η ↦ star (χ j η)) (fun x y η ↦ (A x y η).conjTranspose) U.adjoint →
      ∀ (ρ : E → ℝ), (∀ η, 0 ≤ ρ η) →
      (∀ (B : FullAmplitude n r), ReverseAmplitudeAdmissible K₀ B →
        (∀ x y η, η ∉ F → B x y η = 0) →
        GraphDistributionalRealization (reverseGraphOperator S) (fun j η ↦ star (χ j η)) B (T B) →
        ∀ D : ℝ, 0 ≤ D →
        (∀ w : List (Coordinate n), w.length ≤ μ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w B x y η‖ ≤ D) → ‖T B‖ ≤ C₀ * D) →
      ∀ (q : Option (ScalarIndex n) → ℕ → ℝ) (Hhigh : ℝ),
      (∀ a j, 0 ≤ q a j) → (∀ a, Monotone (q a)) → 1 ≤ Hhigh →
      (∀ a, q a μ ≤ L) → (∀ a, q a (μ + s) ≤ Hhigh) →
      (∀ a j, μ < j → j < μ + s →
        q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
          q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s)) →
      (∀ p ∈ K₀ ×ˢ F, ∀ w,
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤ q none w.length) →
      (∀ p ∈ K₀ ×ˢ F, ∀ a w,
        (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
          q (some a) w.length) →
      (∀ is : List (Fin n), is.length ≤ s →
        ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
          (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) is,
          GraphDistributionalRealization (reverseGraphOperator S) (fun j η ↦ star (χ j η)) p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (U.adjoint u) ∧
          vectorFourierSobolevNorm (s : ℝ) (U.adjoint u) ≤
            C * (vectorFourierSobolevNorm (s : ℝ) u + Hhigh * ‖u‖) := by
  obtain ⟨C, hC, hb⟩ := exists_graph_vector_sobolev_constant_all_data (n := n) (r := r) s
    (C₀ * branchJetConstant n s μ L K)
    (mul_nonneg hC₀ (branchJetConstant_nonneg n s μ (zero_le_one.trans hL) (zero_le_one.trans hK)))
  refine ⟨C, hC, ?_⟩
  intro K₀ F hK₀ hF hF0 O hO hcarrier S hS hinv hhom χ hχ hχs hχ0 T A hA hAF U hadjoint
    ρ hρ hl2 q Hhigh hq hmono hH hlow hhigh hinterp hAmp hScalar hreal u hu
  have hA' := hA.conjTranspose
  have hsupp : ∀ p : Point n, p ∉ K₀ ×ˢ F → uncurry (fun x y η ↦ (A x y η).conjTranspose) p = 0 := by
    intro p hp
    by_cases hk : p.1 ∈ K₀
    · have hf : p.2 ∉ F := fun hf ↦ hp ⟨hk, hf⟩
      simp [uncurry, hAF _ _ _ hf]
    · exact image_eq_zero_of_notMem_tsupport (fun hm ↦ hk (hA'.support hm))
  apply hb (adjointTransferRemainder S) (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) T
    (U.adjoint) Hhigh (zero_le_one.trans hH) ?_ ?_ u hu
  · intro v is his
    exact adjointGraph_realization_weak_derivative_expansion_of_supported hK₀ hF hF0 hO hcarrier S hS hinv hhom
      χ hχ hχs hχ0 T A hA hAF U hadjoint v is
      (fun js hjs p hp ↦ hreal js (hjs.trans his) p hp)
  · intro is his p hp
    have hpQ : ReverseAmplitudeAdmissible K₀ p.1 ∧
        (∀ x y η, η ∉ F → p.1 x y η = 0) := by
      apply fullAmplitudeDerivativeTerms_preserves_predicate _ _
        (fun B ↦ ReverseAmplitudeAdmissible K₀ B ∧ (∀ x y η, η ∉ F → B x y η = 0))
        _ _ _ ⟨hA', fun x y η hη ↦ by simp [hAF x y η hη]⟩ is p hp
      · intro i B hB
        exact ⟨hB.1.adjointTransferRemainder_of_supported S hB.2 hF hF0 hcarrier hS hinv i,
          (adjoint_branches_frequency_support hB.2 i).1⟩
      · intro i j B hB
        exact ⟨hB.1.adjointTransferDatum_of_supported S hB.2 hF hF0 hcarrier hS hinv i j,
          (adjoint_branches_frequency_support hB.2 i).2.1 j⟩
    have hlen := (fullAmplitudeDerivativeTerms_datum_length_le
      (adjointTransferRemainder S) (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) is p hp).trans his
    have hj := adjoint_branch_jet_norm_le_of_supported_geometry
      (A := fun x y η ↦ (A x y η).conjTranspose)
      hK₀ hF hF0 hO hcarrier hS hinv hA'.smooth hsupp
      ρ hρ q hq hmono μ s L K Hhigh hL hK hH hlow hhigh hinterp
      (fun z hz w ↦ by simpa only [uncurry, norm_jet_conjTranspose] using hAmp z hz w)
      hScalar is his p hp
    have hn := hl2 p.1 hpQ.1 hpQ.2 (hreal is his p hp) (branchJetConstant n s μ L K *
      Hhigh ^ (((s - p.2.length : ℕ) : ℝ) / s))
      (mul_nonneg (branchJetConstant_nonneg n s μ (zero_le_one.trans hL) (zero_le_one.trans hK))
        (Real.rpow_nonneg (zero_le_one.trans hH) _)) hj
    simpa only [Nat.cast_sub hlen, mul_assoc] using hn

end JanetCartan.FourierIntegral.SupportedSobolev
