module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.ReverseTransfer

/-!
# Weak transfer for the literal adjoint on a buffered chart

The compact pairing is proved from original supported geometry. A smooth
auxiliary phase is used for integration by parts only; its mixed matrix and
homogeneity are used exclusively on the carrier, where germ agreement proves
them from the original phase. Finite distributional induction then gives the
actual weak derivatives, with no derivative identity assumed of the operator.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory LineDeriv JanetCartan.Pseudodifferential
open scoped ContDiff Topology SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

private theorem mem_carrier_of_ne_zero
    {K : Set (E × E)} {F : Set E} {C : FullAmplitude n r}
    (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    {x y η : E} (hc : C x y η ≠ 0) : ((x, y), η) ∈ K ×ˢ F := by
  refine ⟨hC.support (subset_tsupport _ hc), ?_⟩
  by_contra hη
  exact hc (hfreq x y η hη)

/-- The entire inverse-weighted datum branch is unchanged by phase germ
agreement on the supported carrier. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjointTransferDatum_phase_congr
    {K : Set (E × E)} {F : Set E} {C : FullAmplitude n r} {S S' : E → E → ℝ}
    (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (he : ∀ p ∈ K ×ˢ F, Function.uncurry S' =ᶠ[𝓝 (p.1.1, p.2)] Function.uncurry S)
    (i j : Fin n) : adjointTransferDatum S' i j C = adjointTransferDatum S i j C := by
  funext x y η
  by_cases hc : C x y η = 0
  · simp [adjointTransferDatum, hc]
  · simp only [adjointTransferDatum,
      mixedPhaseMatrix_eq_of_eventuallyEq (he _ (mem_carrier_of_ne_zero hC hfreq hc))]

/-- Germ agreement preserves the complete differentiated inverse-weighted
remainder, including derivatives of all source masks.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjointTransferRemainder_phase_congr
    {K : Set (E × E)} {F : Set E} {C : FullAmplitude n r} {S S' : E → E → ℝ}
    (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (he : ∀ p ∈ K ×ˢ F, Function.uncurry S' =ᶠ[𝓝 (p.1.1, p.2)] Function.uncurry S)
    (i : Fin n) : adjointTransferRemainder S' i C = adjointTransferRemainder S i C := by
  funext x y η
  simp only [adjointTransferRemainder, adjointTransferDatum_phase_congr hC hfreq he]

/-- Literal frequency-cut reverse kernels are unchanged on the supported
carrier, for the original amplitude and every differentiated branch.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem reverseGraphOperator_frequencyCut_phase_congr
    {K : Set (E × E)} {F : Set E} {C : FullAmplitude n r} {S S' : E → E → ℝ}
    (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (he : ∀ p ∈ K ×ˢ F, Function.uncurry S' =ᶠ[𝓝 (p.1.1, p.2)] Function.uncurry S)
    (χ : E → ℂ) (v : E → Fin r → ℂ) :
    reverseGraphOperator S' (frequencyCutFullAmplitude χ C) v =
      reverseGraphOperator S (frequencyCutFullAmplitude χ C) v := by
  apply reverseGraphOperator_phase_congr
  intro x y η hc
  have hCne : C x y η ≠ 0 := by
    intro hz
    exact hc (by simp [frequencyCutFullAmplitude, hz])
  exact (he _ (mem_carrier_of_ne_zero hC hfreq hCne)).eq_of_nhds

/-- The literal adjoint compact weak pairing requires phase regularity,
homogeneity and mixed invertibility only on the buffered supported chart.
No global homogeneous nondegenerate extension is assumed or constructed.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraphOperator_frequencyCut_weak_pairing_of_supported
    {K : Set (E × E)} {F : Set E} {U : Set (Point n)} {C : FullAmplitude n r}
    (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (hK : IsCompact K) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hU : IsOpen U) (hcarrier : K ×ˢ F ⊆ U) (S : E → E → ℝ)
    (hS : SupportedPhaseRegularity S U) (hinv : SupportedMixedInvertibility S U)
    (hhom : SupportedPhaseHomogeneity S U)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχ0 : (0 : E) ∉ tsupport χ)
    (i : Fin n) (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)) :
    (∫ y, partialDeriv φ y i • WithLp.toLp 2
      (reverseGraphOperator S (frequencyCutFullAmplitude χ C) (fun x ↦ (u.val x).ofLp) y)) =
      -((∫ y, φ y • WithLp.toLp 2
          (reverseGraphOperator S (frequencyCutFullAmplitude χ (adjointTransferRemainder S i C))
            (fun x ↦ (u.val x).ofLp) y)) +
        ∑ j, ∫ y, φ y • WithLp.toLp 2
          (reverseGraphOperator S (frequencyCutFullAmplitude χ (adjointTransferDatum S i j C))
            (fun x ↦ ((graphTestPartialDeriv j u).val x).ofLp) y)) := by
  obtain ⟨S', hs', he⟩ := exists_smooth_supported_phase_extension hK hF hF0 hU hcarrier S hS
  have hinv' : SupportedMixedInvertibility S' (K ×ˢ F) := by
    intro p hp
    rw [mixedPhaseMatrix_eq_of_eventuallyEq (he p hp)]
    exact hinv p (hcarrier hp)
  have hhom' : SupportedPhaseHomogeneity S' (K ×ˢ F) := by
    intro p hp hη
    exact phase_homogeneity_of_eventuallyEq (he p hp) (hhom p (hcarrier hp) hη)
  have hw := reverseGraphOperator_frequencyCut_weak_pairing_smooth_supported hC hK S'
    (fun _ _ _ ↦ hs'.contDiffAt) hF hF0 hfreq hinv' hhom' χ hχ hχs hχ0 i u φ
  simp_rw [adjointTransferRemainder_phase_congr hC hfreq he,
    adjointTransferDatum_phase_congr hC hfreq he] at hw
  have hR := hC.adjointTransferRemainder_of_supported S hfreq hF hF0 hcarrier hS hinv i
  have hP (j) := hC.adjointTransferDatum_of_supported S hfreq hF hF0 hcarrier hS hinv i j
  have hf := adjoint_branches_frequency_support (S := S) hfreq i
  simp_rw [reverseGraphOperator_frequencyCut_phase_congr hC hfreq he,
    reverseGraphOperator_frequencyCut_phase_congr hR hf.1 he,
    reverseGraphOperator_frequencyCut_phase_congr (hP _) (hf.2.1 _) he] at hw
  exact hw

/-- All finite weak derivatives of the reverse graph follow from the local
compact pairing and the supplied low distributional realizations.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraph_realization_weak_derivative_expansion_of_supported
    {K : Set (E × E)} {F : Set E} {U : Set (Point n)}
    (hK : IsCompact K) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hU : IsOpen U) (hcarrier : K ×ˢ F ⊆ U) (S : E → E → ℝ)
    (hS : SupportedPhaseRegularity S U) (hinv : SupportedMixedInvertibility S U)
    (hhom : SupportedPhaseHomogeneity S U)
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (hχ0 : ∀ k, (0 : E) ∉ tsupport (χ k))
    (T : FullAmplitude n r → H →L[ℂ] H)
    (C : FullAmplitude n r) (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (u : graphTestSpace n r) (is : List (Fin n))
    (hreal : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S) C js,
        GraphDistributionalRealization (reverseGraphOperator S) χ p.1 (T p.1)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (T C (graphTestToLp u) : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
        (adjointTransferDatum S) C is).map fun p ↦
        (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum := by
  let Q : FullAmplitude n r → Prop := fun B ↦ ReverseAmplitudeAdmissible K B ∧
    (∀ x y η, η ∉ F → B x y η = 0)
  apply fullAmplitudeDerivativeTerms_expansion_of_branch_realizations
    (reverseGraphOperator S) χ (adjointTransferRemainder S) (adjointTransferDatum S) T
    Q _ _ _ C ⟨hC, hfreq⟩ u is hreal
  · intro i B hB
    exact ⟨hB.1.adjointTransferRemainder_of_supported S hB.2 hF hF0 hcarrier hS hinv i,
      (adjoint_branches_frequency_support hB.2 i).1⟩
  · intro i j B hB
    exact ⟨hB.1.adjointTransferDatum_of_supported S hB.2 hF hF0 hcarrier hS hinv i j,
      (adjoint_branches_frequency_support hB.2 i).2.1 j⟩
  · intro B hB k i v φ
    exact reverseGraphOperator_frequencyCut_weak_pairing_of_supported hB.1 hB.2
      hK hF hF0 hU hcarrier S hS hinv hhom (χ k) (hχ k) (hχs k) (hχ0 k) i v φ

/-- Finite weak derivatives of the literal Hilbert adjoint `U.adjoint`. The
reverse coefficients start at `A(x,y,η).conjTranspose` in original coordinate
order, and every later branch uses the same reverse transfer without further
conjugation. Complex regularizers are conjugated exactly once.

`hreal` supplies low L² realizations only of the finitely many modified reverse
amplitudes through the requested order; `hadjoint` identifies the literal Hilbert adjoint itself with the initial
regularized reverse kernel. Both are precise distributional-limit premises,
produced by the graph realization and finite-calculus tasks. Equality with the
initial branch is deduced by uniqueness of limits. The parent strong Sobolev
assembly must instantiate these premises and the geometric data.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem adjointGraph_realization_weak_derivative_expansion_of_supported
    {K : Set (E × E)} {F : Set E} {O : Set (Point n)}
    (hK : IsCompact K) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hO : IsOpen O) (hcarrier : K ×ˢ F ⊆ O) (S : E → E → ℝ)
    (hS : SupportedPhaseRegularity S O) (hinv : SupportedMixedInvertibility S O)
    (hhom : SupportedPhaseHomogeneity S O)
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (hχ0 : ∀ k, (0 : E) ∉ tsupport (χ k))
    (T : FullAmplitude n r → H →L[ℂ] H)
    (A : FullAmplitude n r) (hA : ReverseAmplitudeAdmissible K A)
    (hfreq : ∀ x y η, η ∉ F → A x y η = 0) (U : H →L[ℂ] H)
    (hadjoint : GraphDistributionalRealization (reverseGraphOperator S)
      (fun k η ↦ star (χ k η)) (fun x y η ↦ (A x y η).conjTranspose) U.adjoint)
    (u : graphTestSpace n r) (is : List (Fin n))
    (hreal : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S)
        (fun x y η ↦ (A x y η).conjTranspose) js,
        GraphDistributionalRealization (reverseGraphOperator S)
          (fun k η ↦ star (χ k η)) p.1 (T p.1)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (U.adjoint (graphTestToLp u) : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S)
        (fun x y η ↦ (A x y η).conjTranspose) is).map fun p ↦
        (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum := by
  have hinit := hreal [] (Nat.zero_le _) ((fun x y η ↦ (A x y η).conjTranspose), [])
    (List.mem_singleton_self _)
  rw [← hinit.eq_on_tests hadjoint u]
  apply reverseGraph_realization_weak_derivative_expansion_of_supported hK hF hF0 hO hcarrier S hS hinv hhom
    (fun k η ↦ star (χ k η)) (fun k ↦ (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (hχ k))
    _ _ T _ hA.conjTranspose (fun x y η hη ↦ by simp [hfreq x y η hη]) u is hreal
  · intro k
    exact (hχs k).comp_left (star_zero _)
  · intro k
    apply fun hm ↦ hχ0 k ((tsupport_comp_subset (g := star) (star_zero _) _) hm)


end JanetCartan.FourierIntegral.SupportedSobolev
