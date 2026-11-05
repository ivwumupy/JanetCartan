module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.ForwardDerivative
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Realization

/-!
# Compact-frequency forward weak pairings

The actual `hpair` input of
`fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings`, for
`K = graphOperator S`, `R = graphTransferRemainder S`, and
`P = graphTransferDatum S`. The accompanying admissibility predicate supplies
its `hR` and `hP` inputs. All analytic premises are primitive smoothness,
homogeneity and support conditions. No realization producer is required here.

Source: `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}
variable {U : Set (Point n)} {X Y F : Set (Euclidean n)} {S : Euclidean n → Euclidean n → ℝ}
  {A : FullAmplitude n r} {u : Euclidean n → Fin r → ℂ}

namespace ForwardRegularized
open FourierIntegral.ForwardRegularized

/-- Output integration by parts for the actual full compact-frequency graph
kernel. This array-valued form is converted to the complex Hilbert fiber in
`graphOperator_frequencyCut_weak_pairing`.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem weak_pairing_coordinates
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsClosed Y) (hF : IsClosed F) (hF0 : (0 : Euclidean n) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hhom : SupportedPhaseHomogeneity S U)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hAK : ∀ x y η, η ∉ K → A x y η = 0)
    (φ : Euclidean n → ℂ) (hφ : ContDiff ℝ ∞ φ) (i : Fin n) :
    (∫ x, partialDeriv φ x i • graphOperator S A u x) =
      -((∫ x, φ x • graphOperator S (graphTransferRemainder S i A) u x) +
        ∑ j, ∫ x, φ x • graphOperator S (graphTransferDatum S i j A)
          (fun y ↦ partialDeriv u y j) x) := by
  have hg := smooth_graphOperator hA hX.isClosed hY hF hF0 hcarrier hS hu hus hK hAK
  have hgs := compactSupport_graphOperator (S := S) (u := u) hA hX
  have hi : Integrable (fun x ↦ φ x • graphOperator S A u x) :=
    (hφ.continuous.smul hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hiφ : Integrable (fun x ↦ partialDeriv φ x i • graphOperator S A u x) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hig : Integrable (fun x ↦ φ x • partialDeriv (graphOperator S A u) x i) :=
    (hφ.continuous.smul ((hg.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        (hgs.fderiv_apply ℝ (EuclideanSpace.single i 1)).smul_left
  have hb := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hiφ hig hi
    (fun x _ ↦ hφ.differentiable (by simp) x) (fun x _ ↦ hg.differentiable (by simp) x)
  have hw : (∫ x, partialDeriv φ x i • graphOperator S A u x) =
      -(∫ x, φ x • partialDeriv (graphOperator S A u) x i) := by
    simpa only [partialDeriv, neg_neg] using congrArg Neg.neg hb.symm
  rw [hw]
  simp_rw [partialDeriv_graphOperator_transfer hA hX.isClosed hY hF hF0 hcarrier hS hhom hu hus
    hK hAK _ i, smul_add, Finset.smul_sum]
  congr 1
  have hR := hA.graphTransferRemainder_of_supported S hX.isClosed hY hF hF0 hcarrier hS i
  have hP (j) := hA.graphTransferDatum_of_supported S hX.isClosed hY hF hF0 hcarrier hS i j
  have hRK : ∀ x y η, η ∉ K → graphTransferRemainder S i A x y η = 0 := by
    intro z y η hη
    have ha (z y) : A z y η = 0 := hAK z y η hη
    simp [graphTransferRemainder, ha, partialDeriv]
  have hPK (j) : ∀ x y η, η ∉ K → graphTransferDatum S i j A x y η = 0 := by
    intro z y η hη
    simp [graphTransferDatum, hAK z y η hη]
  have hiR : Integrable (fun x ↦ φ x • graphOperator S (graphTransferRemainder S i A) u x) :=
    (hφ.continuous.smul (smooth_graphOperator hR hX.isClosed hY hF hF0 hcarrier hS hu hus hK hRK).continuous).integrable_of_hasCompactSupport (compactSupport_graphOperator hR hX).smul_left
  have hiP (j) : Integrable (fun x ↦ φ x • graphOperator S (graphTransferDatum S i j A)
      (fun y ↦ partialDeriv u y j) x) :=
    (hφ.continuous.smul (smooth_graphOperator (hP j) hX.isClosed hY hF hF0 hcarrier hS
      ((hu.fderiv_right (by simp)).clm_apply contDiff_const)
      (hus.fderiv_apply ℝ (EuclideanSpace.single j 1)) hK (hPK j)).continuous).integrable_of_hasCompactSupport (compactSupport_graphOperator (hP j) hX).smul_left
  rw [integral_add hiR (integrable_finsetSum Finset.univ (fun j _ ↦ hiP j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hiP j)]

end ForwardRegularized

/-- The actual compact-frequency forward weak pairing, in exactly the source
test space and complex Euclidean fiber required by the `hpair` premise of
`fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings`. The smooth
full amplitude includes both physical masks; its closed frequency carrier
avoids zero but may be unbounded. The cutoff is smooth and compactly supported.
The phase need only be smooth and locally homogeneous on the buffered carrier.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphOperator_frequencyCut_weak_pairing_of_supported
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F) (hF0 : (0 : Euclidean n) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hhom : SupportedPhaseHomogeneity S U)
    (χ : Euclidean n → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (i : Fin n) (u : graphTestSpace n r) (φ : 𝓢(Euclidean n, ℂ)) :
    (∫ x, partialDeriv φ x i • WithLp.toLp 2
      (graphOperator S (frequencyCutFullAmplitude χ A) (fun y ↦ (u.val y).ofLp) x)) =
    -((∫ x, φ x • WithLp.toLp 2
        (graphOperator S (frequencyCutFullAmplitude χ (graphTransferRemainder S i A))
          (fun y ↦ (u.val y).ofLp) x)) +
      ∑ j, ∫ x, φ x • WithLp.toLp 2
        (graphOperator S (frequencyCutFullAmplitude χ (graphTransferDatum S i j A))
          (fun y ↦ ((graphTestPartialDeriv j u).val y).ofLp) x)) := by
  let L := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  let Lr := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)
  have hu : ContDiff ℝ ∞ (fun y ↦ (u.val y).ofLp) := Lr.contDiff.comp u.property.1
  have hus : HasCompactSupport (fun y ↦ (u.val y).ofLp) :=
    u.property.2.comp_left Lr.map_zero
  have hcut : ∀ x y η, η ∉ tsupport χ → frequencyCutFullAmplitude χ A x y η = 0 := by
    intro x y η hη
    simp [frequencyCutFullAmplitude, image_eq_zero_of_notMem_tsupport hη]
  have hw := ForwardRegularized.weak_pairing_coordinates (hA.frequencyCut hχ)
    hX hY.isClosed hF hF0 hcarrier hS hhom hu hus hχs hcut φ (φ.smooth ⊤) i
  simp_rw [graphTransferRemainder_frequencyCutFullAmplitude,
    graphTransferDatum_frequencyCutFullAmplitude] at hw
  have he := congrArg L.symm hw
  simp only [map_neg, map_add, map_sum] at he
  simp_rw [← L.symm.integral_comp_comm] at he
  simp only [map_smul] at he
  simpa only [L, PiLp.coe_symm_continuousLinearEquiv,
    graphTestPartialDeriv_coordinates] using he

/-- Supported finite forward weak derivatives, derived from the literal compact
kernel pairings. Only low distributional realizations are assumed.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`; consumed by the
supported natural-order Sobolev estimates. -/
theorem graph_realization_weak_derivative_expansion_of_supported
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F) (hF0 : (0 : Euclidean n) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hhom : SupportedPhaseHomogeneity S U)
    (χ : ℕ → Euclidean n → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k))
    (T : FullAmplitude n r →
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)))
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (u : graphTestSpace n r) (is : List (Fin n))
    (hreal : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S) A js,
        GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1)) :
    Pseudodifferential.orderedTransferAction
      (fun i ↦ LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (T A (graphTestToLp u) : 𝓢'(Euclidean n, EuclideanSpace ℂ (Fin r))) =
      ((fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S) A is).map
        fun p ↦ (T p.1 (graphTestToLp
          (Pseudodifferential.orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(Euclidean n, EuclideanSpace ℂ (Fin r)))).sum := by
  apply fullAmplitudeDerivativeTerms_expansion_of_branch_realizations
    (graphOperator S) χ (graphTransferRemainder S) (graphTransferDatum S) T
    (ForwardAmplitudeAdmissible X Y F) _ _ _ A hA u is hreal
  · intro i B hB
    exact hB.graphTransferRemainder_of_supported S hX.isClosed hY.isClosed hF hF0 hcarrier hS i
  · intro i j B hB
    exact hB.graphTransferDatum_of_supported S hX.isClosed hY.isClosed hF hF0 hcarrier hS i j
  · intro B hB k i v φ
    exact graphOperator_frequencyCut_weak_pairing_of_supported hB hX hY hF hF0 hcarrier hS hhom
      (χ k) (hχ k) (hχs k) i v φ

end JanetCartan.FourierIntegral.SupportedSobolev
