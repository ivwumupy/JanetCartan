module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.Coordinates
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.CoefficientLocalization
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.SectorEquations
public import JanetCartan.Analysis.Sobolev.Local.Fourier.VectorFirstDerivative
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection

/-!
# Finite distributional sums on the original coefficient domain

The original coefficients need only be smooth on Ω. Extend them near the
closed support of a test, apply the existing L² test pairing and physical
plus-pairing lemmas, then return to the original coefficients. The local
sector equations are the outputs of the common-chart residual producer;
this file proves their finite-sum deduction, not their instantiation.
Sources: `app:ch_regular_base:eq:sector-theorem-identity`,
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral FiniteEvolution
open JanetCartan.CharacteristicTransport.CompleteResidual FourierIntegral
open Realization
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

private theorem exists_test_coefficient_extension
    {Ω : Set E} (hΩ : IsOpen Ω)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (φ : E → ℝ) (hφΩ : tsupport φ ⊆ Ω) :
    ∃ A : E → Fin (d+1) → Mat, ∃ B' : E → Mat,
      (∀ a j k, ContDiff ℝ ∞ (fun y ↦ A y a j k)) ∧
      (∀ j k, ContDiff ℝ ∞ (fun y ↦ B' y j k)) ∧
      (∀ y ∈ tsupport φ,
        A y = fun a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) ∧
      (∀ y ∈ tsupport φ, B' y = B y) := by
  have he (y : E) : physicalCoordinates (0 : Fin (d+1)) y = y := by
    simp [physicalCoordinates]
  obtain ⟨A, B', hA, hB', heq⟩ := exists_smooth_coordinate_coefficients 0 hΩ Q B hQ hB
    (isClosed_tsupport φ) (fun y hy ↦ by simpa only [he] using hφΩ hy)
  refine ⟨A, B', ?_, ?_, ?_, ?_⟩
  · intro a j k
    exact (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp
      ((contDiff_pi.mp hA) a)
  · intro j k
    exact (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp hB'
  · intro y hy
    rw [(heq y hy).1.eq_of_nhds]
    funext a
    simp only [coefficient, he]
  · intro y hy
    simpa only [zeroth, he] using (heq y hy).2.eq_of_nhds

/-- Sum the same transported common-chart equations on the original domain.
The per-chart equations are precisely the tested conclusion of
`SelectedChart.completeResidual_of_common_selected_chart`. This deduction
keeps the original local coefficient hypothesis and all source/residual
operators; it does not assume global coefficient smoothness or a tested
identity for the finite sum (`energy-complete-residual`). -/
theorem finitePhysicalOperator_test {ι : Type*} [Fintype ι]
    {Ω U : Set E} (hΩ : IsOpen Ω) (hUΩ : U ⊆ Ω)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (i : ι → Fin (d+1)) (S T : ι → H →L[ℂ] H)
    (ht : ∀ p u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates (i p) ⁻¹' U → ∀ j,
      physicalTestAction (coefficient (i p) Q) (zeroth (i p) B)
        (fun y ↦ (S p u y).ofLp) φ j = ∫ y, φ y • T p u y j) :
    ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (finitePhysicalOperator i S u y).ofLp) φ j =
          ∫ y, φ y • finitePhysicalOperator i T u y j := by
  classical
  intro u φ hφ hc hs j
  obtain ⟨A, B', hA, hB', hAe, hBe⟩ :=
    exists_test_coefficient_extension hΩ Q B hQ hB φ (hs.trans hUΩ)
  have he (v : H) := physicalTestAction_eq_of_coefficients_on_support A
    (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B' B
    (fun y ↦ (v y).ofLp) φ hAe hBe j
  let L := physicalTestActionLp A B' hA hB' φ hφ hc j
  let N := testCoordinatePairing φ (hφ.continuous.memLp_of_hasCompactSupport hc) j
  have hp (p : ι) : L (physicalOperator (i p) (S p) u) = N (physicalOperator (i p) (T p) u) := by
    rw [physicalTestActionLp_apply, he]
    exact tested_equation_physicalOperator (i p) Q B (S p) (T p) U (ht p) u φ hφ hc hs j
  rw [← he, ← physicalTestActionLp_apply A B' hA hB' φ hφ hc j]
  change L (finitePhysicalOperator i S u) = N (finitePhysicalOperator i T u)
  simp only [finitePhysicalOperator, sum_apply, map_sum]
  exact Finset.sum_congr rfl fun p _ ↦ hp p

/-- For the physical real-coefficient operator the plus pair is S+cSc. Apply
that exact pairing to the SAME finite equation. Neither an anti-real sign nor
an extra factor of i is introduced, and the source remains part of T
(`real-sector-normalization`, `energy-complete-residual`). -/
theorem finitePhysicalOperator_physicalPair_test {ι : Type*} [Fintype ι]
    {Ω U : Set E} (hΩ : IsOpen Ω) (hUΩ : U ⊆ Ω)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (i : ι → Fin (d+1)) (S T : ι → H →L[ℂ] H)
    (ht : ∀ p u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates (i p) ⁻¹' U → ∀ j,
      physicalTestAction (coefficient (i p) Q) (zeroth (i p) B)
        (fun y ↦ (S p u y).ofLp) φ j = ∫ y, φ y • T p u y j) :
    ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (physicalPairedSectorSum {()} (fun _ : Unit ↦ finitePhysicalOperator i S) u y).ofLp)
        φ j = ∫ y, φ y •
          physicalPairedSectorSum {()} (fun _ : Unit ↦ finitePhysicalOperator i T) u y j := by
  classical
  intro u φ hφ hc hs j
  obtain ⟨A, B', hA, hB', hAe, hBe⟩ :=
    exists_test_coefficient_extension hΩ Q B hQ hB φ (hs.trans hUΩ)
  have he (v : H) := physicalTestAction_eq_of_coefficients_on_support A
    (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B' B
    (fun y ↦ (v y).ofLp) φ hAe hBe j
  rw [← he]
  apply physicalPairedSectorSum_test A B' hA hB' {()}
    (fun _ : Unit ↦ finitePhysicalOperator i S) (fun _ : Unit ↦ finitePhysicalOperator i T) hφ hc j
  intro _ _ v
  rw [he]
  exact finitePhysicalOperator_test hΩ hUΩ Q B hQ hB i S T ht _ φ hφ hc hs j

/-- Real compression has the identical distributional equation on embedded
real inputs, for the same finite physical plus pair (`sector-theorem-identity`). -/
theorem finitePhysicalOperator_realCompression_test {ι : Type*} [Fintype ι]
    {Ω U : Set E} (hΩ : IsOpen Ω) (hUΩ : U ⊆ Ω)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (i : ι → Fin (d+1)) (S T : ι → H →L[ℂ] H)
    (ht : ∀ p u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates (i p) ⁻¹' U → ∀ j,
      physicalTestAction (coefficient (i p) Q) (zeroth (i p) B)
        (fun y ↦ (S p u y).ofLp) φ j = ∫ y, φ y • T p u y j)
    (u : Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (j : Fin (d+1)) :
    physicalTestAction
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
      (fun y ↦ (l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ finitePhysicalOperator i S)) u) y).ofLp)
      φ j = ∫ y, φ y • l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ finitePhysicalOperator i T)) u) y j := by
  rw [inclusion_realCompression_physicalPairedSectorSum,
    inclusion_realCompression_physicalPairedSectorSum]
  exact finitePhysicalOperator_physicalPair_test hΩ hUΩ Q B hQ hB i S T ht _ φ hφ hc hs j

/-- Construct the actual weak derivative and a.e. equation of the same finite
output once its positive-order estimate gives Fourier H¹ membership. The
intended input is a compact smooth source; no H¹ assertion on arbitrary L²
sources is made. The domain closure stays inside the original coefficient
domain, and every coefficient and B term is unchanged
(`sector-theorem-identity`, `energy-complete-residual`). -/
theorem finitePhysicalOperator_ae_of_fourier_one {ι : Type*} [Fintype ι]
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : closure U ⊆ Ω)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (i : ι → Fin (d+1)) (S T : ι → H →L[ℂ] H)
    (ht : ∀ p u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates (i p) ⁻¹' U → ∀ j,
      physicalTestAction (coefficient (i p) Q) (zeroth (i p) B)
        (fun y ↦ (S p u y).ofLp) φ j = ∫ y, φ y • T p u y j)
    (u : graphTestSpace (d+1) (d+1))
    (hu : Pseudodifferential.MemVectorFourierSobolev 1
      (finitePhysicalOperator i S (graphTestToLp u))) :
    ∃ D : E → E →L[ℝ] (Fin (d+1) → ℂ),
      Mollification.HasWeakFDerivOn volume
        (fun y ↦ (finitePhysicalOperator i S (graphTestToLp u) y).ofLp) D univ ∧
      MemLp D 2 volume ∧
      physicalWeakApply
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (finitePhysicalOperator i S (graphTestToLp u) y).ofLp) D
        =ᵐ[volume.restrict U] fun y ↦ (finitePhysicalOperator i T (graphTestToLp u) y).ofLp := by
  let P : EuclideanSpace ℂ (Fin (d+1)) →L[ℝ] (Fin (d+1) → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d+1) ↦ ℂ)).toContinuousLinearMap
  obtain ⟨D, hD, hDm, _⟩ := LocalSobolev.exists_vector_firstWeakDerivative _ hu
  have hd := hD.comp_clm_univ P
  have hdm := ((ContinuousLinearMap.compL ℝ E _ _) P).comp_memLp' hDm
  have he (y : E) : physicalCoordinates (0 : Fin (d+1)) y = y := by
    simp [physicalCoordinates]
  obtain ⟨A, B', hA, hB', heq⟩ := exists_smooth_coordinate_coefficients 0 hΩ Q B hQ hB
    isClosed_closure (fun y hy ↦ by simpa only [he] using hUΩ hy)
  have hAe (y : E) (hy : y ∈ U) :
      A y = fun a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1) := by
    rw [(heq y (subset_closure hy)).1.eq_of_nhds]
    funext a
    simp only [coefficient, he]
  have hBe (y : E) (hy : y ∈ U) : B' y = B y := by
    simpa only [zeroth, he] using (heq y (subset_closure hy)).2.eq_of_nhds
  have hAc a j k : ContDiff ℝ ∞ (fun y ↦ A y a j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp ((contDiff_pi.mp hA) a)
  have hBc j k : ContDiff ℝ ∞ (fun y ↦ B' y j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp hB'
  have hg := (P.comp_memLp' (Lp.memLp (finitePhysicalOperator i T (graphTestToLp u)))).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hp := physicalWeakApply_ae_eq_of_test A B' hAc hBc hU (hd.mono (subset_univ U))
    (hg.locallyIntegrableOn U) (by
      intro φ hφ hc hs j
      rw [physicalTestAction_eq_of_coefficients_on_support A
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B' B _ φ
        (fun y hy ↦ hAe y (hs hy)) (fun y hy ↦ hBe y (hs hy)) j]
      exact finitePhysicalOperator_test hΩ (subset_closure.trans hUΩ) Q B hQ hB i S T ht
        _ φ hφ hc hs j)
  refine ⟨fun y ↦ P.comp (D y), hd, hdm, ?_⟩
  filter_upwards [hp, ae_restrict_mem hU.measurableSet] with y hy hyU
  change physicalWeakApply A B'
    (fun y ↦ (finitePhysicalOperator i S (graphTestToLp u) y).ofLp) (fun y ↦ P.comp (D y)) y =
      (finitePhysicalOperator i T (graphTestToLp u) y).ofLp at hy
  funext j
  have hyj := congrFun hy j
  dsimp only [physicalWeakApply] at hyj ⊢
  rw [hAe y hyU, hBe y hyU] at hyj
  exact hyj

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
