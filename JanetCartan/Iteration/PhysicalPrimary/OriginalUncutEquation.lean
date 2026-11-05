module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSolver
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedSmooth.Correction
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutEquationTemplate

/-!
# The original uncut inverse on its original core

The inverse input is the supplied source itself, already localized by the
original source producer. There is no second chi2 multiplication. The localized
analytic residual is inverted; the full angular/source discrepancy is retained
in the physical equation (`app:ch_regular:eq:exact-physical`).

Consumer: the actual uncut completedVariation and its strain-error estimate.
This file does not assert that the full source operator is the identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open Set MeasureTheory Filter Metric
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalUncutEquation
open LocalSobolev SmallSupport FixedDomainInverse
open RegularSector.Realization CharacteristicTransport.CompleteResidual

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The supplied source is acted on by the original inverse first. Only the
existing chi3 extends its output; no second chi2 is introduced
(`app:ch_regular:eq:exact-physical`). -/
def inverseSource {n q : ℕ} {W : Set (Euclidean n)} {x : Euclidean n}
    (χ₃ : ContDiffBump x)
    (Inv : LocalL2 W (Euclidean q) →L[ℝ] LocalL2 W (Euclidean q)) :
    LocalL2 W (Euclidean q) →L[ℝ] LocalL2 W (Euclidean q) :=
  (bumpL2 (p := 2) le_rfl χ₃).comp Inv

/-- The native left-inverse and localized-residual identities imply the exact
core residual equation for chi3*Inv(h), WITHOUT reapplying chi2 to h. The actual
original-current application supplies both operator identities below. -/
theorem uncutInverse_core_ae
    {n q : ℕ} {W U : Set (Euclidean n)} (hU : MeasurableSet U)
    {x : Euclidean n} (χ₂ χ₃ : ContDiffBump x)
    (hcore : ball x χ₂.rIn ⊆ U) (hUW : U ⊆ W)
    (hnest : ∀ y ∈ tsupport (χ₂ : Euclidean n → ℝ), χ₃ y = 1)
    (R : LocalL2 W (Euclidean q) →L[ℝ] LocalL2 U (Euclidean q))
    (K Inv : LocalL2 W (Euclidean q) →L[ℝ] LocalL2 W (Euclidean q))
    (hleft : (1 + K) * Inv = 1)
    (hK : ∀ u, K u =ᵐ[volume.restrict W]
      zeroExtend hU (bumpL2 (p := 2) le_rfl χ₂
        (R (bumpL2 (p := 2) le_rfl χ₃ u))))
    (h : LocalL2 W (Euclidean q)) :
    ∀ᵐ y ∂volume.restrict (ball x χ₂.rIn),
      (bumpL2 (p := 2) le_rfl χ₃ (Inv h)) y +
        R (bumpL2 (p := 2) le_rfl χ₃ (Inv h)) y = h y := by
  let z := bumpL2 (p := 2) le_rfl χ₃ (Inv h)
  have hv : Inv h + K (Inv h) = h := by
    have he := DFunLike.congr_fun hleft h
    change Inv h + K (Inv h) = h at he
    exact he
  have hae : ∀ᵐ y ∂volume.restrict W, Inv h y + K (Inv h) y = h y := by
    filter_upwards [Lp.coeFn_add (Inv h) (K (Inv h))] with y hy
    rw [hv] at hy
    exact hy.symm
  have hcoreW := hcore.trans hUW
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hcoreW hae,
    ae_restrict_of_ae_restrict_of_subset hcoreW (hK (Inv h)),
    ae_restrict_of_ae (zeroExtend_coeFn hU (bumpL2 (p := 2) le_rfl χ₂ (R z))),
    ae_restrict_of_ae_restrict_of_subset hcore
      (bumpL2_coeFn (p := 2) le_rfl χ₂ (R z)),
    ae_restrict_of_ae_restrict_of_subset hcoreW
      (bumpL2_coeFn (p := 2) le_rfl χ₃ (Inv h)),
    ae_restrict_mem isOpen_ball.measurableSet] with y he hk hz hb₂ hb₃ hy
  have h₂ : χ₂ y = 1 := χ₂.one_of_mem_closedBall (ball_subset_closedBall hy)
  have hySupport : y ∈ tsupport (χ₂ : Euclidean n → ℝ) := subset_tsupport _ (by
    change χ₂ y ≠ 0
    rw [h₂]
    exact one_ne_zero)
  have h₃ : χ₃ y = 1 := hnest y hySupport
  change K (Inv h) y = zeroExtend hU (bumpL2 (p := 2) le_rfl χ₂ (R z)) y at hk
  rw [hk, hz, indicator_of_mem (hcore hy), hb₂, h₂, one_smul] at he
  change z y + R z y = h y
  change z y = χ₃ y • Inv h y at hb₃
  rw [hb₃, h₃, one_smul]
  exact he

/-- A globally smooth real representative of the SAME L² solver has the
physical equation a.e. on the original open core. The right side remains its
actual L² class; no smoothness or identity of the angular source is assumed. -/
theorem smooth_real_equation_ae
    {d : ℕ}
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B)
    {V : Set (Euclidean (d + 1))} (hV : IsOpen V)
    (v : Euclidean (d + 1) → Euclidean (d + 1)) (hv : ContDiff ℝ ∞ v)
    (u g : Lp (Euclidean (d + 1)) 2 (volume : Measure (Euclidean (d + 1))))
    (he : v =ᵐ[volume] u)
    (htest : ∀ (φ : Euclidean (d + 1) → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ V → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (l2ComplexInclusion volume u y).ofLp) φ j =
      ∫ y, φ y • l2ComplexInclusion volume g y j) :
    physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
      (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp))
        =ᵐ[volume.restrict V] fun y ↦ (l2ComplexInclusion volume g y).ofLp := by
  let A := fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)
  have hA (a i j : Fin (d + 1)) : ContDiff ℝ ∞ (fun y ↦ A y a i j) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
      (ActualCarriers.contDiff_pencil.comp (hQ.prodMk contDiff_const))
  have hBc (i j : Fin (d + 1)) : ContDiff ℝ ∞ (fun y ↦ B y i j) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp hB
  let P : EuclideanSpace ℂ (Fin (d + 1)) →L[ℝ] (Fin (d + 1) → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℂ)).toContinuousLinearMap
  have hv' : ContDiff ℝ ∞ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp) :=
    P.contDiff.comp ((euclideanComplexInclusion : Euclidean (d + 1) →L[ℝ]
      EuclideanSpace ℂ (Fin (d + 1))).contDiff.comp hv)
  have he' : (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)
      =ᵐ[volume.restrict (univ : Set (Euclidean (d + 1)))]
        (fun y ↦ (l2ComplexInclusion volume u y).ofLp) := by
    rw [Measure.restrict_univ]
    filter_upwards [he, euclideanComplexInclusion.coeFn_compLpL u] with y hy hu
    change l2ComplexInclusion volume u y = euclideanComplexInclusion (u y) at hu
    rw [hy, hu]
  have ht (φ : Euclidean (d + 1) → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ V) (j : Fin (d + 1)) :
      physicalTestAction A B (fun y ↦ (euclideanComplexInclusion (v y)).ofLp) φ j =
        ∫ y, φ y • l2ComplexInclusion volume g y j := by
    rw [RegularSector.FiniteResidual.SelectedChart.physicalTestAction_eq_of_ae_on
      A B MeasurableSet.univ _ _ he' φ (subset_univ _) j]
    exact htest φ hφ hc hs j
  have hg := (P.comp_memLp' (Lp.memLp (l2ComplexInclusion volume g))).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  exact physicalWeakApply_ae_eq_of_test A B hA hBc hV
    (Mollification.hasWeakFDerivOn_of_contDiff volume (hv'.of_le (by simp)) V)
    (hg.locallyIntegrableOn V) ht

end JanetCartan.PhysicalPrimary.OriginalUncutEquation

derive_original_uncut_equation

end
