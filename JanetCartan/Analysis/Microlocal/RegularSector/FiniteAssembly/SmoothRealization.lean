module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.CoefficientLocalization
public import JanetCartan.Analysis.Sobolev.Local.Fourier
public import JanetCartan.Analysis.Sobolev.Local.Smooth

/-!
# Smooth realization of the constructed finite operators

For `app:ch_regular_base:thm:sector`, all-order Fourier membership gives a
unique smooth representative of the literal L² output. Uniqueness preserves
linearity. The tested physical equation then becomes a pointwise equation,
with the full zeroth-order coefficient. `SmoothConstruction` applies these
steps to the actual outputs of `exists_finite_direct_operator_bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open FourierIntegral Pseudodifferential LocalSobolev
open Characteristic.RetardedLocalization Characteristic.ResidualCoordinates
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Realize the same all-order Fourier class as one globally smooth function
(`app:not:fourier`, `sector-theorem-solution`). -/
theorem exists_smooth_representative_of_fourier_all (u : H)
    (hu : ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ) u) :
    ∃ v : E → F, ContDiff ℝ ∞ v ∧ v =ᵐ[volume] u := by
  have hm s : MemRestrictionSobolev univ s (restrictL2 univ u) := by
    obtain ⟨C, hC, h⟩ := vector_restrictionSobolev_nat_bounds (d+1) q s
    exact (h u (hu s) univ _ (restrictL2_coeFn univ u).symm).1
  obtain ⟨v, hv, he⟩ := exists_contDiffOn_infty_ae_eq_of_memRestrictionSobolev
    isOpen_univ (restrictL2 univ u) hm
  exact ⟨v, contDiffOn_univ.mp hv, by
    simpa only [Measure.restrict_univ] using he.trans (restrictL2_coeFn univ u)⟩

/-- Smooth realization is a single complex linear operator on compact smooth
inputs. Its only analytic premise is all-order membership of the actual
outputs, supplied by the finite constructor's proved positive estimates
(`sector-theorem-solution`). -/
theorem exists_smooth_linear_graph_realization (T : H →L[ℂ] H)
    (hT : ∀ (u : graphTestSpace (d+1) q) (s : ℕ),
      MemVectorFourierSobolev (s : ℝ) (T (graphTestToLp u))) :
    ∃ S : graphTestSpace (d+1) q →ₗ[ℂ] (E → F),
      ∀ u, ContDiff ℝ ∞ (S u) ∧ S u =ᵐ[volume] T (graphTestToLp u) := by
  choose v hv he using fun u ↦ exists_smooth_representative_of_fourier_all
    (T (graphTestToLp u)) (hT u)
  have unique {f g : E → F} (hf : Continuous f) (hg : Continuous g)
      (hfg : f =ᵐ[volume] g) : f = g := by
    apply funext
    intro y
    exact Measure.eqOn_open_of_ae_eq (by simpa using hfg)
      isOpen_univ hf.continuousOn hg.continuousOn (mem_univ y)
  refine ⟨{ toFun := v, map_add' := ?_, map_smul' := ?_ }, fun u ↦ ⟨hv u, he u⟩⟩
  · intro u w
    apply unique (hv _).continuous ((hv u).add (hv w)).continuous
    filter_upwards [he (u+w), he u, he w,
      Lp.coeFn_add (T (graphTestToLp u)) (T (graphTestToLp w))] with y hy hu hw ha
    simp only [map_add] at hy
    simpa only [Pi.add_apply, hu, hw] using hy.trans ha
  · intro c u
    apply unique (hv _).continuous ((hv u).const_smul c).continuous
    filter_upwards [he (c • u), he u, Lp.coeFn_smul c (T (graphTestToLp u))]
      with y hy hu hs
    simp only [map_smul] at hy
    simpa only [Pi.smul_apply, hu] using hy.trans hs

/-- Upgrade the tested equation of the original physical coefficients to a
pointwise equation for smooth representatives of the SAME two L² classes.
Coefficient extensions agree on the original measurement set; the full B
term remains in the equation (`sector-theorem-identity`,
`energy-complete-residual`). -/
theorem smooth_representatives_physical_equation
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : closure U ⊆ Ω)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (v g : E → EuclideanSpace ℂ (Fin (d+1)))
    (hv : ContDiff ℝ ∞ v) (hg : ContDiff ℝ ∞ g)
    (u w : Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure E))
    (he : v =ᵐ[volume] u) (hf : g =ᵐ[volume] w)
    (ht : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (u y).ofLp) φ j = ∫ y, φ y • w y j) :
    EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
      (fun y ↦ (v y).ofLp) (fderiv ℝ (fun y ↦ (v y).ofLp)))
      (fun y ↦ (g y).ofLp) U := by
  have he0 (y : E) : physicalCoordinates (0 : Fin (d+1)) y = y := by
    simp [physicalCoordinates]
  obtain ⟨A, B', hA, hB', hcoeff⟩ := exists_smooth_coordinate_coefficients 0 hΩ Q B hQ hB
    isClosed_closure (fun y hy ↦ by simpa only [he0] using hUΩ hy)
  have hAe (y : E) (hy : y ∈ U) :
      A y = fun a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1) := by
    rw [(hcoeff y (subset_closure hy)).1.eq_of_nhds]
    funext a
    simp only [coefficient, he0]
  have hBe (y : E) (hy : y ∈ U) : B' y = B y := by
    simpa only [zeroth, he0] using (hcoeff y (subset_closure hy)).2.eq_of_nhds
  have hAc a j k : ContDiff ℝ ∞ (fun y ↦ A y a j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp ((contDiff_pi.mp hA) a)
  have hBc j k : ContDiff ℝ ∞ (fun y ↦ B' y j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp hB'
  let P : EuclideanSpace ℂ (Fin (d+1)) →L[ℝ] (Fin (d+1) → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d+1) ↦ ℂ)).toContinuousLinearMap
  have hv' : ContDiff ℝ ∞ (fun y ↦ (v y).ofLp) := P.contDiff.comp hv
  have hg' : ContDiff ℝ ∞ (fun y ↦ (g y).ofLp) := P.contDiff.comp hg
  have he' : (fun y ↦ (v y).ofLp) =ᵐ[volume.restrict (univ : Set E)]
      (fun y ↦ (u y).ofLp) := by
    rw [Measure.restrict_univ]
    filter_upwards [he] with y hy
    rw [hy]
  have htest (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ U) (j : Fin (d+1)) : physicalTestAction A B' (fun y ↦ (v y).ofLp) φ j =
      ∫ y, φ y • g y j := by
    rw [physicalTestAction_eq_of_coefficients_on_support A
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B' B _ φ
      (fun y hy ↦ hAe y (hs hy)) (fun y hy ↦ hBe y (hs hy)) j]
    rw [FiniteResidual.SelectedChart.physicalTestAction_eq_of_ae_on _ _
      MeasurableSet.univ _ _ he' φ (subset_univ _) j,
      ht φ hφ hc hs j]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
  have hw := physicalWeakApply_ae_eq_of_test A B' hAc hBc hU
    (Mollification.hasWeakFDerivOn_of_contDiff volume (hv'.of_le (by simp)) U)
    (hg'.continuous.locallyIntegrable.locallyIntegrableOn U) htest
  have hp : Continuous (physicalWeakApply A B' (fun y ↦ (v y).ofLp)
      (fderiv ℝ (fun y ↦ (v y).ofLp))) := by
    apply continuous_pi
    intro j
    apply Continuous.add
    · apply continuous_finsetSum
      intro a _
      apply continuous_finsetSum
      intro k _
      exact (hAc a j k).continuous.smul
        ((continuous_apply k).comp
          ((hv'.continuous_fderiv (by simp)).clm_apply continuous_const))
    · apply continuous_finsetSum
      intro k _
      exact (hBc j k).continuous.smul ((continuous_apply k).comp hv'.continuous)
  have hpoint := Measure.eqOn_open_of_ae_eq hw hU hp.continuousOn hg'.continuous.continuousOn
  intro y hy
  have h := congrFun (hpoint hy)
  funext j
  simpa only [physicalWeakApply, hAe y hy, hBe y hy] using h j

end JanetCartan.RegularSector.FiniteAssembly
