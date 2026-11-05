module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Smooth.Correction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothReal

/-!
# Smooth realization of the same corrected physical solver

The smooth-source part of `app:ch_regular:thm:exact-correction` in Section 3.
The corrected source's compact smooth realization becomes an actual compact
real graph test. Its L² class is the literal zero extension of the existing
Neumann correction, and the existing physical-plus-pair realization applies
to that same class. The resulting solver is a single real linear map at all
orders, not a separately selected representative for each order.

The input Fourier membership and source realization are produced by the actual
finite constructor and its fixed inverse in `DirectSmooth.lean`. This relative
lemma does not replace their construction with an assumed smooth solver.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport RegularSector.Realization
open RegularSector.FiniteAssembly FourierIntegral Pseudodifferential
open CharacteristicTransport.CompleteResidual

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "CF" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp CF 2 (volume : Measure E)

/-- Apply the original smooth physical solver to the actual compact smooth
realization of its corrected L² source (`app:ch_regular:thm:exact-correction`).
The input regularity is supplied by the same finite operator's Fourier bounds,
and the source realization by its fixed Neumann inverse. The output is one real
linear map with literal agreement to the SAME paired solver and zero extension. -/
theorem exists_smooth_corrected_solver_realization
    {W : Set E} (hW : MeasurableSet W) {K : Set E} (hK : IsCompact K)
    (Corr : smoothSource W RF → LocalL2 W RF)
    (z : smoothSource W RF →ₗ[ℝ] (E → RF))
    (hz : ∀ h, ContDiff ℝ ∞ (z h) ∧ z h =ᵐ[volume.restrict W] Corr h ∧
      tsupport (z h) ⊆ K ∧ W.indicator (z h) = z h)
    (T : H →L[ℂ] H)
    (hT : ∀ (u : graphTestSpace (d + 1) q) (s : ℕ),
      MemVectorFourierSobolev (s : ℝ) (T (graphTestToLp u))) :
    ∃ V : smoothSource W RF →ₗ[ℝ] (E → RF), ∀ h,
      ContDiff ℝ ∞ (V h) ∧ V h =ᵐ[volume]
        realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ T))
          (zeroExtend hW (Corr h)) := by
  let Z : smoothSource W RF →ₗ[ℝ] realSectorTestSpace d q :=
    z.codRestrict (realSectorTestSpace d q) fun h ↦
      mem_realSectorTestSpace (hz h).1
        (hK.of_isClosed_subset (isClosed_tsupport _) (hz h).2.2.1)
  have hZ (h : smoothSource W RF) :
      realSectorTestToLp (Z h) = zeroExtend hW (Corr h) := by
    apply Lp.ext
    have hi := (ae_eq_restrict_iff_indicator_ae_eq hW).mp (hz h).2.1
    rw [(hz h).2.2.2] at hi
    exact (realSectorTestToLp_coeFn (Z h)).trans
      (hi.trans (zeroExtend_coeFn hW (Corr h)).symm)
  obtain ⟨S, hS⟩ := exists_smooth_linear_graph_realization T hT
  obtain ⟨P, hP⟩ := exists_smooth_physical_pair_realization T S hS
  obtain ⟨R, hR⟩ := exists_smooth_real_physical_pair T P hP
  refine ⟨R.comp Z, fun h ↦ ⟨(hR (Z h)).1, ?_⟩⟩
  simpa only [LinearMap.comp_apply, hZ] using (hR (Z h)).2.1

/-- The tested physical equation of the actual real solver becomes a pointwise
identity for smooth representatives of the same real L² classes
(`app:ch_regular:eq:exact-physical`). The finite constructor supplies the tested
equation; `exists_smooth_corrected_solver_realization` supplies the two smooth
fields after applying the SAME corrected source. -/
theorem smooth_real_representatives_physical_equation
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : closure U ⊆ Ω)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (v g : E → Euclidean (d+1))
    (hv : ContDiff ℝ ∞ v) (hg : ContDiff ℝ ∞ g)
    (u w : Lp (Euclidean (d+1)) 2 (volume : Measure E))
    (he : v =ᵐ[volume] u) (hf : g =ᵐ[volume] w)
    (ht : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (l2ComplexInclusion volume u y).ofLp) φ j =
          ∫ y, φ y • l2ComplexInclusion volume w y j) :
    EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
      (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (g y)).ofLp) U := by
  have hv' : ContDiff ℝ ∞ (fun y ↦ euclideanComplexInclusion (v y)) :=
    (euclideanComplexInclusion : Euclidean (d+1) →L[ℝ]
      EuclideanSpace ℂ (Fin (d+1))).contDiff.comp hv
  have hg' : ContDiff ℝ ∞ (fun y ↦ euclideanComplexInclusion (g y)) :=
    (euclideanComplexInclusion : Euclidean (d+1) →L[ℝ]
      EuclideanSpace ℂ (Fin (d+1))).contDiff.comp hg
  have he' : (fun y ↦ euclideanComplexInclusion (v y)) =ᵐ[volume]
      l2ComplexInclusion volume u := by
    filter_upwards [he, euclideanComplexInclusion.coeFn_compLpL u] with y hy hu
    exact (congrArg euclideanComplexInclusion hy).trans hu.symm
  have hf' : (fun y ↦ euclideanComplexInclusion (g y)) =ᵐ[volume]
      l2ComplexInclusion volume w := by
    filter_upwards [hf, euclideanComplexInclusion.coeFn_compLpL w] with y hy hw
    exact (congrArg euclideanComplexInclusion hy).trans hw.symm
  exact smooth_representatives_physical_equation hΩ hU hUΩ Q B hQ hB
    _ _ hv' hg' _ _ he' hf' ht

end JanetCartan.FixedDomainInverse
