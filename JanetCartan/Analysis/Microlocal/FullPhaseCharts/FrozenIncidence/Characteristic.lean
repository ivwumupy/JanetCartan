module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhase
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Frozen

/-!
# The actual frozen dispersion is a characteristic graph

The retained Hamilton eikonal equation supplies the characteristic identity.
Differentiating it gives the determinant-normal identity used by frozen
incidence transversality in `app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.FullPhaseCharts.FrozenIncidence
open HamiltonPhase ActualCarriers ActualCarriers.FrozenPhaseReference
open ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The actual frozen covector is the graph of the retained dispersion,
with the positive phase sign (`app:ch_seed:prop:seed-phase-charts`). -/
theorem reference_covector_eq_graph {ζ : Euclidean (n - 1)}
    (hζ : ζ ∈ ball (covectorCenter T) (2 * T.family.radius)) :
    dispersion T ζ • T.data.adapted.normal + T.data.adapted.embedding ζ =
      T.reference.covector (0, ζ) := by
  change ⟪T.data.adapted.normal, T.reference.covector (0, ζ)⟫_ℝ •
    T.data.adapted.normal + T.data.adapted.embedding ζ = _
  simpa only [reference_covector_adjoint T hζ] using
    T.data.adapted.covector_decomposition (T.reference.covector (0, ζ))

/-- The dispersion satisfies the characteristic equation on its whole
construction ball, by the retained frozen flow/eikonal equation, not by an
assumed root formula (`app:ch_seed:prop:seed-phase-charts`). -/
theorem dispersion_characteristic {ζ : Euclidean (n - 1)}
    (hζ : ζ ∈ ball (covectorCenter T) (2 * T.family.radius)) :
    cubeDeterminant
      (dispersion T ζ • T.data.adapted.normal + T.data.adapted.embedding ζ) = 0 := by
  rw [reference_covector_eq_graph T hζ]
  let C := T.data.localReference.family.chart
  have hq : ((0 : Euclidean n), ((0 : ℝ), ζ)) ∈ C.target := by
    apply T.family.reference_target
    simpa only [mem_ball, AdaptedSection.baseData, map_zero, covectorCenter,
      Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hζ
  have he := C.eikonal hq
  rw [C.gradient_phase_eq_chartMomentum hq,
    chartMomentum_eq_of_phase_linear C T.data.localReference.covector
      T.data.localReference.phase_linear hq, frozenSymbol_h] at he
  have hs := C.source_admissible _ (C.maps_to_source _ hq)
  have hm := T.data.localReference.family.flow.state_mem _ hs.1 _ hs.2
  have hp : T.reference.covector (0, ζ) ≠ 0 := by
    have hp := (mem_frozenSymbol_domain _).mp hm
    change C.chartMomentum (0, (0, ζ)) ≠ 0 at hp
    rwa [chartMomentum_eq_of_phase_linear C T.data.localReference.covector
      T.data.localReference.phase_linear hq] at hp
  exact (mul_eq_zero.mp he).resolve_left (zpow_ne_zero _ (norm_ne_zero_iff.mpr hp))

/-- Every spatial patch point on the doubled closed cube belongs to the
smooth dispersion ball (`app:ch_seed:prop:seed-phase-charts`). -/
theorem spatialPatch_mem_dispersion_ball {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) :
    T.reference.spatialPatch z ∈ ball (covectorCenter T) (2 * T.family.radius) := by
  have hb := (mem_ball.mp (T.patch_buffer z hz)).trans_le (min_le_left _ _)
  have hr : T.family.radius < 2 * T.family.radius := by linarith [T.family.radius_pos]
  apply lt_trans _ hr
  change dist (T.data.adapted.embedding.toContinuousLinearMap.adjoint (P.toFun z))
    (T.data.adapted.embedding.toContinuousLinearMap.adjoint T.data.center) < _
  simpa only [AdaptedSection.baseData, Prod.dist_eq, dist_self,
    max_eq_right dist_nonneg] using hb

/-- Differentiating the actual characteristic graph gives the tangential
part of the determinant differential (`app:ch_seed:prop:seed-phase-charts`). -/
theorem determinant_tangential_identity {ζ : Euclidean (n - 1)}
    (hζ : ζ ∈ ball (covectorCenter T) (2 * T.family.radius)) (η : Euclidean (n - 1)) :
    fderiv ℝ cubeDeterminant (T.reference.covector (0, ζ))
        (T.data.adapted.embedding η) =
      - (fderiv ℝ cubeDeterminant (T.reference.covector (0, ζ)) T.data.adapted.normal) *
        ⟪gradient (dispersion T) ζ, η⟫_ℝ := by
  have hH := ((dispersion_smooth T).contDiffAt (isOpen_ball.mem_nhds hζ)).differentiableAt
    (by simp)
  have hg := (hH.hasFDerivAt.smul_const T.data.adapted.normal).add
    T.data.adapted.embedding.toContinuousLinearMap.hasFDerivAt
  have hp := (hasFDerivAt_cubeDeterminant
    (dispersion T ζ • T.data.adapted.normal + T.data.adapted.embedding ζ)).differentiableAt
  have hd := hp.hasFDerivAt.comp ζ hg
  have he : (fun v ↦ cubeDeterminant
      (dispersion T v • T.data.adapted.normal + T.data.adapted.embedding v))
      =ᶠ[𝓝 ζ] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [isOpen_ball.mem_nhds hζ] with v hv
    exact dispersion_characteristic T hv
  have hzero := congrArg (fun L : Euclidean (n - 1) →L[ℝ] ℝ ↦ L η)
    (hd.unique ((hasFDerivAt_const (0 : ℝ) ζ).congr_of_eventuallyEq he))
  rw [reference_covector_eq_graph T hζ] at hzero
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul,
    zero_apply] at hzero
  rw [inner_gradient_left]
  change fderiv ℝ cubeDeterminant (T.reference.covector (0, ζ))
    (T.data.adapted.embedding η) = _
  change fderiv ℝ (dispersion T) ζ η *
    fderiv ℝ cubeDeterminant (T.reference.covector (0, ζ)) T.data.adapted.normal +
    fderiv ℝ cubeDeterminant (T.reference.covector (0, ζ)) (T.data.adapted.embedding η) = 0 at hzero
  nlinarith [hzero]

/-- At every frozen patch point the determinant incidence is the adapted
normal partial times `ω - ∇H₀ · η`. This is the literal identity in the first
paragraph of `app:ch_seed:prop:seed-phase-charts`. -/
theorem determinant_incidence_eq {z : Euclidean 3}
    (hz : z ∈ parameterInterior (2 * P.radius)) (k : Euclidean n) :
    fderiv ℝ cubeDeterminant (P.toFun z) k =
      fderiv ℝ cubeDeterminant (P.toFun z) T.data.adapted.normal *
        (⟪T.data.adapted.normal, k⟫_ℝ -
          ⟪gradient (dispersion T) (T.reference.spatialPatch z),
            T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ) := by
  have ht := determinant_tangential_identity T
    (spatialPatch_mem_dispersion_ball T (fun i ↦ (hz i).le))
    (T.data.adapted.embedding.toContinuousLinearMap.adjoint k)
  have hcov : T.reference.covector (0, T.reference.spatialPatch z) = P.toFun z :=
    T.reference.patch_covector z hz
  rw [hcov] at ht
  conv_lhs => rw [← T.data.adapted.covector_decomposition k]
  rw [map_add, map_smul]
  change ⟪T.data.adapted.normal, k⟫_ℝ * _ + _ = _
  rw [ht]
  ring

end JanetCartan.FullPhaseCharts.FrozenIncidence
