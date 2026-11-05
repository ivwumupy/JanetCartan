module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryRoot

/-!
# Regularity from the selected full-energy chart

The consumer `Compatible.RootBuffers.exists_buffered_primary_root` needs a
transverse direction for the literal primary covector. The energy identity of
`T.currentChart Q` provides this directly, without an additional frame bound
or regularity assumption. Source: `app:ch_response:eq:response-exact-phase`.
-/

open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse RegularSector.Characteristic

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The literal primary covector is a regular point of the current determinant.
Differentiating the SAME chart's full-energy eikonal identity rules out a zero
covector differential. The direct root constructor can therefore select an
actual transverse coordinate, without assuming a new root gap
(`app:ch_response:eq:response-exact-phase`). -/
theorem primary_determinant_fderiv_ne_zero (Q : _) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball 0 T.physicalRadius) (hz : z ∈ parameterInterior (2 * P.radius)) :
    fderiv ℝ (determinant (Q.1 x)) (T.carrierGradient Q x z) ≠ 0 := by
  let C := T.currentChart Q
  let η : ℝ × Euclidean (n - 1) := (0, T.reference.spatialPatch z)
  have ht : (x, η) ∈ C.target := T.reference.target_contains x hx z hz
  have hξ : C.chartMomentum (x, η) = T.carrierGradient Q x z :=
    (C.gradient_phase_eq_chartMomentum ht).symm
  have hcoord : ContDiffOn ℝ ∞ C.coordinates C.target :=
    (T.family.coordinates_smooth Q).mono
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius))
  have hp := ((C.contDiffOn_chartMomentum (T.family.momentum_smooth Q) hcoord).contDiffAt
    (C.isOpen_target.mem_nhds ht)).comp η (contDiffAt_const.prodMk contDiffAt_id)
  have hs := T.primary_state_mem Q hx hz
  have hf : DifferentiableAt ℝ (fun ξ ↦ normalizedSymbol Q.1 (x, ξ)) (C.chartMomentum (x, η)) := by
    rw [hξ]
    exact ((contDiffAt_normalizedSymbol (Q.2.1.contDiffAt (hU.mem_nhds hs.1)) hs.2).comp
      (T.carrierGradient Q x z) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hd := hf.hasFDerivAt.comp η (hp.differentiableAt (by simp)).hasFDerivAt
  have he : (fun ζ ↦ normalizedSymbol Q.1 (x, C.chartMomentum (x, ζ))) =ᶠ[𝓝 η]
      (fun ζ : ℝ × Euclidean (n - 1) ↦ ζ.1) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      (C.isOpen_target.mem_nhds ht)] with ζ hζ
    have h := C.eikonal hζ
    rw [C.gradient_phase_eq_chartMomentum hζ] at h
    exact h
  have hderiv := (hd.congr_of_eventuallyEq he.symm).unique
    (ContinuousLinearMap.fst ℝ ℝ (Euclidean (n - 1))).hasFDerivAt
  intro hzero
  have hnorm : fderiv ℝ (fun ξ ↦ normalizedSymbol Q.1 (x, ξ)) (C.chartMomentum (x, η)) = 0 := by
    rw [hξ, fderiv_covector_normalizedSymbol_of_determinant_eq_zero Q.1 x hs.2
      (T.carrier_characteristic Q hx hz), hzero, smul_zero]
  have hv := congrArg (fun L : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ ↦ L (1, 0)) hderiv
  simp [hnorm] at hv

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
