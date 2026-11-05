module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.MixedHessian
public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# Hamilton coordinates along their actual characteristic

The two identities below connect the inverse projection chart to the null-flow
footpoint in `Canonical.Footpoint`. They follow from the phase differential,
the Hamilton ODE and the differentiated left inverse, without a conservation
premise. Source: `app:lem:common-hamilton-phase`, used in
`app:ch_background:prop:bg-adjoint` and `app:ch_waves:thm:leading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology InnerProductSpace

namespace JanetCartan.ContinuumAdjoint.Canonical.Footpoint
open HamiltonPhase

variable {n : ℕ} {H : HomogeneousSymbol (Euclidean n)}
    {Φ : HamiltonFlow H (Euclidean (n - 1))} (C : ProjectionChart Φ)

/-- The zero-energy covector derivative is the actual initial spatial
coordinate of the Hamilton inverse chart (`app:lem:common-hamilton-phase`).
Consumed by `Canonical.transportPosition_eq_chartCoordinate`. -/
theorem gradient_zeroEnergy_phase_eq_coordinate
    {x : Euclidean n} {ζ : Euclidean (n - 1)}
    (hz : (x, (0, ζ)) ∈ C.target) :
    gradient (fun η ↦ phase C.coordinates (x, (0, η))) ζ =
      (C.coordinates (x, (0, ζ))).2 := by
  have hi : HasFDerivAt (fun η : Euclidean (n - 1) ↦ (x, ((0 : ℝ), η)))
      ((0 : Euclidean (n - 1) →L[ℝ] Euclidean n).prod
        ((0 : Euclidean (n - 1) →L[ℝ] ℝ).prod
          (ContinuousLinearMap.id ℝ (Euclidean (n - 1))))) ζ :=
    (hasFDerivAt_const x ζ).prodMk
      ((hasFDerivAt_const 0 ζ).prodMk (hasFDerivAt_id ζ))
  have hg : HasGradientAt (fun η ↦ phase C.coordinates (x, (0, η)))
      (C.coordinates (x, (0, ζ))).2 ζ := by
    change HasFDerivAt _ (innerSL ℝ (C.coordinates (x, (0, ζ))).2) ζ
    convert! (C.hasFDerivAt_phase hz).comp ζ hi using 1
    ext v
    simp [phaseDifferential_apply]
  exact hg.gradient

/-- The inverse chart sends Hamilton velocity to unit time velocity and zero
initial-position velocity (`app:lem:common-hamilton-phase`). This is the
infinitesimal conservation law used by the actual null characteristic proof. -/
theorem coordinatePositionDerivative_hamiltonVelocity
    {z : Euclidean n × (ℝ × Euclidean (n - 1))} (hz : z ∈ C.target) :
    C.coordinatePositionDerivative z (H.hp (z.1, C.chartMomentum z)) = (1, 0) := by
  let q := chartLift C.coordinates z
  have hq : q ∈ C.source := C.maps_to_source z hz
  have ha := C.source_admissible q hq
  have hp := (Φ.position_derivative q.1 ha.1 q.2 ha.2).comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have hp' : HasDerivAt (fun t ↦ Φ.position (t, q.2))
      (H.hp (z.1, C.chartMomentum z)) q.1 := by
    convert! hp using 1
    simp [flowDifferential_apply, q, C.right_inverse z hz, ProjectionChart.chartMomentum]
  have hpos : Φ.position (q.1, q.2) = z.1 := C.right_inverse z hz
  have hc : HasFDerivAt (fun x ↦ C.coordinates (x, z.2))
      (C.coordinatePositionDerivative z) (Φ.position (q.1, q.2)) := by
    rw [hpos]
    exact C.hasFDerivAt_coordinates_position hz
  have hd := hc.comp_hasDerivAt q.1 hp'
  have he : (fun t ↦ C.coordinates (Φ.position (t, q.2), z.2)) =ᶠ[𝓝 q.1]
      (fun t ↦ (t, q.2.1)) := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (C.isOpen_source.mem_nhds hq)
    filter_upwards [hn] with t ht using C.left_inverse (t, q.2) ht
  exact (hd.congr_of_eventuallyEq he.symm).unique
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2.1))

end JanetCartan.ContinuumAdjoint.Canonical.Footpoint
