module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedGap
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedStationary
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedWhole
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedPrimitivesTemplate

/-! Exact remaining primitive geometric inputs of the native complete residual
and final solver. Both signs of the source have the same differential NORM;
the source sign and literal adjoint remain independent. The whole elapsed
interval, actual multiplier and entire physical box are retained.
Consumer: `exists_physical_history_measured_residual_hstep` and
`exists_physical_history_paired_solver_hstep`
(`app:ch_response:eq:fixed-factor-transfer`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalRetardedPrimitives
open RegularSector RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.FiniteEvolution RegularSector.FinitePdo
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.UniformEvolution
open RegularSector.Characteristic.ResidualCoordinates RegularSector.Characteristic.EvolutionIntegral

/-- The signed source has the SAME differential norm. This is needed because
native53 requests the positive phase band on BOTH signed incidence windows. -/
theorem unsigned_source_band_of_signed {d : ℕ} (negative : Bool)
    (φ : Euclidean (d+1) → (Euclidean 3 × Euclidean d) → ℝ)
    {K : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d))} {lo hi : ℝ}
    (h : ∀ q ∈ K,
      lo ≤ ‖fderiv ℝ (fun y ↦ if negative then -φ y q.2 else φ y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ if negative then -φ y q.2 else φ y q.2) q.1‖ ≤ hi) :
    ∀ q ∈ K,
      lo ≤ ‖fderiv ℝ (fun y ↦ φ y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ φ y q.2) q.1‖ ≤ hi := by
  cases negative <;> simpa only [Bool.false_eq_true, ↓reduceIte, fderiv_fun_neg, norm_neg] using h

/-- The original open half-box lies in the entire closed carrier box. -/
theorem half_box_subset_full_closure {d : ℕ} (z : RootState (Euclidean d))
    {ε : ℝ} (hε : 0 < ε) :
    elapsedPhysicalBox z (ε/2) ⊆ closure (elapsedPhysicalBox z ε) := by
  intro y hy
  apply subset_closure
  have hle : ε/2 ≤ ε := by linarith
  exact ⟨ball_subset_ball hle hy.1,ball_subset_ball hle hy.2⟩

/-- The literal selected multiplier is in the original retained frequency
carrier. This uses its existing angular plateau, not a new high-pass cutoff. -/
theorem selected_multiplier_in_native_frequency {d : ℕ}
    {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
    {K : Set (Euclidean (d+1))}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K M) (p : f.centers)
    {threshold : ℝ} (ht : 1 ≤ threshold) (ε aperture : ℝ)
    (angular : Euclidean d → ℝ)
    (hcone : tsupport (f.angularMask p ∘ physicalCoordinates (f.chart p).index) ∩
      sphere (0 : Euclidean (d+1)) 1 ⊆
      fullAngularCone (f.chart p).radialSection
        (coordinateSplit (f.chart p).index p.val.val).2 (ε/4) (aperture/2))
    (hplateau : ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      conicMask angular =ᶠ[𝓝 (spatialPart ξ)] fun _ ↦ 1) :
    let e := coordinateSplit (f.chart p).index
    let z : RootState (Euclidean d) := ((e x).1,((e x).2,(e p.val.val).2))
    tsupport (selectedEndpointMultiplier f p threshold) ⊆
      retainedFrequencyDomain (f.chart p).radialSection z ε aperture (1/2) := by
  intro e z ξ hξ
  have hc := PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
    (f.angularMask p) (f.chart p).index (zero_lt_one.trans_le ht) hξ
  have hr : ξ ∈ tsupport (dilatedConicMask
      (f.angularMask p ∘ physicalCoordinates (f.chart p).index) threshold) :=
    tsupport_comp_subset Complex.ofReal_zero _ hc
  refine ⟨RegularSector.Characteristic.UniformEvolution.dilatedConicMask_tsupport_subset_fullAngularCone
    (f.chart p).radialSection z (ε/4) (aperture/2) _ hcone (zero_lt_one.trans_le ht) hr, ?_⟩
  have he := (hplateau ξ hξ).self_of_nhds
  have hn : conicMask angular (spatialPart ξ) ≠ 0 := by rw [he]; norm_num
  have hnorm := (conicMask_tsupport_subset angular (subset_tsupport _ hn)).1
  change (1/2 : ℝ) < ‖spatialPart ξ‖
  linarith

retain_original_critical_primitive_projections

end JanetCartan.PhysicalPrimary.OriginalRetardedPrimitives
