module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.Frequency
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.Regularity

/-!
# Homogeneity of the original phase derivative fields

The radial premises of the full covector comparison follow by differentiating
the original homogeneous two-time phase in its physical coordinates. Both
original time variables remain in the temporal term.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}

/-- Original phase homogeneity implies homogeneity of its spatial momentum
and simultaneous-time derivative. The premise is only a local identity of
the original phase on a physical neighborhood; no frequency comparison is
assumed. Consumer: `exists_phaseCovectorMap_comparison_constants`
(`app:ch_regular:eq:high-phase`). -/
theorem phaseFields_homogeneous_of_phase (Ψ : TwoTimePhase d) (r c : ℝ)
    (t : ℝ) (y η : Euclidean d)
    (hd : DifferentiableAt ℝ (fun p => elapsedSpatialPhase Ψ r p η) (t,y))
    (hh : (fun p => elapsedSpatialPhase Ψ r p (c • η)) =ᶠ[𝓝 (t,y)]
      (fun p => c • elapsedSpatialPhase Ψ r p η)) :
    phaseMomentum Ψ r ((t,y),c • η) = c • phaseMomentum Ψ r ((t,y),η) ∧
      phaseShear Ψ r ((t,y),c • η) = c • phaseShear Ψ r ((t,y),η) := by
  have hfd := (hd.hasFDerivAt.const_smul c).congr_of_eventuallyEq hh
  have hi : HasFDerivAt (fun z : Euclidean d => (t,z)) _ y :=
    (hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id y)
  have hys := hd.hasFDerivAt.comp y hi
  have hyc := hfd.comp y hi
  constructor
  · change (InnerProductSpace.toDual ℝ (Euclidean d)).symm
        (fderiv ℝ (fun z => Ψ t (t-r) z (c • η)) y) =
      c • (InnerProductSpace.toDual ℝ (Euclidean d)).symm
        (fderiv ℝ (fun z => Ψ t (t-r) z η) y)
    dsimp only [Function.comp_def, id_eq, elapsedSpatialPhase] at hys hyc
    rw [hyc.fderiv, hys.fderiv, ContinuousLinearMap.smul_comp, map_smul]
  · change fderiv ℝ (fun p => elapsedSpatialPhase Ψ r p (c • η)) (t,y) (1,0) =
      c • fderiv ℝ (fun p => elapsedSpatialPhase Ψ r p η) (t,y) (1,0)
    rw [hfd.fderiv]
    rfl

/-- Full covector comparison directly from original phase smoothness,
radial homogeneity, the spatial mixed half-gap and the temporal mixed-row
budget. The derivative-field homogeneity premises are discharged here.
The constants are independent of elapsed time and frequency scale whenever
the primitive budget is uniform. Consumer: the full-frequency comparison in
`FiniteChain.Graph.exists_graph_factor_sobolev_bound_of_primitive_grades`
(`app:ch_regular:lem:finite-chain`). -/
theorem phaseCovectorMap_comparison_of_original_phase
    (Ψ : TwoTimePhase d) (r : ℝ) (x ξ : Euclidean (d+1)) {L : ℝ} (hL : 0 ≤ L)
    (hs : ContDiffAt ℝ ∞ (Function.uncurry (elapsedSpatialPhase Ψ r))
      (phaseFieldPoint x ξ))
    (hh : ∀ᶠ c : ℝ in 𝓝 1,
      (fun p => elapsedSpatialPhase Ψ r p (c • spatialPart ξ)) =ᶠ[𝓝 (x 0,spatialPart x)]
        (fun p => c • elapsedSpatialPhase Ψ r p (spatialPart ξ)))
    (hg : ‖fderiv ℝ (fun η => phaseMomentum Ψ r ((x 0,spatialPart x),η))
      (spatialPart ξ)-ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤ 1/2)
    (hb : ‖fderiv ℝ (fun η => phaseShear Ψ r ((x 0,spatialPart x),η))
      (spatialPart ξ)‖ ≤ L) :
    (3+2*L)⁻¹*‖ξ‖ ≤ ‖phaseCovectorMap Ψ r x ξ‖ ∧
      ‖phaseCovectorMap Ψ r x ξ‖ ≤ (3+2*L)*‖ξ‖ := by
  have hreg := contDiffAt_phaseFields Ψ r hs
  have hc := (hasFDerivAt_const (𝕜 := ℝ) (x 0,spatialPart x) (spatialPart ξ)).prodMk
    (hasFDerivAt_id (spatialPart ξ))
  have hdm := ((hreg.2.1.differentiableAt (by simp)).hasFDerivAt.comp (spatialPart ξ) hc).differentiableAt
  have hda := ((hreg.2.2.differentiableAt (by simp)).hasFDerivAt.comp (spatialPart ξ) hc).differentiableAt
  have hds : DifferentiableAt ℝ
      (fun p => elapsedSpatialPhase Ψ r p (spatialPart ξ)) (x 0,spatialPart x) :=
    (hs.comp (x 0,spatialPart x)
      (f := fun p : ℝ × Euclidean d => (p,spatialPart ξ))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hhm : ∀ᶠ c : ℝ in 𝓝 1,
      phaseMomentum Ψ r ((x 0,spatialPart x),c • spatialPart ξ) =
        c • phaseMomentum Ψ r ((x 0,spatialPart x),spatialPart ξ) := by
    filter_upwards [hh] with c hc
    exact (phaseFields_homogeneous_of_phase Ψ r c _ _ _ hds hc).1
  have hha : ∀ᶠ c : ℝ in 𝓝 1,
      phaseShear Ψ r ((x 0,spatialPart x),c • spatialPart ξ) =
        c • phaseShear Ψ r ((x 0,spatialPart x),spatialPart ξ) := by
    filter_upwards [hh] with c hc
    exact (phaseFields_homogeneous_of_phase Ψ r c _ _ _ hds hc).2
  exact triangular_covector_comparison
    (F := fun η => phaseMomentum Ψ r ((x 0,spatialPart x),η))
    (a := fun η => phaseShear Ψ r ((x 0,spatialPart x),η)) hL ξ hdm hhm hg hda hha hb

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
