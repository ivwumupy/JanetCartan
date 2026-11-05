module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutReconstruction
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSolverSupport
public import JanetCartan.Iteration.PhysicalPrimary.OriginalObservationPhase
public import JanetCartan.Iteration.PhysicalInitialization.FrameAgreement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSourceTemplate

/-!
# The actual allowed extension in the uncut primary source

The prescribed original extension `qext` is retained literally. In particular
it is not replaced globally by `originalBallExtension`: only its given center
and radius and the original flow range enter the physical phase comparison.
Consumer: the original39 uncut source-class specialization for the finite words
and observed full inverse (`app:ch_response:eq:response-actual-solver-formula`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalUncutSource
open PhysicalInitialization PhysicalSeed ActualCarriers.CurrentFullPhase
open ProtectedFlow ProjectedStressFrame LeadingWave.FullModulation
open ResponsePrimarySources

/-- The raw Hamilton phase agrees with the SAME allowed original extension on
its complete independent-covector domain. The original inner-state certificate
closes the gap and both flow-range premises; `qext` is never reselected
(`app:lem:common-hamilton-phase`). -/
theorem original_native_extension_phase_eq
    {n N : ℕ} (hn : 5 ≤ n) (i : OriginalPatchIndex hn)
    (F : Euclidean n → Euclidean N) (qext : BallExtension.Parameters (Euclidean n))
    (hcenter : qext.center = 0) (hradius : qext.radius = OriginalBoundary.b hn)
    (Qraw Qext : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) (OriginalBoundary.R hn)) ∧
        cNorm (closedBall (0 : Euclidean n)
          (OriginalBoundary.T hn i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (OriginalBoundary.T hn i).family.threshold})
    (hraw : Qraw.1 = projectedStress F)
    (hext : Qext.1 = extendedProjectedStress qext F) :
    EqOn (fun w : Euclidean n × Euclidean (n-1) ↦
        phase (OriginalBoundary.T hn i) Qraw w.1 w.2)
      (fun w ↦ phase (OriginalBoundary.T hn i) Qext w.1 w.2)
      (phaseDomain (OriginalBoundary.T hn i)) := by
  obtain ⟨Rinner,A,_hRinner,hinner,_hprojection,hrange,hgap⟩ :=
    OriginalBoundary.innerState_certificate hn i
  have hcoordinates := (OriginalBoundary.T hn i).coordinates_eqOn_projectedStress_extended F
    qext hcenter hradius (ball_subset_ball (OriginalBoundary.b_lt_R hn).le)
    (OriginalBoundary.stateDomain_subset_ball hn i) Qraw Qext hraw hext hinner.le
    (hgap Qraw) (hrange Qraw) (hrange Qext)
  exact RawPrimary.LocalFrameAgreement.phase_eqOn_of_coordinates_eqOn _ Qraw Qext hcoordinates

/-- The WHOLE closed native physical ball lies in the original protected
phase source. In particular this covers the original uncut solver output,
which need not fit in the smaller source chart. No source-core containment or
new output multiplier is used (`app:ch_response:eq:response-reconstruction-grading`). -/
theorem native_physical_ball_subset_original_source
    {d : ℕ} (hn : 5 ≤ d+1) (r μ : ℝ) (hr : 0 < r) (hμ : 0 < μ)
    {K : Set (Euclidean (d+1))} {M : ℝ}
    (f : RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily
      (ball 0 (OriginalBoundary.b hn)) 0
      (OriginalRegular.coreRadius hn (OriginalRegular.screenedRadius hn r μ))
      (cubeStress (d+1)) K M) (a : OriginalPatchIndex hn) :
    closedBall (0 : Euclidean (d+1)) f.physicalRadius ⊆ OriginalProtected.Xsrc hn a := by
  have hcore := (closedBall_subset_closedBall
    (by linarith only [f.physicalRadius_pos] : f.physicalRadius ≤ 4*f.physicalRadius)).trans
      f.physicalBall_coefficientDomain
  exact hcore.trans
    ((OriginalRegular.core_spec hn (OriginalRegular.screened_pos hn hr hμ)).2.2.2 a).1

/-- The source chart and χ₃ shoulders inherit the same protected inclusion;
this does NOT assert that the solver's entire output lies in this chart. -/
theorem native_chart_subset_original_source
    {d : ℕ} (hn : 5 ≤ d+1) (r μ : ℝ) (hr : 0 < r) (hμ : 0 < μ)
    {K : Set (Euclidean (d+1))} {M : ℝ}
    (f : RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily
      (ball 0 (OriginalBoundary.b hn)) 0
      (OriginalRegular.coreRadius hn (OriginalRegular.screenedRadius hn r μ))
      (cubeStress (d+1)) K M) (t : ℝ) (a : OriginalPatchIndex hn) :
    ball (0 : Euclidean (d+1)) (min t f.physicalRadius) ⊆ OriginalProtected.Xsrc hn a := by
  exact ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall).trans
    (native_physical_ball_subset_original_source hn r μ hr hμ f a)

end JanetCartan.PhysicalPrimary.OriginalUncutSource

retain_original_uncut_chart_source
