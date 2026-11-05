module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LocalFrameAgreement.Formulas

/-!
# The original raw and extended frames have the same full Hamilton phase

The actual inner-state radius, flow range and transverse gap all come from the
SAME `OriginalBoundary` callback. The affine extension is on its original wide
coefficient ball. We prove equality on the entire original Hamilton target and
full independent-covector phase domain, not global equality of the frames.
Consumers: task13's original source/finite-word join, task22's same-current raw
row, and `app:lem:common-hamilton-phase`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization
open PhysicalSeed ActualCarriers.CurrentFullPhase ProtectedFlow ProjectedStressFrame
open LeadingWave.FullModulation

variable {n N : ℕ} (hn : 5 ≤ n) (i : OriginalPatchIndex hn)
  (F : Euclidean n → Euclidean N)
  (Qraw Qext : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) (OriginalBoundary.R hn)) ∧
      cNorm (closedBall (0 : Euclidean n)
        (OriginalBoundary.T hn i).data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < (OriginalBoundary.T hn i).family.threshold})
  (hraw : Qraw.1 = projectedStress F)
  (hext : Qext.1 = extendedProjectedStress (originalBallExtension hn) F)

include hraw hext

/-- Exact original-coordinate equality from the actual retained initializer;
no flow agreement, phase equality, or current transverse gap is assumed. -/
theorem original_raw_extended_coordinates :
    EqOn ((OriginalBoundary.T hn i).currentChart Qraw).coordinates
      ((OriginalBoundary.T hn i).currentChart Qext).coordinates
        (OriginalBoundary.T hn i).target := by
  obtain ⟨Rinner, A, _hRinner, hinner, _hprojection, hrange, hgap⟩ :=
    OriginalBoundary.innerState_certificate hn i
  exact (OriginalBoundary.T hn i).coordinates_eqOn_projectedStress_extended F
    (originalBallExtension hn) (originalBallExtension_center hn)
    (originalBallExtension_radius hn) (ball_subset_ball (OriginalBoundary.b_lt_R hn).le)
    (OriginalBoundary.stateDomain_subset_ball hn i) Qraw Qext hraw hext hinner.le
    (hgap Qraw) (hrange Qraw) (hrange Qext)

/-- The physical Hamilton phase agrees on its complete original free-covector
window, not just at the carrier graph. -/
theorem original_raw_extended_phase :
    EqOn (fun w : Euclidean n × Euclidean (n - 1) ↦
        phase (OriginalBoundary.T hn i) Qraw w.1 w.2)
      (fun w ↦ phase (OriginalBoundary.T hn i) Qext w.1 w.2)
        (phaseDomain (OriginalBoundary.T hn i)) :=
  RawPrimary.LocalFrameAgreement.phase_eqOn_of_coordinates_eqOn _ Qraw Qext
    (original_raw_extended_coordinates hn i F Qraw Qext hraw hext)

/-- Every joint physical/free-covector phase jet is identical on the SAME open
window. This costs no reserve and imposes no frequency restriction. -/
theorem original_raw_extended_phase_jets (m : ℕ) :
    EqOn (iteratedFDeriv ℝ m (fun w : Euclidean n × Euclidean (n - 1) ↦
        phase (OriginalBoundary.T hn i) Qraw w.1 w.2))
      (iteratedFDeriv ℝ m (fun w ↦ phase (OriginalBoundary.T hn i) Qext w.1 w.2))
        (phaseDomain (OriginalBoundary.T hn i)) := by
  intro w hw
  have he := original_raw_extended_phase hn i F Qraw Qext hraw hext
  exact ((eventuallyEq_of_mem (isOpen_ball.mem_nhds hw)
    (fun _ hx ↦ he hx)).iteratedFDeriv ℝ m).eq_of_nhds

/-- The literal physical phase gradients used by the raw normal row and the
extended finite inverse coincide on the original full phase domain. -/
theorem original_raw_extended_phaseGradient :
    EqOn (fun w : Euclidean n × Euclidean (n - 1) ↦
        phaseGradient (OriginalBoundary.T hn i) Qraw w.1 w.2)
      (fun w ↦ phaseGradient (OriginalBoundary.T hn i) Qext w.1 w.2)
        (phaseDomain (OriginalBoundary.T hn i)) :=
  RawPrimary.LocalFrameAgreement.phaseGradient_eqOn_of_coordinates_eqOn _ Qraw Qext
    (original_raw_extended_coordinates hn i F Qraw Qext hraw hext)

end JanetCartan.PhysicalInitialization
