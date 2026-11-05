module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverSourceBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.FullPrimaryResponse
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Displacement

/-!
# Joint corrected-atom regularity from the same direct smooth solver

Substitute the checked source bound into `Response.SmoothParameters` for the
literal full primary response. Canonical integration and the density and
sampling consumers obtain smoothness of the SAME corrected atom, displacement
amplitude and derivative amplitude. No joint response regularity or component
bound is added as a premise. The source cutoff, original scalar, geometry and
single fixed solver remain identical at every parameter and frequency.

Actual selection of that solver on the initialized stationary family and the
frequency-sensitive response estimates remain construction obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open RawPrimary PrimarySourceAdmission ResponseSourceExtension ResponseSmoothParameters
open FixedDomainInverse LocalSobolev
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open FourierIntegral FiniteChain.Graph.KernelLimits

variable {d N : ℕ}
variable {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (F : Euclidean (d + 1) → Euclidean N) (row col : Fin (d + 1))
    (Φ Y : ℝ × (Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) →
      Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))
    (χ η : Euclidean (d + 1) → ℝ) (hη : ContDiff ℝ ∞ η) (hχU : tsupport χ ⊆ U)
    {W core chart : Set (Euclidean (d + 1))}
    (solver : smoothSource W (Euclidean (d + 1)) →ₗ[ℝ] (Euclidean (d + 1) → Euclidean (d + 1)))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (x : Euclidean (d + 1)) (Rout : ℝ) (hcore : closedBall x Rout ⊆ core)
    (D a : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m) (ha : ∀ m, 0 ≤ a m) (β : ℕ)
    (hbound : ∀ (h : smoothSource W (Euclidean (d + 1))) (m : ℕ),
      cNorm (closedBall x Rout) m (solver h) ≤ D m *
        (restrictionSobolevNorm W (m + (d + 2)) (h : LocalL2 W (Euclidean (d + 1))) +
          (1 + a (m + (d + 2) + β)) * ‖(h : LocalL2 W (Euclidean (d + 1)))‖))
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    {Ω O : Set (Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hO : IsOpen O) (hout : ∀ w ∈ O, w.1 ∈ interior (closedBall x Rout))
    (hsrc : ∀ w ∈ O, ∀ y ∈ tsupport χ, (y, w.2) ∈ Ω)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)

set_option quotPrecheck false in
local notation "Bfixed" => fixedSmoothSolverAmbientExtension F Q.1 η hU
  (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ

include hchart hchartU hcore hD ha hbound he hΩ hspace hphase hF hi hrank
  hnonzero hO hout hsrc hχ hc

/-- The direct solver's existing classical source estimate implies joint
regularity of the actual full-primary response. The original source family,
cutoff, measure and single response are retained; no tensor-response bound or
joint regularity is assumed (`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_fullPrimaryResponse_fixedSmoothSolver_of_classical_bound
    (τ : ℝ) (r : Euclidean ((d + 1) - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) :
    ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ Bfixed τ r w.2 w.1) O := by
  have hB := exists_fixedSmoothSolver_tensorComponent_bounds e he F Q.1 η hc hU
    (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ hchart
    (hF.mono hchartU) (fun y hy ↦ hi y (hchartU hy))
    (fun y hy ↦ hrank y (hchartU hy)) x Rout hcore D a hD ha β hbound
  have hBreg (h : compactSmoothSources (tsupport χ)) : ContDiff ℝ ∞ (Bfixed h) :=
    contDiff_fixedSmoothSolverAmbientExtension F Q.1 η hU
      (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ hchart
      (hF.mono hchartU) (fun y hy ↦ hi y (hchartU hy))
      (fun y hy ↦ hrank y (hchartU hy)) h
  exact contDiffOn_fullPrimaryResponse_of_tame T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero χ hχ hc e (isCompact_closedBall x Rout)
    hO hout hsrc Bfixed hBreg hB τ

/-- The SAME corrected field and its two literal modulated amplitudes are
jointly smooth under the accepted direct solver bound. This supplies the
regularity for canonical integration, density estimates, raw slices and
sampling without selecting an inverse for each scalar or frequency
(`app:ch_response:cor:current-atoms`, `app:ch_response:eq:current-atomic-amplitudes`). -/
theorem contDiffOn_fullCorrectedPrimary_family_fixedSmoothSolver
    (hOΩ : O ⊆ Ω) {τ : ℝ} (hτ : τ ≠ 0)
    (r : Euclidean ((d + 1) - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) :
    ContDiffOn ℝ ∞
      (fun w ↦ fullCorrectedPrimaryAtom T Q F row col Φ Y χ Bfixed τ r w.2 w.1) O ∧
      ContDiffOn ℝ ∞ (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ Bfixed r τ) O ∧
      ContDiffOn ℝ ∞ (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ Bfixed r τ) O := by
  have hresp := contDiffOn_fullPrimaryResponse_fixedSmoothSolver_of_classical_bound T Q F row col
    Φ Y χ η hη hχU solver hsolver Ξ hchart hchartU x Rout hcore D a hD ha β hbound
    e he hΩ hspace hphase hF hi hrank hnonzero hO hout hsrc hχ hc τ r hα
  have hspaceO := fun w (hw : w ∈ O) ↦ hspace w (hOΩ hw)
  have hphaseO := fun w (hw : w ∈ O) ↦ hphase w (hOΩ hw)
  have hnO := fun w (hw : w ∈ O) ↦ hnonzero w (hOΩ hw)
  exact ⟨contDiffOn_fullCorrectedPrimaryAtom_joint T Q F row col Φ Y χ Bfixed r
    hO hspaceO hphaseO hF hi hrank (hα.mono hOΩ) hnO τ hresp,
    contDiffOn_fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ Bfixed r
      hO hspaceO hphaseO hF hi hrank (hα.mono hOΩ) hnO hτ hresp,
    contDiffOn_fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ Bfixed r
      hO hspaceO hphaseO hF hi hrank (hα.mono hOΩ) hnO hτ hresp⟩

end JanetCartan.CorrectedAtoms
