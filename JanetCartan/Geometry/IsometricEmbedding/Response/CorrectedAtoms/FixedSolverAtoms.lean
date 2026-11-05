module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolver
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RetainedFamily

/-!
# Literal retained atoms for the fixed smooth solver

The complete real and imaginary cutoff-strain sources are admitted to the
original smooth inverse domain, using `PrimarySourceAdmission`. The fixed
solver's accepted spatial regularity then proves response smoothness and exact
strain cancellation for the same literal retained atom.

This uses the one supplied solver and one existing algebraic extension at all
scalars, carriers and frequencies. Joint parameter regularity, quantitative
envelopes and actual initialized-source-family selection are still required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ η : Euclidean n → ℝ) (hη : ContDiff ℝ ∞ η) (hχU : tsupport χ ⊆ U)
    {W core chart : Set (Euclidean n)}
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)

set_option quotPrecheck false in
local notation "Bfixed" => fixedSmoothSolverAmbientExtension F Q.1 η hU
  (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (c : Euclidean 3 × Euclidean (n - 1))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : ∀ x ∈ tsupport χ, (x, c) ∈ Ω)

include hΩ hspace hphase hF hi hrank hnonzero hchart hchartU hα hχ hc hs

/-- The SAME fixed smooth solver acts on both complete primary quadratures.
Their domain membership and the canonical ambient regularity are proved, so
there is no response-smoothness premise
(`app:ch_response:cor:current-atoms`). -/
theorem contDiff_fullPrimaryResponse_fixedSmoothSolver :
    ContDiff ℝ ∞ (fullPrimaryResponse T Q F row col Φ Y χ Bfixed τ r c) := by
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  obtain ⟨hre, him⟩ := fullPrimaryAtom_source_mem T Q F row col Φ Y r hΩ hspace hF
    τ hw c.1 c.2 χ hχ hc hs
  apply contDiff_complexifyResponse
  · exact contDiff_fixedSmoothSolverAmbientExtension F Q.1 η hU
      (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ hchart
      (hF.mono hchartU) (fun x hx ↦ hi x (hchartU hx))
      (fun x hx ↦ hrank x (hchartU hx)) ⟨_, hre⟩
  · exact contDiff_fixedSmoothSolverAmbientExtension F Q.1 η hU
      (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ hchart
      (hF.mono hchartU) (fun x hx ↦ hi x (hchartU hx))
      (fun x hx ↦ hrank x (hchartU hx)) ⟨_, him⟩

/-- Spatial regularity of the literal corrected atom follows by applying the
fixed smooth solver to its admitted full strain
(`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_fullCorrectedPrimaryAtom_fixedSmoothSolver :
    ContDiffOn ℝ ∞ (fullCorrectedPrimaryAtom T Q F row col Φ Y χ Bfixed τ r c)
      {x : Euclidean n | (x, c) ∈ Ω} :=
  contDiffOn_fullCorrectedPrimaryAtom T Q F row col Φ Y χ Bfixed hΩ hspace hphase
    hF hi hrank hnonzero τ r hα c
    (contDiff_fullPrimaryResponse_fixedSmoothSolver T Q F row col Φ Y χ η hη hχU
      solver hsolver Ξ hΩ hspace hphase hF hi hrank hnonzero hchart hchartU
      τ r hα c hχ hc hs).contDiffOn

/-- Exact full-strain cancellation on the original plateau, with response
differentiability supplied by the accepted smooth inverse. The residual is
that of this same response at every accuracy
(`app:ch_response:cor:current-atoms`). -/
theorem fullCorrectedPrimaryAtom_strain_fixedSmoothSolver
    {x : Euclidean n} (hx : (x, c) ∈ Ω) (hplateau : χ x = 1) :
    WKB.complexLinearizedMetric F
      (fullCorrectedPrimaryAtom T Q F row col Φ Y χ Bfixed τ r c) x =
      -complexAtomicResidual F Bfixed (complexAtomicSource F χ
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2))) x :=
  fullCorrectedPrimaryAtom_strain T Q F row col Φ Y χ Bfixed hΩ hspace hphase
    hF hi hrank hnonzero τ r hα c hx hplateau
    ((contDiff_fullPrimaryResponse_fixedSmoothSolver T Q F row col Φ Y χ η hη hχU
      solver hsolver Ξ hΩ hspace hphase hF hi hrank hnonzero hchart hchartU
      τ r hα c hχ hc hs).differentiable (by simp) x)

end JanetCartan.CorrectedAtoms
