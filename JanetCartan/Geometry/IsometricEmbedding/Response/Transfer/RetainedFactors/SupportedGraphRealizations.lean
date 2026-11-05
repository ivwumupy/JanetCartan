module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedGraphFamily
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.Locality

/-!
# Keep the complete graph certificates under supported phase equality

The controlled representative and the original cancellation phase have identical
full amplitudes. Their supported phase equality retains the original frequency
regularizations, both test actions, strong limits and complete elapsed integral.
Consumer: the actual solver/residual family in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral FourierIntegral.FullLowBounds
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Supported equality preserves the SAME graph regularizations, their low
constant and both literal strong-limit realizations. No quantitative profile
of the original cancellation extension is required. Producer of `he`:
`capped_solver_phase_eq_representative_on_amplitude` or its complete residual
counterpart (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem CappedGraphRealizations.of_supported_phase_eq
    {Δ Cbound : ℝ} {Ψ Ψactual : TwoTimePhase d} {W : TwoTimeAmplitude d q}
    {χout χsource β : E → ℂ}
    (hgraphs : CappedGraphRealizations Δ Ψ W χout χsource β Cbound)
    (he : ∀ t ∈ Icc 0 Δ, ∀ x y ξ,
      elapsedAmplitude W χout χsource β t x y ξ ≠ 0 →
      elapsedPhase Ψactual t x ξ = elapsedPhase Ψ t x ξ) :
    CappedGraphRealizations Δ Ψactual W χout χsource β Cbound := by
  obtain ⟨χ, hχ, hcχ, Treg, hlow, hbound, hreal, hrealAdj, hcut, hlim, hlimAdj⟩ := hgraphs
  have hgraph t (ht : t ∈ Icc 0 Δ) :
      elapsedGraph Ψactual W χout χsource β t = elapsedGraph Ψ W χout χsource β t :=
    fullGraphOperator_phase_congr _ _ _ (he t ht)
  refine ⟨χ, hχ, hcχ, Treg, ?_, hbound, ?_, ?_, hcut, ?_, ?_⟩
  · intro t ht
    rw [hgraph t ht]
    exact hlow t ht
  · intro j t ht u
    have hk := graphTestOutput_phase_congr (elapsedPhase Ψ t) (elapsedPhase Ψactual t)
      (frequencyCutFullAmplitude (χ j) (elapsedAmplitude W χout χsource β t))
      (fun x y ξ h ↦ he t ht x y ξ (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz])))
    simpa only [hk] using hreal j t ht u
  · intro j t ht u
    have hk := reverseGraphOperator_phase_congr (elapsedPhase Ψ t) (elapsedPhase Ψactual t)
      (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
        (fun x y ξ ↦ (elapsedAmplitude W χout χsource β t x y ξ).conjTranspose))
      (fun x y ξ h ↦ he t ht x y ξ (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz])))
      (fun x ↦ (u.val x).ofLp)
    simpa only [hk] using hrealAdj j t ht u
  · intro t ht u
    rw [hgraph t ht]
    exact hlim t ht u
  · intro t ht u
    rw [hgraph t ht]
    exact hlimAdj t ht u

/-- Supported equality retains the SAME bounded complete elapsed operator and
its integral of literal adjoints, with the original interval and low constant.
This keeps the actual cancellation phase and the controlled representative on
one operator (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem CappedIntegralRealization.of_supported_phase_eq
    {Δ Cbound : ℝ} {Ψ Ψactual : TwoTimePhase d} {W : TwoTimeAmplitude d q}
    {χout χsource β : E → ℂ}
    (hintegral : CappedIntegralRealization Δ Ψ W χout χsource β Cbound)
    (he : ∀ t ∈ Icc 0 Δ, ∀ x y ξ,
      elapsedAmplitude W χout χsource β t x y ξ ≠ 0 →
      elapsedPhase Ψactual t x ξ = elapsedPhase Ψ t x ξ) :
    CappedIntegralRealization Δ Ψactual W χout χsource β Cbound := by
  obtain ⟨Op, hOp, hact, hAdj⟩ := hintegral
  have hgraph t (ht : t ∈ Icc 0 Δ) :
      elapsedGraph Ψactual W χout χsource β t = elapsedGraph Ψ W χout χsource β t :=
    fullGraphOperator_phase_congr _ _ _ (he t ht)
  refine ⟨Op, hOp, ?_, ?_⟩
  · intro u
    rw [hact u]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hgraph t ht]
  · intro u
    rw [hAdj u]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hgraph t ht]

/-- The original cancellation phase has the same unregularized graph test
action as its controlled representative. Only equality on the original
nonzero amplitude is used; no quantitative global extension hypothesis is
introduced (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem elapsedGraph_test_action_of_supported_phase_eq
    {Δ : ℝ} {Ψ Ψactual : TwoTimePhase d} {W : TwoTimeAmplitude d q}
    {χout χsource β : E → ℂ}
    (hreal : ∀ t ∈ Icc 0 Δ, ∀ u : graphTestSpace (d+1) q,
      elapsedGraph Ψ W χout χsource β t (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ t) (elapsedAmplitude W χout χsource β t) u)
    (he : ∀ t ∈ Icc 0 Δ, ∀ x y ξ,
      elapsedAmplitude W χout χsource β t x y ξ ≠ 0 →
        elapsedPhase Ψactual t x ξ = elapsedPhase Ψ t x ξ) :
    ∀ t ∈ Icc 0 Δ, ∀ u : graphTestSpace (d+1) q,
      elapsedGraph Ψactual W χout χsource β t (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψactual t) (elapsedAmplitude W χout χsource β t) u := by
  intro t ht u
  have hgraph : elapsedGraph Ψactual W χout χsource β t =
      elapsedGraph Ψ W χout χsource β t := fullGraphOperator_phase_congr _ _ _ (he t ht)
  have hout := graphTestOutput_phase_congr (elapsedPhase Ψ t) (elapsedPhase Ψactual t)
    (elapsedAmplitude W χout χsource β t) (he t ht)
  simpa only [hgraph, hout] using hreal t ht u

end JanetCartan.ResponseTransfer.RetainedFactors
