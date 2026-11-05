module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredGraphLimits
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.UniformSupported.Integrated

/-!
# Measured graph limits from the retained supported auxiliary

Supported equality transfers the uncut test action from the smooth auxiliary
to the original phase, preserving both measurements and literal strong limits.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds FourierIntegral.LowBounds.FrequencyCutoff
open RegularSector.FiniteAssembly RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

/-- The retained smooth auxiliary phase and amplitude give the uncut test action
of the original canonical graph on the same supported carrier. Only the zeroth
primitive amplitude bound is used; an empty source mask is included. Consumer:
measurement covariance for the supported retarded leakage estimate
(`app:ch_regular_base:eq:fixed-time-representation`,
`app:ch_regular_base:eq:measured-adjoint`). -/
theorem elapsedGraph_test_action_of_supported_auxiliary
    (Ψoriginal Ψ : TwoTimePhase d) (boriginal b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (r : ℝ)
    (hΨ : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ))
    (hb : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b))
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℝ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ)
    (C : ℝ) (hbound : ∀ x ∈ tsupport χout, ∀ z ∈ tsupport χsource, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0-r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
    (hameq : elapsedAmplitude b χout χsource β r = elapsedAmplitude boriginal χout χsource β r)
    (hphase : ∀ x z ξ, elapsedAmplitude b χout χsource β r x z ξ ≠ 0 →
      elapsedPhase Ψ r x ξ = elapsedPhase Ψoriginal r x ξ)
    (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace (d+1) q),
      Treg j (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψoriginal r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j)
          (elapsedAmplitude boriginal χout χsource β r)) u)
    (hlim : ∀ u, Tendsto (fun j ↦ Treg j u) atTop
      (𝓝 (elapsedGraph Ψoriginal boriginal χout χsource β r u))) :
    ∀ u : graphTestSpace (d+1) q,
      elapsedGraph Ψoriginal boriginal χout χsource β r (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψoriginal r) (elapsedAmplitude boriginal χout χsource β r) u := by
  have hgraph : elapsedGraph Ψ b χout χsource β r =
      elapsedGraph Ψoriginal boriginal χout χsource β r := by
    calc
      _ = elapsedGraph Ψoriginal b χout χsource β r :=
        FullLowBounds.fullGraphOperator_phase_congr _ _ _ hphase
      _ = _ := by unfold elapsedGraph; rw [hameq]
  have hforward (κ : E → ℂ) : graphTestOutput (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude κ (elapsedAmplitude b χout χsource β r)) =
      graphTestOutput (elapsedPhase Ψoriginal r)
        (frequencyCutFullAmplitude κ (elapsedAmplitude boriginal χout χsource β r)) := by
    rw [← hameq]
    apply graphTestOutput_phase_congr
    intro x z ξ hne
    exact hphase x z ξ (fun hz ↦ hne (by simp only [frequencyCutFullAmplitude, hz, smul_zero]))
  have huncut : graphTestOutput (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r) =
      graphTestOutput (elapsedPhase Ψoriginal r) (elapsedAmplitude boriginal χout χsource β r) := by
    rw [← hameq]
    exact graphTestOutput_phase_congr _ _ _ hphase
  by_cases hsource : (tsupport χsource).Nonempty
  · obtain ⟨z, hz⟩ := hsource
    have h := elapsedGraph_test_action_of_physical_regularizations Ψ b χout χsource β hs hβ
      Cβ hβbound r
      (fun x _ ξ _ ↦ (hΨ.continuous.comp
        ((continuous_const (y := (x 0, x 0-r, spatialPart x))).prodMk continuous_spatialPart)).continuousAt)
      (fun x _ ξ _ ↦ (hb.continuous.comp
        ((continuous_const (y := (x 0, x 0-r, spatialPart x))).prodMk continuous_spatialPart)).continuousAt)
      C (fun x hx ξ hξ ↦ hbound x hx z hz ξ hξ) Treg
      (fun j u ↦ by rw [hforward]; exact hreal j u)
      (fun u ↦ by rw [hgraph]; exact hlim u)
    simpa only [hgraph, huncut] using h
  · have hs0 (z : E) : χsource z = 0 := by
      by_contra hz
      exact hsource ⟨z, subset_tsupport _ hz⟩
    have hzero : ∀ u : graphTestSpace (d+1) q,
        (0 : H →L[ℂ] H) (graphTestToLp u) =ᵐ[volume]
          graphTestOutput (elapsedPhase Ψoriginal r) (elapsedAmplitude boriginal χout χsource β r) u := by
      intro u
      simp only [zero_apply]
      filter_upwards [Lp.coeFn_zero (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)] with x hx
      rw [hx]
      simp [graphTestOutput, graphOperator, elapsedAmplitude, hs0]
    have he := FullLowBounds.fullGraphOperator_eq_of_realizes
      (elapsedPhase Ψoriginal r) (elapsedAmplitude boriginal χout χsource β r) 0 hzero
    change elapsedGraph Ψoriginal boriginal χout χsource β r = 0 at he
    rw [he]
    exact hzero

/-- Supported smooth auxiliary data identify the original measured graph,
its literal adjoint regularizations, strong limits and datum-wise time integral.
The original phase need not be globally smooth. Its supported equality and the
primitive zeroth amplitude bound come from the retained phase/amplitude producers.
Consumer: measured retarded letters of the normalized residual words
(`app:ch_regular_base:eq:fixed-time-representation`,
`app:ch_regular_base:eq:measured-adjoint`, `app:ch_regular:eq:chain-tail`). -/
theorem measured_elapsedGraph_regularizations_of_supported_auxiliary
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℝ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ) (Δ : ℝ)
    (Ψaux : TwoTimePhase d) (baux : TwoTimeAmplitude d q)
    (hΨaux : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψaux))
    (hbaux : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude baux))
    (C : ℝ) (hbound : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout,
      ∀ z ∈ tsupport χsource, ∀ ξ ∈ tsupport β,
      ‖baux (x 0) (x 0-r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
    (hameq : ∀ r ∈ Icc 0 Δ, elapsedAmplitude baux χout χsource β r =
      elapsedAmplitude b χout χsource β r)
    (hphase : ∀ r ∈ Icc 0 Δ, ∀ x z ξ, elapsedAmplitude baux χout χsource β r x z ξ ≠ 0 →
      elapsedPhase Ψaux r x ξ = elapsedPhase Ψ r x ξ)
    (Treg : ℕ → ℝ → H →L[ℂ] H)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j)
          (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x y ξ ↦ (elapsedAmplitude b χout χsource β r x y ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) y))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u)
      (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    (LOW : ℝ) (hlow : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ LOW)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u)))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    let Tm := fun j r ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb (Treg j r)
    let χo := fun x ↦ (μ x : ℂ)*χout x
    let χs := fun y ↦ (ν y : ℂ)*χsource y
    (∀ r ∈ Icc 0 Δ,
      measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
        (elapsedGraph Ψ b χout χsource β r) = elapsedGraph Ψ b χo χs β r) ∧
    (∀ j r, r ∈ Icc 0 Δ → ‖Tm j r‖ ≤ LOW) ∧
    (∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) q,
      Tm j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude b χo χs β r)) u) ∧
    (∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) q,
      (Tm j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x y ξ ↦ (elapsedAmplitude b χo χs β r x y ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) y)) ∧
    (∀ j u, AEStronglyMeasurable (fun r ↦ Tm j r u) (volume.restrict (Icc 0 Δ))) ∧
    (∀ j u, AEStronglyMeasurable (fun r ↦ (Tm j r).adjoint u) (volume.restrict (Icc 0 Δ))) ∧
    (∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Tm j r u) atTop
      (𝓝 (elapsedGraph Ψ b χo χs β r u))) ∧
    (∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Tm j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χo χs β r).adjoint u))) ∧
    ∀ Q : H →L[ℂ] H,
      (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) →
      ∀ u, measuredOperator μ ν hμ.continuous hν.continuous hμb hνb Q u =
        elapsedGraphIntegral Δ Ψ b χo χs β u := by
  intro Tm χo χs
  have hid r (hr : r ∈ Icc 0 Δ) := measured_elapsedGraph_eq Ψ b χout χsource β r
    (elapsedGraph_test_action_of_supported_auxiliary Ψ Ψaux b baux χout χsource β r
      hΨaux hbaux hs hβ Cβ hβbound C (hbound r hr) (hameq r hr) (hphase r hr)
      (fun j ↦ Treg j r) (fun j ↦ hreal j r hr) (hlim r hr)) μ ν hμ hν hμb hνb
  refine ⟨hid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j r hr
    have hi := norm_sourceCutMultiplier_le (r := q) ν hν.continuous hνb
    have ho := norm_sourceCutMultiplier_le (r := q) μ hμ.continuous hμb
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) ho)).trans
      (((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hi)).trans (hlow j r hr))
  · intro j r hr
    exact (measured_elapsed_regularization_test_actions Ψ b χout χsource β
      (complexPhysicalCutoff j) r (Treg j r) (hreal j r hr) (hrealAdj j r hr)
      μ ν hμ hν hμb hνb).1
  · intro j r hr
    exact (measured_elapsed_regularization_test_actions Ψ b χout χsource β
      (complexPhysicalCutoff j) r (Treg j r) (hreal j r hr) (hrealAdj j r hr)
      μ ν hμ hν hμb hνb).2
  · intro j u
    exact (sourceCutMultiplier μ hμ.continuous hμb).continuous.comp_aestronglyMeasurable
      (hm j (sourceCutMultiplier ν hν.continuous hνb u))
  · intro j u
    simp only [Tm, measuredOperator_adjoint]
    exact (sourceCutMultiplier ν hν.continuous hνb).continuous.comp_aestronglyMeasurable
      (hmAdj j (sourceCutMultiplier μ hμ.continuous hμb u))
  · intro r hr u
    rw [← hid r hr]
    exact (sourceCutMultiplier μ hμ.continuous hμb).continuous.continuousAt.tendsto.comp
      (hlim r hr (sourceCutMultiplier ν hν.continuous hνb u))
  · intro r hr u
    rw [← hid r hr]
    simp only [Tm, measuredOperator_adjoint]
    exact (sourceCutMultiplier ν hν.continuous hνb).continuous.continuousAt.tendsto.comp
      (hlimAdj r hr (sourceCutMultiplier μ hμ.continuous hμb u))
  · intro Q hQ u
    have hmeas (v : H) : AEStronglyMeasurable
        (fun r ↦ elapsedGraph Ψ b χout χsource β r v) (volume.restrict (Icc 0 Δ)) := by
      apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun j r ↦ Treg j r v)
      · exact fun j ↦ hm j v
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact hlim r hr v
    have hnorm r (hr : r ∈ Icc 0 Δ) : ‖elapsedGraph Ψ b χout χsource β r‖ ≤ LOW := by
      apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hlow 0 r hr))
      intro v
      apply le_of_tendsto (hlim r hr v).norm
      exact Eventually.of_forall fun j ↦ ((Treg j r).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hlow j r hr) (norm_nonneg v))
    have hi := integrableOn_apply_of_uniform_bound hmeas hnorm
      (sourceCutMultiplier ν hν.continuous hνb u)
    change sourceCutMultiplier μ hμ.continuous hμb
      (Q (sourceCutMultiplier ν hν.continuous hνb u)) = _
    rw [hQ, elapsedGraphIntegral, ← (sourceCutMultiplier μ hμ.continuous hμb).integral_comp_comm hi]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    exact congrArg (fun T : H →L[ℂ] H ↦ T u) (hid r hr)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
