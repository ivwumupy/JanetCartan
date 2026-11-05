module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Endpoint

/-!
# Phase geometry preceding source-dependent budgets

The underlying supported affine-gap construction fixes its cutoff, complete
agreement chart, and frame tolerance before any immersion budget. Retain that
ordering when adding the existing graph and derivative-trade profiles.
Consumer: the retained-leading adjoint in `app:ch_background:prop:bg-adjoint`,
with the derivative identities of `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
open ContinuumRow DerivativeKernels ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open PhaseExtension

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Retain the supported phase constructor's actual order of choices: the
mask, cutoff, and positive frame threshold precede immersion budgets and
geometric coercivity constants. All profiles, both trades, and phase matching
throughout the complete supported chart are proved by the original producers.
No flow, scalar, or operator premise is added. This supplies the phase side of
`app:ch_background:prop:bg-adjoint` for the common source-scale initializer. -/
theorem exists_projected_supported_phase_inputs_before_budgets {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {r cap : ℝ} (hr : 0 < r) (hcap : 0 < cap)
    (hcarrier : closedBall (ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ (a : ℝ) (χ : Euclidean n × CarrierParameter → ℝ) (δ : ℝ),
      0 < a ∧ a ≤ r ∧ a < cap ∧ 4 * a < T.physicalRadius ∧
      ContDiff ℝ ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ extensionDomain T ∧
      supportedChart z₀ a ⊆ interior {p | χ p = 1} ∧ 0 < δ ∧
      ∀ (M : ℝ) {κmet κ : ℝ}, 0 < κmet → 0 < κ →
      ∀ s : ℕ, ∃ (B : ℕ → ℝ) (D : List (InitialCarrierDerivative n) → ℕ → ℝ),
        (∀ i, 0 ≤ B i) ∧ (∀ ds i, 0 ≤ D ds i) ∧
        ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
          (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
          cNorm K (2 * (n + 1) + 5) F ≤ M →
          (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
          (∀ x ∈ K, ∀ w ∈ normalSpace F x,
            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
          ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δ →
          let Q := ⟨ProjectedStressFrame.projectedStress F,
            contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank),
            hlow⟩
          let A := frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)
          let Y := affineExtension A χ (CanonicalCarrier.transportPosition T Q)
          ContDiff ℝ ∞ Y ∧
          HasCompactSupport (fun p ↦ Y p - A p.1) ∧
          (∀ p ∈ supportedChart z₀ a,
            Y =ᶠ[𝓝 p] CanonicalCarrier.transportPosition T Q) ∧
          (∀ x z, TransverseGap (1 / 4) (spatialMatrix Y z x)) ∧
          ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n × Euclidean (n - 1) ↦
            phase Y p.1 p.2.1 p.2.2) ∧
          ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ (p.1, Y (p.2, p.1))) ∧
          (∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦
            initialField Y p.1 p.2 h)) ∧
          (∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦
            carrierField Y p.1 p.2 h)) ∧
          (∀ z x η h, inner ℝ h η =
            fderiv ℝ (fun y ↦ phase Y z y η) x (initialField Y z x h)) ∧
          (∀ z x η h, fderiv ℝ (fun w ↦ phase Y w x η) z h =
            fderiv ℝ (fun y ↦ phase Y z y η) x (carrierField Y z x h)) ∧
          (∀ x z, (x, z) ∈ supportedChart z₀ a →
            spatialMatrix Y z x = phaseMatrix T Q z x ∧
            transverseLeftInverse (spatialMatrix Y z x) = phaseLeftInverse T Q z x ∧
            initialField Y z x = initialField (CanonicalCarrier.transportPosition T Q) z x ∧
            carrierField Y z x = carrierField (CanonicalCarrier.transportPosition T Q) z x ∧
            ∀ η, phase Y z x η = transportPhase T Q z x η) ∧
          (∀ p : CarrierParameter × Euclidean n, ∀ i, 1 ≤ i → i ≤ s + 2 * (n + 1) →
            ‖iteratedFDeriv ℝ i (fun p : CarrierParameter × Euclidean n ↦
              (p.1, Y (p.2, p.1))) p‖ ≤
              B i * (1 + cNorm K (s + 2 * (n + 1) + 5) F) ^
                (((i - 1 - 2 * (n + 1) : ℕ) : ℝ) / (max s 1 : ℕ))) ∧
          (∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
            ∀ p : AdjointSymbolPoint n, ∀ e ∈ ds, ∀ j i, i ≤ ds.length + 2 * (n + 1) →
              ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
                branchField (initialField Y) (carrierField Y) e j p.1) p‖ ≤
                D ds i * (1 + cNorm K (s + 2 * (n + 1) + 5) F) ^
                  (((i - 2 * (n + 1) : ℕ) : ℝ) / (max s 1 : ℕ))) := by
  obtain ⟨a, χ, δ, ha, har, hacap, hphys, hχ, hrange, hc, hs, hp, hδ, hactual⟩ :=
    exists_supported_affine_extensions_transverseGap T hP z₀ hr hcap hcarrier
  let A := frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  refine ⟨a, χ, δ, ha, har, hacap, hphys, hχ, hrange, hc, hs, hp, hδ, ?_⟩
  intro M κmet κ hκmet hκ s
  obtain ⟨B, hB, hgraph⟩ := exists_projected_affineGraph_profile T (N := N) hP A
    hχ hc hs hK hKU hball M hκmet hκ s
  obtain ⟨D, hD, hfield⟩ := exists_projected_affineField_profile T (N := N) hP A
    hχ hc hs hK hKU hball M hκmet hκ hquarter s
  refine ⟨B, D, hB, hD, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hsmall
  dsimp only
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  let Y := affineExtension A χ (CanonicalCarrier.transportPosition T Q)
  obtain ⟨hY, hcompact, hagree, hgap⟩ := hactual Q hsmall
  have hgap' : ∀ z x, TransverseGap (1 / 4) (spatialMatrix Y z x) := fun z x ↦ hgap x z
  refine ⟨hY, hcompact, hagree, hgap, phase_contDiff hY, graph_contDiff hY,
    initialField_contDiff hY hquarter hgap', carrierField_contDiff hY hquarter hgap',
    initialField_trade hY hquarter hgap', carrierField_trade hY hquarter hgap', ?_,
    hgraph F hF hi hrank hFM hmet hnormal hlow,
    hfield F hF hi hrank hFM hmet hnormal hlow (fun p ↦ hgap p.1 p.2)⟩
  intro x z hxz
  have he := hagree (x, z) hxz
  have hdomain := supportedChart_subset_extensionDomain T ha har hphys hcarrier hxz
  have hphase := phasePoint_mem_ball_of_mem_extensionDomain T hP hdomain
  refine ⟨spatialMatrix_eq_phaseMatrix_of_eventuallyEq T Q he hphase,
    transverseLeftInverse_eq_phaseLeftInverse_of_eventuallyEq T Q he hphase,
    initialField_eq_of_eventuallyEq he, carrierField_eq_of_eventuallyEq he, ?_⟩
  intro η
  exact congrArg (fun y ↦ inner ℝ y η) he.eq_of_nhds


end JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
