module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Gap
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Trades

/-!
# Actual global phase inputs for the scalar-transport adjoint

The cutoff, physical radius and positive frame threshold are chosen before
the derivative order and immersion. The actual rank construction discharges
the gap premise of both rectangular trades and the primitive field profiles.
All profiles use the single reserve `2 * (n + 1) + 5` and one high norm.

Consumer: the geometric inputs of
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
The amplitude extensions, conic normal construction and literal carrier
assembly remain with that endpoint's canonical consumer.

Source: `app:ch_background:eq:bg-derivative-trade`,
`app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow DerivativeKernels ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ}

/-- Neighborhood agreement preserves the concrete initial trade field,
including its Gram formula (`app:ch_background:eq:bg-derivative-trade`). -/
theorem initialField_eq_of_eventuallyEq
    {Y₁ Y₂ : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {x : Euclidean n} {z : CarrierParameter} (hY : Y₁ =ᶠ[𝓝 (x, z)] Y₂) :
    initialField Y₁ z x = initialField Y₂ z x := by
  funext h
  unfold initialField
  rw [spatialMatrix_eq_of_eventuallyEq hY]

/-- Neighborhood agreement preserves the full original-carrier trade field,
without dropping any carrier derivative
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem carrierField_eq_of_eventuallyEq
    {Y₁ Y₂ : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {x : Euclidean n} {z : CarrierParameter} (hY : Y₁ =ᶠ[𝓝 (x, z)] Y₂) :
    carrierField Y₁ z x = carrierField Y₂ z x := by
  have he := (hY.comp_tendsto
    (continuousAt_const.prodMk continuousAt_id).tendsto).fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fun w ↦ Y₁ (x, w)) z = fderiv ℝ (fun w ↦ Y₂ (x, w)) z at he
  funext h
  unfold carrierField
  rw [initialField_eq_of_eventuallyEq hY, he]

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the global phase, graph, and rectangular trade inputs for the
actual projected-stress Hamilton chart. The radius is below any prescribed
positive cap. The fixed cutoff agrees with the literal transported position
near the COMPLETE closed physical/carrier mask support, and retains the frozen
affine spatial derivative outside its compact correction.

The squared transverse gap `1/4`, both exact derivative identities, and the
global finite-low/high profiles are conclusions. In particular, the identities
hold for all carrier labels, covectors, directions, and physical points, hence
on the endpoint's fixed compact measurement region. The two profiles have the
endpoint's truncated exponents, including `s = 0`, with the same one high
primitive budget. The primitive immersion bounds and original frame
admissibility are retained; no phase, inverse, or composite-profile premise is
introduced. The buffered carrier rectangle is the one published by
`CanonicalConic.exists_actual_local_charts`.

Consumer: `hY`, `hΦ`, `hL`, `hV`, `hphaseL`, `hphaseV`, `hYB`, and `hcoeff` of
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:eq:bg-derivative-trade`, `app:ch_background:prop:bg-adjoint`). -/
theorem exists_projected_supported_phase_inputs {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {r cap : ℝ} (hr : 0 < r) (hcap : 0 < cap)
    (hcarrier : closedBall (ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ (a : ℝ) (χ : Euclidean n × CarrierParameter → ℝ) (δ : ℝ),
      0 < a ∧ a ≤ r ∧ a < cap ∧ 4 * a < T.physicalRadius ∧
      ContDiff ℝ ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ extensionDomain T ∧
      supportedChart z₀ a ⊆ interior {p | χ p = 1} ∧ 0 < δ ∧
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
  intro s
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

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
