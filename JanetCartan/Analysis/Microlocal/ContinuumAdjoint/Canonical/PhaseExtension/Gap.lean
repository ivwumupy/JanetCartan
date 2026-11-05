module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Gap.Comparison
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Gap.Cutoff

/-!
# The actual global transverse gap for the canonical phase extension

The fixed product cutoff controls the frozen spatial correction. The actual
phase comparison then supplies a positive primitive frame threshold that
controls the current correction. Both choices precede the varying frame.
The resulting smooth extension agrees with the actual transported position
near the complete supported chart and has transverse gap `1/4` everywhere.

Consumer: the canonical scalar-transport endpoint, through
`app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- A radius below any prescribed positive cap, a fixed compact cutoff, and
a positive primitive `C⁶` threshold produce the actual smooth affine
extensions with squared transverse gap `1/4` at every physical point and
every carrier label. The reference is the actual frozen transported position
with its carrier fixed at the center. Agreement holds on a neighborhood of
the complete closed mask support. All choices precede the current frame;
the comparison and cutoff errors are proved from the fixed patch data.

This supplies the global rank input for the rectangular derivative trades
and hence `DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem exists_supported_affine_extensions_transverseGap
    {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {r cap : ℝ} (hr : 0 < r) (hcap : 0 < cap)
    (hcarrier : closedBall (ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ (a : ℝ) (χ : Euclidean n × CarrierParameter → ℝ) (δ : ℝ),
      0 < a ∧ a ≤ r ∧ a < cap ∧ 4 * a < T.physicalRadius ∧
      ContDiff ℝ ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ extensionDomain T ∧
      supportedChart z₀ a ⊆ interior {p | χ p = 1} ∧ 0 < δ ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        let A := frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)
        let Y := affineExtension A χ (CanonicalCarrier.transportPosition T Q)
        ContDiff ℝ ∞ Y ∧ HasCompactSupport (fun p ↦ Y p - A p.1) ∧
          (∀ p ∈ supportedChart z₀ a, Y =ᶠ[𝓝 p] CanonicalCarrier.transportPosition T Q) ∧
          ∀ x z, TransverseGap (1 / 4) (spatialMatrix Y z x) := by
  obtain ⟨a, χ, M, ha, har, hacap, hphys, hχ, hrange, hc, hs, hp, hM, hderiv, hfrozen⟩ :=
    exists_frozen_affineExtension_cutoff T hP z₀ hr hcap hcarrier
  let ε := (1 / 4 : ℝ) / (1 + M)
  have hden : 0 < 1 + M := by linarith
  have hε : 0 < ε := div_pos (by norm_num) hden
  have hbudget : (1 + M) * ε ≤ 1 / 4 := (mul_div_cancel₀ _ hden.ne').le
  obtain ⟨δ, hδ, hcomparison⟩ :=
    exists_transportPosition_comparison_threshold T hP hc.isCompact hs hε
  refine ⟨a, χ, δ, ha, har, hacap, hphys, hχ, hrange, hc, hs, hp, hδ, ?_⟩
  intro Q hQ
  dsimp only
  let A := frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)
  have hY := transportPosition_contDiffOn_extensionDomain T hP Q
  refine ⟨affineExtension_contDiff A (extensionDomain_open T) hχ hY hs, ?_, ?_, ?_⟩
  · have he : (fun p ↦ affineExtension A χ (CanonicalCarrier.transportPosition T Q) p - A p.1) =
        fun p ↦ χ p • (CanonicalCarrier.transportPosition T Q p - A p.1) := by
      funext p
      simp only [affineExtension, add_sub_cancel_left]
    rw [he]
    exact hc.smul_right
  · intro p hps
    exact affineExtension_eventuallyEq A _ (hp hps)
  · apply transverseGap_affineExtension_of_comparison T
      (z₀ 0, ActualComparison.spectatorCenter z₀) hχ hrange hM.le hbudget hderiv hfrozen
    · intro p hps
      exact (((hY.contDiffAt ((extensionDomain_open T).mem_nhds (hs hps))).comp p.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
    · intro p hps
      exact ⟨(hcomparison Q hQ p hps).1.le, (hcomparison Q hQ p hps).2.le⟩

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
