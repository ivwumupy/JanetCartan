module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Smooth affine extensions on the complete supported canonical chart

The cutoff is chosen from the published physical and carrier buffers before
the current frame. Agreement includes the full closed measurement/carrier
support, independently of the frequency and its radial regularization.
These results supply global smoothness and local agreement for the scalar
transport endpoint. They do not yet assert the quantitative rank gap.

Source: `app:ch_background:eq:bg-derivative-trade`,
`app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ}

/-- The complete closed physical/carrier support of the canonical masks.
It contains all angular directions and radial regularizations after forgetting
their covectors (`app:ch_background:prop:bg-adjoint`). -/
def supportedChart (z₀ : Euclidean 3) (a : ℝ) : Set (Euclidean n × CarrierParameter) :=
  closedBall 0 (4 * a) ×ˢ CanonicalConic.carrierSupport z₀ (r := a)

/-- Compactness of the entire supported chart, from the published masks
(`app:ch_background:prop:bg-adjoint`). -/
theorem supportedChart_compact (z₀ : Euclidean 3) (a : ℝ) :
    IsCompact (supportedChart (n := n) z₀ a) :=
  (isCompact_closedBall _ _).prod (CanonicalConic.carrierSupport_compact z₀)

/-- Every nonzero original physical and angular mask lies in this chart,
without restricting the angular direction (`app:ch_background:eq:bg-T`). -/
theorem masks_mem_supportedChart {z₀ : Euclidean 3} {θ₀ : Euclidean (n - 1)}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : Euclidean n} {z : CarrierParameter} {θ : Euclidean (n - 1)}
    (hx : FixedCutoffs.physical ha 1 x ≠ 0)
    (hz : CanonicalConic.angularMask z₀ θ₀ ha hb z θ ≠ 0) :
    (x, z) ∈ supportedChart z₀ a := by
  obtain ⟨hs, hv, _⟩ := CanonicalConic.angularMask_nonzero z₀ θ₀ ha hb hz
  exact ⟨FixedCutoffs.physical_tsupport_four ha 1 (subset_tsupport _ hx),
    ball_subset_closedBall hs, ball_subset_closedBall hv⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- An open domain inside both the actual smoothness chart and the primitive
transport-position budget domain (`app:ch_background:eq:bg-mixed-input`). -/
def extensionDomain : Set (Euclidean n × CarrierParameter) :=
  ball 0 T.physicalRadius ×ˢ
    (CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * P.radius / 2))

/-- The extension domain is fixed and open
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem extensionDomain_open : IsOpen (extensionDomain T) :=
  isOpen_ball.prod ((isOpen_parameterInterior _).preimage CanonicalCarrier.parameter.continuous)

/-- Actual local Hamilton smoothness on the same smaller domain used for
primitive jet budgets (`app:ch_background:eq:bg-mixed-input`). -/
theorem transportPosition_contDiffOn_extensionDomain {c C : ℝ} (hP : P.IsValid c C)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) :
    ContDiffOn ℝ ∞ (CanonicalCarrier.transportPosition T Q) (extensionDomain T) := by
  apply (CanonicalCarrier.transportPosition_smooth T Q hP).mono
  intro p hp
  refine ⟨ball_subset_ball ?_ hp.1, hp.2⟩
  have hpos := T.physicalRadius_pos
  dsimp [PatchQuantitativeFamily.physicalRadius] at hpos ⊢
  linarith [min_le_left T.family.radius (3 * T.family.sourceRadius)]

/-- The published buffered carrier rectangle and a smaller physical radius
contain the complete mask support. Both conditions are geometric choices made
before the current frame (`app:ch_background:eq:bg-derivative-trade`). -/
theorem supportedChart_subset_extensionDomain
    {z₀ : Euclidean 3} {r a : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hphys : 4 * a < T.physicalRadius)
    (hcarrier : closedBall (ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    supportedChart z₀ a ⊆ extensionDomain T := by
  rintro p ⟨hx, hs, hv⟩
  refine ⟨closedBall_subset_ball hphys hx, ?_⟩
  exact hcarrier ⟨closedBall_subset_closedBall (by linarith) hv,
    closedBall_subset_closedBall (by linarith) hs⟩

/-- One fixed compact cutoff produces globally smooth affine extensions of
every current Hamilton transported position, agreeing on a neighborhood of
the COMPLETE closed supported chart. This is the qualitative extension input
to the raw scalar-transport adjoint theorem, not a rank-gap or tame-bound
assertion (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_supported_affine_extensions {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {r a : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hphys : 4 * a < T.physicalRadius)
    (hcarrier : closedBall (ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ χ : Euclidean n × CarrierParameter → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ extensionDomain T ∧ supportedChart z₀ a ⊆ interior {p | χ p = 1} ∧
      ∀ (A : Euclidean n →L[ℝ] Euclidean (n - 1)) Q,
        ContDiff ℝ ∞ (affineExtension A χ (CanonicalCarrier.transportPosition T Q)) ∧
        HasCompactSupport (fun p ↦
          affineExtension A χ (CanonicalCarrier.transportPosition T Q) p - A p.1) ∧
        ∀ p ∈ supportedChart z₀ a,
          affineExtension A χ (CanonicalCarrier.transportPosition T Q) =ᶠ[𝓝 p]
            CanonicalCarrier.transportPosition T Q := by
  obtain ⟨χ, hχ, hrange, hc, hs, hp⟩ := CompatibleResponse.exists_compact_family_cutoff
    (supportedChart_compact z₀ a) (extensionDomain_open T)
    (supportedChart_subset_extensionDomain T ha har hphys hcarrier)
  refine ⟨χ, hχ, hrange, hc, hs, hp, fun A Q ↦ ⟨?_, ?_, ?_⟩⟩
  · exact affineExtension_contDiff A (extensionDomain_open T) hχ
      (transportPosition_contDiffOn_extensionDomain T hP Q) hs
  · have he : (fun p ↦ affineExtension A χ (CanonicalCarrier.transportPosition T Q) p - A p.1) =
        fun p ↦ χ p • (CanonicalCarrier.transportPosition T Q p - A p.1) := by
      funext p
      simp only [affineExtension, add_sub_cancel_left]
    rw [he]
    exact hc.smul_right
  · intro p hps
    exact affineExtension_eventuallyEq A _ (hp hps)

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
