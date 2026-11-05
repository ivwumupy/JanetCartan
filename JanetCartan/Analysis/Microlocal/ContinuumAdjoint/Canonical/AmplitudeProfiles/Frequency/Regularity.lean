module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Frequency.Angular
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Definitions

/-!
# Joint smoothness and original support of the fixed-cutoff amplitude

The high cutoff cancels both frequency singularities at zero. The smoothness
inputs below are exactly the primitive scalar-transport inputs; the initial
scalar, flow, and geometric extension modules produce them. No chart geometry
is needed for the amplitude field of `ModifiedNormalSymbol.PrimitiveRegularity`.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow DerivativeKernels ModifiedNormalSymbol

variable {n N : ℕ}

/-- The literal half-order radial factor vanishes throughout the removed low
frequencies (`app:ch_background:eq:bg-T`). -/
theorem halfOrderRadialFactor_eq_zero {η : Euclidean (n-1)} (hη : ‖η‖ ≤ 1) :
    halfOrderRadialFactor FixedCutoffs.highFrequency η = 0 := by
  simp [halfOrderRadialFactor, FixedCutoffs.highFrequency_zero hη]

/-- Smoothness of the literal cutoff times square root, including the origin.
Consumer: the radial and amplitude regularity hypotheses of the scalar
transport endpoint (`app:ch_background:prop:bg-adjoint`). -/
theorem halfOrderRadialFactor_contDiff :
    ContDiff ℝ ∞ (halfOrderRadialFactor (n := n) FixedCutoffs.highFrequency) := by
  apply contDiff_iff_contDiffAt.mpr
  intro η
  by_cases hη : η = 0
  · subst η
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : Euclidean (n-1)) zero_lt_one] with y hy
    exact halfOrderRadialFactor_eq_zero (by simpa using (mem_ball_zero_iff.mp hy).le)
  · have hn : ContDiffAt ℝ ∞ (fun y : Euclidean (n-1) ↦ ‖y‖) η :=
      contDiffAt_id.norm ℝ hη
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp η
      ((FixedCutoffs.highFrequency_smooth.contDiffAt.comp η hn).mul
        (hn.sqrt (norm_ne_zero_iff.mpr hη)))

/-- The endpoint's scaled radial function is globally smooth for every scale
(`app:ch_background:prop:bg-adjoint`). -/
theorem scaled_halfOrderRadialFactor_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (fun p : AdjointSymbolPoint n ↦
      halfOrderRadialFactor FixedCutoffs.highFrequency (R • p.2)) :=
  halfOrderRadialFactor_contDiff.comp (contDiff_snd.const_smul R)

/-- Global joint smoothness of the actual radial times normalized amplitude.
The cutoff removes the angular normalization singularity at zero. All premises
are the primitive global smoothness hypotheses already consumed by the scalar
transport endpoint (`app:ch_background:prop:bg-adjoint`). -/
theorem frequencyScale_normalizedTransportAmplitude_contDiff
    (c : AdjointJetPoint n → ℂ)
    (mask : CarrierParameter → Euclidean (n-1) → ℂ)
    (r : CarrierVariable n → ℂ) (Y : AdjointJetPoint n → Euclidean (n-1))
    (flow : AdjointJetPoint n → ℂ)
    (hc : ContDiff ℝ ∞ c)
    (hm : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ mask p.1 p.2))
    (hr : ContDiff ℝ ∞ r)
    (hY : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (p.1, Y p)))
    (hf : ContDiff ℝ ∞ flow) :
    ContDiff ℝ ∞ (fun q : AmplitudeVariables n ↦
      frequencyScaleAmplitude (halfOrderRadialFactor FixedCutoffs.highFrequency)
        (normalizedTransportAmplitude c mask r Y flow) q.1 q.2.1 q.2.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q.2.2 = 0
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have he : ∀ᶠ p : AmplitudeVariables n in 𝓝 q, ‖p.2.2‖ < 1 :=
      continuous_snd.snd.norm.continuousAt.eventually_lt continuousAt_const (by simp [hq])
    filter_upwards [he] with p hp
    simp [frequencyScaleAmplitude, halfOrderRadialFactor_eq_zero hp.le]
  · have hpr : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ (p.1, p.2.1)) :=
      contDiff_fst.prodMk contDiff_snd.fst
    have hnorm : ContDiffAt ℝ ∞ (fun p : AmplitudeVariables n ↦ ‖p.2.2‖⁻¹ • p.2.2) q :=
      ((contDiffAt_snd.snd.norm ℝ hq).inv (norm_ne_zero_iff.mpr hq)).smul
        contDiffAt_snd.snd
    exact (halfOrderRadialFactor_contDiff.comp contDiff_snd.snd).contDiffAt.mul
      ((((hc.comp hpr).contDiffAt.mul
        (hm.contDiffAt.comp q (contDiffAt_fst.prodMk hnorm))).mul
        ((hr.comp hY).comp hpr).contDiffAt).mul (hf.comp hpr).contDiffAt)

/-- The amplitude field of `PrimitiveRegularity` for the original component,
derived from the scalar transport's primitive formula and smoothness. The
geometric, initial-scalar, and flow producers supply `hc`, `hr`, `hf`, and `hY`;
the fixed mask producer supplies `hm`. The high cutoff remains the actual one
(`app:ch_background:prop:bg-adjoint`). -/
theorem frequencyScale_carrierChartNormalizedComponent_contDiff
    (d : CarrierData n N) (χ : Euclidean n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N)
    (r : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (hν : ∀ z x, d.normalField x z =
      (r (z, d.transportedPosition x z) * flow (z,x)) • ν (z,x))
    (hhigh : d.highCutoff = FixedCutoffs.highFrequency)
    (j : Fin n) (hc : ContDiff ℝ ∞ (carrierChartGeometryComponent d χ ν j))
    (hm : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hr : ContDiff ℝ ∞ (fun p ↦ (r p : ℂ)))
    (hf : ContDiff ℝ ∞ (fun p ↦ (flow p : ℂ)))
    (hY : ContDiff ℝ ∞
      (fun p : AdjointJetPoint n ↦ (p.1, d.transportedPosition p.2 p.1))) :
    ContDiff ℝ ∞ (fun q : AmplitudeVariables n ↦
      frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
        (carrierChartNormalizedComponent d χ j) q.1 q.2.1 q.2.2) := by
  rw [hhigh, carrierChartNormalizedComponent_eq_scalarTransport d χ ν r flow hν j]
  exact frequencyScale_normalizedTransportAmplitude_contDiff _ _ _ _ _
    hc hm (hr.pow 2) hY (hf.pow 2)

/-- Nonvanishing of the original component forces the compact physical,
carrier, and unit-direction support and the original radial cutoff `1`.
Only the actual masks enter; transported scalars and normals are unrestricted.
The mask identities are definitional for `CanonicalCarrier.data` and remain
definitional after `scalarTransportData` (`app:ch_background:eq:bg-T`). -/
theorem frequencyScale_carrierChartNormalizedComponent_support
    (d : CarrierData n N) (z₀ : Euclidean 3) (θ₀ : Euclidean (n-1))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmask : d.angularCutoff = CanonicalConic.angularMask z₀ θ₀ ha hb)
    (hhigh : d.highCutoff = FixedCutoffs.highFrequency)
    (j : Fin n) (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n-1))
    (hne : frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
      (carrierChartNormalizedComponent d (FixedCutoffs.physical ha 1) j) z x η ≠ 0) :
    z ∈ CanonicalConic.carrierSupport z₀ (r := a) ∧
      x ∈ closedBall 0 (4*a) ∧
      ‖η‖⁻¹ • η ∈ sphere 0 1 ∩ closedBall θ₀ (b/2) ∧ 1 ≤ ‖η‖ := by
  have hrad : 1 < ‖η‖ := by
    by_contra h
    exact hne (by simp [frequencyScaleAmplitude, hhigh,
      halfOrderRadialFactor_eq_zero (le_of_not_gt h)])
  have hnorm : η ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hrad)
  have hm : CanonicalConic.angularMask z₀ θ₀ ha hb z (‖η‖⁻¹ • η) ≠ 0 := by
    intro hm
    apply hne
    simp [frequencyScaleAmplitude, carrierChartNormalizedComponent, hmask, hm]
  have hx : FixedCutoffs.physical ha 1 x ≠ 0 := by
    intro hx
    apply hne
    simp [frequencyScaleAmplitude, carrierChartNormalizedComponent, hx]
  obtain ⟨hz, hv, hθ⟩ := CanonicalConic.angularMask_nonzero z₀ θ₀ ha hb hm
  exact ⟨⟨ball_subset_closedBall hz, ball_subset_closedBall hv⟩,
    FixedCutoffs.physical_tsupport_four ha 1 (subset_tsupport _ hx),
    ⟨mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hnorm),
      ball_subset_closedBall hθ⟩, hrad.le⟩

/-- Compact original supports for the scalar-transport endpoint. The direction
set consists only of unit vectors (`app:ch_background:prop:bg-adjoint`). -/
theorem fixed_frequency_supports_compact (z₀ : Euclidean 3)
    (θ₀ : Euclidean (n-1)) (a b : ℝ) :
    IsCompact (closedBall (0 : Euclidean n) (4*a)) ∧
      IsCompact (CanonicalConic.carrierSupport z₀ (r := a)) ∧
      IsCompact (sphere (0 : Euclidean (n-1)) 1 ∩ closedBall θ₀ (b/2)) ∧
      sphere (0 : Euclidean (n-1)) 1 ∩ closedBall θ₀ (b/2) ⊆ {η | ‖η‖ = 1} :=
  ⟨isCompact_closedBall _ _, CanonicalConic.carrierSupport_compact z₀,
    (isCompact_sphere _ _).inter_right isClosed_closedBall,
    fun _ h ↦ mem_sphere_zero_iff_norm.mp h.1⟩

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
