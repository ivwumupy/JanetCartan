module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FrequencyCutoffs

/-!
# Compact support buffers for the actual regularized carrier

The compact input sets below contain the original masks at every finite radial
regularization. Their images are compact and remain inside the actual conic
image. These are the slice buffers in `TransportKernel.SymbolInputs`, proved
from the masks and the constructed geometry (`bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol
open NormedSpace

variable {n : ℕ}

/-- Closed angular directions with the same strict cone buffer as the actual
mask (`app:ch_background:defn:bg-row`). -/
def closedDirections (ηb : Euclidean (n - 1)) (r : ℝ) : Set (Euclidean (n - 1)) :=
  sphere 0 1 ∩ closedBall (normalize ηb) (angularWidth ηb r / 2)

/-- The actual closed direction set is compact (`bg-full-complex-amplitude`). -/
theorem closedDirections_compact (ηb : Euclidean (n - 1)) (r : ℝ) :
    IsCompact (closedDirections ηb r) :=
  (isCompact_sphere _ _).inter_right isClosed_closedBall

/-- Finite-band covectors with the original high cutoff and angular buffer
(`app:ch_background:eq:bg-T`). -/
def bandCovectors (ηb : Euclidean (n - 1)) (r R : ℝ) : Set (Euclidean (n - 1)) :=
  (fun p : ℝ × Euclidean (n - 1) ↦ p.1 • p.2) ''
    (Icc 1 (2 * R) ×ˢ closedDirections ηb r)

/-- Compactness uses the literal finite radial regularization (`bg-row`). -/
theorem bandCovectors_compact (ηb : Euclidean (n - 1)) (r R : ℝ) :
    IsCompact (bandCovectors ηb r R) :=
  (isCompact_Icc.prod (closedDirections_compact ηb r)).image
    (continuous_fst.smul continuous_snd)

/-- Every retained finite-band covector is nonzero and has the same buffered
direction (`app:ch_background:eq:bg-Psi`). -/
theorem bandCovectors_spec {ηb η : Euclidean (n - 1)} {r R : ℝ}
    (hη : η ∈ bandCovectors ηb r R) :
    1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * R ∧ normalize η ∈
      closedBall (normalize ηb) (angularWidth ηb r / 2) := by
  obtain ⟨⟨t, θ⟩, ⟨ht, hθ⟩, rfl⟩ := hη
  have hθnorm : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ.1
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hθnorm, mul_one,
    normalize_smul_of_pos htpos, normalize_eq_self_of_norm_eq_one hθnorm] using
      And.intro ht.1 (And.intro ht.2 hθ.2)

/-- The original nonzero angular and high/radial masks produce membership
in the compact band; no transformed support is assumed (`bg-T`). -/
theorem mem_bandCovectors_of_masks {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a R : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hR : 0 < R)
    {z : CarrierParameter} {η : Euclidean (n - 1)}
    (hang : angularMask z₀ (normalize ηb) ha (angularWidth_spec hηb hr).1
      z (‖η‖⁻¹ • η) ≠ 0)
    (hhi : FixedCutoffs.highFrequency ‖η‖ * FixedCutoffs.radialRegularization (‖η‖ / R) ≠ 0) :
    η ∈ bandCovectors ηb r R := by
  have hnorm : 1 < ‖η‖ := lt_of_not_ge (fun h ↦
    (mul_ne_zero_iff.mp hhi).1 (FixedCutoffs.highFrequency_zero h))
  have hne : η ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hnorm)
  have hrad : ‖η‖ / R ∈ ball (0 : ℝ) 2 :=
    FixedCutoffs.radialRegularization.support_eq ▸ (mul_ne_zero_iff.mp hhi).2
  have hupper : ‖η‖ ≤ 2 * R := by
    have hh : |‖η‖ / R| < 2 := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hrad
    exact ((div_lt_iff₀ hR).mp ((le_abs_self _).trans_lt hh)).le
  refine ⟨(‖η‖, normalize η), ⟨⟨hnorm.le, hupper⟩, ?_⟩, norm_smul_normalize η⟩
  exact ⟨mem_sphere_zero_iff_norm.mpr (norm_normalize hne),
    ball_subset_closedBall (angularMask_nonzero z₀ (normalize ηb) ha
      (angularWidth_spec hηb hr).1 hang).2.2⟩

/-- Closed original input support at finite frequency, with both physical
positions and the full original carrier labels (`bg-full-complex-amplitude`). -/
def bandInputSupport (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a R : ℝ) :
    Set (InputVariables n) :=
  (closedBall 0 (4 * a) ×ˢ closedBall 0 (4 * a)) ×ˢ
    (carrierSupport z₀ (r := a) ×ˢ bandCovectors ηb r R)

/-- Compactness is proved before applying the actual forward map (`bg-row`). -/
theorem bandInputSupport_compact (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a R : ℝ) :
    IsCompact (bandInputSupport z₀ ηb r a R) :=
  ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod
    ((carrierSupport_compact z₀).prod (bandCovectors_compact ηb r R))

/-- The closed input support stays strictly inside the SAME open cone
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem bandInputSupport_subset {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a R : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : a ≤ r) :
    bandInputSupport z₀ ηb r a R ⊆ symbolInputDomain z₀ ηb r (6 * a) := by
  rintro p ⟨⟨hx, hy⟩, ⟨⟨hs, hv⟩, hη⟩⟩
  obtain ⟨hl, _, hθ⟩ := bandCovectors_spec hη
  refine ⟨⟨closedBall_subset_ball (by linarith) hv,
    closedBall_subset_ball (by linarith) hx, closedBall_subset_ball (by linarith) hy⟩,
    closedBall_subset_ball (by linarith) hs, norm_pos_iff.mp (zero_lt_one.trans_le hl), ?_⟩
  exact closedBall_subset_ball (by linarith [(angularWidth_spec hηb hr).1]) hθ

/-- Literal primitive-mask containment in the compact input band
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem primitive_masks_mem_bandInputSupport {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a R : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hR : 0 < R)
    {p : InputVariables n}
    (hx : FixedCutoffs.physical ha 1 p.1.1 ≠ 0)
    (hy : FixedCutoffs.physical ha 1 p.1.2 ≠ 0)
    (hang : angularMask z₀ (normalize ηb) ha (angularWidth_spec hηb hr).1
      p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0)
    (hhi : FixedCutoffs.highFrequency ‖p.2.2‖ *
      FixedCutoffs.radialRegularization (‖p.2.2‖ / R) ≠ 0) :
    p ∈ bandInputSupport z₀ ηb r a R := by
  obtain ⟨hs, hv, _⟩ := angularMask_nonzero z₀ (normalize ηb) ha
    (angularWidth_spec hηb hr).1 hang
  exact ⟨⟨FixedCutoffs.physical_tsupport_four ha 1 (subset_tsupport _ hx),
    FixedCutoffs.physical_tsupport_four ha 1 (subset_tsupport _ hy)⟩,
    ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩,
    mem_bandCovectors_of_masks hηb hr ha hR hang hhi⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a R : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : a ≤ r)

include hηb hr ha har in
/-- Every transformed compact input lies in the actual constructed conic
image, retaining both positions and spectator (`bg-full-complex-amplitude`). -/
theorem bandImage_subset_symbolDomain :
    augmentedTransportGradient (transportPosition T Q) '' bandInputSupport z₀ ηb r a R ⊆
      symbolDomain T Q z₀ ηb r (6 * a) := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' := bandInputSupport_subset hηb hr ha har hp
  exact ⟨hp'.1, (p.2.1.1, p.2.2), hp'.2, rfl⟩

include hηb hr ha har in
/-- The transformed support is compact, proved from actual smoothness and
the original compact band (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem bandImage_compact
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r))) :
    IsCompact (augmentedTransportGradient (transportPosition T Q) ''
      bandInputSupport z₀ ηb r a R) := by
  apply (bandInputSupport_compact z₀ ηb r a R).image_of_continuousOn
  have hh := (transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).continuousOn
  exact ((continuousOn_fst.fst.prodMk (continuousOn_fst.snd.prodMk hh)).prodMk
    continuousOn_snd.fst.snd).mono (bandInputSupport_subset hηb hr ha har)

include hηb hr ha har in
/-- Closedness on each spectator slice is a consequence of the compact
transformed original band (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem bandImage_slice_closed
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (p : Variables n) :
    IsClosed {v : Euclidean 2 | (p, v) ∈
      augmentedTransportGradient (transportPosition T Q) '' bandInputSupport z₀ ηb r a R} :=
  (bandImage_compact T Q hηb hr ha har hf).isClosed.preimage
    (continuous_const.prodMk continuous_id)

end JanetCartan.ContinuumRow.CanonicalConic
