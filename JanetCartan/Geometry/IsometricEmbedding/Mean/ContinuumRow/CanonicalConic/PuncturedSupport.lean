module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportBuffers

/-!
# The punctured image of the original compact angular support

The radial variable is unbounded. Normalizing its actual output reduces the
closure argument to the image of a compact unit-input support. This proves
the punctured buffer required by the supported global carrier construction,
without assuming any transformed support (`bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol
open NormedSpace

variable {n : ℕ}

/-- The original closed physical/carrier/angular masks, with arbitrary
nonzero radial frequency (`app:ch_background:defn:bg-row`). -/
def conicMaskSupport (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Set (InputVariables n) :=
  {p | p.1 ∈ closedBall 0 (4 * a) ×ˢ closedBall 0 (4 * a) ∧
    p.2.1 ∈ carrierSupport z₀ (r := a) ∧ p.2.2 ≠ 0 ∧
    normalize p.2.2 ∈ closedDirections ηb r}

/-- Compact unit-frequency section of the original masks (`bg-row`). -/
def unitInputSupport (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Set (InputVariables n) :=
  (closedBall 0 (4 * a) ×ˢ closedBall 0 (4 * a)) ×ˢ
    (carrierSupport z₀ (r := a) ×ˢ closedDirections ηb r)

/-- This compact set is fixed before the immersion (`bg-full-complex-amplitude`). -/
theorem unitInputSupport_compact (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    IsCompact (unitInputSupport z₀ ηb r a) :=
  ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod
    ((carrierSupport_compact z₀).prod (closedDirections_compact ηb r))

/-- Normalizing only the covector retains every original mask (`bg-Psi`). -/
theorem conicMaskSupport_normalize {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a : ℝ} {p : InputVariables n} (hp : p ∈ conicMaskSupport z₀ ηb r a) :
    scaleInput ‖p.2.2‖⁻¹ p ∈ unitInputSupport z₀ ηb r a :=
  ⟨hp.1, hp.2.1, hp.2.2.2⟩

/-- The compact section belongs to the original conic support (`bg-Psi`). -/
theorem unitInputSupport_subset_conicMaskSupport (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) (r a : ℝ) :
    unitInputSupport z₀ ηb r a ⊆ conicMaskSupport z₀ ηb r a := by
  intro p hp
  have hn : ‖p.2.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp.2.2.1
  exact ⟨hp.1, hp.2.1, norm_pos_iff.mp (by rw [hn]; norm_num),
    by simpa only [normalize_eq_self_of_norm_eq_one hn] using hp.2.2⟩

/-- The full original conic mask has a strict buffer inside the constructed
open input domain (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem conicMaskSupport_subset {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : a ≤ r) :
    conicMaskSupport z₀ ηb r a ⊆ symbolInputDomain z₀ ηb r (6 * a) := by
  intro p hp
  exact ⟨⟨closedBall_subset_ball (by linarith) hp.2.1.2,
    closedBall_subset_ball (by linarith) hp.1.1,
    closedBall_subset_ball (by linarith) hp.1.2⟩,
    closedBall_subset_ball (by linarith) hp.2.1.1, hp.2.2.1,
    closedBall_subset_ball (by linarith [(angularWidth_spec hηb hr).1]) hp.2.2.2.2⟩

/-- Literal primitive masks imply membership in the original conic support;
no high-frequency cutoff or transformed density is used (`bg-row`). -/
theorem primitive_masks_mem_conicMaskSupport {z₀ : Euclidean 3}
    {ηb : Euclidean (n - 1)} {r a : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a)
    {p : InputVariables n} (hη : p.2.2 ≠ 0)
    (hx : FixedCutoffs.physical ha 1 p.1.1 ≠ 0)
    (hy : FixedCutoffs.physical ha 1 p.1.2 ≠ 0)
    (hang : angularMask z₀ (normalize ηb) ha (angularWidth_spec hηb hr).1
      p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0) :
    p ∈ conicMaskSupport z₀ ηb r a := by
  obtain ⟨hs, hv, hθ⟩ := angularMask_nonzero z₀ (normalize ηb) ha
    (angularWidth_spec hηb hr).1 hang
  exact ⟨⟨FixedCutoffs.physical_tsupport_four ha 1 (subset_tsupport _ hx),
    FixedCutoffs.physical_tsupport_four ha 1 (subset_tsupport _ hy)⟩,
    ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩, hη,
    mem_sphere_zero_iff_norm.mpr (norm_normalize hη), ball_subset_closedBall hθ⟩

/-- Normalize the physical output frequency, retaining both positions and
the original spectator (`app:ch_background:eq:bg-Psi`). -/
def normalizeOutput (p : Variables n × Euclidean 2) : Variables n × Euclidean 2 :=
  (scaleFrequency ‖p.1.2.2‖⁻¹ p.1, p.2)

/-- Output normalization is continuous at every nonzero frequency (`bg-Psi`). -/
theorem normalizeOutput_continuousAt {p : Variables n × Euclidean 2}
    (hp : p.1.2.2 ≠ 0) : ContinuousAt normalizeOutput p :=
  (continuousAt_fst.fst.prodMk (continuousAt_fst.snd.fst.prodMk
    ((continuousAt_fst.snd.snd.norm.inv₀ (norm_ne_zero_iff.mpr hp)).smul
      continuousAt_fst.snd.snd))).prodMk continuousAt_snd

/-- Positive radial dilation does not change the normalized output (`bg-Psi`). -/
theorem normalizeOutput_scale {p : Variables n × Euclidean 2} {t : ℝ} (ht : 0 < t) :
    normalizeOutput (scaleFrequency t p.1, p.2) = normalizeOutput p := by
  simp only [normalizeOutput, scaleFrequency, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht, mul_inv_rev, smul_smul]
  congr 3
  rw [mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : a ≤ r)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr htrans in
/-- Actual transverse comparison excludes zero output on the open cone
(`app:ch_background:eq:bg-Psi`). -/
theorem transportGradient_ne_zero {p : InputVariables n}
    (hp : p ∈ symbolInputDomain z₀ ηb r (6 * a)) :
    transportAveragedGradient (transportPosition T Q) p ≠ 0 := by
  intro hz
  have he : adaptedTransportChart T Q (p.2.1.2, p.1.1, p.1.2) (p.2.1.1, p.2.2) = 0 := by
    change (adaptedSliceCoordinates T).equiv
      (transportAveragedGradient (transportPosition T Q) p) = 0
    rw [hz, map_zero]
  have hb := htrans _ hp.1 _ hp.2
  rw [he, Prod.snd_zero, zero_sub, norm_neg] at hb
  have hn := norm_pos_iff.mpr hp.2.2.1
  have hw := (angularWidth_spec hηb hr).2.1
  nlinarith

include hηb hr ha har htrans in
/-- The normalized image of the original unit support is compact. Smoothness
and nonzero frequency are proved on that support (`bg-full-complex-amplitude`). -/
theorem normalizedMaskImage_compact
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r))) :
    IsCompact ((normalizeOutput ∘ augmentedTransportGradient (transportPosition T Q)) ''
      unitInputSupport z₀ ηb r a) := by
  apply (unitInputSupport_compact z₀ ηb r a).image_of_continuousOn
  have hc := (transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).continuousOn
  have haug := (continuousOn_fst.fst.prodMk (continuousOn_fst.snd.prodMk hc)).prodMk
    continuousOn_snd.fst.snd
  intro p hp
  have hp' := conicMaskSupport_subset hηb hr ha har
    (unitInputSupport_subset_conicMaskSupport z₀ ηb r a hp)
  exact (normalizeOutput_continuousAt (transportGradient_ne_zero T Q hηb hr htrans hp')).comp_continuousWithinAt
    ((haug.mono (fun _ h ↦ conicMaskSupport_subset hηb hr ha har
      (unitInputSupport_subset_conicMaskSupport z₀ ηb r a h))) p hp)

include hηb hr ha har htrans in
/-- Punctured closure of the transported original support stays strictly
inside the actual conic image. This supplies the global supported-shell
constructor's `hpunctured` premise (`bg-full-complex-amplitude`). -/
theorem conicMaskImage_punctured_buffer
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r))) :
    closure (augmentedTransportGradient (transportPosition T Q) ''
      conicMaskSupport z₀ ηb r a) ∩ {p | p.1.2.2 ≠ 0} ⊆
      symbolDomain T Q z₀ ηb r (6 * a) := by
  rintro p ⟨hp, hpne⟩
  let K := (normalizeOutput ∘ augmentedTransportGradient (transportPosition T Q)) ''
    unitInputSupport z₀ ηb r a
  have hK : IsClosed K := (normalizedMaskImage_compact T Q hηb hr ha har htrans hf).isClosed
  have hmap : MapsTo normalizeOutput
      (augmentedTransportGradient (transportPosition T Q) '' conicMaskSupport z₀ ηb r a) K := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨scaleInput ‖q.2.2‖⁻¹ q, conicMaskSupport_normalize hq, ?_⟩
    dsimp only [Function.comp_apply]
    rw [augmentedTransportGradient_scaleInput]
    exact normalizeOutput_scale (inv_pos.mpr (norm_pos_iff.mpr hq.2.2.1))
  have hpK : normalizeOutput p ∈ K := hK.closure_eq ▸
    (normalizeOutput_continuousAt hpne).continuousWithinAt.mem_closure hp hmap
  obtain ⟨q, hq, he⟩ := hpK
  have hq' := conicMaskSupport_subset hηb hr ha har
    (unitInputSupport_subset_conicMaskSupport z₀ ηb r a hq)
  have hqΩ : augmentedTransportGradient (transportPosition T Q) q ∈
      symbolDomain T Q z₀ ηb r (6 * a) :=
    ⟨hq'.1, (q.2.1.1, q.2.2), hq'.2, rfl⟩
  have hnΩ : normalizeOutput (augmentedTransportGradient (transportPosition T Q) q) ∈
      symbolDomain T Q z₀ ηb r (6 * a) :=
    (symbolDomain_smul_iff T Q
      (inv_pos.mpr (norm_pos_iff.mpr (transportGradient_ne_zero T Q hηb hr htrans hq'))) _).mpr hqΩ
  rw [show normalizeOutput (augmentedTransportGradient (transportPosition T Q) q) =
    normalizeOutput p from he] at hnΩ
  exact (symbolDomain_smul_iff T Q (inv_pos.mpr (norm_pos_iff.mpr hpne)) p).mp hnΩ

end JanetCartan.ContinuumRow.CanonicalConic
