module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AnnularData

/-!
# Joint regularity of the actual supported conic chart

The literal local inverse is evaluated at the frozen covector magnitude.
This connects the annular construction to the same physical carrier, without
choosing a new inverse or assuming regularity on the cone. The inputs below
are the checked outputs of `exists_actual_local_charts` and
`exists_supported_transverse_threshold`; `exists_actual_conic_inverse`
instantiates them from the primitive projected-stress assumptions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction.ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Joint image of the supported cone with the physical positions and spectator
retained. This is the inverse domain in `app:ch_background:eq:bg-Psi`. -/
def supportedOutput (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Set ((Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))) :=
  {q | q.1 ∈ physicalParameterSet z₀ a ∧ q.2 ∈ adaptedTransportChart T Q q.1 ''
    supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)}

/-- Explicit conic continuation of the retained local inverse. The normalization
uses the frozen transverse magnitude, preserving the local chart's center
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def localConicInverse (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r : ℝ)
    (q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))) :
    ℝ × Euclidean (n - 1) :=
  radialScale (‖q.2.2‖ / ‖ηb‖)
    (phaseChartInverse (adaptedTransportChart T Q) (dataSet z₀ ηb (2 * r))
      q.1 ((‖ηb‖ / ‖q.2.2‖) • q.2))

variable {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}

/-- Normalizing an input by its own covector norm lands in the actual inner
chart, with the incidence variable fixed (`app:ch_background:eq:bg-Psi`). -/
theorem normalizedInput_mem_dataSet (hηb : ηb ≠ 0) (hr : 0 < r)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) :
    radialScale (‖ηb‖ / ‖u.2‖) u ∈ dataSet z₀ ηb r := by
  have hη := norm_pos_iff.mpr hu.2.1
  have hn : ‖(radialScale ‖u.2‖⁻¹ u).2‖ = 1 := by
    simp [radialScale, norm_smul, hη.ne']
  have h := annular_dilation_mem_dataSet z₀ hηb (angularWidth_spec hηb hr).2.2.1.le
    (radialScale_mem_supportedCone hu (inv_pos.mpr hη))
    (by rw [hn]; linarith [(angularWidth_spec hηb hr).1])
    (by rw [hn]; linarith [(angularWidth_spec hηb hr).1])
  simpa only [radialScale_mul, div_eq_mul_inv] using h

/-- The actual forward chart is jointly smooth on the whole supported cone.
Its local smoothness is supplied by the projected-stress chart construction;
positive covector normalization proves the extension
(`app:ch_background:eq:bg-Psi`). -/
theorem adaptedTransportChart_smooth_on_cone (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r))) :
    ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ
        supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) := by
  let D := physicalParameterSet (n := n) z₀ a ×ˢ
    supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)
  have hn : ContDiffOn ℝ ∞ (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ ‖q.2.2‖) D :=
    contDiffOn_snd.snd.norm ℝ (fun _ h ↦ h.2.2.1)
  have hi := hn.inv (fun _ h ↦ norm_ne_zero_iff.mpr h.2.2.1)
  have harg : ContDiffOn ℝ ∞ (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ (q.1, radialScale (‖ηb‖ / ‖q.2.2‖) q.2)) D :=
    contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk
      ((contDiffOn_const.mul hi).smul contDiffOn_snd.snd))
  have hcomp := hf.comp harg (fun q hq ↦
    ⟨hq.1, prod_mono (ball_subset_ball (by linarith : r ≤ 3 * r))
      (ball_subset_ball (by linarith : r ≤ 3 * r))
        (normalizedInput_mem_dataSet hηb hr hq.2)⟩)
  apply ((hn.div_const ‖ηb‖).smul hcomp).congr
  intro q hq
  change adaptedTransportChart T Q q.1 q.2 =
    (‖q.2.2‖ / ‖ηb‖) • adaptedTransportChart T Q q.1
      (radialScale (‖ηb‖ / ‖q.2.2‖) q.2)
  rw [adaptedTransportChart_radialScale, smul_smul]
  have hη := norm_ne_zero_iff.mpr hq.2.2.1
  have hμ := norm_ne_zero_iff.mpr hηb
  rw [div_mul_div_cancel₀ hμ, div_self hη, one_smul]

variable (hηb : ηb ≠ 0) (hr : 0 < r)
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr hInv htrans

/-- Transverse output normalization lands in the same inner data chart.
This is the missing normalization containment for the smooth inverse in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem normalizedOutputInput_mem_dataSet
    {p : Euclidean 2 × Euclidean n × Euclidean n} (hp : p ∈ physicalParameterSet z₀ a)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) :
    radialScale (‖ηb‖ / ‖(adaptedTransportChart T Q p u).2‖) u ∈ dataSet z₀ ηb r := by
  let A := supportedAnnularData T Q z₀ hηb hr p (hInv.injective p hp) (htrans p hp)
  have hh := A.normalize_mem_annulus hu
  have h := annular_dilation_mem_dataSet z₀ hηb (angularWidth_spec hηb hr).2.2.1.le
    hh.1 hh.2.1 hh.2.2
  simpa only [radialScale_mul, div_eq_mul_inv, A, supportedAnnularData] using h

/-- The explicit continuation is a left inverse of the original averaged
transport gradient (`app:ch_background:eq:bg-Psi`). -/
theorem localConicInverse_map
    {p : Euclidean 2 × Euclidean n × Euclidean n} (hp : p ∈ physicalParameterSet z₀ a)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) :
    localConicInverse T Q z₀ ηb r (p, adaptedTransportChart T Q p u) = u := by
  let A := supportedAnnularData T Q z₀ hηb hr p (hInv.injective p hp) (htrans p hp)
  have hn : 0 < ‖(adaptedTransportChart T Q p u).2‖ := A.transverse_norm_pos hu
  have hw := normalizedOutputInput_mem_dataSet T Q hηb hr hInv htrans hp hu
  have hw' : radialScale (‖ηb‖ / ‖(adaptedTransportChart T Q p u).2‖) u ∈
      dataSet z₀ ηb (2 * r) :=
    prod_mono (ball_subset_ball (by linarith)) (ball_subset_ball (by linarith)) hw
  unfold localConicInverse
  rw [← adaptedTransportChart_radialScale T Q p u, hInv.left_inv p hp _ hw', radialScale_mul]
  rw [div_mul_div_cancel₀ (norm_ne_zero_iff.mpr hηb), div_self hn.ne', radialScale_one]

/-- The normalized output lies in the actual common buffered inverse range,
not an assumed conic chart (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalizedOutput_mem_inverseRange (hLV : L ⊆ V)
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ supportedOutput T Q z₀ ηb r a) :
    (q.1, (‖ηb‖ / ‖q.2.2‖) • q.2) ∈ physicalParameterSet z₀ a ×ˢ V := by
  refine ⟨hq.1, ?_⟩
  obtain ⟨u, hu, he⟩ := hq.2
  have hw := normalizedOutputInput_mem_dataSet T Q hηb hr hInv htrans hq.1 hu
  apply hLV
  apply hInv.image_subset q.1 hq.1
  refine ⟨radialScale (‖ηb‖ / ‖q.2.2‖) u, ?_, ?_⟩
  · rw [← he]
    exact prod_mono ball_subset_closedBall ball_subset_closedBall hw
  · exact (adaptedTransportChart_radialScale T Q _ _ _).trans (congrArg _ he)

/-- Joint smoothness of the SAME inverse in both physical positions,
spectator and conic output (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem localConicInverse_smooth (hLV : L ⊆ V) :
    ContDiffOn ℝ ∞ (localConicInverse T Q z₀ ηb r) (supportedOutput T Q z₀ ηb r a) := by
  have hne : ∀ q ∈ supportedOutput T Q z₀ ηb r a, q.2.2 ≠ 0 := by
    intro q hq
    obtain ⟨u, hu, he⟩ := hq.2
    let A := supportedAnnularData T Q z₀ hηb hr q.1 (hInv.injective q.1 hq.1)
      (htrans q.1 hq.1)
    rw [← he]
    exact norm_pos_iff.mp (A.transverse_norm_pos hu)
  have hn : ContDiffOn ℝ ∞ (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ ‖q.2.2‖) (supportedOutput T Q z₀ ηb r a) :=
    contDiffOn_snd.snd.norm ℝ hne
  have hi := hn.inv (fun q hq ↦ norm_ne_zero_iff.mpr (hne q hq))
  have harg : ContDiffOn ℝ ∞ (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ (q.1, (‖ηb‖ / ‖q.2.2‖) • q.2))
      (supportedOutput T Q z₀ ηb r a) :=
    contDiffOn_fst.prodMk ((contDiffOn_const.mul hi).smul contDiffOn_snd)
  have hg := hInv.smooth.comp harg
    (fun _ hq ↦ normalizedOutput_mem_inverseRange T Q hηb hr hInv htrans hLV hq)
  exact hg.fst.prodMk ((hn.div_const ‖ηb‖).smul hg.snd)

end JanetCartan.ContinuumRow.CanonicalConic
