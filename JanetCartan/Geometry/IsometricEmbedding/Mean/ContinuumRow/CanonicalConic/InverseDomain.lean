module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.ConeRegularity

/-!
# The open conic image and a measurable inverse

The image is proved open using the actual buffered local inverse. Zero
extension outside that image supplies the global measurability needed by
`TransportKernel.ChartInputs`; on the image it retains the same smooth
inverse and the two homogeneity laws of `app:ch_background:eq:bg-Psi`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction.ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}

/-- Positive output dilation preserves the actual conic image, with the
physical positions and spectator unchanged (`app:ch_background:eq:bg-Psi`). -/
theorem supportedOutput_smul_iff {t : ℝ} (ht : 0 < t)
    (q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))) :
    (q.1, t • q.2) ∈ supportedOutput T Q z₀ ηb r a ↔
      q ∈ supportedOutput T Q z₀ ηb r a := by
  have hscale : ∀ w ∈ supportedOutput T Q z₀ ηb r a, ∀ s : ℝ, 0 < s →
      (w.1, s • w.2) ∈ supportedOutput T Q z₀ ηb r a := by
    intro w hw s hs
    obtain ⟨u, hu, he⟩ := hw.2
    exact ⟨hw.1, radialScale s u, radialScale_mem_supportedCone hu hs,
      (adaptedTransportChart_radialScale T Q _ _ _).trans (congrArg _ he)⟩
  constructor
  · intro h
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using
      hscale _ h t⁻¹ (inv_pos.mpr ht)
  · exact fun h ↦ hscale q h t ht

variable (hηb : ηb ≠ 0) (hr : 0 < r)
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
include hηb hr hInv htrans

/-- The conic image excludes zero transverse output, a proved consequence of
the actual transverse comparison (`app:ch_background:eq:bg-Psi`). -/
theorem supportedOutput_transverse_ne_zero
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ supportedOutput T Q z₀ ηb r a) : q.2.2 ≠ 0 := by
  obtain ⟨u, hu, he⟩ := hq.2
  let A := supportedAnnularData T Q z₀ hηb hr q.1 (hInv.injective q.1 hq.1)
    (htrans q.1 hq.1)
  rw [← he]
  exact norm_pos_iff.mp (A.transverse_norm_pos hu)

/-- The inverse lands in the original supported incidence/angular cone
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem localConicInverse_mem
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ supportedOutput T Q z₀ ηb r a) :
    localConicInverse T Q z₀ ηb r q ∈
      supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r) := by
  obtain ⟨u, hu, he⟩ := hq.2
  rw [show q = (q.1, adaptedTransportChart T Q q.1 u) from Prod.ext rfl he.symm,
    localConicInverse_map T Q hηb hr hInv htrans hq.1 hu]
  exact hu

/-- The original forward map is a right inverse on the constructed output
image (`app:ch_background:eq:bg-Psi`). -/
theorem map_localConicInverse
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ supportedOutput T Q z₀ ηb r a) :
    adaptedTransportChart T Q q.1 (localConicInverse T Q z₀ ηb r q) = q.2 := by
  obtain ⟨u, hu, he⟩ := hq.2
  have heq : localConicInverse T Q z₀ ηb r q = u := by
    rw [show q = (q.1, adaptedTransportChart T Q q.1 u) from Prod.ext rfl he.symm]
    exact localConicInverse_map T Q hηb hr hInv htrans hq.1 hu
  exact heq ▸ he

/-- Degree zero in incidence and degree one in the covector for the SAME
joint inverse (`app:ch_background:eq:bg-Psi`). -/
theorem localConicInverse_smul
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ supportedOutput T Q z₀ ηb r a) {t : ℝ} (ht : 0 < t) :
    localConicInverse T Q z₀ ηb r (q.1, t • q.2) =
      radialScale t (localConicInverse T Q z₀ ηb r q) := by
  obtain ⟨u, hu, he⟩ := hq.2
  have hleft := localConicInverse_map T Q hηb hr hInv htrans hq.1
    (radialScale_mem_supportedCone hu ht)
  rw [adaptedTransportChart_radialScale, he] at hleft
  rw [hleft]
  congr 1
  rw [show q = (q.1, adaptedTransportChart T Q q.1 u) from Prod.ext rfl he.symm]
  exact (localConicInverse_map T Q hηb hr hInv htrans hq.1 hu).symm

/-- Ambient smoothness of the explicit inverse at every output point follows
from the actual buffered annular range (`app:ch_background:eq:bg-Psi`). -/
theorem localConicInverse_contDiffAt (hV : IsOpen V) (hLV : L ⊆ V)
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ supportedOutput T Q z₀ ηb r a) :
    ContDiffAt ℝ ∞ (localConicInverse T Q z₀ ηb r) q := by
  have hne := supportedOutput_transverse_ne_zero T Q hηb hr hInv htrans hq
  have hn : ContDiffAt ℝ ∞ (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ ‖q.2.2‖) q := contDiffAt_snd.snd.norm ℝ hne
  have hi := hn.inv (norm_ne_zero_iff.mpr hne)
  have harg : ContDiffAt ℝ ∞ (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ (q.1, (‖ηb‖ / ‖q.2.2‖) • q.2)) q :=
    contDiffAt_fst.prodMk ((contDiffAt_const.mul hi).smul contDiffAt_snd)
  have hg := (hInv.smooth.contDiffAt (((physicalParameterSet_open z₀ a).prod hV).mem_nhds
    (normalizedOutput_mem_inverseRange T Q hηb hr hInv htrans hLV hq))).comp q harg
  exact hg.fst.prodMk ((hn.div_const ‖ηb‖).smul hg.snd)

/-- Openness of the actual joint conic image is a conclusion of the buffered
inverse construction (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem supportedOutput_open (hV : IsOpen V) (hLV : L ⊆ V) :
    IsOpen (supportedOutput T Q z₀ ηb r a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hne := supportedOutput_transverse_ne_zero T Q hηb hr hInv htrans hq
  have hn : ContinuousAt (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ ‖q.2.2‖) q := continuous_snd.snd.norm.continuousAt
  have harg : ContinuousAt (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ (‖ηb‖ / ‖q.2.2‖) • q.2) q :=
    (continuousAt_const.div hn (norm_ne_zero_iff.mpr hne)).smul continuous_snd.continuousAt
  have hpre := harg.preimage_mem_nhds (hV.mem_nhds
    (normalizedOutput_mem_inverseRange T Q hηb hr hInv htrans hLV hq).2)
  have hp := continuous_fst.continuousAt.preimage_mem_nhds
    ((physicalParameterSet_open z₀ a).mem_nhds hq.1)
  have hnonzero := (isOpen_ne_fun continuous_snd.snd continuous_const).mem_nhds hne
  have hu := ((localConicInverse_contDiffAt T Q hηb hr hInv htrans hV hLV hq).continuousAt).preimage_mem_nhds ((supportedCone_open z₀ (NormedSpace.normalize ηb) r
      (angularWidth ηb r)).mem_nhds (localConicInverse_mem T Q hηb hr hInv htrans hq))
  filter_upwards [hp, hnonzero, hpre, hu] with w hwp hwn hwV hwu
  refine ⟨hwp, localConicInverse T Q z₀ ηb r w, hwu, ?_⟩
  unfold localConicInverse
  rw [adaptedTransportChart_radialScale, hInv.right_inv w.1 hwp _ hwV, smul_smul,
    div_mul_div_cancel₀ (norm_ne_zero_iff.mpr hηb),
    div_self (norm_ne_zero_iff.mpr hwn), one_smul]

omit hηb hr hInv htrans in
/-- A globally defined measurable choice, equal to the actual smooth inverse
on its conic image. The zero value outside the image does not alter any kernel
substitution (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def conicInverse (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    ((Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))) →
      ℝ × Euclidean (n - 1) :=
  (supportedOutput T Q z₀ ηb r a).indicator (localConicInverse T Q z₀ ηb r)

omit hηb hr hInv htrans in
/-- The measurable extension retains the actual inverse on the image
(`app:ch_background:eq:bg-Psi`). -/
theorem conicInverse_eq
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ supportedOutput T Q z₀ ηb r a) :
    conicInverse T Q z₀ ηb r a q = localConicInverse T Q z₀ ηb r q :=
  indicator_of_mem hq _

/-- Global measurability required for the literal Lebesgue substitution in
`TransportKernel.ChartInputs` (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem conicInverse_measurable (hV : IsOpen V) (hLV : L ⊆ V) :
    Measurable (conicInverse T Q z₀ ηb r a) := by
  classical
  exact (localConicInverse_smooth T Q hηb hr hInv htrans hLV).continuousOn.measurable_piecewise
    continuousOn_const (supportedOutput_open T Q hηb hr hInv htrans hV hLV).measurableSet

/-- Zero extension preserves joint smoothness on the actual open image
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem conicInverse_smooth (hLV : L ⊆ V) :
    ContDiffOn ℝ ∞ (conicInverse T Q z₀ ηb r a) (supportedOutput T Q z₀ ηb r a) :=
  (localConicInverse_smooth T Q hηb hr hInv htrans hLV).congr
    (fun _ hq ↦ conicInverse_eq T Q hq)

end JanetCartan.ContinuumRow.CanonicalConic
