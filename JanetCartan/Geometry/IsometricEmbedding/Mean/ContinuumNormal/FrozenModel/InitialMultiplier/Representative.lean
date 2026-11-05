module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.InitialMultiplier.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.MultiplierComparison.InitialData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Tests

/-!
# A bounded smooth representative on the actual angular labels

A fixed bump equals one on the ENTIRE compact carrier support and vanishes
inside the existing open buffer. Multiplying by it extends the locally smooth
initial footpoint weight without assuming a global smooth initial scalar.
The bound depends only on a local C⁰ budget fixed before the initial data.
Consumer: the input L² multiplier for `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
open FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic

/-- A fixed label cutoff with plateau on the original compact angular
support (`app:ch_background:defn:bg-row`). It is independent of the initial
scalar, the flow and the measurement radius. -/
def labelCutoff (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a) :
    ContDiffBump ((z₀ 0), spectatorCenter z₀) where
  rIn := a / 2
  rOut := a
  rIn_pos := half_pos ha
  rIn_lt_rOut := by linarith

/-- The whole retained carrier support lies in the plateau
(`app:ch_background:defn:bg-row`). -/
theorem labelCutoff_eq_one (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a)
    {z : CarrierParameter} (hz : z ∈ carrierSupport z₀ (r := a)) :
    labelCutoff z₀ ha z = 1 := by
  apply (labelCutoff z₀ ha).one_of_mem_closedBall
  change z ∈ closedBall ((z₀ 0), spectatorCenter z₀) (a / 2)
  simpa only [carrierSupport, closedBall_prod_same] using hz

/-- The cutoff's closed support is inside the precise open label buffer
used by `canonicalFrozenCarrier_kernel_inputs`. The inequality `6*a ≤ 3*r`
is the existing frozen geometry output (`new:lem:scaling`). -/
theorem labelCutoff_tsupport_subset (z₀ : Euclidean 3) {a r : ℝ}
    (ha : 0 < a) (har : 6 * a ≤ 3 * r) :
    tsupport (labelCutoff z₀ ha) ⊆
      ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a) := by
  rw [(labelCutoff z₀ ha).tsupport_eq]
  intro z hz
  change z ∈ closedBall ((z₀ 0), spectatorCenter z₀) a at hz
  have hp : z ∈ closedBall (z₀ 0) a ×ˢ closedBall (spectatorCenter z₀) a := by
    simpa only [closedBall_prod_same] using hz
  exact ⟨closedBall_subset_ball (by linarith) hp.1,
    closedBall_subset_ball (by linarith) hp.2⟩

/-- Construct a smooth, compactly supported, nonnegative representative of
`labelWeight` from local initial smoothness, the actual flow's smoothness and
range, and a fixed local C⁰ budget. No global initial regularity or bounded
multiplier is assumed. `ActualAmplitude.exists_projected_local_positive_amplitude`
produces the flow smoothness/range on its retained tube; matching that tube to
this label buffer is the parent's explicit `hseed` obligation. The SAME buffer
is used by the existing frozen kernel and symbol regularity producers.
Source: `new:lem:scaling`, `app:ch_background:prop:bg-frame`. -/
theorem exists_bounded_smooth_labelWeight {n : ℕ}
    (z₀ : Euclidean 3) {a r : ℝ} (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (B : ℝ) (hB : 0 ≤ B)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hi : ContDiffOn ℝ ∞ initial D) (hY : ContDiffOn ℝ ∞ Y Dflow)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D) (hbound : ∀ q ∈ D, ‖initial q‖ ≤ B) :
    ∃ b : CarrierParameter → ℝ,
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∀ z, 0 ≤ b z) ∧ (∀ z, ‖b z‖ ≤ B ^ 2) ∧
      EqOn b (labelWeight Y initial) (carrierSupport z₀ (r := a)) := by
  let χ := labelCutoff z₀ ha
  let Z := ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)
  have hZ : IsOpen Z := isOpen_ball.prod isOpen_ball
  have hs : tsupport χ ⊆ Z := labelCutoff_tsupport_subset z₀ ha har
  have hy : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦ Y (0, (0, parameter z))) Z :=
    hY.comp (contDiffOn_const.prodMk (contDiffOn_const.prodMk parameter.contDiff.contDiffOn))
      hseed
  have hw : ContDiffOn ℝ ∞ (labelWeight Y initial) Z :=
    (hi.comp hy (hYrange.comp hseed)).pow 2
  refine ⟨fun z ↦ χ z * labelWeight Y initial z, ?_, χ.hasCompactSupport.mul_right,
    fun z ↦ mul_nonneg χ.nonneg (labelWeight_nonneg Y initial z), ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact χ.contDiffAt.mul (hw.contDiffAt (hZ.mem_nhds (hs hz)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with q hq
      simp only [hq, Pi.zero_apply, zero_mul]
  · intro z
    change ‖χ z * labelWeight Y initial z‖ ≤ B ^ 2
    by_cases hz : z ∈ tsupport χ
    · have hnorm := hbound _ (hYrange (hseed (hs hz)))
      have hwbound : ‖labelWeight Y initial z‖ ≤ B ^ 2 := by
        simpa only [labelWeight, norm_pow] using
          (sq_le_sq₀ (norm_nonneg _) hB).mpr hnorm
      calc
        ‖χ z * labelWeight Y initial z‖ = χ z * ‖labelWeight Y initial z‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
        _ ≤ 1 * B ^ 2 := mul_le_mul χ.le_one hwbound (norm_nonneg _) zero_le_one
        _ = B ^ 2 := one_mul _
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, norm_zero]
      exact sq_nonneg B
  · intro z hz
    change χ z * labelWeight Y initial z = labelWeight Y initial z
    rw [show χ z = 1 from labelCutoff_eq_one z₀ ha hz, one_mul]

/-- The original forward/inverse flow identities compute the time-zero
footpoint. These identities are outputs of
`ActualAmplitude.exists_projected_local_positive_amplitude`; the initial
section containment is deliberately explicit (`new:lem:scaling`). -/
theorem labelWeight_eq_initial_of_flow {n : ℕ}
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {I : Set ℝ} {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (h0 : (0 : ℝ) ∈ I) (hΦ0 : ∀ p ∈ L, Φ (0, p) = p)
    (hYΦ : ∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p)
    {z : CarrierParameter} (hz : ((0 : Euclidean (n - 1)), parameter z) ∈ L) :
    labelWeight Y initial z = initial (0, parameter z) ^ 2 := by
  have h := hYΦ _ hz 0 h0
  rw [hΦ0 _ hz] at h
  simp only [labelWeight, h]

/-- The full original density interval, without smallness in higher
 derivatives, supplies local smoothness, a uniform C⁰ budget and a positive
lower bound for `sqrt (1+v)`. Thus the fixed-low class of
`app:ch_background:prop:bg-frame` is retained, rather than replaced by an
all-derivative smallness assumption. The `C^{d₀}` bound belongs to subsequent
current-family variation and is not needed for this frozen multiplication. -/
theorem sqrt_initial_properties_of_density_range {n : ℕ}
    {v : Euclidean (n - 1) × Euclidean 3 → ℝ}
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    (hv : ContDiffOn ℝ ∞ v D)
    (hden : ∀ q ∈ D, (1 / 2 : ℝ) ≤ 1 + v q ∧ 1 + v q ≤ 3 / 2) :
    ContDiffOn ℝ ∞ (fun q ↦ Real.sqrt (1 + v q)) D ∧
      (∀ q ∈ D, (1 / 2 : ℝ) ≤ Real.sqrt (1 + v q)) ∧
      (∀ q ∈ D, ‖Real.sqrt (1 + v q)‖ ≤ 2) := by
  refine ⟨(contDiffOn_const.add hv).sqrt (fun q hq ↦ by linarith [(hden q hq).1]),
    ?_, ?_⟩
  · intro q hq
    apply Real.le_sqrt_of_sq_le
    linarith [(hden q hq).1]
  · intro q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by linarith [(hden q hq).2]⟩

/-- Multiplication by the smooth representative preserves the ORIGINAL
compact smooth initial domain. This is the test input used to identify the
composition of the unit carrier with the bounded multiplier
(`app:ch_background:eq:bg-T`). -/
def multiplyInitialTest {n : ℕ} (b : CarrierParameter → ℝ) (hb : ContDiff ℝ ∞ b)
    (f : carrierInitialTestSpace n) : carrierInitialTestSpace n :=
  ⟨fun u ↦ (b u.1 : ℂ) * f.val u,
    (Complex.ofRealCLM.contDiff.comp (hb.comp contDiff_fst)).mul f.property.1,
    f.property.2.mul_left⟩

/-- For every scalar in the original density interval, construct the
bounded smooth label representative and prove its lower bound on the entire
retained angular support. Both bounds are fixed before `v`; no derivative
smallness is needed for this frozen step (`app:ch_background:prop:bg-frame`).
The sole geometric containment is exactly the `hseed` of the existing frozen
kernel/regularity producers. -/
theorem exists_bounded_smooth_sqrt_labelWeight {n : ℕ}
    (z₀ : Euclidean 3) {a r : ℝ} (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hv : ContDiffOn ℝ ∞ v D)
    (hden : ∀ q ∈ D, (1 / 2 : ℝ) ≤ 1 + v q ∧ 1 + v q ≤ 3 / 2)
    (hY : ContDiffOn ℝ ∞ Y Dflow)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D) :
    ∃ b : CarrierParameter → ℝ,
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∀ z, 0 ≤ b z) ∧ (∀ z, ‖b z‖ ≤ 4) ∧
      EqOn b (labelWeight Y (fun q ↦ Real.sqrt (1 + v q)))
        (carrierSupport z₀ (r := a)) ∧
      ∀ z ∈ carrierSupport z₀ (r := a), (1 / 4 : ℝ) ≤ b z := by
  obtain ⟨hi, hlo, hup⟩ := sqrt_initial_properties_of_density_range hv hden
  obtain ⟨b, hb, hc, hn, hbound, he⟩ := exists_bounded_smooth_labelWeight z₀ ha har
    2 (by norm_num) Y (fun q ↦ Real.sqrt (1 + v q)) hi hY hseed hYrange hup
  refine ⟨b, hb, hc, hn, by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hbound, he, ?_⟩
  intro z hz
  have hZ : z ∈ ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a) :=
    ⟨closedBall_subset_ball (by linarith) hz.1,
      closedBall_subset_ball (by linarith) hz.2⟩
  have h := hlo _ (hYrange (hseed hZ))
  rw [he hz]
  dsimp only [labelWeight]
  nlinarith

end JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
