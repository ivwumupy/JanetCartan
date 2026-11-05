module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.PuncturedSupport

/-!
# Smaller original masks inside the fixed conic chart

The mask radii can shrink independently of the already constructed inverse
domain. Their radial section at the frozen input magnitude fits any prescribed
neighborhood. The masks themselves remain `angularMask` and
`FixedCutoffs.physical`, with the positive plateaus proved in `Masks`.
Consumer: the supported normalized-shell premise of the global carrier
constructor (`app:ch_background:eq:bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff
namespace JanetCartan.ContinuumRow.CanonicalConic
open FullPhaseCharts.ActualComparison ContinuumNormalReduction.TransportSymbol

variable {n : ℕ}

/-- Shrinking the annular mask parameter shrinks its angular width, without
changing the selected direction (`app:ch_background:defn:bg-row`). -/
theorem angularWidth_mono (ηb : Euclidean (n - 1)) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    angularWidth ηb r₁ ≤ angularWidth ηb r₂ :=
  min_le_min_left _ (div_le_div_of_nonneg_right hr (by positivity))

/-- The closed direction masks refine monotonically (`bg-row`). -/
theorem closedDirections_mono (ηb : Euclidean (n - 1)) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    closedDirections ηb r₁ ⊆ closedDirections ηb r₂ :=
  inter_subset_inter_right _ (closedBall_subset_closedBall
    (div_le_div_of_nonneg_right (angularWidth_mono ηb hr) (by norm_num)))

/-- Smaller original masks retain the original larger conic support. In
particular its punctured image buffer is inherited by closure monotonicity
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem conicMaskSupport_mono (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    {r₁ r₂ a₁ a₂ : ℝ} (hr : r₁ ≤ r₂) (ha : a₁ ≤ a₂) :
    conicMaskSupport z₀ ηb r₁ a₁ ⊆ conicMaskSupport z₀ ηb r₂ a₂ := by
  intro p hp
  exact ⟨⟨closedBall_subset_closedBall (by linarith) hp.1.1,
    closedBall_subset_closedBall (by linarith) hp.1.2⟩,
    ⟨closedBall_subset_closedBall (by linarith) hp.2.1.1,
      closedBall_subset_closedBall (by linarith) hp.2.1.2⟩,
    hp.2.2.1, closedDirections_mono ηb hr hp.2.2.2⟩

/-- The representative at the frozen input magnitude lies arbitrarily near
the same augmented center when the original masks shrink (`bg-Psi`). -/
theorem conicMaskSupport_radial_section_mem_ball {z₀ : Euclidean 3}
    {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0) {r a d : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hphysical : 4 * a < d) (hradial : r ≤ d)
    {p : InputVariables n} (hp : p ∈ conicMaskSupport z₀ ηb r a) :
    scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈
      ball (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) d := by
  have he : (‖ηb‖ / ‖p.2.2‖) • p.2.2 = ‖ηb‖ • normalize p.2.2 := by
    simp only [NormedSpace.normalize, div_eq_mul_inv, smul_smul]
  have hdist : dist ((‖ηb‖ / ‖p.2.2‖) • p.2.2) ηb < d := by
    rw [he]
    conv_lhs => arg 2; rw [← norm_smul_normalize ηb]
    rw [dist_smul₀, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    have hθ := mem_closedBall.mp hp.2.2.2.2
    have hw := (angularWidth_spec hηb hr).2.2.1
    have hpos := (angularWidth_spec hηb hr).1
    have hn := norm_pos_iff.mpr hηb
    have hmul := mul_le_mul_of_nonneg_left hθ hn.le
    nlinarith
  simp only [mem_ball, scaleInput, Prod.dist_eq, max_lt_iff]
  exact ⟨⟨(mem_closedBall.mp hp.1.1).trans_lt hphysical,
    (mem_closedBall.mp hp.1.2).trans_lt hphysical⟩,
    ⟨(mem_closedBall.mp hp.2.1.1).trans_lt (by linarith),
      (mem_closedBall.mp hp.2.1.2).trans_lt (by linarith)⟩, hdist⟩

/-- Choose smaller positive physical/carrier and angular mask radii before
any current immersion. They retain all plateau assertions of `angularMask_one`
and fit a prescribed input ball (`app:ch_background:defn:bg-row`). -/
theorem exists_refined_mask_radii {r a d : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hd : 0 < d) :
    ∃ r' > (0 : ℝ), r' ≤ r ∧ r' ≤ d ∧
      ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ r' ∧ 4 * a' < d := by
  let r' := min r d / 2
  have hr' : 0 < r' := by dsimp [r']; positivity
  have hrr : r' ≤ r := by dsimp [r']; linarith [min_le_left r d]
  have hrd : r' ≤ d := by dsimp [r']; linarith [min_le_right r d]
  let a' := min a r' / 8
  have ha' : 0 < a' := by dsimp [a']; positivity
  exact ⟨r', hr', hrr, hrd, a', ha',
    by dsimp [a']; linarith [min_le_left a r'],
    by dsimp [a']; linarith [min_le_right a r'],
    by dsimp [a']; linarith [min_le_right a r']⟩

/-- Normalization onto a fixed output sphere, retaining both original
positions and the spectator (`app:ch_background:eq:bg-Psi`). -/
def normalizeOutputRadius (ℓ : ℝ) (p : Variables n × Euclidean 2) :
    Variables n × Euclidean 2 :=
  (scaleFrequency (ℓ / ‖p.1.2.2‖) p.1, p.2)

/-- Fixed-radius output normalization is continuous off zero (`bg-Psi`). -/
theorem normalizeOutputRadius_continuousAt (ℓ : ℝ) {p : Variables n × Euclidean 2}
    (hp : p.1.2.2 ≠ 0) : ContinuousAt (normalizeOutputRadius ℓ) p :=
  (continuousAt_fst.fst.prodMk (continuousAt_fst.snd.fst.prodMk
    ((continuousAt_const.div continuousAt_fst.snd.snd.norm (norm_ne_zero_iff.mpr hp)).smul
      continuousAt_fst.snd.snd))).prodMk continuousAt_snd

/-- Positive scaling preserves the fixed-radius normalized output (`bg-Psi`). -/
theorem normalizeOutputRadius_scale (ℓ : ℝ) (p : Variables n × Euclidean 2)
    {t : ℝ} (ht : 0 < t) :
    normalizeOutputRadius ℓ (scaleFrequency t p.1, p.2) = normalizeOutputRadius ℓ p := by
  simp only [normalizeOutputRadius, scaleFrequency, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht, div_eq_mul_inv, mul_inv_rev, smul_smul]
  congr 3
  rw [mul_assoc, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

/-- A point already on the selected sphere is fixed by normalization
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalizeOutputRadius_eq_self {ℓ : ℝ} (hℓ : 0 < ℓ)
    {p : Variables n × Euclidean 2} (hp : ‖p.1.2.2‖ = ℓ) :
    normalizeOutputRadius ℓ p = p := by
  simp only [normalizeOutputRadius, hp, div_self hℓ.ne', scaleFrequency, one_smul]

/-- The normalized support estimate passes to the closure of the transported
original masks. This is exactly the supported shell premise, and does not
assert containment of the entire conic chart (`bg-full-complex-amplitude`). -/
theorem supported_shell_of_normalized_image {ℓ τ : ℝ} (hℓ : 0 < ℓ)
    (F : InputVariables n → Variables n × Euclidean 2) (Z : Set (InputVariables n))
    (b : Variables n × Euclidean 2)
    (hs : ∀ p ∈ Z, normalizeOutputRadius ℓ (F p) ∈ closedBall b τ) :
    ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (F '' Z) → (x, v) ∈ closedBall b τ := by
  intro x hx v hv
  have hne : x.2.2 ≠ 0 := norm_pos_iff.mp (by rw [hx]; exact hℓ)
  have hm : MapsTo (normalizeOutputRadius ℓ) (F '' Z) (closedBall b τ) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hs p hp
  have hc : normalizeOutputRadius ℓ (x, v) ∈ closure (closedBall b τ) :=
    (normalizeOutputRadius_continuousAt ℓ (p := (x, v)) hne).continuousWithinAt.mem_closure hv hm
  have hc' : normalizeOutputRadius ℓ (x, v) ∈ closedBall b τ :=
    (isClosed_closedBall : IsClosed (closedBall b τ)).closure_eq ▸ hc
  simpa only [normalizeOutputRadius, hx, div_self hℓ.ne', scaleFrequency, one_smul] using hc'

/-- The fixed sphere satisfies the supported constructor's unrestricted
normalization input, with no restriction on either physical position
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem scaleFrequency_mem_fixed_sphere {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : Variables n) (hp : ℓ ≤ ‖p.2.2‖) :
    ‖(scaleFrequency (ℓ / ‖p.2.2‖) p).2.2‖ = ℓ := by
  have hn : 0 < ‖p.2.2‖ := hℓ.trans_le hp
  simp only [scaleFrequency, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hℓ hn), div_mul_cancel₀ _ hn.ne']

end JanetCartan.ContinuumRow.CanonicalConic
