module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.FullBandMean
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# A smooth positive majorant of the original sampling mean

For the mask-free proof following `app:ch_waves:eq:sampling-operator-bounds`,
choose a smooth angular cutoff from the original patch and an open buffered
chart. Its support radius is fixed before frequencies, bands, and colors.
The original weight is retained on the left of the normal comparison; only
the dominating full-band operators use the smooth cutoff. No smoothness of
the square root of the original weight is used.

The primitive input `tsupport ψ ⊆ U`, with `U` open, must be supplied by
RawPrimary's actual fixed cutoffs on the same angular chart. This module
constructs the cutoff and proves the comparison from that input. The parent
kernel-identification task still owns that instantiation and the normalized
full-phase matching of these very operators.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition SeparatedSampling BackgroundQuadrature ContinuumRow

/-- Construct the smooth angular majorant for
`app:ch_waves:eq:sampling-operator-bounds`. The only chart input is an open
neighborhood of the original closed support, supplied by RawPrimary's fixed
cutoffs. Neither the cutoff nor its support radius depends on any kernel,
frequency, band, or color. The plateau holds on a neighborhood of `tsupport ψ`. -/
theorem exists_smooth_patch_majorant {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) {U : Set Point} (hU : IsOpen U)
    (hψU : tsupport ψ ⊆ U) :
    ∃ (χ : Point → ℝ) (R : ℝ), 0 < R ∧ ContDiff ℝ ∞ χ ∧
      HasCompactSupport χ ∧ PatchBounds χ R 1 ∧ tsupport χ ⊆ U ∧
      tsupport ψ ⊆ interior {z | χ z = 1} := by
  have hψc : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Point) B)
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hψ.radius_nonneg).mpr
      (fun i ↦ by simpa only [Real.norm_eq_abs] using hψ.support z hz i)
  obtain ⟨χ, hχ, hrange, hc, hs, hp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hψc.isCompact hU hψU
  obtain ⟨R, hR, hbound⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  refine ⟨χ, R, hR, hχ, hc, ⟨hR.le, fun z ↦ (hrange z).1,
    fun z ↦ (hrange z).2, ?_⟩, hs, hp⟩
  intro z hz i
  calc
    |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
    _ ≤ R := hbound z (subset_tsupport χ hz)

/-- Squaring the constructed unit cutoff preserves compact patch bounds.
This is the weight used by the full-band normal identity in
`app:ch_waves:eq:sampling-prefix-normal`. -/
theorem patchBounds_cutoff_sq {χ : Point → ℝ} {R : ℝ}
    (hχ : PatchBounds χ R 1) : PatchBounds (fun z ↦ χ z ^ 2) R 1 where
  radius_nonneg := hχ.radius_nonneg
  nonneg z := sq_nonneg _
  le_bound z := (sq_le_one_iff_abs_le_one _).mpr
    (by simpa only [abs_of_nonneg (hχ.nonneg z)] using hχ.le_bound z)
  support z hz := hχ.support z (fun he ↦ hz (by simp only [he, zero_pow (by decide : 2 ≠ 0)]))

private theorem integral_patch_normal_le_cutoff_sq
    {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ψ χ : Point → ℝ} {B P R : ℝ}
    (hψ : PatchBounds ψ B P) (hψc : Continuous ψ)
    (hχ : PatchBounds χ R 1) (hχc : Continuous χ)
    (hplateau : ∀ z, ψ z ≠ 0 → χ z = 1)
    (T : Point → E →L[ℂ] H) (hT : Continuous T) :
    (∫ z : Point, ψ z • atomNormal (T z)) ≤
      P • ∫ z : Point, χ z ^ 2 • atomNormal (T z) := by
  rw [← integral_smul]
  apply integral_mono (integrable_patch_normal hψ hψc T hT)
    ((integrable_patch_normal (patchBounds_cutoff_sq hχ) (hχc.pow 2) T hT).smul P)
  intro z
  simpa only [Pi.smul_apply, smul_smul] using smul_le_smul_of_nonneg_right
    (patchWeight_le_cutoff_sq hψ ((hψ.nonneg 0).trans (hψ.le_bound 0)) hplateau z)
    (atomNormal_nonneg (T z))

variable {n J : ℕ} {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q]
  [LocallyCompactSpace Q]

/-- Operator-valued spectator integrability of the constructed smooth-cutoff
normal follows from compact patch support and continuous wide-band columns,
via the proved full-band identity (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_fullBandKernelOperator_cutoff_normal
    (D : BandKernelData (Fin J × Q) n) (j : Fin J) (q : Point → Q) (hq : Continuous q)
    {χ : Point → ℝ} {R : ℝ} (hχ : PatchBounds χ R 1) (hc : Continuous χ) :
    Integrable (fun v : Euclidean 2 ↦
      atomNormal (fullBandKernelOperator D (fun z ↦ (j, q z))
        (continuous_const.prodMk hq) χ hc j.val R v)) := by
  simp_rw [fullBandKernelOperator_normal_eq_integral D _ _ χ hc j.val R _
    (fun z hz ↦ hχ.support z hz 0)]
  exact (carrierSamplingEquiv_measurePreserving.integrable_comp_of_integrable
    (integrable_wideBand_patch_normal D j q hq (patchBounds_cutoff_sq hχ)
      (hc.pow 2))).integral_prod_right

/-- Fubini identifies the spectator integral of the smooth-cutoff full-band
normal with the literal `χ²` weighted wide-band normal. All Bochner
integrability is proved from compact supports and continuity
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_fullBandKernelOperator_cutoff_normal
    (D : BandKernelData (Fin J × Q) n) (j : Fin J) (q : Point → Q) (hq : Continuous q)
    {χ : Point → ℝ} {R : ℝ} (hχ : PatchBounds χ R 1) (hc : Continuous χ) :
    (∫ v : Euclidean 2, atomNormal (fullBandKernelOperator D (fun z ↦ (j, q z))
      (continuous_const.prodMk hq) χ hc j.val R v)) =
      ∫ z : Point, χ z ^ 2 • atomNormal (wideBandKernelOperator D j.val (j, q z)) := by
  simp_rw [fullBandKernelOperator_normal_eq_integral D _ _ χ hc j.val R _
    (fun z hz ↦ hχ.support z hz 0)]
  exact (integral_wideBand_normal_eq_spectator D j q hq
    (patchBounds_cutoff_sq hχ) (hc.pow 2)).symm

/-- The original unmasked mean is dominated in operator order by the smooth
majorant, with every original band retained. Positivity and scalar comparison
are used before any full-phase estimate; no normal or norm bound is assumed
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem integral_refinedKernelPrefix_normal_le_cutoff_fullBand
    (D : BandKernelData (Fin J × Q) n) (q : Point → Q) (hq : Continuous q)
    {ψ χ : Point → ℝ} {B P R : ℝ}
    (hψ : PatchBounds ψ B P) (hψc : Continuous ψ)
    (hχ : PatchBounds χ R 1) (hχc : Continuous χ)
    (hplateau : ∀ z, ψ z ≠ 0 → χ z = 1) :
    (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D J (q z))) ≤
      P • ∑ j : Fin J, ∫ v : Euclidean 2,
        atomNormal (fullBandKernelOperator D (fun z ↦ (j, q z))
          (continuous_const.prodMk hq) χ hχc j.val R v) := by
  rw [integral_refinedKernelPrefix_normal_eq_wide D q hq hψ hψc, Finset.smul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [integral_fullBandKernelOperator_cutoff_normal D j q hq hχ hχc]
  exact integral_patch_normal_le_cutoff_sq hψ hψc hχ hχc hplateau _
    ((continuous_wideBandKernelOperator D j.val).comp (continuous_const.prodMk hq))

/-- All charts and colors remain in the majorized original unmasked mean.
The same cutoff and support bound for each chart are used for every band and
color, as required after mask removal in
`app:ch_waves:eq:sampling-operator-bounds`. -/
theorem sum_integral_refinedKernelPrefix_normal_le_cutoff_fullBand
    {A : Type*} [Fintype A] {p : ℕ}
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    {ψ χ : A → Point → ℝ} {B : ℝ} {P R : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    (hχ : ∀ a, PatchBounds (χ a) (R a) 1) (hχc : ∀ a, Continuous (χ a))
    (hplateau : ∀ a z, ψ a z ≠ 0 → χ a z = 1) :
    (∑ a, ∑ c, ∫ z : Point,
      ψ a z • atomNormal (refinedKernelPrefix (D a) J (c, z))) ≤
      ∑ a, P a • ∑ c, ∑ j : Fin J, ∫ v : Euclidean 2,
        atomNormal (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))
          (χ a) (hχc a) j.val (R a) v) := by
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro c _
  exact integral_refinedKernelPrefix_normal_le_cutoff_fullBand (D a) (fun z ↦ (c, z))
    (continuous_const.prodMk continuous_id) (hψ a) (hψc a) (hχ a) (hχc a) (hplateau a)

/-- Construct the smooth majorants and prove domination of the original mean,
retaining all charts, colors, and bands
(`app:ch_waves:eq:sampling-operator-bounds`). The cutoffs and support radii are
chosen before the dimension, band count, color count, and kernel data. All
spectator integrals are Bochner integrable. RawPrimary's fixed cutoffs must
supply the displayed open-chart support inclusion; normalized full-phase
matching remains with the parent kernel-identification construction. -/
theorem exists_smooth_majorants_unmasked_mean
    {A : Type*} [Fintype A] {ψ : A → Point → ℝ} {B : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    {U : A → Set Point} (hU : ∀ a, IsOpen (U a))
    (hψU : ∀ a, tsupport (ψ a) ⊆ U a) :
    ∃ (χ : A → Point → ℝ) (R : A → ℝ) (hχs : ∀ a, ContDiff ℝ ∞ (χ a)),
      (∀ a, 0 < R a) ∧ (∀ a, HasCompactSupport (χ a)) ∧
      (∀ a, PatchBounds (χ a) (R a) 1) ∧ (∀ a, tsupport (χ a) ⊆ U a) ∧
      (∀ a, tsupport (ψ a) ⊆ interior {z | χ a z = 1}) ∧
      ∀ (n J p : ℕ)
        (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n),
        (∀ a c (j : Fin J), Integrable (fun v : Euclidean 2 ↦
          atomNormal (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
            (continuous_const.prodMk (continuous_const.prodMk continuous_id))
            (χ a) (hχs a).continuous j.val (R a) v))) ∧
        (∑ a, ∑ c, ∫ z : Point,
          ψ a z • atomNormal (refinedKernelPrefix (D a) J (c, z))) ≤
          ∑ a, P a • ∑ c, ∑ j : Fin J, ∫ v : Euclidean 2,
            atomNormal (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
              (continuous_const.prodMk (continuous_const.prodMk continuous_id))
              (χ a) (hχs a).continuous j.val (R a) v) := by
  classical
  choose χ R hR hχs hc hb hs hp using
    fun a ↦ exists_smooth_patch_majorant (hψ a) (hU a) (hψU a)
  refine ⟨χ, R, hχs, hR, hc, hb, hs, hp, ?_⟩
  intro n J p D
  constructor
  · intro a c j
    exact integrable_fullBandKernelOperator_cutoff_normal (D a) j (fun z ↦ (c, z))
      (continuous_const.prodMk continuous_id) (hb a) (hχs a).continuous
  · exact sum_integral_refinedKernelPrefix_normal_le_cutoff_fullBand D hψ hψc hb
      (fun a ↦ (hχs a).continuous)
      (fun a z hz ↦ interior_subset (s := {z | χ a z = 1})
        (hp a (subset_tsupport (ψ a) hz)))

end JanetCartan.Sampling.MeanNormalBound
