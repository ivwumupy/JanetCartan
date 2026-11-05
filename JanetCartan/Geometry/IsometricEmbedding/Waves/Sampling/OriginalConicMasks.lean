module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundPreservingMasks
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.FullBand

/-!
# Sampling weights of the original normalized conic masks

Factor the literal `CanonicalConic.angularMask` into its original carrier
cutoff and direction cutoff. The sampling mass is the square of that carrier
cutoff in the existing measure-preserving coordinates. No mask, radius or
high-pass is chosen again. These concrete functions instantiate the balanced
refinement used by the retained all-prefix event.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff
namespace JanetCartan.Sampling
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open SeparatedSampling FullPhaseCharts MeanNormalBound

/-- The original incidence/spectator cutoff squared, expressed on the SAME
three-dimensional sampling labels (`app:ch_waves:eq:sampling-prefix-normal`,
`app:ch_background:defn:bg-row`). -/
def originalConicCarrierWeight (z₀ : Euclidean 3) {r : ℝ} (hr : 0 < r)
    (z : Point) : ℝ :=
  (incidenceMask z₀ hr (carrierSamplingEquiv.symm z).1 *
    spectatorMask z₀ hr (carrierSamplingEquiv.symm z).2) ^ 2

/-- The original direction cutoff after exactly the normalized transverse
projection used by the continuum row (`app:ch_background:defn:bg-row`). -/
def originalConicDetector {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (η : Euclidean (n - 1)) : ℂ :=
  (directionMask (normalize ηb) (angularWidth_spec hηb hr).1 (normalize η) : ℝ)

/-- The original carrier weight is smooth; no square-root regularity is
assumed (`app:ch_waves:thm:sampling`). -/
theorem contDiff_originalConicCarrierWeight (z₀ : Euclidean 3) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (originalConicCarrierWeight z₀ hr) := by
  have he := carrierSamplingLinearEquiv.symm.toContinuousLinearEquiv.contDiff (n := ∞)
  exact (((incidenceMask z₀ hr).contDiff.comp he.fst).mul
    ((spectatorMask z₀ hr).contDiff.comp he.snd)).pow 2

/-- Nonzero original sampling mass lies in the selector's original closed
carrier support (`app:ch_waves:thm:sampling`). -/
theorem originalConicCarrierWeight_support (z₀ : Euclidean 3) {r : ℝ} (hr : 0 < r)
    {z : Point} (hz : originalConicCarrierWeight z₀ hr z ≠ 0) :
    carrierSamplingEquiv.symm z ∈ carrierSupport z₀ (r := r) := by
  have hm : incidenceMask z₀ hr (carrierSamplingEquiv.symm z).1 *
      spectatorMask z₀ hr (carrierSamplingEquiv.symm z).2 ≠ 0 := by
    intro h
    exact hz (by simp [originalConicCarrierWeight, h])
  exact ⟨ball_subset_closedBall ((incidenceMask z₀ hr).support_eq ▸ (mul_ne_zero_iff.mp hm).1),
    ball_subset_closedBall ((spectatorMask z₀ hr).support_eq ▸ (mul_ne_zero_iff.mp hm).2)⟩

/-- The same original compact carrier support contains the support in the
sampling coordinates (`app:ch_waves:eq:background-quadrature`). -/
theorem hasCompactSupport_originalConicCarrierWeight
    (z₀ : Euclidean 3) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (originalConicCarrierWeight z₀ hr) := by
  apply HasCompactSupport.intro
    ((carrierSupport_compact z₀).image continuous_carrierSamplingEquiv)
  intro z hz
  by_contra hne
  exact hz ⟨carrierSamplingEquiv.symm z, originalConicCarrierWeight_support z₀ hr hne,
    carrierSamplingEquiv.apply_symm_apply z⟩

/-- The literal original carrier mass satisfies the sampling patch contract
with bound one and one fixed coordinate cube (`app:ch_waves:thm:sampling`). -/
theorem exists_originalConicCarrierWeight_patchBounds
    (z₀ : Euclidean 3) {r : ℝ} (hr : 0 < r) :
    ∃ B > (0 : ℝ), PatchBounds (originalConicCarrierWeight z₀ hr) B 1 := by
  obtain ⟨B, hB, hb⟩ := (hasCompactSupport_originalConicCarrierWeight z₀ hr).isCompact.isBounded.exists_pos_norm_le
  refine ⟨B, hB, hB.le, fun _ ↦ sq_nonneg _, ?_, ?_⟩
  · intro z
    have hnonneg : 0 ≤ incidenceMask z₀ hr (carrierSamplingEquiv.symm z).1 *
        spectatorMask z₀ hr (carrierSamplingEquiv.symm z).2 :=
      mul_nonneg (ContDiffBump.nonneg _) (ContDiffBump.nonneg _)
    have hle : incidenceMask z₀ hr (carrierSamplingEquiv.symm z).1 *
        spectatorMask z₀ hr (carrierSamplingEquiv.symm z).2 ≤ 1 :=
      (mul_le_of_le_one_left (ContDiffBump.nonneg _) (ContDiffBump.le_one _)).trans
        (ContDiffBump.le_one _)
    exact (pow_le_pow_left₀ hnonneg hle 2).trans_eq (one_pow 2)
  · intro z hz i
    exact (show |z i| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i).trans
      (hb z (subset_tsupport _ hz))

/-- The original compact carrier domain is reached by the literal adapted
parameter map, with no coordinate Jacobian or transported measure
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem originalConicCarrierWeight_parameter_support
    (z₀ : Euclidean 3) {r : ℝ} (hr : 0 < r)
    {z : Point} (hz : originalConicCarrierWeight z₀ hr z ≠ 0) :
    WithLp.toLp 2 z ∈ parameter '' carrierSupport z₀ (r := r) := by
  refine ⟨carrierSamplingEquiv.symm z, originalConicCarrierWeight_support z₀ hr hz, ?_⟩
  obtain ⟨p, rfl⟩ := carrierSamplingEquiv.surjective z
  rw [carrierSamplingEquiv.symm_apply_apply, parameter_apply]
  ext i
  fin_cases i <;> rfl

/-- Taking the positive square root recovers exactly the original carrier
cutoff, so the retained normal uses the SAME continuum angular mask
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem originalConicCarrierWeight_sqrt_mul_direction
    {n : ℕ} (z₀ : Euclidean 3) {ρ r : ℝ} (hρ : 0 < ρ)
    {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0) (hr : 0 < r)
    (z : CarrierParameter) (θ : Euclidean (n - 1)) :
    Real.sqrt (originalConicCarrierWeight z₀ hρ (carrierSamplingEquiv z)) *
        directionMask (normalize ηb) (angularWidth_spec hηb hr).1 θ =
      angularMask z₀ (normalize ηb) hρ (angularWidth_spec hηb hr).1 z θ := by
  rw [originalConicCarrierWeight, carrierSamplingEquiv.symm_apply_apply,
    Real.sqrt_sq (mul_nonneg (ContDiffBump.nonneg _) (ContDiffBump.nonneg _))]
  rfl

/-- Smoothness of the literal detector on every nonzero transverse covector
(`app:ch_waves:thm:sampling`). -/
theorem originalConicDetector_contDiffAt {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) {η : Euclidean (n - 1)} (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ (originalConicDetector hηb hr) η := by
  have hn : ContDiffAt ℝ ∞ (normalize : Euclidean (n - 1) → _) η :=
    ((contDiffAt_id.norm ℝ hη).inv (norm_ne_zero_iff.mpr hη)).smul contDiffAt_id
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp η
    ((directionMask (normalize ηb) (angularWidth_spec hηb hr).1).contDiff.contDiffAt.comp η hn)

/-- Positive dilation fixes the original detector, including its value at
zero (`app:ch_waves:setup:oscillatory`). -/
theorem originalConicDetector_homogeneous {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (t : ℝ) (ht : 0 < t) (η : Euclidean (n - 1)) :
    originalConicDetector hηb hr (t • η) = originalConicDetector hηb hr η := by
  simp only [originalConicDetector, normalize_smul_of_pos ht]

/-- The actual detector vanishes at zero; its angular support keeps the
original normalized projection (`app:ch_background:defn:bg-row`). -/
theorem originalConicDetector_zero {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) : originalConicDetector hηb hr 0 = 0 := by
  have hz : directionMask (normalize ηb) (angularWidth_spec hηb hr).1 (0 : Euclidean (n - 1)) = 0 := by
    apply ContDiffBump.zero_of_le_dist
    change angularWidth ηb r / 2 ≤ dist 0 (normalize ηb)
    rw [dist_zero_left, norm_normalize hηb]
    linarith [(angularWidth_spec hηb hr).2.1]
  simp [originalConicDetector, hz]

/-- Every nonzero value of the literal detector lies in the original closed
direction set used by the normalized selector (`app:ch_waves:thm:sampling`). -/
theorem originalConicDetector_support {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) {η : Euclidean (n - 1)}
    (h : originalConicDetector hηb hr η ≠ 0) : normalize η ∈ closedDirections ηb r := by
  have hη : η ≠ 0 := fun he ↦ h (he ▸ originalConicDetector_zero hηb hr)
  have hdir : directionMask (normalize ηb) (angularWidth_spec hηb hr).1 (normalize η) ≠ 0 := by
    intro hz
    exact h (by simp [originalConicDetector, hz])
  exact ⟨mem_sphere_zero_iff_norm.mpr (norm_normalize hη),
    ball_subset_closedBall ((directionMask (normalize ηb) (angularWidth_spec hηb hr).1).support_eq ▸ hdir)⟩

/-- The original central direction has detector value one, so the balanced
background partition has a nonempty direction witness (`app:ch_waves:thm:sampling`). -/
theorem originalConicDetector_center {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) : originalConicDetector hηb hr ηb = 1 := by
  have h := (directionMask (normalize ηb) (angularWidth_spec hηb hr).1).one_of_mem_closedBall
    (mem_closedBall_self (directionMask (normalize ηb) (angularWidth_spec hηb hr).1).rIn_pos.le)
  simp only [originalConicDetector, h, Complex.ofReal_one]

/-- The sampling weight and the original detector retain the square of the
literal continuum mask at every frequency. The supplied high-pass is
unchanged, including its transition between one and two
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_background:defn:bg-row`). -/
theorem originalConicCarrierWeight_detectorMask_sq
    {n : ℕ} (z₀ : Euclidean 3) {ρ r : ℝ} (hρ : 0 < ρ)
    {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0) (hr : 0 < r)
    (highPass : Euclidean (n - 1) → ℝ) (z : Point) (η : Euclidean (n - 1)) :
    originalConicCarrierWeight z₀ hρ z *
        ‖RawPrimary.MaskProfiles.detectorMask (originalConicDetector hηb hr) highPass η‖ ^ 2 =
      ‖(angularMask z₀ (normalize ηb) hρ (angularWidth_spec hηb hr).1
          (carrierSamplingEquiv.symm z) (normalize η) : ℂ) * (highPass η : ℂ)‖ ^ 2 := by
  simp only [originalConicCarrierWeight, originalConicDetector, RawPrimary.MaskProfiles.detectorMask,
    angularMask, Complex.ofReal_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end JanetCartan.Sampling
