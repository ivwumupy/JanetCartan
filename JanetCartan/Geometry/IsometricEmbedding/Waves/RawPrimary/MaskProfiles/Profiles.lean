module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.DerivativeBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.MaskedSynthesis
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The literal normalized detector and high-pass profiles

The scale remains `dyadicScale j = 2^j / 2`. After dilation by `2^j`,
the original wide band is supported between radii `1/2` and `2`.
The high-pass transition is retained in labels zero and one; every higher
label has exactly the same profile. These identities supply the fixed-mask
inputs of `CanonicalSlice.exists_canonical_rawSliceSobolev`, from
`app:ch_waves:eq:B-bounds` and `app:ch_waves:eq:individual-raw-slice`.
No parity condition is imposed on the complex angular detector.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.RawPrimary.MaskProfiles
open RawInputPartition

variable {n : ℕ}
local notation "E" => Euclidean (n - 1)

/-- The unchanged angular detector times the original real high-pass
(`app:ch_background:defn:bg-row`). -/
def detectorMask (a : E → ℂ) (H : E → ℝ) (η : E) : ℂ := a η * (H η : ℂ)

/-- The literal normalized half-weighted mask consumed by the raw slice
estimate (`app:ch_waves:eq:individual-raw-slice`). -/
def normalizedMask (a : E → ℂ) (H : E → ℝ) (j : ℕ) (θ : E) : ℂ :=
  (Real.sqrt ‖θ‖ : ℂ) * weightedRadialBand (detectorMask a H) j ((2 : ℝ) ^ j • θ)

/-- Exact radial rescaling with the original half-size dyadic convention
(`app:ch_waves:eq:B-bounds`). -/
theorem radialBand_dyadic_rescale (j : ℕ) (θ : E) :
    radialBand n j ((2 : ℝ) ^ j • θ) = radialBand n 0 θ := by
  simp only [radialBand, scalarBand, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j), dyadicScale, pow_zero]
  congr 1
  field_simp

/-- Rescaling leaves the angular detector unchanged, without any evenness
assumption (`app:ch_waves:eq:B-bounds`). -/
theorem normalizedMask_eq_fixed_radial (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ) (j : ℕ) (θ : E) :
    normalizedMask a H j θ = (Real.sqrt ‖θ‖ : ℂ) *
      (a θ * (H ((2 : ℝ) ^ j • θ) : ℂ) * (radialBand n 0 θ : ℂ)) := by
  simp only [normalizedMask, weightedRadialBand, detectorMask, radialBand_dyadic_rescale,
    ha ((2 : ℝ) ^ j) (pow_pos (by norm_num) j)]

/-- The actual annular vanishing removes the apparent half-weight
singularity at zero (`app:ch_waves:eq:individual-raw-slice`). -/
theorem normalizedMask_eq_zero_of_le (a : E → ℂ) (H : E → ℝ) (j : ℕ)
    {θ : E} (hθ : ‖θ‖ ≤ 1 / 2) : normalizedMask a H j θ = 0 := by
  have hrad : radialBand n 0 θ = 0 :=
    scalarBand_eq_zero_of_le (by simpa [dyadicScale] using hθ)
  simp [normalizedMask, weightedRadialBand, radialBand_dyadic_rescale, hrad]

/-- The entire original normalized wide band fits in radius two
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem normalizedMask_eq_zero_of_ge (a : E → ℂ) (H : E → ℝ) (j : ℕ)
    {θ : E} (hθ : 2 ≤ ‖θ‖) : normalizedMask a H j θ = 0 := by
  have hrad : radialBand n 0 θ = 0 :=
    scalarBand_eq_zero_of_ge (by norm_num [dyadicScale]; exact hθ)
  simp [normalizedMask, weightedRadialBand, radialBand_dyadic_rescale, hrad]

/-- Support in the unchanged radius-two core
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem support_normalizedMask_subset (a : E → ℂ) (H : E → ℝ) (j : ℕ) :
    Function.support (normalizedMask a H j) ⊆ closedBall 0 2 := by
  intro θ hθ
  exact mem_closedBall_zero_iff.mpr (le_of_not_gt (fun h ↦
    hθ (normalizedMask_eq_zero_of_ge a H j h.le)))

/-- Closed support stays in radius two, hence strictly inside the consumer's
radius-four extension (`app:ch_waves:eq:individual-raw-slice`). -/
theorem tsupport_normalizedMask_subset (a : E → ℂ) (H : E → ℝ) (j : ℕ) :
    tsupport (normalizedMask a H j) ⊆ closedBall 0 2 :=
  closure_minimal (support_normalizedMask_subset a H j) isClosed_closedBall

/-- Compact support of the literal normalized complex mask
(`app:ch_waves:eq:B-bounds`). -/
theorem hasCompactSupport_normalizedMask (a : E → ℂ) (H : E → ℝ) (j : ℕ) :
    HasCompactSupport (normalizedMask a H j) :=
  (isCompact_closedBall (0 : E) 2).of_isClosed_subset isClosed_closure
    (tsupport_normalizedMask_subset a H j)

/-- Above label one the original high-pass is one wherever the band is
nonzero. Both exceptional low profiles retain the full transition
(`app:ch_waves:eq:B-bounds`). -/
theorem normalizedMask_eq_of_two_le (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ)
    (hH : ∀ η, 2 ≤ ‖η‖ → H η = 1) {j : ℕ} (hj : 2 ≤ j) :
    normalizedMask a H j = normalizedMask a H 2 := by
  funext θ
  by_cases hθ : ‖θ‖ ≤ 1 / 2
  · rw [normalizedMask_eq_zero_of_le a H j hθ,
      normalizedMask_eq_zero_of_le a H 2 hθ]
  · have hpow : (4 : ℝ) ≤ 2 ^ j := by
      convert (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) using 1
      norm_num
    have hnorm (i : ℕ) (hi : (4 : ℝ) ≤ 2 ^ i) : 2 ≤ ‖(2 : ℝ) ^ i • θ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (by norm_num) i)]
      nlinarith [norm_nonneg θ, lt_of_not_ge hθ]
    rw [normalizedMask_eq_fixed_radial a H ha,
      normalizedMask_eq_fixed_radial a H ha,
      hH _ (hnorm j hpow), hH _ (hnorm 2 (by norm_num))]

/-- There are just three exact normalized profiles, independently of every
finite band ceiling (`app:ch_waves:eq:B-bounds`). -/
theorem normalizedMask_eq_min (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ)
    (hH : ∀ η, 2 ≤ ‖η‖ → H η = 1) (j : ℕ) :
    normalizedMask a H j = normalizedMask a H (min j 2) := by
  rcases le_total j 2 with hj | hj
  · rw [min_eq_left hj]
  · rw [min_eq_right hj]
    exact normalizedMask_eq_of_two_le a H ha hH hj

variable {Z : Type*} [NormedAddCommGroup Z]

/-- Joint carrier/input support has the same radius-two input bound;
carrier derivatives therefore introduce no frequency tail
(`app:ch_waves:eq:B-bounds`). -/
theorem tsupport_normalizedMask_joint_subset (a : Z → E → ℂ) (H : E → ℝ) (j : ℕ) :
    tsupport (fun q : Z × E ↦ normalizedMask (a q.1) H j q.2) ⊆
      Prod.snd ⁻¹' closedBall 0 2 := by
  apply closure_minimal _ (isClosed_closedBall.preimage continuous_snd)
  intro q hq
  exact support_normalizedMask_subset (a q.1) H j hq

variable [NormedSpace ℝ Z]

/-- Joint smoothness, including carrier derivatives, follows from primitive
angular smoothness on the punctured space. At zero the whole mask is locally
zero; no smoothness of `sqrt ‖θ‖` at zero is asserted
(`app:ch_waves:eq:B-bounds`). -/
theorem contDiffAt_normalizedMask_joint (a : Z → E → ℂ) (H : E → ℝ)
    {z : Z} (ha : ∀ θ : E, θ ≠ 0 →
      ContDiffAt ℝ ∞ (fun q : Z × E ↦ a q.1 q.2) (z, θ))
    (hH : ContDiff ℝ ∞ H) (j : ℕ) (θ : E) :
    ContDiffAt ℝ ∞ (fun q : Z × E ↦ normalizedMask (a q.1) H j q.2) (z, θ) := by
  by_cases hθ : θ = 0
  · subst θ
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hn : ∀ᶠ q : Z × E in nhds (z, 0), ‖q.2‖ < 1 / 2 :=
      (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simp)
    filter_upwards [hn] with q hq
    exact normalizedMask_eq_zero_of_le _ H j hq.le
  · have hd : ContDiff ℝ ∞ (fun η : E ↦ (2 : ℝ) ^ j • η) :=
      by fun_prop
    have hscaled : (2 : ℝ) ^ j • θ ≠ 0 :=
      smul_ne_zero (ne_of_gt (pow_pos (by norm_num) j)) hθ
    have ha' := (ha _ hscaled).comp (z, θ)
      (contDiffAt_fst.prodMk (hd.contDiffAt.comp (z, θ) contDiffAt_snd))
    have hroot : ContDiffAt ℝ ∞ (fun q : Z × E ↦ (Real.sqrt ‖q.2‖ : ℂ)) (z, θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (z, θ)
        ((contDiffAt_snd.norm ℝ hθ).sqrt (norm_ne_zero_iff.mpr hθ))
    have hhigh : ContDiff ℝ ∞ (fun q : Z × E ↦ (H ((2 : ℝ) ^ j • q.2) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hH.comp (hd.comp contDiff_snd))
    have hrad : ContDiff ℝ ∞
        (fun q : Z × E ↦ (radialBand n j ((2 : ℝ) ^ j • q.2) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_radialBand n j).comp (hd.comp contDiff_snd))
    exact hroot.mul ((ha'.mul hhigh.contDiffAt).mul hrad.contDiffAt)

/-- Global smooth extension of each original normalized mask from primitive
punctured angular smoothness (`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiff_normalizedMask (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ θ : E, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hH : ContDiff ℝ ∞ H) (j : ℕ) : ContDiff ℝ ∞ (normalizedMask a H j) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  exact (contDiffAt_normalizedMask_joint (fun _ : ℝ ↦ a) H
    (z := 0) (fun η hη ↦ (ha η hη).comp (0, η) contDiffAt_snd) hH j θ).comp θ
      (contDiffAt_const.prodMk contDiffAt_id)

end JanetCartan.RawPrimary.MaskProfiles
