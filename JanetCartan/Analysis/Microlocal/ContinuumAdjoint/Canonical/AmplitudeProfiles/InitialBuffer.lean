module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.FlowSupport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.LocalConstruction

/-!
# A fixed buffer for the original initial scalar

The initial scalar in `app:ch_background:prop:bg-adjoint` is measured on the
original closed ball of radius `R / 8`. A cutoff used to extend that scalar
must have its support inside this same ball. The retained inverse-flow
estimate and the time-zero inverse identity place all supported footpoints
inside a smaller fixed ball, without assuming a compact footpoint buffer.

Consumer: the initial-scalar extension and the supported kernel equality in
`Canonical.AmplitudeProfiles`. The flow identities, smoothness and paired
`C¹` estimate below are outputs of
`NullTransport.exists_projected_local_positive_amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ActualFlow FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- A mask cap chosen before the immersion and retained flow puts both the
complete supported chart in the amplitude working cylinder and its actual
footpoints in the open `R / 16` initial ball. Only the original primitive
`C⁶` immersion budget and the producer's paired `C¹` flow estimate are used.
This closes the initial-cutoff domain obligation for
`app:ch_background:prop:bg-adjoint`, preserving the original `R / 8` scalar
norm domain from `app:ch_waves:eq:joint-tame`. -/
theorem exists_supportedChart_initialBuffer_cap
    (K : Set (Euclidean n)) (z₀ : Euclidean 3)
    {τ R H₁ : ℝ} (hτ : 0 < τ) (hR : 0 < R) (hH₁ : 0 < H₁) (M : ℝ) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ}, 0 < a → a < cap →
      ∀ (F : Euclidean n → Euclidean N)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3),
      let p₀ := ((0 : Euclidean (n - 1)), z₀)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      cNorm K 6 F ≤ M →
      ContDiffOn ℝ ∞ Y
        (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      cNorm J 1 Φ + cNorm J 1 Y ≤ H₁ * (1 + cNorm K 6 F) →
      (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) →
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, Y (t, Φ (t, p)) = p) →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
        (supportedChart z₀ a) (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64)) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ odeInitialPoint T Y (p.2, p.1))
        (supportedChart z₀ a) (ball p₀ (R / 16)) := by
  let B := H₁ * (1 + max M 0)
  have hB : 0 < B := mul_pos hH₁ (by linarith [le_max_right M 0])
  let δ := min (τ / 2) (min (R / 64) (R / (32 * B)))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδτ : δ ≤ τ / 2 := min_le_left ..
  have hδR : δ ≤ R / 64 := (min_le_right ..).trans (min_le_left ..)
  have hδB : B * δ ≤ R / 32 := by
    have hh : δ ≤ R / (32 * B) := (min_le_right ..).trans (min_le_right ..)
    have hh' := (le_div_iff₀ (by positivity : 0 < 32 * B)).mp hh
    nlinarith
  obtain ⟨cap, hcap, hmaps⟩ := exists_supportedChart_flowCylinder_cap T z₀ hδ
    (show 0 < 32 * δ by positivity)
  refine ⟨cap, hcap, ?_⟩
  intro a ha hacap F Φ Y
  dsimp only
  intro hFM hY hflow hinit hYΦ
  let p₀ := ((0 : Euclidean (n - 1)), z₀)
  let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
  let O := Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)
  have hJO : J ⊆ O := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      (mem_closedBall.mp hq.2).trans_lt (by linarith)⟩
  have hJ : IsCompact J := isCompact_Icc.prod (isCompact_closedBall ..)
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_ball
  have hYat (q) (hq : q ∈ J) : ContDiffAt ℝ ∞ Y q :=
    hY.contDiffAt (hO.mem_nhds (hJO hq))
  have hnorm : cNorm J 1 Y ≤ B := by
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add_left (hFM.trans (le_max_left M 0)) 1) hH₁.le
    dsimp [B]
    linarith [cNorm_nonneg J 1 Φ]
  have hder (q) (hq : q ∈ J) : ‖fderiv ℝ Y q‖ ≤ B := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
      (fun q hq ↦ (hYat q hq).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hq (le_refl 1)
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans hnorm
  have hp₀ : p₀ ∈ ball p₀ (R / 8) := mem_ball_self (by positivity)
  have hzero : Y (0, p₀) = p₀ := by
    simpa only [hinit p₀ hp₀] using hYΦ p₀ hp₀ 0 ⟨by linarith, hτ⟩
  have hzeroJ : (0, p₀) ∈ J :=
    ⟨⟨by linarith, hτ.le⟩, mem_closedBall_self (by positivity)⟩
  have hsmall (p) (hp : p ∈ supportedChart (n := n) z₀ a) :
      let q := coordinates (adaptedCoordinates T.data.adapted)
        (p.1, CanonicalCarrier.parameter p.2)
      q ∈ Ioo (-δ) δ ×ˢ ball p₀ δ := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (32 : ℝ) ≠ 0)] using
      hmaps ha hacap hp
  have hwork (p) (hp : p ∈ supportedChart (n := n) z₀ a) :
      coordinates (adaptedCoordinates T.data.adapted)
        (p.1, CanonicalCarrier.parameter p.2) ∈
        Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64) := by
    have hh := hsmall p hp
    exact ⟨⟨by linarith [hh.1.1], by linarith [hh.1.2]⟩,
      (mem_ball.mp hh.2).le.trans hδR⟩
  refine ⟨hwork, ?_⟩
  intro p hp
  let q := coordinates (adaptedCoordinates T.data.adapted)
    (p.1, CanonicalCarrier.parameter p.2)
  have hq := hsmall p hp
  have hqJ : q ∈ J := by
    have hh := hwork p hp
    exact ⟨⟨by linarith [hh.1.1], by linarith [hh.1.2]⟩,
      (mem_closedBall.mp hh.2).trans (by linarith)⟩
  have hdist : ‖q - (0, p₀)‖ < δ := by
    rw [← dist_eq_norm, Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa only [Real.dist_eq, sub_zero, abs_lt] using
      (show -δ < q.1 ∧ q.1 < δ from hq.1), hq.2⟩
  have hh := ((convex_Icc (-τ) τ).prod (convex_closedBall p₀ (R / 8))).norm_image_sub_le_of_norm_fderiv_le
      (fun q hq ↦ (hYat q hq).differentiableAt (by simp)) hder hzeroJ hqJ
  change dist (Y q) p₀ < R / 16
  rw [dist_eq_norm, ← hzero]
  exact (hh.trans_lt (mul_lt_mul_of_pos_left hdist hB)).trans_le
    (hδB.trans (by linarith))

/-- Fixed scalar cutoff, chosen inside the SAME `R / 8` initial norm domain.
Its open plateau contains the actual footpoints supplied by
`exists_supportedChart_initialBuffer_cap`
(`app:ch_background:prop:bg-adjoint`, `app:ch_waves:eq:joint-tame`). -/
def initialBump (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R) :
    ContDiffBump ((0 : Euclidean (n - 1)), z₀) where
  rIn := R / 16
  rOut := 3 * R / 32
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The extension cutoff is supported strictly inside the original scalar
norm domain; no norm on a larger initial set is introduced
(`app:ch_waves:eq:joint-tame`). -/
theorem initialBump_tsupport_subset (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R) :
    tsupport (initialBump (n := n) z₀ hR) ⊆
      ball ((0 : Euclidean (n - 1)), z₀) (R / 8) := by
  rw [(initialBump z₀ hR).tsupport_eq]
  exact closedBall_subset_ball (by change 3 * R / 32 < R / 8; linarith)

/-- The fixed initial cutoff equals one on an open neighborhood of each
footpoint in the smaller buffer, as needed for equality of all supported
jets in `app:ch_background:prop:bg-adjoint`. -/
theorem initialBump_eventuallyEq_one (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    {p : Euclidean (n - 1) × Euclidean 3}
    (hp : p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) :
    (initialBump z₀ hR : (Euclidean (n - 1) × Euclidean 3) → ℝ) =ᶠ[𝓝 p] 1 :=
  (initialBump z₀ hR).eventuallyEq_one_of_mem_ball hp

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
