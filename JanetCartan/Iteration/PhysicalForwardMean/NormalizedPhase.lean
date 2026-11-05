module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicHighPass

/-!
# Smooth normalized original phase off the removed zero-frequency region

The original input mask vanishes for norm eta at most one. This leaf uses the
already fixed high-pass at twice that norm ONLY to extend the normalized phase
through zero; it never changes the input mask, row kernel, full amplitude or
source. At every active original frequency, the entire physical phase and all
physical jets agree with the literal original phase divided by norm eta.
Consumer: `app:ch_mean_pairs:eq:block-normal`, the forward binary expansion.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.PhysicalForwardMean
open ContinuumRow

variable {d n : ℕ}

/-- Smooth off-mask extension of the literal normalized phase. The fixed
high-pass factor is auxiliary ANALYSIS data and is not a new operator mask. -/
def normalizedForwardPhase (φ : Euclidean d → Euclidean n → ℝ)
    (η : Euclidean d) (x : Euclidean n) : ℝ :=
  FixedCutoffs.highFrequency (2 * ‖η‖) * φ η x / ‖η‖

/-- The normalized phase extension is jointly smooth, including zero initial
frequency. No derivative norm in the initial variable is asserted or used. -/
theorem contDiff_normalizedForwardPhase
    (φ : Euclidean d → Euclidean n → ℝ)
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ)) :
    ContDiff ℝ ∞ (Function.uncurry (normalizedForwardPhase φ)) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.1 = 0
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hn : ∀ᶠ p : Euclidean d × Euclidean n in 𝓝 q, ‖p.1‖ < (1 / 2 : ℝ) :=
      (continuous_norm.comp continuous_fst).continuousAt.eventually
        (gt_mem_nhds (by simp [hq] : ‖q.1‖ < (1 / 2 : ℝ)))
    filter_upwards [hn] with p hp
    change normalizedForwardPhase φ p.1 p.2 = 0
    rw [normalizedForwardPhase,
      FixedCutoffs.highFrequency_zero (by linarith : 2 * ‖p.1‖ ≤ 1), zero_mul, zero_div]
  · have hn : ContDiffAt ℝ ∞ (fun p : Euclidean d × Euclidean n ↦ ‖p.1‖) q :=
      contDiffAt_fst.norm ℝ hq
    exact ((FixedCutoffs.highFrequency_smooth.contDiffAt.comp q
      (contDiffAt_const.mul hn)).mul hφ.contDiffAt).div hn (norm_ne_zero_iff.mpr hq)

/-- On every original active frequency the normalized extension equals the
literal normalized phase as an ENTIRE physical function, so all physical jets
are unchanged, not merely its value (`app:ch_mean_pairs:eq:block-normal`). -/
theorem normalizedForwardPhase_eq_on_highFrequency
    (φ : Euclidean d → Euclidean n → ℝ) (η : Euclidean d) (hη : 1 ≤ ‖η‖) :
    normalizedForwardPhase φ η = fun x ↦ φ η x / ‖η‖ := by
  funext x
  simp only [normalizedForwardPhase, FixedCutoffs.highFrequency_one (by linarith : 2 ≤ 2 * ‖η‖), one_mul]

/-- Exact reconstruction of the unchanged literal phase on the original mask;
there is no leading-phase approximation (`app:ch_mean_pairs:eq:block-fields`). -/
theorem norm_mul_normalizedForwardPhase
    (φ : Euclidean d → Euclidean n → ℝ) (η : Euclidean d) (hη : 1 ≤ ‖η‖) (x : Euclidean n) :
    ‖η‖ * normalizedForwardPhase φ η x = φ η x := by
  rw [normalizedForwardPhase_eq_on_highFrequency φ η hη]
  exact mul_div_cancel₀ _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hη))

/-- All physical normalized-phase jets supplied by the actual original phase
producer are inherited literally, without an auxiliary-cutoff derivative cost. -/
theorem iteratedFDeriv_normalizedForwardPhase_on_highFrequency
    (φ : Euclidean d → Euclidean n → ℝ) (η : Euclidean d) (hη : 1 ≤ ‖η‖)
    (j : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ j (normalizedForwardPhase φ η) x =
      iteratedFDeriv ℝ j (fun y ↦ φ η y / ‖η‖) x := by
  rw [normalizedForwardPhase_eq_on_highFrequency φ η hη]

end JanetCartan.PhysicalForwardMean
