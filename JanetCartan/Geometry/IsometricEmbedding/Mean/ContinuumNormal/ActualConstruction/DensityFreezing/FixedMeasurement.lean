module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing.ZeroAmplitude

/-!
# Spatial freezing on the existing measurement masks

Construct the auxiliary Taylor cutoffs from the original physical measurement
radius. They are used only in the proof; neither carrier mask is changed.
The operator box is the original `4r` box. All choices precede the density
and the eventual small support. Consumer: absorption in the initialized local
gap (`app:ch_background:prop:bg-frame`, `bg-local-bound`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Metric
open scoped ContDiff NNReal Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs.WideDensity Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- With the SAME physical measurement cutoff, the literal transported-density
limit and frozen-label normal have a uniform `C(AActual+AFrozen)r` quadratic
error on support radius `r`. The Taylor cutoffs, their compactness, their
plateaus, the operator support box and the origin equality are all constructed.
Only the exact amplitude bounds and smoothness from
`exists_source_zero_density_reflected_bounds` remain as analytic inputs here.
Consumer: `exists_initialized_source_density_limit_coercivity`
(`app:ch_background:eq:bg-local-bound`, `bg-full-complex-amplitude`). -/
theorem exists_fixed_measurement_sourceDensityLimit_error_constant
    {n : ℕ} (hn : 0 < n) {rMeas : ℝ} (hrMeas : 0 < rMeas) :
    ∃ C > 0, ∀ {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
      (T : PatchQuantitativeFamily P U hU)
      (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
      {N : ℕ} (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → SliceVariable n)
      (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
      (hm : a.measurement = FixedCutoffs.physical hrMeas 1),
      let hs : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * rMeas := by
        intro x hx j
        rw [hm] at hx
        exact (PiLp.norm_apply_le x j).trans
          (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four hrMeas 1
            (subset_tsupport _ hx)))
      let aActual := {a with
        normal := fun p ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, p))) • a.normal p}
      let aFrozen := {a with
        normal := fun p ↦ Real.sqrt (1 + v (0, parameter p.2)) • a.normal p}
      let bActual := fullReflectedMatrixAmplitude aActual J u Ω S
      let bFrozen := fullReflectedMatrixAmplitude aFrozen J u Ω S
      ∀ (hbActual : ContDiff ℝ ∞ (Function.uncurry bActual))
        (hbFrozen : ContDiff ℝ ∞ (Function.uncurry bFrozen)) (AActual AFrozen : ℝ≥0)
        (hActual : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ bActual ξ z i j)
          (2 * (n + 1) + 1) AActual)
        (hFrozen : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ bFrozen ξ z i j)
          (2 * (n + 1) + 1) AFrozen),
      let NActual := realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn (4 * rMeas) bActual hbActual
          (fullReflectedMatrixAmplitude_supportedInCenteredBox aActual J u Ω S (4 * rMeas) hs)
          AActual (fun i j ξ is his ↦ hActual i j ξ is (by omega))))
      let NFrozen := realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn (4 * rMeas) bFrozen hbFrozen
          (fullReflectedMatrixAmplitude_supportedInCenteredBox aFrozen J u Ω S (4 * rMeas) hs)
          AFrozen (fun i j ξ is his ↦ hFrozen i j ξ is (by omega))))
      ∀ r ∈ Icc (0 : ℝ) rMeas, ∀ w : OutputL2 n,
      (∀ᵐ x ∂volume, x ∉ torusChart (closedBall (0 : Euclidean n) r) → w x = 0) →
      |inner ℝ ((NActual - NFrozen) w) w| ≤ C * (AActual + AFrozen) * r * ‖w‖ ^ 2 := by
  let β : Euclidean n → ℝ := FixedCutoffs.physical hrMeas 2
  let θ : Euclidean (2 * n) → ℝ := fun z ↦
    β (freezingOutputProjection z) * β (freezingSourceProjection z)
  have hθ : ContDiff ℝ ∞ θ :=
    ((FixedCutoffs.physical hrMeas 2).contDiff.comp freezingOutputProjection.contDiff).mul
      ((FixedCutoffs.physical hrMeas 2).contDiff.comp freezingSourceProjection.contDiff)
  have hpositions (z : Euclidean (2 * n)) (hz : θ z ≠ 0) :
      freezingOutputProjection z ∈ closedBall 0 (4 * rMeas) ∧
      freezingSourceProjection z ∈ closedBall 0 (4 * rMeas) := by
    have hp := mul_ne_zero_iff.mp hz
    exact ⟨FixedCutoffs.physical_tsupport_four hrMeas 2 (subset_tsupport _ hp.1),
      FixedCutoffs.physical_tsupport_four hrMeas 2 (subset_tsupport _ hp.2)⟩
  have hθbox : ∀ z, θ z ≠ 0 → ∀ j, |z j| ≤ 4 * rMeas := by
    intro z hz j
    obtain ⟨hx, hy⟩ := hpositions z hz
    by_cases hj : j.val < n
    · exact (PiLp.norm_apply_le (freezingOutputProjection z) ⟨j.val, hj⟩).trans
        (mem_closedBall_zero_iff.mp hx)
    · simpa [freezingSourceProjection, show n + (j.val - n) = j.val by omega] using
        (PiLp.norm_apply_le (freezingSourceProjection z) ⟨j.val - n, by omega⟩).trans
          (mem_closedBall_zero_iff.mp hy)
  have hθs : HasCompactSupport θ := by
    apply HasCompactSupport.of_support_subset_isCompact
      (((isCompact_closedBall (0 : Euclidean n) (4 * rMeas)).prod
        (isCompact_closedBall (0 : Euclidean n) (4 * rMeas))).image pairedPositionCLM.continuous)
    intro z hz
    refine ⟨(freezingOutputProjection z, freezingSourceProjection z), hpositions z hz, ?_⟩
    ext j
    by_cases hj : j.val < n
    · simp [pairedPositionCLM, pairedPosition, hj, freezingOutputProjection]
    · simp [pairedPositionCLM, pairedPosition, hj, freezingSourceProjection,
        show n + (j.val - n) = j.val by omega]
  let χ := bufferedBallBump (0 : Euclidean n) (4 * rMeas) (5 * rMeas)
    (by positivity) (by linarith)
  have hχone : ∀ x ∈ closedBall (0 : Euclidean n) (4 * rMeas), χ x = 1 := by
    intro x hx
    have hp : x ∈ interior {x : Euclidean n | χ x = 1} :=
      bufferedBallBump_plateau _ _ _ _ _ hx
    exact (interior_subset (s := {x : Euclidean n | χ x = 1})) hp
  have hχθ : ∀ x y, θ (pairedPosition x y) ≠ 0 → χ x = 1 ∧ χ y = 1 := by
    intro x y hxy
    have hp := hpositions _ hxy
    simp only [freezingOutputProjection_pairedPosition, freezingSourceProjection_pairedPosition] at hp
    exact ⟨hχone _ hp.1, hχone _ hp.2⟩
  obtain ⟨C, hC, herror⟩ := exists_sourceDensityLimit_frozen_error_constant
    hn (4 * rMeas) θ hθ hθs hθbox χ χ.continuous χ.hasCompactSupport hχθ
  refine ⟨C, hC, ?_⟩
  intro P U hU T Y v N a J u Ω S hm
  dsimp only
  intro hbActual hbFrozen AActual AFrozen hActual hFrozen r hr w hw
  apply herror T Y v a J u Ω S _ _ hbActual hbFrozen AActual AFrozen hActual hFrozen r hr.1 _ w hw
  · intro x hx j
    rw [hm] at hx
    exact (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four hrMeas 1
        (subset_tsupport _ hx)))
  · intro z hx hy
    rw [hm] at hx hy
    simp only [θ, β, FixedCutoffs.source_one_on_measurement hrMeas hx,
      FixedCutoffs.source_one_on_measurement hrMeas hy, one_mul]
  · intro x hx
    apply hχone
    exact (closedBall_subset_closedBall (by linarith only [hr.2, hrMeas] : r ≤ 4 * rMeas)) hx

end JanetCartan.ContinuumNormal.ActualConstruction
