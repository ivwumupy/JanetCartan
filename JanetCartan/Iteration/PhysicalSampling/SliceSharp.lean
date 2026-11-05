module

public import JanetCartan.Iteration.PhysicalSampling.SliceBandAction

/-!
# Sharp scalar bounds for the original physical sampling bands

The completed single-channel construction is transported by the actual physical
Lebesgue isometry and identified with the unchanged scalar kernel. Both sharp
Hilbert refinements are contractions of that same wide input. No scalar or
measured row bound is assumed (`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase RawPrimary RawPrimary.SliceBounds RawPrimary.SliceGeometry
open LeadingWave.FullModulation FullPhaseCharts FullPhaseCharts.ActualPhase Sampling.MeasuredAmplitude
open Sampling Sampling.RawKernel Sampling.MeanNormalBound SamplingKernelBounds
open RawInputPartition RawPrimary.MaskProfiles PhysicalMean NormalComparison

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The actual scalar wide-band and both original sharp refinements satisfy
one uniform `C*R` squared bound. Its constant precedes the current immersion,
phase, inverse frequency, carrier, ceiling and original mask labels. The phase
and scalar-amplitude normal family is constructed by `SliceGeometry`. -/
theorem exists_retainedScalar_sharp_bound
    (G : UniformNormalGeometry (m + 1 - 1) (m + 1)) (Cnormal : ℕ → ℝ)
    {a e b : ℝ} (ha : 0 < a) (haR : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b) (hGe : G.ε₀ = e) :
    ∃ Cband > (0 : ℝ),
    ∀ (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {σ : ℝ} (hσ : 0 < σ) {c C : ℝ} (hP : P.IsValid c C)
    (hcarrier : closedBall center.2.1 (2 * σ) ⊆ parameterInterior (2 * P.radius))
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (hang : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
    (Bdet : ℝ) (hBdet : 0 ≤ Bdet) (hdB : ∀ η, ‖detectorMask angular H η‖ ≤ Bdet),
    closedBall center (2 * σ) ⊆ domain T →
    tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (a / 4) →
    Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall center.1 (σ / 2) →
    ∀ (p J : ℕ) (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ₀ : ∀ color, τ color ≠ 0)
    (color : Fin 3 → Fin (p + 1)) (j : Fin J) (z : Euclidean 3),
    ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)) →
    (z, T.reference.spatialPatch z) ∈ closedBall center.2 (σ / 4) →
    τ color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀ →
    |τ color * (2 : ℝ) ^ j.val| ≤ σ / 8 →
    ∀ (N : (t : ℝ) → t ∈ Ioo (-a) a → UniformNormalData G Cnormal),
      (∀ t (ht : t ∈ Ioo (-a) a), (N t ht).phase = fun ε y η ↦
        rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)
          (ε, (t, y), η)) →
      (∀ t (ht : t ∈ Ioo (-a) a), (N t ht).amplitude = fun _ y η ↦
        scalarSliceAmplitude T.data.adapted χ angular H (by omega) j.val (t, y, η)) →
    let D := retainedScalarKernelData (J := J) T Q χ center hσ hP hcarrier
      angular H hang hH hH₀ Bdet hBdet hdB τ hτ₀
    ‖wideBandKernelOperator D j.val (j, (color, z.ofLp))‖ ^ 2 ≤ Cband * (2 : ℝ) ^ j.val ∧
      ∀ q : Fin 2, ‖D.operator (refinedRadius (j, q)) (j, (color, z.ofLp))‖ ^ 2 ≤
        Cband * refinedRadius (j, q) := by
  obtain ⟨Cband, hCband, hband⟩ := exists_scalarSliceBandOperator T (by omega) G Cnormal
    ha haR he heb hGe
  refine ⟨Cband, hCband, ?_⟩
  intro Q χ center σ hσ c C hP hcarrier angular H hang hH hH₀ Bdet hBdet hdB
    hphase hχa hχσ p J τ hτ₀ color j z hb hzg hε hscale N hNp hNa D
  obtain ⟨L, hL, hnorm⟩ := hband Q z hb χ angular H hang hH hχa j.val
    (τ color * (2 : ℝ) ^ j.val) hε N hNp hNa
  have heq : wideBandKernelOperator D j.val (j, (color, z.ofLp)) =
      (adaptedL2Equiv T.data.adapted (EuclideanSpace ℂ (Fin (m + 1)))).toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
    unfold D retainedScalarKernelData scalarAuxiliaryKernel
    apply bandKernelData_wideOperator_eq_adapted
    intro f
    refine (hL f).trans (Filter.Eventually.of_forall fun q ↦ ?_)
    simpa only [WithLp.toLp_ofLp, scalarAuxiliaryAmplitude] using scalarSliceBandIntegral_eq_retained_raw T Q χ
      angular H center hσ hphase ha haR he heb hχa hχσ z hb hzg (hτ₀ color) j.val
      (by simpa only [hGe] using hε) hscale f q
  have hwide : ‖wideBandKernelOperator D j.val (j, (color, z.ofLp))‖ ^ 2 ≤
      Cband * (2 : ℝ) ^ j.val := by
    rw [heq, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp]
    exact hnorm
  refine ⟨hwide, ?_⟩
  intro q
  apply (pow_le_pow_left₀ (norm_nonneg _)
    (norm_annularOperator_le_wideBand D j.val (j, (color, z.ofLp)) q) 2).trans
  apply hwide.trans
  apply mul_le_mul_of_nonneg_left _ hCband.le
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)

end JanetCartan.PhysicalSampling
