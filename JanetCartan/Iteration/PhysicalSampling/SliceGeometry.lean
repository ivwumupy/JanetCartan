module

public import JanetCartan.Iteration.PhysicalSampling.SliceOperator

/-!
# Scalar slice family from the original current immersion

The transverse geometry is selected before the reference/high jet budgets. The
scalar cutoff is subsequently chosen inside its fixed spatial buffer (by the
full-normal scalar construction), and its inner radius is supplied as an
original seed cap. This preserves the SAME measured/source cutoffs. All scalar
phase data below are constructed from the actual projected stress, with no
normal-chart or operator-bound premise (`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase NormalComparison RawPrimary
open RawPrimary.SliceGeometry RawPrimary.SliceBounds RawInputPartition Sampling FullPhaseCharts.ActualPhase
open ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Choose the original slice buffers before the scalar cutoff, all history
bounds and the current map; then produce its actual canonical scalar normal
family from the SAME projected stress. -/
theorem exists_retained_scalarSliceFamily (hn : 2 ≤ n)
    {c C : ℝ} (hP : P.IsValid c C)
    {amax bmax emax : ℝ} (hamax : 0 < amax) (hbmax : 0 < bmax) (hemax : 0 < emax) :
    ∃ a > (0 : ℝ), 4 * a ≤ amax ∧ 4 * a < T.family.radius ∧
    ∃ b > (0 : ℝ), b ≤ bmax ∧
      (∀ z ∈ parameterCube P.radius, ball (T.reference.spatialPatch z) b ⊆
        ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ 16 * e < b ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ G : UniformNormalGeometry (n - 1) n,
      G.X = sliceSpatialDomain n a ∧ G.D = sliceInputDomain n ∧
      G.X₀ = sliceSpatialCore n a ∧ G.D₀ = sliceInputCore n ∧ G.ε₀ = e ∧
    ∀ (χ : ContDiffBump (0 : Euclidean n)),
      tsupport (χ : Euclidean n → ℝ) ⊆ closedBall 0 (a / 4) →
    ∀ (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ),
      (∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) →
      (∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ) →
      ContDiff ℝ ∞ H → (∀ η, 2 ≤ ‖η‖ → H η = 1) →
    ∀ {K : Set (Euclidean n)}, IsCompact K → K ⊆ U →
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) →
    ∀ (M : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ →
    ∃ Cscalar : ℕ → ℝ, (∀ k, 0 < Cscalar k) ∧
    ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
      (hrank : HasFullNormalRankOn F U),
      cNorm K (20 * ((n - 1) + 1) + 5) F ≤ M →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δ →
      ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ z ∈ parameterCube P.radius,
      ∃ Ns : ℕ → (t : ℝ) → t ∈ Ioo (-a) a → UniformNormalData G Cscalar,
        (∀ j t (ht : t ∈ Ioo (-a) a), (Ns j t ht).phase = fun ε y η ↦
          rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)
            (ε, (t, y), η)) ∧
        (∀ j t (ht : t ∈ Ioo (-a) a), (Ns j t ht).amplitude = fun _ y η ↦
          scalarSliceAmplitude T.data.adapted χ angular H (by omega) j (t, y, η)) := by
  obtain ⟨a, ha, hacap, haR, b, hb, hbcap, hbcov, e, he, hecap, heb,
    δ, hδ, hδcap, G, hX, hD, hX₀, hD₀, hε, _hband, _hcore, hbudgets⟩ :=
    exists_uniform_canonicalSliceNormalData_before_immersion_bounds T hn hP hamax hbmax hemax
  refine ⟨a, ha, hacap, haR, b, hb, hbcap, hbcov, e, he, hecap, heb,
    δ, hδ, hδcap, scalarSliceGeometry (by omega) G, hX, hD, hX₀, hD₀, hε, ?_⟩
  intro χ hχ angular H hang hah hH hH₁ K hK hKU hball M γ κ hγ hκ
  obtain ⟨Cphase, hCphase, hphase⟩ := hbudgets hK hKU hball M hγ hκ
  obtain ⟨Camp, hCamp, hamp⟩ := exists_scalarSliceNormalData T.data.adapted χ angular H
    hang hah hH hH₁ (by omega) G Cphase ha hX₀ hD₀ hχ
  refine ⟨fun k ↦ Cphase k + Camp k, fun k ↦ add_pos (hCphase k) (hCamp k), ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hsmall
  obtain ⟨hlow, hfamily⟩ := hphase F hF hi hrank hFM hmetric hnormal hsmall
  refine ⟨hlow, ?_⟩
  intro Q z hz
  obtain ⟨N₀, hN₀⟩ := hfamily z hz
  choose Ns hNs using fun j t ht ↦ hamp t ht j (N₀ t ht)
  refine ⟨Ns, ?_, ?_⟩
  · intro j t ht
    exact (hNs j t ht).1.trans (hN₀ t ht).1
  · intro j t ht
    exact (hNs j t ht).2.2.2

end JanetCartan.PhysicalSampling
