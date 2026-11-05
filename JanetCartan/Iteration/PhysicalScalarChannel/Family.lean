module

public import JanetCartan.Iteration.PhysicalScalarChannel.Annulus
public import JanetCartan.Iteration.PhysicalSampling.SliceGeometry

/-!
# Actual full-band scalar slice normals before the current immersion

The original carrier cube comparison is chosen first. The existing scalar slice
constructor then uses smaller physical and epsilon radii. Only its certified
radial support is restricted; its original phase, amplitude, integration domain
and operators remain literal. The resulting complete dyadic normal sum is bounded
uniformly before histories, samples and the number of shells. This is the slice
input to the full unweighted scalar tester in `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalScalarChannel
open ActualCarriers FrozenMenu CurrentFullPhase NormalComparison RawPrimary
open RawPrimary.SliceGeometry RawInputPartition Sampling PhysicalSampling FullPhaseCharts.ActualPhase
open ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The actual original scalar slice family has a full-band normal bound with
no logarithm, sample count, or inverse sample weight. Every analytic phase and
amplitude premise is discharged by the original current-immersion constructors. -/
theorem exists_retained_scalar_full_band_slice_family (hn : 2 ≤ n)
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
      G.X₀ = sliceSpatialCore n a ∧
      G.D₀ = sliceInputCore n ∩ {η | (1 / 2 : ℝ) ≤ ‖η‖} ∧ G.ε₀ = e ∧
    ∀ (χ : ContDiffBump (0 : Euclidean n)),
      tsupport (χ : Euclidean n → ℝ) ⊆ closedBall 0 (a / 4) →
    ∀ (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ),
      (∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) →
      (∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ) →
      ContDiff ℝ ∞ H → (∀ η, 2 ≤ ‖η‖ → H η = 1) →
    ∀ {K : Set (Euclidean n)}, IsCompact K → K ⊆ U →
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) →
    ∀ (M : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ →
    ∃ Cscalar : ℕ → ℝ, (∀ k, 0 < Cscalar k) ∧ ∃ Csum > (0 : ℝ),
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
        (∀ j t (ht : t ∈ Ioo (-a) a), (Ns j t ht).phase = canonicalSlicePhase T Q z t) ∧
        (∀ j t (ht : t ∈ Ioo (-a) a), (Ns j t ht).amplitude = fun _ y η ↦
          scalarSliceAmplitude T.data.adapted χ angular H (by omega) j (t, y, η)) ∧
        ∀ (J : ℕ) (ε : Fin J → ℝ), (∀ j, ε j ∈ Icc 0 G.ε₀) →
        ∀ t (ht : t ∈ Ioo (-a) a),
          ‖∑ j, ((Ns j.val t ht).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).comp
            ((Ns j.val t ht).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).adjoint‖ ≤ Csum := by
  obtain ⟨ac, hac, haccap, ec, hec, heccap, δc, hδc, hcompare⟩ :=
    exists_uniform_scalar_transverse_comparison T hP hamax hemax
  obtain ⟨a, ha, hacap, haR, b, hb, hbcap, hbcov, e, he, hecap, heb,
    δ₀, hδ₀, hδ₀cap, G, hX, hD, hX₀, hD₀, hε, hfamily⟩ :=
    exists_retained_scalarSliceFamily T hn hP hac hbmax hec
  have haac : a ≤ ac := by linarith
  let δ := min δ₀ δc
  let G' := annularGeometry G
  refine ⟨a, ha, hacap.trans haccap, haR, b, hb, hbcap, hbcov, e, he,
    hecap.trans heccap, heb, δ, lt_min hδ₀ hδc,
    (min_le_left _ _).trans hδ₀cap, G', hX, hD, hX₀, ?_, hε, ?_⟩
  · change G.D₀ ∩ {η | (1 / 2 : ℝ) ≤ ‖η‖} = _
    rw [hD₀]
  · intro χ hχ angular H hang hah hH hH₁ K hK hKU hball M γ κ hγ hκ
    obtain ⟨Cscalar, hCscalar, hcurrent⟩ :=
      hfamily χ hχ angular H hang hah hH hH₁ hK hKU hball M hγ hκ
    obtain ⟨Csum, hCsum, hsum⟩ :=
      MeanNormalBound.exists_uniform_powTwoNormal_bound G' Cscalar (by norm_num : (0 : ℝ) < 1 / 4)
    refine ⟨Cscalar, hCscalar, Csum, hCsum, ?_⟩
    intro F hF hi hrank hFM hmetric hnormal hsmall
    obtain ⟨hlow, hN⟩ := hcurrent F hF hi hrank hFM hmetric hnormal
      (hsmall.trans_le (min_le_left _ _))
    refine ⟨hlow, ?_⟩
    intro Q z hz
    obtain ⟨Ns, hphase, hamp⟩ := hN z hz
    have hann (j : ℕ) (t : ℝ) (ht : t ∈ Ioo (-a) a) :
        ∀ ε ∈ Icc 0 G.ε₀, ∀ x η, (Ns j t ht).amplitude ε x η ≠ 0 → (1 / 2 : ℝ) ≤ ‖η‖ := by
      intro ε _ x η hnonzero
      rw [hamp j t ht] at hnonzero
      exact scalarSliceAmplitude_annular T.data.adapted χ angular H (by omega) j t x η hnonzero
    let Ns' := fun j t ht ↦ annularData (Ns j t ht) (hann j t ht)
    refine ⟨Ns', ?_, ?_, ?_⟩
    · intro j t ht
      exact hphase j t ht
    · intro j t ht
      exact hamp j t ht
    · intro J ε hεs t ht
      apply hsum J (fun j ↦ Ns' j.val t ht) ε hεs
      intro j x hx y hy η hη
      apply averagedGradient_gap_of_annular_comparison _ x y η hη.2
      change ‖averagedGradient ((Ns j.val t ht).phase (ε j)) x y η - η‖ < (1 / 4 : ℝ)
      rw [hphase j.val t ht]
      apply hcompare z hz Q (hsmall.trans_le (min_le_right _ _)) t
        ⟨by linarith [ht.1], ht.2.trans_le haac⟩ (ε j)
        ⟨(hεs j).1, ((hεs j).2.trans_eq hε).trans hecap⟩
      · have hx' : x ∈ sliceSpatialCore n a := hX₀ ▸ hx
        exact closedBall_subset_ball (by linarith : a / 2 < ac) hx'
      · have hy' : y ∈ sliceSpatialCore n a := hX₀ ▸ hy
        exact closedBall_subset_ball (by linarith : a / 2 < ac) hy'
      · have hη' : η ∈ sliceInputCore n := hD₀ ▸ hη.1
        exact closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 3) hη'

end JanetCartan.PhysicalScalarChannel
