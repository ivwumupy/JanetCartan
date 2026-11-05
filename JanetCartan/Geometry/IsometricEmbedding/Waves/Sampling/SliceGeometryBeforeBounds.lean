module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.UniformSliceGeometry

/-!
# Canonical slice geometry before immersion budgets

The existing domain and inverse geometry constructors make their choices
before the immersion enters the phase-budget theorem. Retain that order for
the corrected sharp-band application, so its source cap and physical cutoffs
can be fixed before the initialized reference and its quantitative gaps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling
open RawPrimary RawPrimary.UniformSliceGeometry
open SliceGeometry ActualCarriers FrozenMenu CurrentFullPhase SliceBounds NormalComparison
open FullPhaseCharts.ActualPhase ProjectedStressFrame RawInputPartition
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (n - 1)

/-- Choose the original slice radii, frame tolerance and normal geometry
before immersion bounds and metric/normal gaps. The existing domain and
inverse-geometry producers supply those witnesses; only the phase budgets
use the later quantitative data. This strengthens the order of choices in
`RawPrimary.UniformSliceGeometry.exists_uniform_canonicalSliceNormalData`
without changing its original phase, input core or derivative reserve.
Consumer: `exists_uniform_canonical_cutCorrectedSliceSobolev_before_immersion_bounds`
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_uniform_canonicalSliceNormalData_before_immersion_bounds (hn : 2 ≤ n)
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {amax bmax emax : ℝ} (hamax : 0 < amax) (hbmax : 0 < bmax) (hemax : 0 < emax) :
    ∃ a > (0 : ℝ), 4 * a ≤ amax ∧ 4 * a < T.family.radius ∧
    ∃ b > (0 : ℝ), b ≤ bmax ∧
      (∀ z ∈ parameterCube P.radius, ball (T.reference.spatialPatch z) b ⊆
        ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ 16 * e < b ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ G : UniformNormalGeometry (n - 1) (embeddingDimension n * n),
      G.X = sliceSpatialDomain n a ∧ G.D = sliceInputDomain n ∧
      G.X₀ = sliceSpatialCore n a ∧ G.D₀ = sliceInputCore n ∧ G.ε₀ = e ∧
      wideBand n 0 ⊆ G.D₀ ∧
      (∀ t ∈ Ioo (-a) a, ∀ ε ∈ Icc 0 G.ε₀,
        ∀ w ∈ closure G.X ×ˢ closure G.D,
          (ε, (t, w.1), w.2) ∈ sliceClosedCore n a e) ∧
    ∀ {K : Set (Euclidean n)} (_hK : IsCompact K) (_hKU : K ⊆ U)
    (_hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (_hγ : 0 < γ) (_hκ : 0 < κ),
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm K (20 * ((n - 1) + 1) + 5) F ≤ M →
        (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ z ∈ parameterCube P.radius, ∃ N : (t : ℝ) → t ∈ Ioo (-a) a → UniformNormalData G C,
          ∀ t (ht : t ∈ Ioo (-a) a),
            (N t ht).phase = (fun ε y η ↦ rawSlicePhaseExtension
              (fun q ξ ↦ LeadingWave.FullModulation.phase T Q
                (adaptedPhysicalCoordinates T.data.adapted q) ξ)
              (T.reference.spatialPatch z) (ε, (t, y), η)) ∧
            (N t ht).amplitude = 0 ∧
            (N t ht).parameterDomain = sliceParameterDomain e ∧
            (N t ht).extensionDomain = sliceExtensionDomain n a ∧
            MapsTo (fun q : ℝ × (E × E) ↦ (q.1, (t, q.2.1), q.2.2))
              ((N t ht).parameterDomain ×ˢ (N t ht).extensionDomain)
              (sliceShiftDomain T a e) := by
  obtain ⟨a₀, ha₀, ha₀cap, ha₀R, b, hb, hbcap, hbcov, e₀, he₀, he₀b⟩ :=
    exists_uniform_slice_domain_radii T hP hamax hbmax
  obtain ⟨a, ha, haa₀, e, he, hecap, δ₀, hδ₀, β, hβ, c, hc, V, hV, hVc, hinverse⟩ :=
    exists_uniform_slice_inverse_geometry T hP ha₀ (lt_min he₀ hemax)
  have hacap : 4 * a ≤ amax := (by linarith : 4 * a ≤ 4 * a₀).trans ha₀cap
  have haR : 4 * a < T.family.radius := lt_of_le_of_lt (by linarith) ha₀R
  have hemax' : e ≤ emax := hecap.trans (min_le_right e₀ emax)
  have heb : 16 * e < b := by
    have := hecap.trans (min_le_left e₀ emax)
    linarith
  let δ := min δ₀ T.family.threshold
  have hδ : 0 < δ := lt_min hδ₀ T.family.threshold_pos
  let G := sliceNormalGeometry hn ha he hβ hc V hV hVc
  refine ⟨a, ha, hacap, haR, b, hb, hbcap, hbcov, e, he, hemax', heb,
    δ, hδ, min_le_right _ _, G, rfl, rfl, rfl, rfl, rfl,
    wideBand_zero_subset_sliceInputCore, ?_, ?_⟩
  · intro t ht ε hε w hw
    exact sliceClosedCore_contains ht hε hw
  · intro K hK hKU hball M γ κ hγ hκ
    obtain ⟨C, hC, hbudget⟩ := exists_uniform_canonicalSlicePhase_input_budgets T hP
      ha haR he heb hbcov hK hKU hball M hγ hκ
    refine ⟨C, hC, ?_⟩
    intro F hF hi hrank hFM hmet hnormal hsmall
    have hlow := hsmall.trans_le (min_le_right δ₀ T.family.threshold)
    refine ⟨hlow, ?_⟩
    intro Q z hz
    have hsmall₀ := hsmall.trans_le (min_le_left δ₀ T.family.threshold)
    let N (t : ℝ) (ht : t ∈ Ioo (-a) a) : UniformNormalData G C := {
      phase := canonicalSlicePhase T Q z t
      amplitude := 0
      parameterDomain := sliceParameterDomain e
      extensionDomain := sliceExtensionDomain n a
      isOpen_parameterDomain := isOpen_Ioo
      isOpen_extensionDomain := isOpen_ball.prod isOpen_ball
      parameter_subset := sliceParameterDomain_contains he
      spatial_subset := sliceExtensionDomain_contains ha
      phase_smooth := canonicalSlicePhase_smooth T Q z ha haR he heb (hbcov z hz) ht
      amplitude_smooth := contDiffOn_const
      amplitude_support := by simp
      input_jets := by
        intro ε hε w hw k hk
        simpa only [Pi.zero_apply, Function.uncurry_def, iteratedFDeriv_fun_zero,
          norm_zero, add_zero, deriv_const] using
          hbudget F hF hi hrank hFM hmet hnormal hlow z hz t ht ε hε w hw k hk
      gradient_injective := fun ε hε x hx y hy ↦
        (hinverse z hz Q hsmall₀ t ht ε hε x hx y hy).1
      image_buffer := fun ε hε x hx y hy ↦
        (hinverse z hz Q hsmall₀ t ht ε hε x hx y hy).2.1
      chart_buffer := fun ε hε x hx y hy ↦
        (hinverse z hz Q hsmall₀ t ht ε hε x hx y hy).2.2.1
      jacobian_gap := fun ε hε x hx y hy ↦
        (hinverse z hz Q hsmall₀ t ht ε hε x hx y hy).2.2.2 }
    exact ⟨N, fun t ht ↦
      ⟨rfl, rfl, rfl, rfl, sliceExtensionDomain_mapsTo_shiftDomain T ha ht⟩⟩


end JanetCartan.Sampling
