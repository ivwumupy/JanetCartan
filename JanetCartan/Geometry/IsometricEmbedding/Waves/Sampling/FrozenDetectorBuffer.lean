module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.TransverseDetectorCover
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# Original incidence-domain buffers in the literal sampling coordinates

At an incident covector, the normalized frozen input map takes the original
adapted direction back to that same physical direction. Continuity constructs
carrier and angular buffers inside any prescribed original open incidence
chart. These are the `hchart` inputs of `transverseDetectorIncidenceSupport_spec`
for cutoffs supported in the returned buffers, chosen before current fields.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric NormedSpace Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open FullPhaseCharts.ActualPhase ContinuumRow.CanonicalConic

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Continuity of the literal normalized physical input covector, with its
original carrier and transverse coordinates (`app:ch_seed:prop:seed-phase-charts`). -/
theorem continuousAt_normalize_frozenInputCovector {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {θ : Euclidean (n - 1)} (hθ : θ ≠ 0) :
    ContinuousAt (fun q : Euclidean 3 × Euclidean (n - 1) ↦
      normalize (frozenInputCovector T q.1 q.2)) (z, θ) := by
  have hzD := parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz i).le)
  have hg : ContinuousAt
      (fun w : Euclidean 3 ↦ gradient (dispersion T) (T.reference.spatialPatch w)) z :=
    ((FrozenIncidence.patch_gradient_smooth T hP).contDiffAt
      ((isOpen_parameterInterior _).mem_nhds hzD)).continuousAt
  have hgrad : ContinuousAt
      (fun q : Euclidean 3 × Euclidean (n - 1) ↦
        gradient (dispersion T) (T.reference.spatialPatch q.1)) (z, θ) :=
    ContinuousAt.comp
      (g := fun w : Euclidean 3 ↦ gradient (dispersion T) (T.reference.spatialPatch w))
      (f := fun q : Euclidean 3 × Euclidean (n - 1) ↦ q.1) (x := (z, θ))
      hg continuousAt_fst
  have hinner : ContinuousAt
      (fun q : Euclidean 3 × Euclidean (n - 1) ↦
        inner ℝ (gradient (dispersion T) (T.reference.spatialPatch q.1)) q.2) (z, θ) :=
    hgrad.inner (𝕜 := ℝ) continuousAt_snd
  have hembed : ContinuousAt
      (fun q : Euclidean 3 × Euclidean (n - 1) ↦ T.data.adapted.embedding q.2) (z, θ) :=
    (T.data.adapted.embedding.continuous.comp continuous_snd).continuousAt
  have hnormal : ContinuousAt
      (fun _ : Euclidean 3 × Euclidean (n - 1) ↦ T.data.adapted.normal) (z, θ) :=
    continuousAt_const
  have hc : ContinuousAt
      (fun q : Euclidean 3 × Euclidean (n - 1) ↦ frozenInputCovector T q.1 q.2) (z, θ) :=
    (hinner.smul hnormal).add hembed
  exact (hc.norm.inv₀ (norm_ne_zero_iff.mpr
    (frozenInputCovector_ne_zero T z hθ))).smul hc

/-- At every original incidence pair, the input direction maps to the SAME
normalized physical covector. No independently chosen chart is identified
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem normalize_frozenInputCovector_of_incidence {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z) = 0) :
    normalize (frozenInputCovector T z
      (normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k))) = normalize k := by
  have he := FrozenIncidence.tangential_direction_ne_zero T hP hz hk hinc
  change normalize (frozenInputCovector T z
    (‖T.data.adapted.embedding.toContinuousLinearMap.adjoint k‖⁻¹ •
      T.data.adapted.embedding.toContinuousLinearMap.adjoint k)) = _
  rw [frozenInputCovector_smul, frozenInputCovector_of_incidence T hP hz hinc,
    normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr he))]

/-- Passing from the nonzero detector to its closed unit-direction support
preserves the literal canonical cone, including its boundary. The closed
homogeneous cone also contains the origin, so no continuity of normalization
at zero is used. This supplies the full-support input of
`transverseDetectorIncidenceSupport_spec` (`app:ch_waves:thm:sampling`). -/
theorem detectorDirectionSupport_subset_closedDirections
    (a : Euclidean (n - 1) → ℂ) (ηb : Euclidean (n - 1)) (r : ℝ)
    (hsupport : ∀ η, a η ≠ 0 → normalize η ∈ closedDirections ηb r) :
    detectorDirectionSupport a ⊆ closedDirections ηb r := by
  let cone : Set (Euclidean (n - 1)) :=
    {η | ‖η - ‖η‖ • normalize ηb‖ ≤ (angularWidth (n := n) ηb r / 2) * ‖η‖}
  have hc : IsClosed cone := isClosed_le (by fun_prop) (by fun_prop)
  have ht : tsupport a ⊆ cone := by
    apply closure_minimal _ hc
    intro η hη
    have hd : ‖normalize η - normalize ηb‖ ≤ angularWidth (n := n) ηb r / 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using (hsupport η hη).2
    change ‖η - ‖η‖ • normalize ηb‖ ≤ _
    calc
      _ = ‖‖η‖ • (normalize η - normalize ηb)‖ := by
        rw [smul_sub, norm_smul_normalize]
      _ = ‖η‖ * ‖normalize η - normalize ηb‖ := by
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
      _ ≤ ‖η‖ * (angularWidth (n := n) ηb r / 2) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ = _ := mul_comm _ _
  intro θ hθ
  have hn : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ.1
  have hb := ht hθ.2
  refine ⟨hθ.1, ?_⟩
  simpa only [cone, mem_ofPred_eq, hn, one_smul, mul_one, mem_closedBall,
    dist_eq_norm] using hb

/-- Construct closed carrier and angular buffers inside the ORIGINAL open
incidence domain. Every smaller returned local angular radius remains valid.
This supplies the chart-domain premise for `transverseDetectorIncidenceSupport_spec`
without assuming a coordinate-equivalence or discarding any point of a later
finite cover (`app:ch_waves:thm:sampling`). -/
theorem exists_frozenDetector_chart_buffer {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    {O : Set (Euclidean n)} (hO : IsOpen O) (hkO : normalize k ∈ O)
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ d > (0 : ℝ), ∃ r > (0 : ℝ), r ≤ rmax ∧
      closedBall z₀ d ⊆ parameterInterior P.radius ∧
      (∀ r' : ℝ, r' ≤ r → ∀ z ∈ closedBall z₀ d,
        ∀ θ ∈ closedDirections
          (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) r',
          normalize (frozenInputCovector T z θ) ∈ O) ∧
      ∀ r' : ℝ, r' ≤ r → ∀ Z : Set (Euclidean 3), Z ⊆ closedBall z₀ d →
        ∀ a : Euclidean (n - 1) → ℂ,
          (∀ η, a η ≠ 0 → normalize η ∈ closedDirections
            (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) r') →
          ∀ z ∈ Z, ∀ θ ∈ detectorDirectionSupport a,
            normalize (frozenInputCovector T z θ) ∈ O := by
  let η := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hη : η ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hθ : normalize η ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_normalize hη]; norm_num)
  have hc := continuousAt_normalize_frozenInputCovector T hP hz₀ hθ
  have he : normalize (frozenInputCovector T z₀ (normalize η)) ∈ O := by
    rw [normalize_frozenInputCovector_of_incidence T hP hz₀ hk hinc]
    exact hkO
  have hN : (parameterInterior P.radius ×ˢ (univ : Set (Euclidean (n - 1)))) ∩
      (fun q : Euclidean 3 × Euclidean (n - 1) ↦
        normalize (frozenInputCovector T q.1 q.2)) ⁻¹' O ∈ 𝓝 (z₀, normalize η) :=
    inter_mem ((isOpen_parameterInterior _).prod isOpen_univ |>.mem_nhds ⟨hz₀, mem_univ _⟩)
      (hc.preimage_mem_nhds (hO.mem_nhds he))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  let d := ε / 2
  let r := min rmax (4 * ‖η‖ * ε)
  have hd : 0 < d := half_pos hε
  have hr : 0 < r := lt_min hrmax (mul_pos (mul_pos (by norm_num) (norm_pos_iff.mpr hη)) hε)
  have hwidth : angularWidth (n := n) η r / 2 ≤ ε / 4 := by
    have hnorm := norm_pos_iff.mpr hη
    have hh : angularWidth (n := n) η r ≤ ε / 2 := by
      apply (min_le_right _ _).trans
      apply (div_le_iff₀ (by positivity : 0 < 8 * ‖η‖)).mpr
      dsimp [r]
      nlinarith [min_le_right rmax (4 * ‖η‖ * ε)]
    linarith
  have hpair (z : Euclidean 3) (hz : z ∈ closedBall z₀ d)
      (θ : Euclidean (n - 1)) (hθ : dist θ (normalize η) ≤ ε / 2) :
      (z, θ) ∈ ball (z₀, normalize η) ε := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hz).trans_lt (by dsimp [d]; linarith), hθ.trans_lt (by linarith)⟩
  have hinside (r' : ℝ) (hr' : r' ≤ r) (z : Euclidean 3)
      (hz : z ∈ closedBall z₀ d) (θ : Euclidean (n - 1))
      (hθ' : θ ∈ closedDirections η r') :
      normalize (frozenInputCovector T z θ) ∈ O := by
    have hθr : θ ∈ closedDirections η r := closedDirections_mono η hr' hθ'
    exact (hball (hpair z hz θ ((mem_closedBall.mp hθr.2).trans
      (hwidth.trans (by linarith))))).2
  refine ⟨d, hd, r, hr, min_le_left _ _, ?_, hinside, ?_⟩
  · intro z hz
    exact (hball (hpair z hz (normalize η) (by simpa using hd.le))).1.1
  · intro r' hr' Z hZ a ha z hz θ hθ'
    exact hinside r' hr' z (hZ hz) θ
      (detectorDirectionSupport_subset_closedDirections (n := n) a η r' ha hθ')

end JanetCartan.Sampling
