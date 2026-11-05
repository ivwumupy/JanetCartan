module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.UniformSliceGeometry.InverseGeometry

/-!
# Actual uniform transverse gradient gap on original annular inputs

Retain the value comparison that the original inverse-geometry proof discarded.
The current full phase, original closed carrier cube and physical coordinates are
unchanged. Finite subcover minima precede immersion bounds, reference selection,
all source scales, and samples. On the original radial annulus the averaged
transverse phase gradient is bounded away from zero, which is the missing input
to a band-count-independent scalar slice normal estimate.

Consumer: `Sampling.MeanNormalBound.exists_uniform_powTwoNormal_bound`, for
`new:eq:amplitude-test` and the individual adjoint moment bounds.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalScalarChannel
open RawPrimary.SliceGeometry ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu NormalComparison
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

private theorem spacetime_mem_ball {r a t : ℝ} {y : Euclidean (n - 1)}
    (har : 2 * a ≤ r) (ht : t ∈ Ioo (-a) a) (hy : y ∈ sliceSpatialDomain n a) :
    WithLp.toLp 2 (t, y) ∈ ball 0 r := by
  have hn : ‖WithLp.toLp 2 (t, y)‖ ≤ |t| + ‖y‖ := by
    have hh := norm_add_le (WithLp.toLp 2 (t, (0 : Euclidean (n - 1))))
      (WithLp.toLp 2 ((0 : ℝ), y))
    have he : WithLp.toLp 2 (t, (0 : Euclidean (n - 1))) +
        WithLp.toLp 2 ((0 : ℝ), y) = WithLp.toLp 2 (t, y) := by
      apply WithLp.ofLp_injective
      simp
    rw [he] at hh
    simpa only [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd, Real.norm_eq_abs] using hh
  have ht' := abs_lt.mpr ht
  have hy' : ‖y‖ < a := mem_ball_zero_iff.mp hy
  rw [mem_ball, dist_zero_right]
  linarith

/-- The literal current transverse averaged gradient is within `1/4` of its
original input on the full radius-three ball, uniformly over the SAME closed
carrier cube. All geometric choices precede the current map. -/
theorem exists_uniform_scalar_transverse_comparison {c C : ℝ} (hP : P.IsValid c C)
    {amax emax : ℝ} (hamax : 0 < amax) (hemax : 0 < emax) :
    ∃ a > (0 : ℝ), a ≤ amax ∧ ∃ e > (0 : ℝ), e ≤ emax ∧
    ∃ δ > (0 : ℝ), ∀ z ∈ parameterCube P.radius, ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ t ∈ Ioo (-a) a, ∀ ε ∈ Icc 0 e,
      ∀ x ∈ sliceSpatialDomain n a, ∀ y ∈ sliceSpatialDomain n a,
      ∀ η ∈ closedBall (0 : Euclidean (n - 1)) 3,
        ‖averagedGradient (canonicalSlicePhase T Q z t ε) x y η - η‖ < (1 / 4 : ℝ) := by
  classical
  choose r hr hrR hbox using
    fun z : parameterCube P.radius ↦ exists_slice_comparison_radius T hP z.2
  choose d hd ec hec hcomp using fun z : parameterCube P.radius ↦
    exists_slice_transverse_comparison T hP z.1 (hrR z) (hbox z) (by norm_num : (0 : ℝ) < 1 / 4)
  let O (z : parameterCube P.radius) : Set (Euclidean 3) :=
    {w | spectatorCenter w ∈ ball (spectatorCenter z.1) (r z) ∧
      w 0 ∈ ball (z.1 0) (r z)}
  have hO (z) : IsOpen (O z) := by
    apply IsOpen.inter
    · exact isOpen_ball.preimage (by unfold spectatorCenter; fun_prop)
    · exact isOpen_ball.preimage (by fun_prop)
  have hcover : parameterCube P.radius ⊆ ⋃ z : parameterCube P.radius, O z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr _), mem_ball_self (hr _)⟩
  obtain ⟨centers, hcenters⟩ := (isCompact_parameterCube P.radius).elim_finite_subcover O hO hcover
  obtain ⟨a₁, δ, _, ha₁, _, hδ, _, hcommon⟩ := exists_common_phase_buffers
    (fun j : centers ↦ r j.1) (fun j : centers ↦ d j.1) (fun _ ↦ (0 : ℝ))
    (fun j ↦ hr j.1) (fun j ↦ hd j.1)
  obtain ⟨e₁, _, _, he₁, _, _, _, hecommon⟩ := exists_common_phase_buffers
    (fun j : centers ↦ ec j.1) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
    (fun j ↦ hec j.1) (fun _ ↦ zero_lt_one)
  let a := min amax a₁
  let e := min emax e₁
  have ha : 0 < a := lt_min hamax ha₁
  have he : 0 < e := lt_min hemax he₁
  refine ⟨a, ha, min_le_left _ _, e, he, min_le_left _ _, δ, hδ, ?_⟩
  intro z hz Q hQ t ht ε hε x hx y hy η hη
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcenters hz)
  obtain ⟨hj', hzj⟩ := mem_iUnion.mp hj
  let i : centers := ⟨j, hj'⟩
  have hee : e < ec j := by
    have := (hecommon i).1
    have : e ≤ e₁ := min_le_right _ _
    linarith
  have har : 2 * a ≤ r j := by
    have := (hcommon i).1
    have : a ≤ a₁ := min_le_right _ _
    linarith
  have hp : (ε, spectatorCenter z, t, z 0, x, y) ∈
      transverseParameterSet j.1 (r j) (ec j) :=
    ⟨⟨by linarith [hε.1], hε.2.trans_lt hee⟩, hzj.1, hzj.2,
      spacetime_mem_ball har ht hx, spacetime_mem_ball har ht hy⟩
  rw [averagedGradient_canonicalSlicePhase]
  exact (hcomp j Q (hQ.trans_le (hcommon i).2.1) _ hp η hη).1

end JanetCartan.PhysicalScalarChannel
