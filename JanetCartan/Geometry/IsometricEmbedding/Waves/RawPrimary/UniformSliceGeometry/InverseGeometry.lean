module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.InverseGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

/-!
# Common inverse geometry over the original closed carrier cube

An actual finite open cover of the closed cube is extracted from the existing
transverse comparison neighborhoods. The inverse theorem chooses its image,
buffers and determinant gap once, before this cover and before any carrier is
sampled. Finite minima give common physical and epsilon radii and a common
state-ball frame threshold for `exists_uniform_canonicalSliceNormalData`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.UniformSliceGeometry
open SliceGeometry ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu NormalComparison
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

/-- Common inverse geometry before the carrier ranges over its original
closed cube. The finite localization covers every original label, uses the
SAME phase and leaves the radius-two core, radius-three injectivity domain and
radius-four smooth extension intact. This supplies the inverse fields of
`exists_uniform_canonicalSliceNormalData`
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:setup:oscillatory`). -/
theorem exists_uniform_slice_inverse_geometry {c C : ℝ} (hP : P.IsValid c C)
    {amax emax : ℝ} (hamax : 0 < amax) (hemax : 0 < emax) :
    ∃ a > (0 : ℝ), a ≤ amax ∧ ∃ e > (0 : ℝ), e ≤ emax ∧
    ∃ δ > (0 : ℝ), ∃ β > (0 : ℝ), ∃ γ > (0 : ℝ),
    ∃ V : Set (Euclidean (n - 1)), IsOpen V ∧ IsCompact (closure V) ∧
      ∀ z ∈ parameterCube P.radius, ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        ∀ t ∈ Ioo (-a) a, ∀ ε ∈ Icc 0 e,
        ∀ x ∈ sliceSpatialDomain n a, ∀ y ∈ sliceSpatialDomain n a,
          InjOn (averagedGradient (canonicalSlicePhase T Q z t ε) x y)
            (sliceInputDomain n) ∧
          cthickening β
            (averagedGradient (canonicalSlicePhase T Q z t ε) x y '' sliceInputCore n) ⊆ V ∧
          cthickening β (closure V) ⊆
            averagedGradient (canonicalSlicePhase T Q z t ε) x y '' sliceInputDomain n ∧
          ∀ η ∈ sliceInputDomain n,
            γ ≤ |(fderiv ℝ (averagedGradient (canonicalSlicePhase T Q z t ε) x y) η).det| := by
  classical
  obtain ⟨γ, hγ, β, hβ, V, L, hV, hVc, _, _, hinv⟩ :=
    exists_transverseChart_inverseFamily (P := Euclidean 2)
      (isCompact_closedBall (0 : Euclidean (n - 1)) 2) isOpen_ball
      (closedBall_subset_ball (by norm_num : (2 : ℝ) < 3)) ball_subset_closedBall
      (convex_closedBall (0 : Euclidean (n - 1)) 3)
  let τ := min β (1 / 4)
  have hτ : 0 < τ := lt_min hβ (by norm_num)
  choose r hr hrR hbox using
    fun z : parameterCube P.radius ↦ exists_slice_comparison_radius T hP z.2
  choose es hes hsmooth using fun z : parameterCube P.radius ↦
    exists_slice_transverse_smooth T hP z.1 (hrR z).le (hbox z)
  choose d hd ec hec hcomp using fun z : parameterCube P.radius ↦
    exists_slice_transverse_comparison T hP z.1 (hrR z) (hbox z) hτ
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
    (fun j : centers ↦ min (es j.1) (ec j.1)) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
    (fun j ↦ lt_min (hes j.1) (hec j.1)) (fun _ ↦ zero_lt_one)
  let a := min amax a₁
  let e := min emax e₁
  have ha : 0 < a := lt_min hamax ha₁
  have he : 0 < e := lt_min hemax he₁
  refine ⟨a, ha, min_le_left _ _, e, he, min_le_left _ _, δ, hδ, β, hβ,
    γ, hγ, V, hV, hVc, ?_⟩
  intro z hz Q hQ
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcenters hz)
  obtain ⟨hj', hzj⟩ := mem_iUnion.mp hj
  let i : centers := ⟨j, hj'⟩
  let e₀ := min (es j) (ec j)
  have hee : e < e₀ := by
    have := (hecommon i).1
    have : e ≤ e₁ := min_le_right _ _
    dsimp only [e₀]
    linarith
  have har : 2 * a ≤ r j := by
    have := (hcommon i).1
    have : a ≤ a₁ := min_le_right _ _
    linarith
  have hparam {b : ℝ} (hb : e₀ ≤ b) :
      transverseParameterSet (n := n) j.1 (r j) e₀ ⊆
        transverseParameterSet j.1 (r j) b := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2.trans_le hb⟩, hp.2⟩
  have hc := fun p hp η hη ↦ hcomp j Q (hQ.trans_le (hcommon i).2.1)
    p (hparam (min_le_right _ _) hp) η hη
  have hs : ContDiffOn ℝ ∞
      (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
      (transverseParameterSet j.1 (r j) e₀ ×ˢ sliceInputExtension n) :=
    (hsmooth j Q).mono (prod_mono (hparam (min_le_left _ _)) Subset.rfl)
  have hi := hinv (current T Q) (spatialCarrier T)
    (transverseParameterSet j.1 (r j) e₀) (sliceInputExtension n)
    (isOpen_transverseParameterSet j.1 (r j) e₀) isOpen_ball
    (closedBall_subset_ball (by norm_num : (3 : ℝ) < 4)) hs
    (fun p hp η hη ↦ (hc p hp η hη).2.le.trans (min_le_right β (1 / 4)))
    (fun p hp η hη ↦ (hc p hp η
      (closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 3) hη)).1.le.trans
        (min_le_left β (1 / 4)))
  intro t ht ε hε x hx y hy
  have hp : (ε, spectatorCenter z, t, z 0, x, y) ∈
      transverseParameterSet j.1 (r j) e₀ :=
    ⟨⟨by linarith [hε.1], hε.2.trans_lt hee⟩, hzj.1, hzj.2,
      spacetime_mem_ball har ht hx, spacetime_mem_ball har ht hy⟩
  have hg : averagedGradient (canonicalSlicePhase T Q z t ε) x y =
      transverseChartFamily (current T Q) (spatialCarrier T)
        (ε, spectatorCenter z, t, z 0, x, y) :=
    funext (averagedGradient_canonicalSlicePhase T Q z t ε x y)
  rw [hg]
  exact ⟨(hi.injective _ hp).mono ball_subset_closedBall,
    hi.inner_buffer _ hp, hi.outer_buffer _ hp,
    fun η hη ↦ (hi.differential_bounds _ hp η (ball_subset_closedBall hη)).2.2⟩

end JanetCartan.RawPrimary.UniformSliceGeometry
