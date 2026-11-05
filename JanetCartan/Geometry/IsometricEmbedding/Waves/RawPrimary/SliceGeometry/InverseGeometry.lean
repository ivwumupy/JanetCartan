module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.InverseGeometry.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.InverseGeometry.Smoothness

/-!
# Actual inverse geometry for canonical raw slices

The entire normalized radius-two input core is retained. The canonical averaged
gradient is injective on the radius-three ball, has a common buffered image and
a uniform positive determinant gap. All choices precede the current frame.
These are the four inverse-geometry fields of the `UniformNormalData` used by
`SliceBounds.exists_rawPhysicalSliceSobolev_wkbGrades`. Phase jet budgets and
the final normal-data assembly are separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu NormalComparison
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

private theorem slice_spacetime_mem_ball {r a t : ℝ} {y : Euclidean (n - 1)}
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

/-- Actual common inverse geometry of the SAME canonical raw slice phase,
including epsilon zero and every point of the original closed carrier cube.
The radius-two core and radius-three injectivity domain are independent of the
arbitrarily capped physical and epsilon radii. All four assertions are proved
from primitive state-ball frame closeness, using the smooth radius-four input
extension; no inverse geometry or phase comparison is an assumption
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:setup:oscillatory`). -/
theorem exists_slice_inverse_geometry {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterCube P.radius)
    {amax emax : ℝ} (hamax : 0 < amax) (hemax : 0 < emax) :
    ∃ a > (0 : ℝ), a ≤ amax ∧ ∃ e > (0 : ℝ), e ≤ emax ∧
    ∃ δ > (0 : ℝ), ∃ β > (0 : ℝ), ∃ γ > (0 : ℝ),
    ∃ V : Set (Euclidean (n - 1)), IsOpen V ∧ IsCompact (closure V) ∧
      ∀ Q,
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
  obtain ⟨r, hr, hrR, hbox⟩ := exists_slice_comparison_radius T hP hz
  obtain ⟨es, hes, hsmooth⟩ := exists_slice_transverse_smooth T hP z hrR.le hbox
  obtain ⟨γ, hγ, β, hβ, V, L, hV, hVc, _, _, hinv⟩ :=
    exists_transverseChart_inverseFamily (P := Euclidean 2)
      (isCompact_closedBall (0 : Euclidean (n - 1)) 2) isOpen_ball
      (closedBall_subset_ball (by norm_num : (2 : ℝ) < 3)) ball_subset_closedBall
      (convex_closedBall (0 : Euclidean (n - 1)) 3)
  let τ := min β (1 / 4)
  have hτ : 0 < τ := lt_min hβ (by norm_num)
  obtain ⟨δ, hδ, ec, hec, hcomp⟩ := exists_slice_transverse_comparison T hP z hrR hbox hτ
  let e₀ := min es ec
  have he₀ : 0 < e₀ := lt_min hes hec
  let a := min amax (r / 4)
  have ha : 0 < a := lt_min hamax (by positivity)
  have har : 2 * a ≤ r := by
    have := min_le_right amax (r / 4)
    dsimp only [a]; linarith
  let e := min emax (e₀ / 2)
  have he : 0 < e := lt_min hemax (by positivity)
  have hee : e < e₀ := (min_le_right _ _).trans_lt (half_lt_self he₀)
  have hparam {b : ℝ} (hb : e₀ ≤ b) :
      transverseParameterSet (n := n) z r e₀ ⊆ transverseParameterSet z r b := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2.trans_le hb⟩, hp.2⟩
  refine ⟨a, ha, min_le_left _ _, e, he, min_le_left _ _, δ, hδ, β, hβ,
    γ, hγ, V, hV, hVc, ?_⟩
  intro Q hQ
  have hc := fun p hp η hη ↦ hcomp Q hQ p (hparam (min_le_right es ec) hp) η hη
  have hs : ContDiffOn ℝ ∞
      (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
      (transverseParameterSet z r e₀ ×ˢ sliceInputExtension n) :=
    (hsmooth Q).mono (prod_mono (hparam (min_le_left es ec)) Subset.rfl)
  have hi := hinv (current T Q) (spatialCarrier T)
    (transverseParameterSet z r e₀) (sliceInputExtension n)
    (isOpen_transverseParameterSet z r e₀) isOpen_ball
    (closedBall_subset_ball (by norm_num : (3 : ℝ) < 4)) hs
    (fun p hp η hη ↦ (hc p hp η hη).2.le.trans (min_le_right β (1 / 4)))
    (fun p hp η hη ↦ (hc p hp η
      (closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 3) hη)).1.le.trans
        (min_le_left β (1 / 4)))
  intro t ht ε hε x hx y hy
  have hp : (ε, spectatorCenter z, t, z 0, x, y) ∈ transverseParameterSet z r e₀ :=
    ⟨⟨by linarith [hε.1], hε.2.trans_lt hee⟩, mem_ball_self hr, mem_ball_self hr,
      slice_spacetime_mem_ball har ht hx, slice_spacetime_mem_ball har ht hy⟩
  have hg : averagedGradient (canonicalSlicePhase T Q z t ε) x y =
      transverseChartFamily (current T Q) (spatialCarrier T)
        (ε, spectatorCenter z, t, z 0, x, y) :=
    funext (averagedGradient_canonicalSlicePhase T Q z t ε x y)
  rw [hg]
  exact ⟨(hi.injective _ hp).mono ball_subset_closedBall,
    hi.inner_buffer _ hp, hi.outer_buffer _ hp,
    fun η hη ↦ (hi.differential_bounds _ hp η (ball_subset_closedBall hη)).2.2⟩

end JanetCartan.RawPrimary.SliceGeometry
