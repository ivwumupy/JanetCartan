module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Bounds
public import JanetCartan.Analysis.Calculus.PhaseQuotient
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The literal averaged transport gradient

`app:ch_background:eq:bg-Psi` uses the actual initial-coordinate map `Y`,
with its spectator held fixed. This leaf connects the conic API to the shared
averaged-gradient convention and proves homogeneity from the phase formula.
It does not construct `Y` or its annular inverse.
-/

@[expose] public noncomputable section
open scoped InnerProductSpace
namespace JanetCartan.ContinuumNormalReduction.ConicChart
variable {X E V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The transport phase `Y(x,s,v) · η` in `app:ch_background:eq:bg-Psi`.
In the application `V` is the shared Euclidean spectator space of dimension two. -/
def transportPhase (Y : X → ℝ → V → E) (v : V) (u : ℝ × E) (x : X) : ℝ :=
  ⟪Y x u.1 v, u.2⟫_ℝ

/-- The literal integral in `app:ch_background:eq:bg-Psi`, using the existing
physical Hilbert gradient and segment convention. -/
def transportChart (Y : X → ℝ → V → E) (v : V) (x x' : X) (u : ℝ × E) : X :=
  averagedPhaseGradient (transportPhase Y v) u x x'

/-- Homogeneity follows from linearity in the covector in
`app:ch_background:eq:bg-Psi`. It holds with `s` and `v` fixed. -/
theorem transportChart_radialScale (Y : X → ℝ → V → E) (v : V)
    (x x' : X) (u : ℝ × E) (t : ℝ) :
    transportChart Y v x x' (radialScale t u) = t • transportChart Y v x x' u := by
  have he : transportPhase Y v (radialScale t u) = t • transportPhase Y v u := by
    funext z
    simp [transportPhase, radialScale, real_inner_smul_right]
  unfold transportChart averagedPhaseGradient
  rw [he]
  simp only [gradient, fderiv_const_smul_field, Pi.smul_apply, map_smul]
  exact intervalIntegral.integral_smul t _

/-- The exact two-point phase identity used before changing variables in
Step 1 of `app:ch_background:prop:bg-frame`. -/
theorem transportPhase_sub_eq_inner_transportChart
    (Y : X → ℝ → V → E) (v : V) (u : ℝ × E)
    {U : Set X} (hU : IsOpen U) (hc : Convex ℝ U)
    (hY : ContDiffOn ℝ 1 (fun z ↦ Y z u.1 v) U)
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) :
    transportPhase Y v u x - transportPhase Y v u x' =
      ⟪transportChart Y v x x' u, x - x'⟫_ℝ :=
  phase_sub_eq_inner_averagedPhaseGradient hU hc (hY.inner ℝ contDiffOn_const) hx hx'

variable [CompleteSpace E]

/-- Full time/transverse coordinates for the literal transport gradient,
matching `FullPhaseCharts.Comparison.fullChart` in
`app:ch_background:eq:bg-Psi`. The physical space retains its Hilbert norm. -/
def fullTransportChart (Y : WithLp 2 (ℝ × E) → ℝ → V → E) (v : V)
    (x x' : WithLp 2 (ℝ × E)) (u : ℝ × E) : ℝ × E :=
  (transportChart Y v x x' u).ofLp

/-- The homogeneity input of `AnnularData` is proved for the actual formula
in `app:ch_background:eq:bg-Psi`; only its analytic annular inputs remain. -/
theorem fullTransportChart_radialScale
    (Y : WithLp 2 (ℝ × E) → ℝ → V → E) (v : V)
    (x x' : WithLp 2 (ℝ × E)) (u : ℝ × E) (t : ℝ) :
    fullTransportChart Y v x x' (radialScale t u) =
      t • fullTransportChart Y v x x' u := by
  simp only [fullTransportChart, transportChart_radialScale, WithLp.ofLp_smul]

omit [CompleteSpace E] in
/-- The magnitude comparison holds in the physical Hilbert norm as well as
the product coordinate norm. This retains the Euclidean convention of
`app:ch_background:eq:bg-Psi`. -/
theorem AnnularData.physical_norm_bounds (A : AnnularData E)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ u ∈ A.annulus, ‖A.map u‖ ≤ M)
    {u : ℝ × E} (hu : u ∈ A.cone) :
    (1 - A.error) * ‖u.2‖ ≤ ‖WithLp.toLp 2 (A.map u)‖ ∧
      ‖WithLp.toLp 2 (A.map u)‖ ≤
        (‖(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap‖ *
          (M * (1 + A.error))) * ‖u.2‖ := by
  constructor
  · exact (A.transverse_norm_bounds hu).1.trans
      (WithLp.norm_snd_le ℝ (WithLp.toLp 2 (A.map u)))
  · calc
      _ ≤ ‖(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap‖ *
          ‖A.map u‖ :=
        (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap‖ *
          ((M * (1 + A.error)) * ‖u.2‖) :=
        mul_le_mul_of_nonneg_left (A.norm_upper_of_annular_bound hM hb hu) (by positivity)
      _ = _ := by ring

variable [FiniteDimensional ℝ E]

/-- The literal transport map has the degree-one Jacobian and positive conic
bounds of `app:ch_background:eq:bg-jacobian`. The only quantitative inputs
are annular bounds; global homogeneity is discharged by the phase formula.
The cone may lie over a closed compact support. -/
theorem transport_jacobian_bounds (A : AnnularData E)
    (Y : WithLp 2 (ℝ × E) → ℝ → V → E) (v : V)
    (x x' : WithLp 2 (ℝ × E)) (hmap : A.map = fullTransportChart Y v x x')
    (hd : ∀ u ∈ A.cone, DifferentiableAt ℝ A.map u)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ u ∈ A.annulus, c ≤ A.jacobian u ∧ A.jacobian u ≤ C) :
    (∀ u ∈ A.cone, ∀ t : ℝ, 0 < t →
      A.jacobian (radialScale t u) = t * A.jacobian u) ∧
    (∃ a > 0, ∃ b > 0, ∀ u ∈ A.cone,
      a * ‖u.2‖ ≤ A.jacobian u ∧ A.jacobian u ≤ b * ‖u.2‖) := by
  have hhom : ∀ u : ℝ × E, ∀ t : ℝ, 0 < t →
      A.map (radialScale t u) = t • A.map u := by
    intro u t _
    rw [hmap]
    exact fullTransportChart_radialScale Y v x x' u t
  exact ⟨fun _ hu _ ht ↦ A.jacobian_radialScale hhom hd hu ht,
    A.exists_jacobian_bounds hhom hd hc hC hb⟩

end JanetCartan.ContinuumNormalReduction.ConicChart
