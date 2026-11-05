module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.Setup
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Actual inverse and transport coefficients

Definitions for `app:ch_osc:prop:osc-normal` in `paper.tex`. The inverse is
constructed from the actual averaged gradient. No regularity or estimates for
it are included in the input data.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The actual inverse of the averaged gradient on the input box, used in
`app:ch_osc:eq:osc-exact-normal-kernel`. Values outside the image are immaterial. -/
def UniformNormalData.inverseChart (F : UniformNormalData G C)
    (ε : ℝ) (x y v : Euclidean n) : Euclidean n :=
  Function.invFunOn (averagedGradient (F.phase ε) x y) G.D v

/-- The velocity `w = (DᵤΨ)⁻¹ ∂εΨ` from Step 2 of
`app:ch_osc:prop:osc-normal`, with both physical positions retained. -/
def UniformNormalData.transportVelocity (F : UniformNormalData G C)
    (ε : ℝ) (x y u : Euclidean n) : Euclidean n :=
  (fderiv ℝ (averagedGradient (F.phase ε) x y) u).inverse
    (deriv (fun t ↦ averagedGradient (F.phase t) x y u) ε)

/-- The literal coefficients `c₀` and `cⱼ` of
`app:ch_osc:prop:osc-normal`. There are no mask factors in these coefficients. -/
def UniformNormalData.normalTransportCoefficient (F : UniformNormalData G C)
    (ε : ℝ) (k : Option (Fin n)) (x y u : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  match k with
  | none => transportCoefficient
      (fun v ↦ deriv (fun t ↦ normalAmplitude (F.amplitude t) x y v) ε)
      (fun j v ↦ F.transportVelocity ε x y v j • normalAmplitude (F.amplitude ε) x y v) u
  | some j => -(F.transportVelocity ε x y u j • normalAmplitude (F.amplitude ε) x y u)

/-- The mask-free amplitude, zero-extended off the common buffered output
chart, in `app:ch_osc:eq:osc-exact-normal-kernel`. The absolute Jacobian and
the two independent positions are retained. -/
def UniformNormalData.maskFreeInverseAmplitude (F : UniformNormalData G C)
    (ε : ℝ) (x y v : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  G.V.indicator (inverseJacobianAmplitude (F.amplitude ε) (fun _ ↦ 1) x y
    (F.inverseChart ε x y) (fderiv ℝ (averagedGradient (F.phase ε) x y))) v

/-- The output chart lies in the actual averaged-gradient image
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.chart_subset_image (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) :
    G.V ⊆ averagedGradient (F.phase ε) x y '' G.D :=
  subset_closure.trans ((self_subset_cthickening _).trans (F.chart_buffer ε hε x hx y hy))

/-- The constructed inverse has its values in the input box
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.inverseChart_mem (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y v : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hv : v ∈ G.V) :
    F.inverseChart ε x y v ∈ G.D :=
  Function.invFunOn_mem (F.chart_subset_image hε hx hy hv)

/-- The actual right inverse identity on the common chart
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem UniformNormalData.averagedGradient_inverseChart (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y v : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hv : v ∈ G.V) :
    averagedGradient (F.phase ε) x y (F.inverseChart ε x y v) = v :=
  Function.invFunOn_eq (F.chart_subset_image hε hx hy hv)

/-- Injectivity gives the actual left inverse identity throughout the input
box (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem UniformNormalData.inverseChart_averagedGradient (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    F.inverseChart ε x y (averagedGradient (F.phase ε) x y u) = u :=
  (F.gradient_injective ε hε x hx y hy).leftInvOn_invFunOn hu

/-- The determinant gap makes the actual input differential invertible;
this supplies the inverse used in the velocity of
`app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.jacobian_isInvertible (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    (fderiv ℝ (averagedGradient (F.phase ε) x y) u).IsInvertible := by
  let J := fderiv ℝ (averagedGradient (F.phase ε) x y) u
  have hdet : IsUnit J.toLinearMap.det := isUnit_iff_ne_zero.mpr
    (abs_pos.mp (G.gap_pos.trans_le (F.jacobian_gap ε hε x hx y hy u hu)))
  refine ⟨(LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.equivOfIsUnitDet_apply hdet v

/-- The velocity solves the differentiated phase-gradient equation exactly,
as required in Step 2 of `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.jacobian_transportVelocity (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    fderiv ℝ (averagedGradient (F.phase ε) x y) u (F.transportVelocity ε x y u) =
      deriv (fun t ↦ averagedGradient (F.phase t) x y u) ε :=
  (F.jacobian_isInvertible hε hx hy hu).self_apply_inverse _

/-- The full matrix amplitude vanishes off the compact input support
(`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.normalAmplitude_eq_zero_of_not_mem_input
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (x y : Euclidean n) {u : Euclidean n} (hu : u ∉ G.D₀) :
    normalAmplitude (F.amplitude ε) x y u = 0 := by
  have ha : F.amplitude ε x u = 0 := by
    by_contra h
    exact hu (F.amplitude_support ε hε
      (show (x, u) ∈ Function.support (Function.uncurry (F.amplitude ε)) from h)).2
  ext i j
  simp [normalAmplitude, ha]

/-- Zero extension from the common chart equals zero extension from the
entire image, as used in `app:ch_osc:eq:osc-exact-normal-kernel`. This is an
equality of the complete matrix amplitude with its absolute Jacobian. -/
theorem UniformNormalData.maskFreeInverseAmplitude_eq_image_indicator
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {x y : Euclidean n} (hx : x ∈ G.X) (hy : y ∈ G.X) (v : Euclidean n) :
    F.maskFreeInverseAmplitude ε x y v =
      (averagedGradient (F.phase ε) x y '' G.D).indicator
        (inverseJacobianAmplitude (F.amplitude ε) (fun _ ↦ 1) x y
          (F.inverseChart ε x y) (fderiv ℝ (averagedGradient (F.phase ε) x y))) v := by
  classical
  by_cases hv : v ∈ G.V
  · simp [maskFreeInverseAmplitude, hv, F.chart_subset_image hε hx hy hv]
  by_cases hi : v ∈ averagedGradient (F.phase ε) x y '' G.D
  · have hu : F.inverseChart ε x y v ∉ G.D₀ := by
      intro hu
      have he : averagedGradient (F.phase ε) x y (F.inverseChart ε x y v) = v :=
        Function.invFunOn_eq hi
      exact hv (F.image_buffer ε hε x hx y hy
        (self_subset_cthickening _ ⟨F.inverseChart ε x y v, hu, he⟩))
    simp [maskFreeInverseAmplitude, hv, hi, inverseJacobianAmplitude,
      F.normalAmplitude_eq_zero_of_not_mem_input hε x y hu]
  · simp [maskFreeInverseAmplitude, hv, hi]

end JanetCartan.NormalComparison
