module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Basic

/-!
# Exact reference charts

Identify the reference of the comparison paragraph following
`app:ch_seed:eq:seed-quotient-integral` from the literal integral formulas.
At zero shift, differentiability of `H₀` at the carrier suffices. At nonzero
shift, local `C¹` regularity along the shifted segment suffices.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The covector gradient of the exact reference phase in
`app:ch_seed:prop:seed-phase-charts`. -/
theorem gradient_referencePhase_covector {H₀ : E → ℝ} {ξ : E}
    (hH : DifferentiableAt ℝ H₀ ξ) (x : WithLp 2 (ℝ × E)) :
    gradient (fun ξ ↦ referencePhase H₀ (x, ξ)) ξ =
      x.ofLp.1 • gradient H₀ ξ + x.ofLp.2 := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  have hd := (hH.hasFDerivAt.const_mul x.ofLp.1).add (innerSL ℝ x.ofLp.2).hasFDerivAt
  calc
    _ = x.ofLp.1 • fderiv ℝ H₀ ξ + innerSL ℝ x.ofLp.2 := hd.fderiv
    _ = _ := by
      ext w
      simp

/-- At zero shift the published integral quotient is `t G + ⟪y, η⟫`,
with `G = ⟪∇H₀(ζ(p,z₁)), η⟫` (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem modulationPhase_reference_zero {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (hH : DifferentiableAt ℝ H₀ (ζ (p, u.1)))
    (x : WithLp 2 (ℝ × E)) :
    modulationPhase (referencePhase H₀) ζ 0 p u x =
      x.ofLp.1 * ⟪gradient H₀ (ζ (p, u.1)), u.2⟫_ℝ + ⟪x.ofLp.2, u.2⟫_ℝ := by
  rw [modulationPhase, phaseShiftQuotient_zero, gradient_referencePhase_covector hH]
  simp [inner_add_left, inner_smul_left]

private theorem gradient_linear_spacetime (a : ℝ) (v : E) (x : WithLp 2 (ℝ × E)) :
    gradient (fun y : WithLp 2 (ℝ × E) ↦ y.ofLp.1 * a + ⟪y.ofLp.2, v⟫_ℝ) x =
      WithLp.toLp 2 (a, v) := by
  have he : (fun y : WithLp 2 (ℝ × E) ↦ y.ofLp.1 * a + ⟪y.ofLp.2, v⟫_ℝ) =
      (innerSL ℝ (WithLp.toLp 2 (a, v))) := by
    funext y
    simp [real_inner_comm, mul_comm]
  rw [he, gradient, (innerSL ℝ (WithLp.toLp 2 (a, v))).fderiv]
  exact (InnerProductSpace.toDual ℝ (WithLp 2 (ℝ × E))).symm_apply_apply _

/-- The physical gradient of the zero-shift reference quotient is the frozen
full chart, with the Euclidean physical norm
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem gradient_modulationPhase_reference_zero {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (hH : DifferentiableAt ℝ H₀ (ζ (p, u.1)))
    (x : WithLp 2 (ℝ × E)) :
    gradient (modulationPhase (referencePhase H₀) ζ 0 p u) x =
      WithLp.toLp 2 (frozenChart (fun z ↦ gradient H₀ (ζ (p, z))) u) := by
  rw [show modulationPhase (referencePhase H₀) ζ 0 p u =
    (fun y ↦ y.ofLp.1 * ⟪gradient H₀ (ζ (p, u.1)), u.2⟫_ℝ + ⟪y.ofLp.2, u.2⟫_ℝ)
    from funext (modulationPhase_reference_zero ζ p u hH)]
  exact gradient_linear_spacetime _ _ _

/-- Averaging over either physical segment leaves the zero-shift frozen full
chart unchanged (`app:ch_seed:prop:seed-phase-charts`). -/
theorem modulationChart_reference_zero {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (hH : DifferentiableAt ℝ H₀ (ζ (p, u.1)))
    (x x' : WithLp 2 (ℝ × E)) :
    modulationChart (referencePhase H₀) ζ 0 p x x' u =
      WithLp.toLp 2 (frozenChart (fun z ↦ gradient H₀ (ζ (p, z))) u) := by
  unfold modulationChart averagedPhaseGradient
  simp_rw [gradient_modulationPhase_reference_zero ζ p u hH]
  simp

/-- The full chart's reference is exactly `FullPhaseCharts.frozenChart`,
not an additional comparison assumption (`app:ch_seed:prop:seed-phase-charts`). -/
theorem fullChart_reference_zero {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (hH : DifferentiableAt ℝ H₀ (ζ (p, u.1)))
    (x x' : WithLp 2 (ℝ × E)) :
    fullChart (referencePhase H₀) ζ 0 p x x' u =
      frozenChart (fun z ↦ gradient H₀ (ζ (p, z))) u := by
  simp only [fullChart, modulationChart_reference_zero ζ p u hH, WithLp.ofLp_toLp]

/-- The transverse physical gradient of the zero-shift reference quotient
is exactly the data direction (`app:ch_seed:prop:seed-phase-charts`). -/
theorem gradient_transverse_modulationPhase_reference_zero {H₀ : E → ℝ}
    (ζ : P × ℝ → E) (p : P) (u : ℝ × E)
    (hH : DifferentiableAt ℝ H₀ (ζ (p, u.1))) (t : ℝ) (y : E) :
    gradient (modulationPhase
      (fun q : E × E ↦ referencePhase H₀ (WithLp.toLp 2 (t, q.1), q.2))
      ζ 0 p u) y = u.2 := by
  let a := t * ⟪gradient H₀ (ζ (p, u.1)), u.2⟫_ℝ
  have he : modulationPhase
      (fun q : E × E ↦ referencePhase H₀ (WithLp.toLp 2 (t, q.1), q.2))
      ζ 0 p u = (fun y ↦ a + (innerSL ℝ u.2) y) := by
    funext y
    change modulationPhase (referencePhase H₀) ζ 0 p u (WithLp.toLp 2 (t, y)) = _
    rw [modulationPhase_reference_zero ζ p u hH]
    simp only [innerSL_apply_apply, real_inner_comm y u.2, a]
  have hd := (hasFDerivAt_const a y).add (innerSL ℝ u.2).hasFDerivAt
  have hd' : HasFDerivAt (fun y ↦ a + (innerSL ℝ u.2) y) (innerSL ℝ u.2) y := by
    convert hd using 1
    simp
  rw [he, gradient, hd'.fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _

/-- The reference transverse averaged-gradient map is the identity for all
physical endpoints and all times (`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverseChart_reference_zero {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (hH : DifferentiableAt ℝ H₀ (ζ (p, u.1)))
    (t : ℝ) (y y' : E) :
    transverseChart (referencePhase H₀) ζ 0 p t y y' u = u.2 := by
  unfold transverseChart modulationChart averagedPhaseGradient
  simp_rw [gradient_transverse_modulationPhase_reference_zero ζ p u hH]
  simp

/-- The actual data differential of the zero-shift reference transverse map
is the identity (`app:ch_seed:prop:seed-phase-charts`). -/
theorem fderiv_transverseChart_reference_zero {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (z : ℝ) (hH : DifferentiableAt ℝ H₀ (ζ (p, z)))
    (t : ℝ) (y y' η : E) :
    fderiv ℝ (fun η ↦ transverseChart (referencePhase H₀) ζ 0 p t y y' (z, η)) η =
      ContinuousLinearMap.id ℝ E := by
  have he : (fun η ↦ transverseChart (referencePhase H₀) ζ 0 p t y y' (z, η)) = id :=
    funext fun η ↦ transverseChart_reference_zero ζ p (z, η) hH t y y'
  rw [he, fderiv_id]

/-- The integral reference quotient at every admissible shift is affine in
physical spacetime (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem modulationPhase_reference_shift {H : E → ℝ} (ζ : P × ℝ → E) (p : P) (u : ℝ × E) (ε : ℝ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 H (ζ (p, u.1) + (s * ε) • u.2))
    (x : WithLp 2 (ℝ × E)) :
    modulationPhase (referencePhase H) ζ ε p u x =
      x.ofLp.1 * phaseShiftQuotient (fun _ : Unit ↦ H) () (ζ (p, u.1)) u.2 ε +
        ⟪x.ofLp.2, u.2⟫_ℝ := by
  have hc : ContinuousOn (fun s : ℝ ↦
      ⟪gradient H (ζ (p, u.1) + (s * ε) • u.2), u.2⟫_ℝ) (Icc 0 1) := by
    intro s hs
    have hg : ContinuousAt (gradient H) (ζ (p, u.1) + (s * ε) • u.2) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp
        ((hH s hs).continuousAt_fderiv one_ne_zero)
    have hcomp : ContinuousAt (fun s : ℝ ↦ gradient H (ζ (p, u.1) + (s * ε) • u.2)) s :=
      hg.comp (f := fun s : ℝ ↦ ζ (p, u.1) + (s * ε) • u.2) (by fun_prop)
    exact (hcomp.inner continuousAt_const).continuousWithinAt
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  unfold modulationPhase phaseShiftQuotient
  calc
    _ = ∫ s in (0 : ℝ)..1,
        x.ofLp.1 * ⟪gradient H (ζ (p, u.1) + (s * ε) • u.2), u.2⟫_ℝ +
          ⟪x.ofLp.2, u.2⟫_ℝ := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [gradient_referencePhase_covector ((hH s (by simpa using hs)).differentiableAt one_ne_zero)]
      simp [inner_add_left, inner_smul_left]
    _ = _ := by
      rw [intervalIntegral.integral_add (hi.const_mul x.ofLp.1) intervalIntegrable_const,
        intervalIntegral.integral_const_mul]
      simp

/-- The physical gradient of the reference quotient is independent of the
physical point, also at nonzero shift (`app:ch_seed:prop:seed-phase-charts`). -/
theorem gradient_modulationPhase_reference_shift {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (ε : ℝ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 H₀ (ζ (p, u.1) + (s * ε) • u.2))
    (x : WithLp 2 (ℝ × E)) :
    gradient (modulationPhase (referencePhase H₀) ζ ε p u) x =
      WithLp.toLp 2
        (phaseShiftQuotient (fun _ : Unit ↦ H₀) () (ζ (p, u.1)) u.2 ε, u.2) := by
  rw [show modulationPhase (referencePhase H₀) ζ ε p u =
    (fun y ↦ y.ofLp.1 * phaseShiftQuotient (fun _ : Unit ↦ H₀) ()
      (ζ (p, u.1)) u.2 ε + ⟪y.ofLp.2, u.2⟫_ℝ)
    from funext (modulationPhase_reference_shift ζ p u ε hH)]
  exact gradient_linear_spacetime _ _ _

/-- Exact evaluation of the reference full chart for every admissible shift.
Only its time component varies with epsilon
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem fullChart_reference_shift {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (ε : ℝ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 H₀ (ζ (p, u.1) + (s * ε) • u.2))
    (x x' : WithLp 2 (ℝ × E)) :
    fullChart (referencePhase H₀) ζ ε p x x' u =
      (phaseShiftQuotient (fun _ : Unit ↦ H₀) () (ζ (p, u.1)) u.2 ε, u.2) := by
  unfold fullChart modulationChart averagedPhaseGradient
  simp_rw [gradient_modulationPhase_reference_shift ζ p u ε hH]
  simp

/-- The transverse physical gradient of the reference quotient is exactly
`η` for every admissible shift (`app:ch_seed:prop:seed-phase-charts`). -/
theorem gradient_transverse_modulationPhase_reference_shift {H₀ : E → ℝ}
    (ζ : P × ℝ → E) (p : P) (u : ℝ × E) (ε : ℝ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 H₀ (ζ (p, u.1) + (s * ε) • u.2)) (t : ℝ) (y : E) :
    gradient (modulationPhase
      (fun q : E × E ↦ referencePhase H₀ (WithLp.toLp 2 (t, q.1), q.2))
      ζ ε p u) y = u.2 := by
  let a := t * phaseShiftQuotient (fun _ : Unit ↦ H₀) () (ζ (p, u.1)) u.2 ε
  have he : modulationPhase
      (fun q : E × E ↦ referencePhase H₀ (WithLp.toLp 2 (t, q.1), q.2))
      ζ ε p u = (fun y ↦ a + (innerSL ℝ u.2) y) := by
    funext y
    change modulationPhase (referencePhase H₀) ζ ε p u (WithLp.toLp 2 (t, y)) = _
    rw [modulationPhase_reference_shift ζ p u ε hH]
    simp only [innerSL_apply_apply, real_inner_comm y u.2, a]
  have hd := (hasFDerivAt_const a y).add (innerSL ℝ u.2).hasFDerivAt
  have hd' : HasFDerivAt (fun y ↦ a + (innerSL ℝ u.2) y) (innerSL ℝ u.2) y := by
    convert hd using 1
    simp
  rw [he, gradient, hd'.fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _

/-- The transverse reference chart is exactly the identity even away from
zero epsilon (`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverseChart_reference_shift {H₀ : E → ℝ} (ζ : P × ℝ → E)
    (p : P) (u : ℝ × E) (ε : ℝ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 H₀ (ζ (p, u.1) + (s * ε) • u.2)) (t : ℝ) (y y' : E) :
    transverseChart (referencePhase H₀) ζ ε p t y y' u = u.2 := by
  unfold transverseChart modulationChart averagedPhaseGradient
  simp_rw [gradient_transverse_modulationPhase_reference_shift ζ p u ε hH]
  simp

end JanetCartan.FullPhaseCharts.Comparison
