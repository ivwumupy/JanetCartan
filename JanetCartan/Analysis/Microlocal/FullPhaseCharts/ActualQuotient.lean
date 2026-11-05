module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualBuffers
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness

/-!
# The actual smooth modulation and its two-point gradient

This instantiates the quotient calculus on the SAME constructed current chart.
The shift radius is positive and precedes the current frame. All three carrier
coordinates, the direction, physical points, and both signs of epsilon remain
joint variables. These are concrete regularity conclusions for
`app:ch_seed:eq:seed-exact-phase-quotient` and
`app:ch_seed:eq:seed-quotient-integral`, not assumed analytic fields.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualPhase
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The literal integral modulation of the actual current full phase, with
all carrier and direction coordinates retained
(`app:ch_seed:eq:seed-quotient-integral`). -/
def modulation
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (p : (Euclidean 3 × Euclidean (n - 1)) × ℝ)
    (x : WithLp 2 (ℝ × Euclidean (n - 1))) : ℝ :=
  phaseShiftQuotient (fun x ζ ↦ current T Q (x, ζ)) x
    (T.reference.spatialPatch p.1.1) p.1.2 p.2

/-- The actual zero-shift value is the covector derivative, with no division
or limit convention left implicit (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem modulation_zero (Q : _) (p : Euclidean 3 × Euclidean (n - 1))
    (x : WithLp 2 (ℝ × Euclidean (n - 1))) :
    modulation T Q (p, 0) x =
      fderiv ℝ (fun ζ ↦ current T Q (x, ζ)) (T.reference.spatialPatch p.1) p.2 := by
  simp only [modulation, phaseShiftQuotient_zero, inner_gradient_left]

/-- Actual joint smoothness through epsilon zero, and the literal nonzero
difference quotient identity, on fixed open integration buffers. Every input
to `QuotientSmoothness` is discharged from the constructed phase and patch.
The last two assertions concern the actual two-point physical gradient and
its first epsilon derivative (`app:ch_seed:prop:seed-phase-charts`).

The inverse charts, Jacobian/annular bounds and quantitative inverse estimates
are separate conclusions still to be assembled. -/
theorem exists_smooth_modulation {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M) :
    ∃ εStar > (0 : ℝ), ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧ cNorm
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      let V := parameterInterior (3 * P.radius / 2) ×ˢ
        ball (0 : Euclidean (n - 1)) M
      let I := Ioo (-εStar) εStar
      let X := ball (0 : WithLp 2 (ℝ × Euclidean (n - 1))) T.family.radius
      let B := ball (0 : WithLp 2 (ℝ × Euclidean (n - 1))) (T.family.radius / 8)
      ContDiffOn ℝ ∞ (Function.uncurry (modulation T Q)) ((V ×ˢ I) ×ˢ X) ∧
      (∀ p ∈ V, ∀ ε ∈ I, ε ≠ 0 → ∀ x ∈ X,
        modulation T Q (p, ε) x =
          (current T Q (x, T.reference.spatialPatch p.1 + ε • p.2) -
            current T Q (x, T.reference.spatialPatch p.1)) / ε) ∧
      ContDiffOn ℝ ∞ (fun q : ((Euclidean 3 × Euclidean (n - 1)) × ℝ) ×
          WithLp 2 (ℝ × Euclidean (n - 1)) × WithLp 2 (ℝ × Euclidean (n - 1)) ↦
        averagedPhaseGradient (modulation T Q) q.1 q.2.1 q.2.2) ((V ×ˢ I) ×ˢ B ×ˢ B) ∧
      ContDiffOn ℝ ∞ (fun q : ((Euclidean 3 × Euclidean (n - 1)) × ℝ) ×
          WithLp 2 (ℝ × Euclidean (n - 1)) × WithLp 2 (ℝ × Euclidean (n - 1)) ↦
        deriv (fun ε ↦ averagedPhaseGradient (modulation T Q)
          (q.1.1, ε) q.2.1 q.2.2) q.1.2) ((V ×ˢ I) ×ˢ B ×ˢ B) := by
  obtain ⟨εStar, he, hshift⟩ := exists_covector_shift_buffer T hP hM
  refine ⟨εStar, he, fun Q ↦ ?_⟩
  dsimp only
  let V := parameterInterior (3 * P.radius / 2) ×ˢ ball (0 : Euclidean (n - 1)) M
  let I := Ioo (-εStar) εStar
  let X := ball (0 : WithLp 2 (ℝ × Euclidean (n - 1))) T.family.radius
  let B := ball (0 : WithLp 2 (ℝ × Euclidean (n - 1))) (T.family.radius / 8)
  let Z := ball (covectorCenter T) T.family.radius
  let S := fun (p : (Euclidean 3 × Euclidean (n - 1)) ×
      WithLp 2 (ℝ × Euclidean (n - 1))) (ζ : Euclidean (n - 1)) ↦ current T Q (p.2, ζ)
  let z := fun p : Euclidean 3 × Euclidean (n - 1) ↦ T.reference.spatialPatch p.1
  let v := fun p : Euclidean 3 × Euclidean (n - 1) ↦ p.2
  have hV : IsOpen V := (isOpen_parameterInterior _).prod isOpen_ball
  have hI : IsOpen I := isOpen_Ioo
  have hX : IsOpen X := isOpen_ball
  have hZ : IsOpen Z := isOpen_ball
  have hB : IsOpen B := isOpen_ball
  have hW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun _ h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩
  have hS : ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ X) ×ˢ Z) := by
    apply (current_smooth T Q).comp (contDiffOn_fst.snd.prodMk contDiffOn_snd)
    intro q hq
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hq.1.2).trans (by linarith [T.family.radius_pos]),
      (mem_ball.mp hq.2).trans (by linarith [T.family.radius_pos])⟩
  have hz : ContDiffOn ℝ ∞ z V :=
    (T.reference.spatialPatch_smooth hP).comp contDiffOn_fst
      (fun q hq ↦ (middle_parameter_buffers hP).2 (fun i ↦ (hq.1 i).le))
  have hv : ContDiffOn ℝ ∞ v V := contDiffOn_snd
  have hshift' : ∀ p ∈ V, ∀ ε ∈ I, ∀ s ∈ Ioo (-1 : ℝ) 2,
      z p + (s * ε) • v p ∈ Z := by
    intro p hp ε hε s hs
    exact hshift p.1 (fun i ↦ (hp.1 i).le) p.2 (by simpa using (mem_ball.mp hp.2).le)
      ε ((abs_lt.mpr hε).le) s hs
  have hphysical : ∀ x ∈ B, ∀ y ∈ B, ∀ s ∈ Ioo (-1 : ℝ) 2,
      y + s • (x - y) ∈ X := fun _ hx _ hy _ hs ↦
    physical_segment_mem_phase_ball T (ball_subset_closedBall hx) (ball_subset_closedBall hy) hs
  have hquot := contDiffOn_carrierQuotient (S := S) (z := z) (v := v)
    hV hX hZ hI isOpen_Ioo hW hS hz hv hshift'
  have havg := contDiffOn_carrierQuotient_average (S := S) (z := z) (v := v)
    hV hX hZ hI isOpen_Ioo hW hS hz hv hshift' hB isOpen_Ioo hW hphysical
  have heps := contDiffOn_deriv_epsilon_carrierQuotient_average (S := S) (z := z) (v := v)
    hV hX hZ hI isOpen_Ioo hW hS hz hv hshift' hB isOpen_Ioo hW hphysical
  refine ⟨hquot, ?_, havg, heps⟩
  intro p hp ε hε hne x hx
  exact carrierQuotient_eq_div (S := S) (z := z) (v := v)
    hZ hW hS hshift' (convex_ball _ _) hp hx hε hne

end JanetCartan.FullPhaseCharts.ActualPhase
