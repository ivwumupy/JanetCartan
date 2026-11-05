module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualBuffers

/-!
# Fixed boxes for the actual phase comparison

The comparison and inverse-family consumers of `app:ch_seed:prop:seed-phase-charts`
need boxes chosen before the tolerance and current frame. The radius below can
be decreased arbitrarily; the triple-radius boxes still have the required
physical and carrier buffers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.ActualComparison
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu

/-- The two spectators at the chosen carrier point
(`app:ch_seed:prop:seed-phase-charts`). -/
def spectatorCenter (z : Euclidean 3) : Euclidean 2 :=
  WithLp.toLp 2 ![z 1, z 2]

/-- Reassembling the base parameters recovers the original patch point
(`app:ch_seed:prop:seed-phase-charts`). -/
@[simp] theorem carrierParameters_spectatorCenter (z : Euclidean 3) :
    carrierParameters (spectatorCenter z, z 0) = z := by
  ext i
  fin_cases i <;> rfl

/-- Positive boxes, with room for threefold enlargement, chosen solely from
fixed phase geometry. Every smaller positive radius is admissible for the
incidence-gap and annulus assembly in `app:ch_seed:prop:seed-phase-charts`. -/
theorem exists_box_radius {n : ℕ} {P : Patch n} {U : Set (Euclidean n)}
    {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C) {z₀ : Euclidean 3}
    (hz₀ : z₀ ∈ parameterInterior P.radius) :
    ∃ ρ₀ > (0 : ℝ), ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
      ρ ≤ 1 ∧ 3 * ρ < T.family.radius / 8 ∧
      closedBall (spectatorCenter z₀) (3 * ρ) ×ˢ closedBall (z₀ 0) (3 * ρ) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) := by
  have hO : IsOpen (carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :=
    (isOpen_parameterInterior _).preimage carrierParameters.continuous
  have hz : (spectatorCenter z₀, z₀ 0) ∈
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) := by
    simp only [mem_preimage, carrierParameters_spectatorCenter]
    exact (ActualPhase.middle_parameter_buffers hP).1 (fun i ↦ (hz₀ i).le)
  obtain ⟨d, hd, hsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hz)
  refine ⟨min 1 (min (d / 4) (T.family.radius / 32)),
    lt_min zero_lt_one (lt_min (by positivity) (div_pos T.family.radius_pos (by norm_num))), ?_⟩
  intro ρ hρ hρ₀
  have hρd := hρ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρR := hρ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hρ₀.trans (min_le_left _ _), by linarith [T.family.radius_pos], ?_⟩
  intro q hq
  apply hsub
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨(mem_closedBall.mp hq.1).trans_lt (by linarith),
    (mem_closedBall.mp hq.2).trans_lt (by linarith)⟩

/-- The open full-chart parameter neighborhood, with epsilon retained as a
joint parameter (`app:ch_seed:prop:seed-phase-charts`). -/
def fullParameterSet {n : ℕ} (z₀ : Euclidean 3) (r e : ℝ) :
    Set (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
      WithLp 2 (ℝ × Euclidean (n - 1))) :=
  Ioo (-e) e ×ˢ ball (spectatorCenter z₀) r ×ˢ ball 0 r ×ˢ ball 0 r

/-- The open normalized-data neighborhood at the prescribed direction
(`app:ch_seed:prop:seed-phase-charts`). -/
def dataSet {n : ℕ} (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r : ℝ) :
    Set (ℝ × Euclidean (n - 1)) := ball (z₀ 0) r ×ˢ ball ηb r

/-- The transverse parameter neighborhood keeps both fixed-time physical
endpoints inside the full physical ball
(`app:ch_seed:prop:seed-phase-charts`). -/
def transverseParameterSet {n : ℕ} (z₀ : Euclidean 3) (r e : ℝ) :
    Set (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) :=
  {q | q.1 ∈ Ioo (-e) e ∧ q.2.1 ∈ ball (spectatorCenter z₀) r ∧
    q.2.2.2.1 ∈ ball (z₀ 0) r ∧
    WithLp.toLp 2 (q.2.2.1, q.2.2.2.2.1) ∈ ball 0 r ∧
    WithLp.toLp 2 (q.2.2.1, q.2.2.2.2.2) ∈ ball 0 r}

/-- Openness of the joint full parameter extension, including zero epsilon
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem isOpen_fullParameterSet {n : ℕ} (z₀ : Euclidean 3) (r e : ℝ) :
    IsOpen (fullParameterSet (n := n) z₀ r e) :=
  isOpen_Ioo.prod (isOpen_ball.prod (isOpen_ball.prod isOpen_ball))

/-- Openness of the normalized-data extension
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem isOpen_dataSet {n : ℕ} (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r : ℝ) :
    IsOpen (dataSet z₀ ηb r) := isOpen_ball.prod isOpen_ball

/-- Openness of the transverse joint parameter extension
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem isOpen_transverseParameterSet {n : ℕ} (z₀ : Euclidean 3) (r e : ℝ) :
    IsOpen (transverseParameterSet (n := n) z₀ r e) := by
  let A := ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)
  have h₁ : IsOpen {q : A | q.1 ∈ Ioo (-e) e} :=
    isOpen_Ioo.preimage (by fun_prop)
  have h₂ : IsOpen {q : A | q.2.1 ∈ ball (spectatorCenter z₀) r} :=
    isOpen_ball.preimage (by fun_prop)
  have h₃ : IsOpen {q : A | q.2.2.2.1 ∈ ball (z₀ 0) r} :=
    isOpen_ball.preimage (by fun_prop)
  have h₄ : IsOpen {q : A | WithLp.toLp 2 (q.2.2.1, q.2.2.2.2.1) ∈ ball 0 r} :=
    isOpen_ball.preimage (by fun_prop)
  have h₅ : IsOpen {q : A | WithLp.toLp 2 (q.2.2.1, q.2.2.2.2.2) ∈ ball 0 r} :=
    isOpen_ball.preimage (by fun_prop)
  exact h₁.inter (h₂.inter (h₃.inter (h₄.inter h₅)))

end JanetCartan.FullPhaseCharts.ActualComparison
