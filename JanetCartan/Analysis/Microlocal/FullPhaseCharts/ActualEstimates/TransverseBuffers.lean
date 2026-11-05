module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.IntegralBalls
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes

/-!
# Actual primitive transverse-chart buffers

The open domains, positive integration balls, joint primitive regularity and
phase-ball containment needed by `InverseEstimates.PhaseBounds` are constructed
from the fixed carrier patch. Every choice precedes the current frame in
`app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ActualComparison
open InverseEstimates

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (n - 1)
local notation "X" => E

/-- Open carrier/direction domain for the primitive transverse-chart estimate
(`app:ch_seed:eq:seed-quotient-integral`). -/
def transversePrimitiveDomain (ηb : E) : Set ((Euclidean 2 × ℝ × ℝ) × E) :=
  {p | carrierParameters (p.1.1, p.1.2.2) ∈ parameterInterior (3 * P.radius / 2) ∧
    |p.1.2.1| < T.family.radius / 8 ∧ ‖p.2‖ < ‖ηb‖ + 1}

/-- The primitive transverse domain is open, so derivatives at closed-ball boundary
points are ambient derivatives. -/
theorem isOpen_transversePrimitiveDomain (ηb : E) : IsOpen (transversePrimitiveDomain T ηb) := by
  have hc : Continuous (fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ carrierParameters (p.1.1, p.1.2.2)) := by fun_prop
  have ht : Continuous (fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ |p.1.2.1|) := by fun_prop
  have hn : Continuous (fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ ‖p.2‖) := by fun_prop
  exact ((isOpen_parameterInterior _).preimage hc).inter
    ((isOpen_lt ht continuous_const).inter (isOpen_lt hn continuous_const))

private theorem norm_spacetime_le (t : ℝ) (y : E) :
    ‖WithLp.toLp 2 (t,y)‖ ≤ |t| + ‖y‖ := by
  have hh := norm_add_le (WithLp.toLp 2 (t, (0 : E))) (WithLp.toLp 2 ((0 : ℝ),y))
  have he : WithLp.toLp 2 (t, (0 : E)) + WithLp.toLp 2 ((0 : ℝ),y) = WithLp.toLp 2 (t,y) := by
    apply WithLp.ofLp_injective
    simp
  rw [he] at hh
  simpa only [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd, Real.norm_eq_abs] using hh

/-- All integration-ball and primitive smoothness inputs of the transverse inverse
estimate for the SAME constructed phase. No shift containment, phase existence,
phase bound, or carrier bound is assumed. The corresponding low and high budgets
are `exists_primitive_low_bounds` and `exists_primitive_projected_budget`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_transverse_primitive_buffers {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius) (ηb : E) :
    let p₀ := ((spectatorCenter z₀, (0 : ℝ), z₀ 0), ηb)
    let z := fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ spatialCarrier T (p.1.1, p.1.2.2)
    let v := fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ p.2
    let V := transversePrimitiveDomain T ηb
    let X₀ := ball (0 : X) (T.family.radius / 2)
    let B := ball (0 : X) (T.family.radius / 32)
    let Z := ball (covectorCenter T) T.family.radius
    ∃ e > (0 : ℝ), ∃ σ > (0 : ℝ), ∃ ρ > (0 : ℝ),
      let I := Ioo (-e) e
      closedBall ((p₀, (0 : X)), z p₀) σ ⊆ (V ×ˢ X₀) ×ˢ Z ∧
      closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ ⊆ (V ×ˢ I) ×ˢ X₀ ∧
      closedBall p₀ ρ ⊆ V ∧
      closedBall ((p₀, (0 : ℝ)), ((0 : X), (0 : X))) ρ ⊆ (V ×ˢ I) ×ˢ B ×ˢ B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (carrierSubstitution z v t)
        (closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ)
        (closedBall ((p₀, (0 : X)), z p₀) σ)) ∧
      (∀ q ∈ closedBall ((p₀, (0 : ℝ)), ((0 : X), (0 : X))) ρ,
        ∀ t ∈ Icc (0 : ℝ) 1,
          jointPhysicalSegment t q ∈ closedBall ((p₀, (0 : ℝ)), (0 : X)) ρ) ∧
      MapsTo quotientChartReindex
        (closedBall (((0 : ℝ), (p₀.1, (0 : X), (0 : X))), p₀.2) ρ)
        (closedBall ((p₀, (0 : ℝ)), ((0 : X), (0 : X))) ρ) ∧
      MapsTo transversePhaseProjection (closedBall ((p₀, (0 : X)), z p₀) σ)
        (closedBall (0, covectorCenter T) T.family.radius) ∧
      ContDiffOn ℝ ∞ z V ∧ ContDiffOn ℝ ∞ v V ∧
      (∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ Ioo (-1 : ℝ) 2, z p + (t * ε) • v p ∈ Z) ∧
      (∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2, y + t • (x - y) ∈ X₀) ∧
      ∀ Q, ContDiffOn ℝ ∞ (fun q : (((Euclidean 2 × ℝ × ℝ) × E) × X) × E ↦
        current T Q (WithLp.toLp 2 (q.1.1.1.2.1, q.1.2), q.2)) ((V ×ˢ X₀) ×ˢ Z) := by
  dsimp only
  let p₀ := ((spectatorCenter z₀, (0 : ℝ), z₀ 0), ηb)
  let z := fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ spatialCarrier T (p.1.1, p.1.2.2)
  let v := fun p : (Euclidean 2 × ℝ × ℝ) × E ↦ p.2
  let V := transversePrimitiveDomain T ηb
  let X₀ := ball (0 : X) (T.family.radius / 2)
  let B := ball (0 : X) (T.family.radius / 32)
  let Z := ball (covectorCenter T) T.family.radius
  obtain ⟨e, he, hshift⟩ := exists_covector_shift_buffer T hP
    (show 0 < ‖ηb‖ + 1 by positivity)
  let I := Ioo (-e) e
  have hV : IsOpen V := isOpen_transversePrimitiveDomain T ηb
  have hp₀ : p₀ ∈ V := by
    refine ⟨?_, ?_, by dsimp [p₀]; linarith⟩
    · simpa only [p₀, carrierParameters_spectatorCenter] using
        (middle_parameter_buffers hP).1 (fun i ↦ (hz₀ i).le)
    · dsimp [p₀]; simp only [abs_zero]; have := T.family.radius_pos; positivity
  have hI₀ : (0 : ℝ) ∈ I := ⟨by linarith, he⟩
  have hX₀ : (0 : X) ∈ X₀ := mem_ball_self (by have := T.family.radius_pos; positivity)
  have hB₀ : (0 : X) ∈ B := mem_ball_self (by have := T.family.radius_pos; positivity)
  have hz : ContDiffOn ℝ ∞ z V :=
    (spatialCarrier_smooth T hP).comp (contDiffOn_fst.fst.prodMk contDiffOn_fst.snd.snd)
      (fun p hp ↦ (middle_parameter_buffers hP).2 (fun i ↦ (hp.1 i).le))
  have hv : ContDiffOn ℝ ∞ v V := contDiffOn_snd
  have hshift' : ∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ Ioo (-1 : ℝ) 2,
      z p + (t * ε) • v p ∈ Z := by
    intro p hp ε hε t ht
    exact hshift (carrierParameters (p.1.1,p.1.2.2)) (fun i ↦ (hp.1 i).le)
      p.2 hp.2.2.le ε (abs_lt.mpr hε).le t ht
  have hz₀ : z p₀ ∈ Z := by
    simpa using hshift' p₀ hp₀ 0 hI₀ 0 (by constructor <;> norm_num)
  obtain ⟨σ, hσ, ρ, hρ, hb, ha, hp, hd, hm, hs, hc⟩ :=
    exists_carrier_integration_balls p₀ z v hV isOpen_Ioo isOpen_ball
      isOpen_ball isOpen_ball hp₀ hI₀ hX₀ hB₀ hz₀
      (hz.continuousOn.continuousAt (hV.mem_nhds hp₀))
      (hv.continuousOn.continuousAt (hV.mem_nhds hp₀))
  have hproj : MapsTo (transversePhaseProjection (n := n)) ((V ×ˢ X₀) ×ˢ Z)
      (closedBall (0, covectorCenter T) T.family.radius) := by
    intro q hq
    change (WithLp.toLp 2 (q.1.1.1.2.1, q.1.2),q.2) ∈ closedBall (0, covectorCenter T) T.family.radius
    rw [← closedBall_prod_same]
    refine ⟨?_, ball_subset_closedBall hq.2⟩
    rw [mem_closedBall, dist_zero_right]
    have ht := hq.1.1.2.1
    have hy : ‖q.1.2‖ < T.family.radius / 2 := by simpa only [X₀, mem_ball, dist_zero_right] using hq.1.2
    have hh := norm_spacetime_le q.1.1.1.2.1 q.1.2
    linarith [T.family.radius_pos]
  refine ⟨e, he, σ, hσ, ρ, hρ, hb, ha, hp, hd, hm, hs, hc,
    hproj.mono_left hb, hz, hv, hshift', ?_, ?_⟩
  · intro x hx y hy t ht
    have hx' : ‖x‖ < T.family.radius / 32 := by simpa only [mem_ball, dist_zero_right] using hx
    have hy' : ‖y‖ < T.family.radius / 32 := by simpa only [mem_ball, dist_zero_right] using hy
    have ht' : |t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩
    rw [mem_ball, dist_zero_right]
    have hmul : ‖t • (x - y)‖ ≤ 2 * (‖x‖ + ‖y‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul ht' (norm_sub_le x y) (norm_nonneg _) (by norm_num)
    have hh := (norm_add_le y (t • (x - y))).trans (add_le_add le_rfl hmul)
    linarith [T.family.radius_pos]
  · intro Q
    exact (current_smooth T Q).comp transversePhaseProjection.contDiff.contDiffOn
      (fun q hq ↦ closedBall_subset_ball
        (by linarith [T.family.radius_pos] : T.family.radius < 2 * T.family.radius) (hproj hq))

end JanetCartan.FullPhaseCharts.ActualEstimates
