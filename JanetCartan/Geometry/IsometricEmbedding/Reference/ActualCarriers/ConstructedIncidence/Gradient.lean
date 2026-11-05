module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierProperties

/-!
# Full first-jet comparison of the selected carrier gradients

The incidence continuation in Step 3 of `app:ch_seed:prop:seed-actual-menu`
needs physical as well as parameter derivatives. These estimates concern the
literal carrier of the fixed quantitative chart family. Their only analytic
input is primitive frame closeness; phase continuity supplies the comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu CurrentFullPhase

/-- Joint chain rule for the physical gradient of the literal zero-energy
carrier, used by the full incidence differential comparison
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem hasFDerivAt_carrierGradient_joint {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)} {Φ : HamiltonFlow H (Euclidean (n - 1))}
    (A : ProjectionChart Φ) {ζ : Euclidean 3 → Euclidean (n - 1)}
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hA : ContDiffOn ℝ ∞ A.coordinates A.target)
    {q : Euclidean n × Euclidean 3} (hζ : DifferentiableAt ℝ ζ q.2)
    (hq : (q.1, (0, ζ q.2)) ∈ A.target) :
    HasFDerivAt (fun w : Euclidean n × Euclidean 3 ↦
      gradient (fun y ↦ carrierPhase A ζ y w.2) w.1)
      ((fderiv ℝ A.chartMomentum (q.1, (0, ζ q.2))).comp
        ((ContinuousLinearMap.fst ℝ _ _).prod
          ((0 : (Euclidean n × Euclidean 3) →L[ℝ] ℝ).prod
            ((fderiv ℝ ζ q.2).comp (ContinuousLinearMap.snd ℝ _ _))))) q := by
  have hm := ((A.contDiffOn_chartMomentum hp hA).contDiffAt
    (A.isOpen_target.mem_nhds hq)).differentiableAt (by simp)
  have hj := (hasFDerivAt_fst (p := q)).prodMk
    ((hasFDerivAt_const (0 : ℝ) q).prodMk
      (hζ.hasFDerivAt.comp q (hasFDerivAt_snd (p := q))))
  apply (hm.hasFDerivAt.comp q hj).congr_of_eventuallyEq
  have hn := (continuousAt_fst.prodMk
    (continuousAt_const.prodMk (hζ.continuousAt.comp continuousAt_snd))).preimage_mem_nhds
      (A.isOpen_target.mem_nhds hq)
  filter_upwards [hn] with w hw
  exact (hasGradientAt_carrierPhase A ζ hw).gradient

/-- The frozen identity holds on an open joint neighborhood, hence identifies
the full derivative, including its vanishing physical part
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem CarrierPhaseReference.frozen_gradient_joint_derivative {n : ℕ} {P : Patch n}
    (R : CarrierPhaseReference P) {q : Euclidean n × Euclidean 3}
    (hx : q.1 ∈ ball (0 : Euclidean n) R.radius)
    (hz : q.2 ∈ parameterInterior (2 * P.radius)) :
    fderiv ℝ (fun w : Euclidean n × Euclidean 3 ↦
      gradient (fun y ↦ carrierPhase R.chart R.spatialPatch y w.2) w.1) q =
      fderiv ℝ (fun w : Euclidean n × Euclidean 3 ↦ P.toFun w.2) q := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds
    (show q ∈ ball (0 : Euclidean n) R.radius ×ˢ parameterInterior (2 * P.radius)
      from ⟨hx, hz⟩)] with w hw
  exact R.frozen_gradient hw.1 hw.2

/-- A full chart-momentum comparison controls the joint first derivative of
its carrier after restriction. This supplies the physical derivatives absent
from the parameter-only comparison (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem CarrierFullPhaseInput.carrier_joint_comparison {n : ℕ} {P : Patch n}
    {R : CarrierPhaseReference P} {H : HomogeneousSymbol (Euclidean n)} {ε L : ℝ}
    (I : CarrierFullPhaseInput R H ε) (hε : 0 ≤ ε)
    {c C : ℝ} (hP : P.IsValid c C) (hL : 1 ≤ L)
    {q : Euclidean n × Euclidean 3}
    (hx : q.1 ∈ ball (0 : Euclidean n) R.radius)
    (hz : q.2 ∈ parameterCube P.radius) (hζL : ‖fderiv ℝ R.spatialPatch q.2‖ ≤ L) :
    ‖fderiv ℝ (fun w : Euclidean n × Euclidean 3 ↦
        gradient (fun y ↦ carrierPhase I.chart R.spatialPatch y w.2) w.1) q -
      fderiv ℝ (fun w : Euclidean n × Euclidean 3 ↦ P.toFun w.2) q‖ ≤ ε * L := by
  have hz' := parameterCube_subset_doubledInterior hP.1 hz
  have ht₀ := R.target_contains q.1 hx q.2 hz'
  have ht : (q.1, (0, R.spatialPatch q.2)) ∈ I.chart.target := I.target_eq ▸ ht₀
  have hζ := ((R.spatialPatch_smooth hP).contDiffAt
    ((isOpen_parameterInterior _).mem_nhds hz')).differentiableAt (by simp)
  rw [← R.frozen_gradient_joint_derivative hx hz',
    (hasFDerivAt_carrierGradient_joint I.chart I.momentum_smooth
      I.coordinates_smooth hζ ht).fderiv,
    (hasFDerivAt_carrierGradient_joint R.chart R.momentum_smooth
      R.coordinates_smooth hζ ht₀).fderiv]
  let A := (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean 3)).prod
    ((0 : (Euclidean n × Euclidean 3) →L[ℝ] ℝ).prod
      ((fderiv ℝ R.spatialPatch q.2).comp (ContinuousLinearMap.snd ℝ _ _)))
  have hA (v : Euclidean n × Euclidean 3) : ‖A v‖ ≤ L * ‖v‖ := by
    change ‖(v.1, (0, fderiv ℝ R.spatialPatch q.2 v.2))‖ ≤ _
    simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), max_le_iff]
    constructor
    · exact (norm_fst_le v).trans (le_mul_of_one_le_left (norm_nonneg _) hL)
    · exact ((fderiv ℝ R.spatialPatch q.2).le_opNorm v.2).trans
        (mul_le_mul hζL (norm_snd_le v) (norm_nonneg _) (by linarith))
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (by linarith))
  intro v
  have hb := (fderiv ℝ I.chart.chartMomentum (q.1, (0, R.spatialPatch q.2)) -
    fderiv ℝ R.chart.chartMomentum (q.1, (0, R.spatialPatch q.2))).le_opNorm (A v)
  exact hb.trans ((mul_le_mul_of_nonneg_right (I.comparison _ ht₀).2 (norm_nonneg _)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hA v) hε))

namespace CurrentFullPhase.PatchQuantitativeFamily
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Primitive frame `C⁶` closeness gives both value and full joint derivative
comparison for the same canonical carrier, using the family’s `C⁵` phase
continuity and the exact frozen gradient. No carrier-jet comparison is an
assumption. The consumer is the literal incidence comparison on buffered
cylinders (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem exists_carrier_joint_comparison_threshold {c C : ℝ} (hP : P.IsValid c C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n)
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius,
      ∀ z ∈ parameterCube P.radius,
        ‖T.carrierGradient Q x z - P.toFun z‖ ≤ ε ∧
        ‖fderiv ℝ (fun w : Euclidean n × Euclidean 3 ↦ T.carrierGradient Q w.1 w.2)
            (x, z) - fderiv ℝ (fun w : Euclidean n × Euclidean 3 ↦ P.toFun w.2)
              (x, z)‖ ≤ ε := by
  obtain ⟨L, hL, hderiv⟩ := T.reference.exists_patch_derivative_bound hP
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨δ, hδ, hphase⟩ := T.family.phase_continuity 5 (ε / L) (div_pos hε hLpos)
  refine ⟨δ, hδ, fun Q hQ x hx z hz ↦ ?_⟩
  have hKW : closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
      T.data.adapted.baseData.2) T.family.radius ⊆
      ball (T.data.adapted.embedding T.data.adapted.baseData.1,
        T.data.adapted.baseData.2) (2 * T.family.radius) :=
    closedBall_subset_ball (by linarith [T.family.radius_pos])
  have hR : ContDiffOn ℝ ∞ T.data.localReference.family.chart.coordinates
      T.data.localReference.family.chart.target := by
    rw [T.data.localReference.family.reference_control.target_eq]
    exact T.data.localReference.family.reference_control.coordinates_smooth
  have hS := T.data.localReference.family.chart.contDiffOn_phase hR
  have hc (q) (hq : q ∈ T.target) :
      ‖(T.currentChart Q).chartMomentum q - T.reference.chart.chartMomentum q‖ ≤ ε / L ∧
      ‖fderiv ℝ (T.currentChart Q).chartMomentum q -
        fderiv ℝ T.reference.chart.chartMomentum q‖ ≤ ε / L := by
    have hqK := ball_subset_closedBall hq
    have hb := chartMomentum_comparison_le_phase_cNorm_two
      (T.family.chart Q) T.data.localReference.family.chart
      (isCompact_closedBall _ _) (hKW.trans (T.family.target_contains Q))
      (hKW.trans T.family.reference_target)
      (fun w hw ↦ (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds (hKW hw)))
      (fun w hw ↦ hS.contDiffAt (T.data.localReference.family.chart.isOpen_target.mem_nhds
        (T.family.reference_target (hKW hw)))) hqK
    have hsmall := (cNorm_mono_order (by norm_num : 2 ≤ 5)).trans_lt (hphase Q hQ)
    exact ⟨hb.1.trans hsmall.le, hb.2.trans hsmall.le⟩
  let I : CarrierFullPhaseInput T.reference (normalizedHomogeneousSymbol hU Q.1 Q.2.1)
      (ε / L) := {
    flow := T.family.flow Q
    chart := T.currentChart Q
    target_eq := rfl
    section_eq := T.family.section_eq Q
    momentum_smooth := T.family.momentum_smooth Q
    coordinates_smooth := (T.family.coordinates_smooth Q).mono
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius))
    section_source := fun _ hu _ hz ↦ T.current_section_source Q hu (fun i ↦ (hz i).le)
    comparison := hc }
  have hv := (I.carrier_comparison (div_nonneg hε.le hLpos.le) hP hx hz).1
  have hd := I.carrier_joint_comparison (q := (x, z)) (div_nonneg hε.le hLpos.le) hP hL hx hz
    (hderiv z hz).1
  exact ⟨hv.trans (div_le_self hε.le hL), hd.trans_eq (div_mul_cancel₀ ε hLpos.ne')⟩

end CurrentFullPhase.PatchQuantitativeFamily
end JanetCartan.ActualCarriers
