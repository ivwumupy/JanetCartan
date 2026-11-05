module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedFlowProfiles.FrozenMinorCover

/-!
# Frozen minors retained by the projected coefficient construction

The same null-vector refinement supplies the projected coefficients and its
frozen minor. This is the original choice used by the carrier-flow cell, before
geometric budgets or finite histories are introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace
namespace JanetCartan.CurrentCoefficientProfiles
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport

/-- Retain the frozen minor of the SAME null-vector cover while constructing
all projected transport coefficients. The cube-frame member identifies its
frozen value without selecting another refinement. Consumer:
`exists_transport_coefficient_bounds_before_geometry_with_frozen_minors`
(`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_projected_transport_coefficients_with_frozen_minors {n N : ℕ}
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U} (hn : 2 ≤ n) {c₀ C₀ : ℝ}
    (hP : P.IsValid c₀ C₀) (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ μ κ : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        (∀ z ∈ parameterCube (3 * P.radius / 2), ∀ r c, z ∈ V r c →
          μ ≤ |(cubePencil (P.toFun z)).adjugate r c|) ∧
        ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
          (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
          cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
          ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
          ∀ r c,
            let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              (parameterInterior (3 * P.radius / 2) ∩ V r c)
            ContDiffOn ℝ ∞ (carrierNullvector T Q c) Ω ∧
              ContDiffOn ℝ ∞ (carrierConullvector T Q r) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportDirection T Q r c) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportPotential T Q F r c) Ω ∧
              ∀ w ∈ Ω,
                carrierNullvector T Q c w ≠ 0 ∧ carrierConullvector T Q r w ≠ 0 ∧
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ carrierNullvector T Q c w j) = 0 ∧
                carrierConullvector T Q r w ᵥ*
                  reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
                μ * κ ≤ |carrierAdaptedDenominator T Q r c w| ∧
                carrierAdaptedDenominator T Q r c w ≠ 0 ∧
                |(carrierAdaptedDenominator T Q r c w)⁻¹| ≤ (μ * κ)⁻¹ := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hnull⟩ :=
    exists_actual_nullvectors hn hP T hK hKU hball
  refine ⟨min δ T.family.threshold, μ, κ, lt_min hδ T.family.threshold_pos,
    hμ, hκ, V, hV, hcover, ?_, ?_⟩
  · let Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
      ⟨fun _ ↦ cubeStress n, contDiffOn_const, by
        rw [sub_self, cNorm_zero]
        exact T.family.threshold_pos⟩
    have hsmall : cNorm K 6 (Q₀.1 - fun _ ↦ cubeStress n) < δ := by
      change cNorm K 6 ((fun _ ↦ cubeStress n) - fun _ ↦ cubeStress n) < δ
      rw [sub_self, cNorm_zero]
      exact hδ
    intro z hz r c hzV
    have hzero : (0 : Euclidean n) ∈ ball 0 T.physicalRadius :=
      mem_ball_self T.physicalRadius_pos
    have hg := ContinuumRow.NormalizedFlowProfiles.carrierGradient_eq_frozen_of_cube_frame
      T Q₀ rfl hzero (fun i ↦ (hz i).trans_lt (by linarith [hP.1]))
    have hm := (hnull Q₀ hsmall (fun _ _ i ↦ cubeStress_isSymm i) 0 hzero
      (hball (mem_closedBall_self T.data.localReference.stateRadius_pos.le))
      z hz r c hzV).2.1
    simpa only [hg, Q₀, reducedSymbol_eq_pencil, pencil_cubeStress] using hm
  intro F hF hi hrank hclose
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt
      (hclose.trans_le (min_le_right _ _))
    intro x hx
    exact ((hframe.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  refine ⟨hlow, ?_⟩
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  change ∀ r c, _
  intro r c
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V r c)
  have hΩ : IsOpen Ω := (isOpen_ball.inter isOpen_interior).prod
    ((isOpen_parameterInterior _).inter (hV r c))
  have hxU {w : Euclidean n × Euclidean 3} (hw : w ∈ Ω) : w.1 ∈ U :=
    hKU (interior_subset hw.1.2)
  have hzC {w : Euclidean n × Euclidean 3} (hw : w ∈ Ω) :
      w.2 ∈ parameterCube (3 * P.radius / 2) := fun i ↦ (hw.2.1 i).le
  have hs (x) (hx : x ∈ U) (i) : (Q.1 x i).IsSymm :=
    (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds hx)).of_le (by simp)) (hrank x hx) i).1
  have hb (w) (hw : w ∈ Ω) := hnull Q (hclose.trans_le (min_le_left _ _)) hs w.1 hw.1.1
    (interior_subset hw.1.2) w.2 (hzC hw) r c hw.2.2
  have hd (w) (hw : w ∈ Ω) : carrierAdaptedDenominator T Q r c w ≠ 0 :=
    (hb w hw).2.2.2.2.2.2.2.1
  have hQ (i j a : Fin n) :
      ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean 3 ↦ Q.1 w.1 i j a) Ω := by
    exact ((Matrix.entryLinearMap ℝ ℝ j a).toContinuousLinearMap.contDiff.comp_contDiffOn
      (contDiffOn_projectedStress hU hF hi hrank i)).comp
        contDiffOn_fst (fun _ hw ↦ hxU hw)
  have hξ : ContDiffOn ℝ ∞
      (fun w : Euclidean n × Euclidean 3 ↦ T.carrierGradient Q w.1 w.2) Ω :=
    (T.carrierGradient_smooth hP Q).mono fun _ hw ↦
      ⟨hw.1.1, fun i ↦ (hw.2.1 i).trans (by linarith [hP.1])⟩
  have hk := contDiffOn_rightNullvector_reducedSymbol hQ hξ c
  have hl := contDiffOn_leftNullvector_reducedSymbol hQ hξ r
  have hke : ContDiffOn ℝ ∞ (carrierNullvector T Q c) Ω :=
    (contDiffOn_piLp 2).mpr (contDiffOn_pi.mp hk)
  have hden : ContDiffOn ℝ ∞ (carrierAdaptedDenominator T Q r c) Ω := by
    unfold carrierAdaptedDenominator adaptedTimeCoefficient
    exact ContDiffOn.sum fun a _ ↦ contDiffOn_const.mul
      (contDiffOn_transportField hQ hl hk a)
  have hdir : ContDiffOn ℝ ∞ (carrierTransportDirection T Q r c) Ω := by
    apply (contDiffOn_piLp 2).mpr
    intro a
    exact (contDiffOn_transportField hQ hl hk a).div hden hd
  have hpot : ContDiffOn ℝ ∞ (carrierTransportPotential T Q F r c) Ω := by
    apply ContDiffOn.div _ hden hd
    exact ContDiffOn.sum fun i _ ↦ (contDiffOn_pi.mp hl i).mul
      (contDiffOn_reducedOperator_joint hΩ
        (hF.comp contDiffOn_fst (fun _ hw ↦ hxU hw))
        (fun _ hw ↦ hi _ (hxU hw)) hQ hke i)
  refine ⟨hke, hl, hdir, hpot, ?_⟩
  intro w hw
  have hh := hb w hw
  refine ⟨?_, hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩
  intro hkzero
  apply hh.2.2.1
  exact congrArg (fun v : Euclidean n ↦ fun j ↦ v j) hkzero


end JanetCartan.CurrentCoefficientProfiles
