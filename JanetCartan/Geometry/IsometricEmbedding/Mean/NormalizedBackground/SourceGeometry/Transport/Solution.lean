module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport.Flow

/-!
# Positive null transport after source dilation

The seed scalar is the output of `FlowAmplitude.exists_positive_null_amplitude_of_flow`
with initial value `1`. This module transports its proved equation to the actual
source geometry, as required in `app:ch_background:eq:bg-Nsigma`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

open NullTransport NullTransport.FlowAmplitude

variable {n N : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The source amplitude has the positive scalar, actual selected nullvector,
and literal scalar-projected reduced transport equation of
`app:ch_background:eq:bg-Nsigma` and `app:ch_waves:thm:leading`.

All transport and characteristic hypotheses concern only the seed. Its scalar
and its equation are produced by `exists_positive_null_amplitude_of_flow`;
phase, covector, minor and root data come from the seed carrier/Hamilton
construction. No scaled PDE or scaled transport solution is an input. -/
theorem sourceAmplitude_positive_null_transport
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiff ℝ ∞ F)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1) (hrank : HasFullNormalRankOn F U)
    {S : Euclidean n × Z → ℝ}
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦
      gradient (fun y ↦ S (y, w.2)) w.1) (U ×ˢ V))
    (row col time : Fin n) {α : Euclidean n × Z → ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) {w : Euclidean n × Z}
    (hw : (ρ • w.1, w.2) ∈ U ×ˢ V)
    (hα : DifferentiableAt ℝ α (ρ • w.1, w.2))
    (hpos : 0 < α (ρ • w.1, w.2))
    (hchar : ((projectedPhaseGeometry F S row col time).symbol (ρ • w.1, w.2)).det = 0)
    (hminor : ((projectedPhaseGeometry F S row col time).symbol
      (ρ • w.1, w.2)).adjugate row col ≠ 0)
    (hroot : partialDeriv
      (reducedDeterminant (ProjectedStressFrame.projectedStress F (ρ • w.1)))
      (gradient (fun y ↦ S (y, w.2)) (ρ • w.1)) time ≠ 0)
    (hpde : (projectedPhaseGeometry F S row col time).dual (ρ • w.1, w.2) ⬝ᵥ
      reducedOperator F (ProjectedStressFrame.projectedStress F)
        (fun y ↦ α (y, w.2) • (projectedPhaseGeometry F S row col time).kernel (y, w.2))
        (ρ • w.1) = 0) :
    let g := projectedPhaseGeometry F S row col time
    let gρ := projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time
    let b := fun q ↦ α q • g.kernel q
    sourceAmplitude b ρ w = sourceAmplitude α ρ w • gρ.kernel w ∧
      0 < sourceAmplitude α ρ w ∧
      gρ.symbol w *ᵥ (fun j ↦ sourceAmplitude b ρ w j) = 0 ∧
      gρ.dual w ⬝ᵥ reducedOperator (sourceDilation F ρ)
        (ProjectedStressFrame.projectedStress (sourceDilation F ρ))
        (fun y ↦ sourceAmplitude b ρ (y, w.2)) w.1 = 0 ∧
      gρ.kernel w ≠ 0 ∧ gρ.dual w ≠ 0 ∧ gρ.timeCoefficient w ≠ 0 := by
  dsimp only
  let g := projectedPhaseGeometry F S row col time
  let gρ := projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time
  have hSp : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1) :=
    ((hS.contDiffAt ((hU.prod hV).mem_nhds hw)).comp (ρ • w.1)
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hk := projectedPhaseGeometry_kernel_sourceDilation hF hρ (hrank _ hw.1)
    hSp row col time
  have hl := projectedPhaseGeometry_dual_sourceDilation hF hρ (hrank _ hw.1)
    hSp row col time
  have hM := projectedPhaseGeometry_symbol_sourceDilation hF hρ (hrank _ hw.1)
    hSp row col time
  have hkreg := contDiffOn_projectedPhaseGeometry_kernel hU hF.contDiffOn hflat hrank
    hξ row col time
  have hαx : DifferentiableAt ℝ (fun y ↦ α (y, w.2)) (ρ • w.1) :=
    hα.comp (ρ • w.1) (differentiableAt_id.prodMk (differentiableAt_const w.2))
  have hbp (j : Fin n) : DifferentiableAt ℝ
      (fun y ↦ (α (y, w.2) • g.kernel (y, w.2)) j) (ρ • w.1) := by
    have hkj := ((contDiffAt_piLp 2).mp
      ((hkreg.contDiffAt ((hU.prod hV).mem_nhds hw)).comp (ρ • w.1)
        (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
    exact hαx.mul hkj
  have hdecomp : sourceAmplitude (fun q ↦ α q • g.kernel q) ρ w =
      sourceAmplitude α ρ w • gρ.kernel w := by
    rw [sourceAmplitude_smul, hk]
  refine ⟨hdecomp, sourceAmplitude_pos hρ hpos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdecomp]
    change gρ.symbol w *ᵥ (sourceAmplitude α ρ w • rightNullvector (gρ.symbol w) col) = 0
    rw [Matrix.mulVec_smul, mulVec_rightNullvector (hM.trans (rfl) ▸ hchar), smul_zero]
  · rw [hl, reducedOperator_sourceAmplitude hU hF hflat hρ hw.1 (hrank _ hw.1) hbp,
      dotProduct_smul, hpde, smul_zero]
  · rw [hk]
    intro hz
    exact rightNullvector_ne_zero hminor
      (congrArg (fun v : Euclidean n ↦ fun j ↦ v j) hz)
  · rw [hl]
    exact leftNullvector_ne_zero hminor
  · rw [projectedPhaseGeometry_timeCoefficient_sourceDilation hF hρ (hrank _ hw.1) hSp]
    apply Geometry.timeCoefficient_ne_zero (g := g) _ hchar hminor hroot
    intro i
    exact (ProjectedStressFrame.projectedStress_mem_stressSpace
      (hF.contDiffAt.of_le (by simp)) (hrank _ hw.1) i).1

end JanetCartan.NormalizedBackground.SourceGeometry
