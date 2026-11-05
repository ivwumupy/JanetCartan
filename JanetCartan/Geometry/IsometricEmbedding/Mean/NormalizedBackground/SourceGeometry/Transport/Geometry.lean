module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport.Operator

/-!
# The same selected adjugate row and column after source dilation

The geometric data in `app:ch_background:eq:bg-Nsigma`, using the physical
gradient of the named source phase and the actual projected stress frame.
These identities feed the positive scalar transport construction; no scaled
transport identity is assumed.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

open NullTransport NullTransport.FlowAmplitude

variable {n N : ℕ} {Z : Type}

/-- The actual data for `app:ch_waves:thm:leading` at a chosen phase and fixed
adjugate indices. Carrier/canonical labels are all contained in `Z`. -/
def projectedPhaseGeometry (F : Euclidean n → Euclidean N)
    (S : Euclidean n × Z → ℝ) (row col time : Fin n) : Geometry n N Z where
  immersion := fun _ ↦ F
  frame := fun _ ↦ ProjectedStressFrame.projectedStress F
  covector := fun z x ↦ gradient (fun y ↦ S (y, z)) x
  row := row
  col := col
  time := time

/-- Smoothness of the actual selected kernel, supplied by the projected-frame
and physical-covector producers (`app:ch_waves:thm:leading`). -/
theorem contDiffOn_projectedPhaseGeometry_kernel
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1) (hrank : HasFullNormalRankOn F U)
    {S : Euclidean n × Z → ℝ}
    (hξ : ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦
      gradient (fun y ↦ S (y, w.2)) w.1) (U ×ˢ V)) (row col time : Fin n) :
    ContDiffOn ℝ ∞ (projectedPhaseGeometry F S row col time).kernel (U ×ˢ V) := by
  apply Geometry.contDiffOn_kernel
  · intro i j a
    have himm : IsImmersionOn F U :=
      isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1)
        (fun _ _ ↦ Matrix.PosDef.one) (fun y hy ↦ hflat y hy)
    have hQ := ProjectedStressFrame.contDiffOn_projectedStress hU hF himm hrank i
    exact ((Matrix.entryLinearMap ℝ ℝ j a).toContinuousLinearMap.contDiff.comp_contDiffOn hQ).comp
      contDiffOn_fst (fun _ hw ↦ hw.1)
  · exact (contDiffOn_piLp 2).mp hξ

/-- The literal matrix pulls back with the physical covector of the scaled
phase (`app:ch_background:eq:bg-Nsigma`). -/
theorem projectedPhaseGeometry_symbol_sourceDilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {w : Euclidean n × Z}
    (hrank : Set.range (normalMap F (ρ • w.1)) =
      (normalSpace F (ρ • w.1) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1))
    (row col time : Fin n) :
    (projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).symbol w =
      (projectedPhaseGeometry F S row col time).symbol (ρ • w.1, w.2) := by
  have hQ := funext (ProjectedStressFrame.projectedStress_sourceDilation hρ hF w.1 hrank)
  simp only [Geometry.symbol, projectedPhaseGeometry,
    gradient_sourcePhase_position (ne_of_gt hρ) hS, hQ]

/-- The selected column retains its index and normalization
(`app:ch_background:eq:bg-Nsigma`). -/
theorem projectedPhaseGeometry_kernel_sourceDilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {w : Euclidean n × Z}
    (hrank : Set.range (normalMap F (ρ • w.1)) =
      (normalSpace F (ρ • w.1) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1))
    (row col time : Fin n) :
    (projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).kernel w =
      (projectedPhaseGeometry F S row col time).kernel (ρ • w.1, w.2) := by
  unfold Geometry.kernel
  rw [projectedPhaseGeometry_symbol_sourceDilation hF hρ hrank hS]
  rfl

/-- The selected row retains its index and normalization
(`app:ch_background:eq:bg-Nsigma`). -/
theorem projectedPhaseGeometry_dual_sourceDilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {w : Euclidean n × Z}
    (hrank : Set.range (normalMap F (ρ • w.1)) =
      (normalSpace F (ρ • w.1) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1))
    (row col time : Fin n) :
    (projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).dual w =
      (projectedPhaseGeometry F S row col time).dual (ρ • w.1, w.2) := by
  unfold Geometry.dual
  rw [projectedPhaseGeometry_symbol_sourceDilation hF hρ hrank hS]
  rfl

/-- The unnormalized principal field pulls back, so its time denominator
does too (`app:ch_background:eq:bg-Nsigma`). -/
theorem projectedPhaseGeometry_transportField_sourceDilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {w : Euclidean n × Z}
    (hrank : Set.range (normalMap F (ρ • w.1)) =
      (normalSpace F (ρ • w.1) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1))
    (row col time : Fin n) :
    let g := projectedPhaseGeometry F S row col time
    let gρ := projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time
    transportField (gρ.frame w.2 w.1) (gρ.dual w) (fun j ↦ gρ.kernel w j) =
      transportField (g.frame w.2 (ρ • w.1)) (g.dual (ρ • w.1, w.2))
        (fun j ↦ g.kernel (ρ • w.1, w.2) j) := by
  dsimp only
  rw [projectedPhaseGeometry_dual_sourceDilation hF hρ hrank hS,
    projectedPhaseGeometry_kernel_sourceDilation hF hρ hrank hS]
  congr 1
  exact funext (ProjectedStressFrame.projectedStress_sourceDilation hρ hF w.1 hrank)

/-- Normalized physical direction, with unchanged carrier labels
(`app:ch_background:eq:bg-Nsigma`). -/
theorem projectedPhaseGeometry_direction_sourceDilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {w : Euclidean n × Z}
    (hrank : Set.range (normalMap F (ρ • w.1)) =
      (normalSpace F (ρ • w.1) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1))
    (row col time : Fin n) :
    (projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).direction w =
      (projectedPhaseGeometry F S row col time).direction (ρ • w.1, w.2) := by
  unfold Geometry.direction Geometry.timeCoefficient
  rw [projectedPhaseGeometry_transportField_sourceDilation hF hρ hrank hS]
  rfl

/-- The same time root normalizes both transport equations
(`app:ch_background:eq:bg-Nsigma`). -/
theorem projectedPhaseGeometry_timeCoefficient_sourceDilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {w : Euclidean n × Z}
    (hrank : Set.range (normalMap F (ρ • w.1)) =
      (normalSpace F (ρ • w.1) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1))
    (row col time : Fin n) :
    (projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).timeCoefficient w =
      (projectedPhaseGeometry F S row col time).timeCoefficient (ρ • w.1, w.2) := by
  unfold Geometry.timeCoefficient
  rw [projectedPhaseGeometry_transportField_sourceDilation hF hρ hrank hS]
  rfl

private theorem reducedOperator_congr_germ
    (F : Euclidean n → Euclidean N) (Q : Euclidean n → Fin n → MetricTensor n)
    {b c : Euclidean n → Euclidean n} {x : Euclidean n}
    (h : b =ᶠ[nhds x] c) : reducedOperator F Q b x = reducedOperator F Q c x := by
  have hd (j : Fin n) : (fun y ↦ b y j) =ᶠ[nhds x] (fun y ↦ c y j) :=
    h.mono fun _ hy ↦ congrArg (fun v : Euclidean n ↦ v j) hy
  have hs : symmCovariantDeriv F b x = symmCovariantDeriv F c x := by
    ext i j
    simp only [symmCovariantDeriv, partialDeriv]
    rw [(hd j).fderiv_eq, (hd i).fderiv_eq, h.eq_of_nhds]
  exact congrArg (fun A ↦ fun i ↦ tensorPairing (Q x i) A) hs

/-- The actual normalized scalar coefficient acquires one factor of `ρ`.
Its derivative is that of the selected adjugate column, and its connection is
the induced one (`app:ch_background:eq:bg-Nsigma`). The seed kernel regularity
is produced by `Geometry.contDiffOn_kernel` from the smooth frame and covector. -/
theorem projectedPhaseGeometry_coefficient_sourceDilation
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1) (hrank : HasFullNormalRankOn F U)
    {S : Euclidean n × Z → ℝ} {z : Z}
    (hS : DifferentiableOn ℝ (fun y ↦ S (y, z)) U)
    (row col time : Fin n) {ρ : ℝ} (hρ : 0 < ρ)
    {x : Euclidean n} (hx : ρ • x ∈ U)
    (hk : ∀ j, DifferentiableAt ℝ
      (fun y ↦ (projectedPhaseGeometry F S row col time).kernel (y, z) j) (ρ • x)) :
    (projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).coefficient
        (x, z) =
      ρ * (projectedPhaseGeometry F S row col time).coefficient (ρ • x, z) := by
  have hSx := hS.differentiableAt (hU.mem_nhds hx)
  have hg : (fun y ↦
      (projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).kernel
        (y, z)) =ᶠ[nhds x]
      (fun y ↦ (projectedPhaseGeometry F S row col time).kernel (ρ • y, z)) := by
    filter_upwards [(hU.preimage (continuous_id.const_smul ρ)).mem_nhds hx] with y hy
    change ρ • y ∈ U at hy
    exact projectedPhaseGeometry_kernel_sourceDilation (w := (y, z)) hF hρ (hrank _ hy)
      (hS.differentiableAt (hU.mem_nhds hy)) row col time
  have hop := reducedOperator_congr_germ (sourceDilation F ρ)
    (ProjectedStressFrame.projectedStress (sourceDilation F ρ)) hg
  have hscale := reducedOperator_sourceDilation_pullback hU hF hflat hρ hx (hrank _ hx) hk 1
  simp only [one_smul, one_mul] at hscale
  unfold Geometry.coefficient Geometry.timeCoefficient
  rw [projectedPhaseGeometry_transportField_sourceDilation hF hρ (hrank _ hx) hSx,
    projectedPhaseGeometry_dual_sourceDilation hF hρ (hrank _ hx) hSx]
  change (_ ⬝ᵥ reducedOperator (sourceDilation F ρ)
    (ProjectedStressFrame.projectedStress (sourceDilation F ρ)) _ x) / _ = _
  rw [hop, hscale, dotProduct_smul, smul_eq_mul, mul_div_assoc]
  rfl

end JanetCartan.NormalizedBackground.SourceGeometry
