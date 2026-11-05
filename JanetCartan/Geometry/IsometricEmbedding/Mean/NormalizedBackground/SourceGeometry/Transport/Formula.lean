module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport.Solution

/-!
# Identification with the actual positive characteristic solution

The exponential-integral formula for `app:ch_background:eq:bg-Nsigma` uses the
actual scaled geometric coefficient. The seed flow stays in the original open
flat rank domain throughout the oriented integration interval. No identity for
the scaled coefficient is a hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

open NullTransport NullTransport.FlowAmplitude

variable {n N : ℕ} {X Z : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Adapted physical coordinates commute with dilation; carrier/canonical
labels stay fixed (`app:ch_background:eq:bg-Nsigma`). -/
theorem coordinates_source_dilation (e : Euclidean n ≃L[ℝ] (ℝ × X))
    (ρ : ℝ) (w : Euclidean n × Z) :
    coordinates e (ρ • w.1, w.2) = transportCoordinateDilation ρ (coordinates e w) := by
  simp [coordinates_apply, transportCoordinateDilation, transportLabelDilation]

/-- The inverse adapted coordinates scale only physical position
(`app:ch_background:eq:bg-Nsigma`). -/
theorem coordinates_symm_source_dilation (e : Euclidean n ≃L[ℝ] (ℝ × X))
    (ρ : ℝ) (q : ℝ × (X × Z)) :
    (coordinates e).symm (transportCoordinateDilation ρ q) =
      (ρ • ((coordinates e).symm q).1, ((coordinates e).symm q).2) := by
  apply (coordinates e).injective
  rw [(coordinates e).apply_symm_apply, coordinates_source_dilation,
    (coordinates e).apply_symm_apply]

/-- The named source scalar equals the published characteristic solution with
initial scalar `ρ` and the *actual* scaled geometric coefficient
(`app:ch_background:eq:bg-Nsigma`).

The seed flow-domain and footpoint-domain hypotheses are the original ones
from `FlowAmplitude.exists_positive_null_amplitude_of_flow`. Only their
restriction to the indicated characteristic is needed for this identity. -/
theorem sourceAmplitude_eq_actual_characteristic_solution
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiff ℝ ∞ F)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1) (hrank : HasFullNormalRankOn F U)
    {S : Euclidean n × Z → ℝ}
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦
      gradient (fun y ↦ S (y, w.2)) w.1) (U ×ˢ V))
    (row col time : Fin n) (e : Euclidean n ≃L[ℝ] (ℝ × X))
    {I : Set ℝ} {A : Set (X × Z)} (hI : OrdConnected I) (h0 : 0 ∈ I)
    {Φ Y : ℝ × (X × Z) → X × Z}
    (hΦU : ∀ t ∈ I, ∀ p ∈ A, (coordinates e).symm (t, Φ (t, p)) ∈ U ×ˢ V)
    {ρ : ℝ} (hρ : 0 < ρ) (q : ℝ × (X × Z))
    (ht : ρ * q.1 ∈ I) (hp : Y (transportCoordinateDilation ρ q) ∈ A) :
    let g := projectedPhaseGeometry F S row col time
    let gρ := projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time
    let α := fun w ↦ transportFromFootpoint
      (flowTransportCoefficient (fun v ↦ g.coefficient ((coordinates e).symm v)) Φ)
      0 (fun _ ↦ 1) Y (coordinates e w)
    sourceAmplitude α ρ ((coordinates e).symm q) =
      transportFromFootpoint
        (flowTransportCoefficient (fun v ↦ gρ.coefficient ((coordinates e).symm v))
          (sourceTransportFlow Φ ρ))
        0 (fun _ ↦ ρ) (sourceTransportFlow Y ρ) q := by
  let C := coordinates (Z := Z) e
  let g := projectedPhaseGeometry F S row col time
  let gρ := projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time
  let c : ℝ × (X × Z) → ℝ := fun v ↦ g.coefficient (C.symm v)
  let cρ : ℝ × (X × Z) → ℝ := fun v ↦ gρ.coefficient (C.symm v)
  let cp : ℝ × (X × Z) → ℝ := fun v ↦ ρ * c (transportCoordinateDilation ρ v)
  have hkreg := contDiffOn_projectedPhaseGeometry_kernel hU hF.contDiffOn hflat hrank
    hξ row col time
  have hcoeff (v : ℝ × (X × Z))
      (hv : C.symm (transportCoordinateDilation ρ v) ∈ U ×ˢ V) : cρ v = cp v := by
    rw [coordinates_symm_source_dilation] at hv
    have hSp : DifferentiableOn ℝ (fun y ↦ S (y, (C.symm v).2)) U := by
      intro y hy
      have hm : (y, (C.symm v).2) ∈ U ×ˢ V := ⟨hy, hv.2⟩
      exact (((hS.contDiffAt ((hU.prod hV).mem_nhds hm)).comp y
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).differentiableWithinAt
    have hkp (j : Fin n) : DifferentiableAt ℝ
        (fun y ↦ g.kernel (y, (C.symm v).2) j) (ρ • (C.symm v).1) :=
      ((contDiffAt_piLp 2).mp
        ((hkreg.contDiffAt ((hU.prod hV).mem_nhds hv)).comp (ρ • (C.symm v).1)
          (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
    dsimp [cρ, cp, c]
    rw [coordinates_symm_source_dilation]
    exact projectedPhaseGeometry_coefficient_sourceDilation hU hF hflat hrank hSp
      row col time hρ hv.1 hkp
  have hpath (s : ℝ) :
      transportCoordinateDilation ρ
        (s, sourceTransportFlow Φ ρ (s, sourceTransportFlow Y ρ q)) =
      (ρ * s, Φ (ρ * s, Y (transportCoordinateDilation ρ q))) := by
    simp [transportCoordinateDilation, sourceTransportFlow,
      transportLabelDilation_inv (ne_of_gt hρ)]
  have he : EqOn
      (fun s ↦ flowTransportCoefficient cρ (sourceTransportFlow Φ ρ)
        (s, sourceTransportFlow Y ρ q))
      (fun s ↦ flowTransportCoefficient cp (sourceTransportFlow Φ ρ)
        (s, sourceTransportFlow Y ρ q)) (uIcc 0 q.1) := by
    intro s hs
    apply hcoeff
    rw [hpath]
    apply hΦU _ _ _ hp
    apply hI.uIcc_subset h0 ht
    have hm : Monotone (fun t : ℝ ↦ ρ * t) := fun _ _ h ↦ mul_le_mul_of_nonneg_left h hρ.le
    simpa only [mul_zero] using hm.image_uIcc_subset (mem_image_of_mem _ hs)
  have hi := intervalIntegral.integral_congr (μ := MeasureTheory.volume) he
  have hformula : transportFromFootpoint (flowTransportCoefficient cρ (sourceTransportFlow Φ ρ))
      0 (fun _ ↦ ρ) (sourceTransportFlow Y ρ) q =
      transportFromFootpoint (flowTransportCoefficient cp (sourceTransportFlow Φ ρ))
        0 (fun _ ↦ ρ) (sourceTransportFlow Y ρ) q := by
    simp only [transportFromFootpoint, characteristicTransport, scalarTransport, transportFactor, hi]
  dsimp only
  change sourceAmplitude (fun w ↦ transportFromFootpoint (flowTransportCoefficient c Φ)
    0 (fun _ ↦ 1) Y (C w)) ρ (C.symm q) = _
  rw [hformula, transportFromFootpoint_sourceTransportFlow c Φ Y (ne_of_gt hρ)]
  simp only [sourceAmplitude, smul_eq_mul, C, coordinates_source_dilation,
    (coordinates e).apply_symm_apply]

/-- The actual scalar formula has initial value exactly `ρ` on the unchanged
linear Cauchy section (`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceAmplitude_characteristic_initial
    (e : Euclidean n ≃L[ℝ] (ℝ × X)) (c : ℝ × (X × Z) → ℝ)
    (Φ Y : ℝ × (X × Z) → X × Z) (ρ : ℝ) (p : X × Z) :
    sourceAmplitude
      (fun w ↦ transportFromFootpoint (flowTransportCoefficient c Φ)
        0 (fun _ ↦ 1) Y (coordinates e w)) ρ (e.symm (0, p.1), p.2) = ρ := by
  let j : X →L[ℝ] Euclidean n := e.symm.toContinuousLinearMap.comp
    ((0 : X →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ X))
  change sourceAmplitude _ ρ (j p.1, p.2) = ρ
  apply sourceAmplitude_initial_scalar j
  simp [j, coordinates_apply, transportFromFootpoint, characteristicTransport]

/-- The directly transformed seed flow solves the direction ODE for the
actual scaled projected frame and scaled phase
(`app:ch_background:eq:bg-Nsigma`). -/
theorem hasDerivAt_sourceTransportFlow_projectedPhaseGeometry
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U) {S : Euclidean n × Z → ℝ}
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (row col time : Fin n) (e : Euclidean n ≃L[ℝ] (ℝ × X))
    {Φ : ℝ × (X × Z) → X × Z} {ρ : ℝ} (hρ : 0 < ρ)
    {t : ℝ} {p : X × Z}
    (hmem : (coordinates e).symm
      (ρ * t, Φ (ρ * t, transportLabelDilation ρ p)) ∈ U ×ˢ V)
    (hΦ : HasDerivAt (fun s ↦ Φ (s, transportLabelDilation ρ p))
      ((e ((projectedPhaseGeometry F S row col time).direction
        ((coordinates e).symm (ρ * t, Φ (ρ * t, transportLabelDilation ρ p))))).2, 0)
      (ρ * t)) :
    HasDerivAt (fun s ↦ sourceTransportFlow Φ ρ (s, p))
      ((e ((projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time).direction
        ((coordinates e).symm (t, sourceTransportFlow Φ ρ (t, p))))).2, 0) t := by
  let w := (coordinates (Z := Z) e).symm (t, sourceTransportFlow Φ ρ (t, p))
  have heq : (ρ • w.1, w.2) = (coordinates e).symm
      (ρ * t, Φ (ρ * t, transportLabelDilation ρ p)) := by
    rw [← coordinates_symm_source_dilation]
    congr 1
    simp [transportCoordinateDilation, sourceTransportFlow,
      transportLabelDilation_inv (ne_of_gt hρ)]
  have hw : (ρ • w.1, w.2) ∈ U ×ˢ V := heq.symm ▸ hmem
  have hSp : DifferentiableAt ℝ (fun y ↦ S (y, w.2)) (ρ • w.1) :=
    ((hS.contDiffAt ((hU.prod hV).mem_nhds hw)).comp (ρ • w.1)
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hd := projectedPhaseGeometry_direction_sourceDilation hF hρ (hrank _ hw.1)
    hSp row col time
  rw [heq] at hd
  change HasDerivAt _ ((e ((projectedPhaseGeometry (sourceDilation F ρ)
    (sourcePhase S ρ) row col time).direction w)).2, 0) t
  rw [hd]
  exact hasDerivAt_sourceTransportFlow (ne_of_gt hρ) hΦ

end JanetCartan.NormalizedBackground.SourceGeometry
