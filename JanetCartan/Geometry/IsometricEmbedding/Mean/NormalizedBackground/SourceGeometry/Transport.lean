module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport.Formula

/-!
# Source-dilated positive geometric null transport

`app:ch_background:eq:bg-Nsigma`, using the seed transport from
`app:ch_waves:thm:leading`. The core is the explicit closed ball of radius `r`,
buffered by the open ball of radius `R`; its image lies in the original seed
domain. All frame, kernel, dual and coefficient scaling is proved in the leaves.

This deduction takes the genuine **seed** phase and positive characteristic
transport from `jc-hamilton-phase`, `jc-actual-carriers`, `jc-null-transport`,
and `jc-leading-wave`. The parent must supply those seed constructions. No
source-scaling identity or scaled solution is an input, and this is not an
unconditional construction of the seed or Theorem 1.1.
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

/-- Assemble the positive source transport on an explicit buffered core,
including identification with the actual characteristic formula, initial
scalar exactly `ρ`, nullness, and the literal projected reduced equation
(`app:ch_background:eq:bg-Nsigma`).

The only scalar formula and transport PDE hypotheses are for the seed at
initial scalar `1`, exactly as supplied by
`FlowAmplitude.exists_positive_null_amplitude_of_flow`. The seed flow stays
in its original geometric domain and its footpoint stays in its original
parameter domain. These original chart hypotheses justify every integral
comparison; no extension of the flat metric beyond that domain is used. -/
theorem source_transport_on_buffered_core
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiff ℝ ∞ F)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1) (hrank : HasFullNormalRankOn F U)
    {S : Euclidean n × Z → ℝ}
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦
      gradient (fun y ↦ S (y, w.2)) w.1) (U ×ˢ V))
    (row col time : Fin n) (e : Euclidean n ≃L[ℝ] (ℝ × X))
    (he : ∀ v : Euclidean n, (e v).1 = v time)
    {I : Set ℝ} {A : Set (X × Z)} {D : Set (ℝ × (X × Z))}
    (hI : OrdConnected I) (h0 : 0 ∈ I) (hD : IsOpen D)
    (hDU : MapsTo (coordinates e).symm D (U ×ˢ V))
    {Φ Y : ℝ × (X × Z) → X × Z}
    (hΦU : ∀ t ∈ I, ∀ p ∈ A, (coordinates e).symm (t, Φ (t, p)) ∈ U ×ˢ V)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ A))
    (hΦ₀ : ∀ p ∈ A, Φ (0, p) = p)
    (hYΦ : ∀ p ∈ A, ∀ t ∈ I, Y (t, Φ (t, p)) = p)
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2)
    (hvelocity : ∀ p ∈ A, ∀ t ∈ I,
      HasDerivAt (fun s ↦ Φ (s, p))
        ((e ((projectedPhaseGeometry F S row col time).direction
          ((coordinates e).symm (t, Φ (t, p))))).2, 0) t)
    {α : Euclidean n × Z → ℝ}
    (hαeq : α = fun w ↦ transportFromFootpoint
      (flowTransportCoefficient (fun v ↦
        (projectedPhaseGeometry F S row col time).coefficient ((coordinates e).symm v)) Φ)
      0 (fun _ ↦ 1) Y (coordinates e w))
    (hα : ContDiffOn ℝ ∞ α (coordinates e ⁻¹' D))
    (hchar : ∀ w ∈ coordinates e ⁻¹' D,
      ((projectedPhaseGeometry F S row col time).symbol w).det = 0)
    (hminor : ∀ w ∈ coordinates e ⁻¹' D,
      ((projectedPhaseGeometry F S row col time).symbol w).adjugate row col ≠ 0)
    (hroot : ∀ w ∈ coordinates e ⁻¹' D, partialDeriv
      (reducedDeterminant (ProjectedStressFrame.projectedStress F w.1))
      (gradient (fun y ↦ S (y, w.2)) w.1) time ≠ 0)
    (hpde : ∀ w ∈ coordinates e ⁻¹' D, (projectedPhaseGeometry F S row col time).dual w ⬝ᵥ
      reducedOperator F (ProjectedStressFrame.projectedStress F)
        (fun y ↦ α (y, w.2) • (projectedPhaseGeometry F S row col time).kernel (y, w.2))
        w.1 = 0)
    {ρ r R : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrR : r < R)
    (hbuffer : MapsTo (fun w : Euclidean n × Z ↦ coordinates e (ρ • w.1, w.2))
      (Metric.ball 0 R ×ˢ V) D) :
    let g := projectedPhaseGeometry F S row col time
    let gρ := projectedPhaseGeometry (sourceDilation F ρ) (sourcePhase S ρ) row col time
    let b := fun w ↦ α w • g.kernel w
    (0 : Euclidean n) ∈ Metric.ball 0 r ∧
    (∀ p : X × Z, sourceAmplitude α ρ (e.symm (0, p.1), p.2) = ρ) ∧
    ContDiffOn ℝ ∞ (sourceAmplitude α ρ)
      {w | coordinates e (ρ • w.1, w.2) ∈ D} ∧
    ContDiffOn ℝ ∞ (sourceAmplitude b ρ)
      {w | coordinates e (ρ • w.1, w.2) ∈ D} ∧
    (∀ p : X × Z, transportLabelDilation ρ p ∈ A →
      sourceTransportFlow Φ ρ (0, p) = p) ∧
    (∀ p : X × Z, transportLabelDilation ρ p ∈ A → ∀ t : ℝ, ρ * t ∈ I →
      sourceTransportFlow Y ρ (t, sourceTransportFlow Φ ρ (t, p)) = p) ∧
    (∀ q : ℝ × (X × Z), transportCoordinateDilation ρ q ∈ D →
      sourceTransportFlow Φ ρ (q.1, sourceTransportFlow Y ρ q) = q.2) ∧
    (∀ p : X × Z, transportLabelDilation ρ p ∈ A → ∀ t : ℝ, ρ * t ∈ I →
      HasDerivAt (fun s ↦ sourceTransportFlow Φ ρ (s, p))
        ((e (gρ.direction ((coordinates e).symm (t, sourceTransportFlow Φ ρ (t, p))))).2, 0) t) ∧
    ∀ x ∈ Metric.closedBall (0 : Euclidean n) r, ∀ z ∈ V,
      sourceAmplitude α ρ (x, z) = transportFromFootpoint
        (flowTransportCoefficient (fun v ↦ gρ.coefficient ((coordinates e).symm v))
          (sourceTransportFlow Φ ρ))
        0 (fun _ ↦ ρ) (sourceTransportFlow Y ρ) (coordinates e (x, z)) ∧
      sourceAmplitude b ρ (x, z) = sourceAmplitude α ρ (x, z) • gρ.kernel (x, z) ∧
      0 < sourceAmplitude α ρ (x, z) ∧
      gρ.symbol (x, z) *ᵥ (fun j ↦ sourceAmplitude b ρ (x, z) j) = 0 ∧
      gρ.dual (x, z) ⬝ᵥ reducedOperator (sourceDilation F ρ)
        (ProjectedStressFrame.projectedStress (sourceDilation F ρ))
        (fun y ↦ sourceAmplitude b ρ (y, z)) x = 0 ∧
      gρ.kernel (x, z) ≠ 0 ∧ gρ.dual (x, z) ≠ 0 ∧ gρ.timeCoefficient (x, z) ≠ 0 ∧
      (e (gρ.direction (x, z))).1 = 1 := by
  dsimp only
  refine ⟨Metric.mem_ball_self hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hαeq]
    exact sourceAmplitude_characteristic_initial e _ Φ Y ρ p
  · exact (contDiffOn_sourceAmplitude hα).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ hw)
  · have hsub : coordinates e ⁻¹' D ⊆ U ×ˢ V := by
      intro w hw
      simpa only [(coordinates e).symm_apply_apply] using hDU (x := coordinates e w) hw
    have hk := contDiffOn_projectedPhaseGeometry_kernel hU hF.contDiffOn hflat hrank
      hξ row col time
    exact (contDiffOn_sourceAmplitude (hα.smul (hk.mono hsub))).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ hw)
  · intro p hp
    exact sourceTransportFlow_initial (ne_of_gt hρ) (hΦ₀ _ hp)
  · intro p hp t ht
    exact sourceTransportFlow_left_inverse (ne_of_gt hρ) (hYΦ _ hp _ ht)
  · intro q hq
    apply sourceTransportFlow_right_inverse (ne_of_gt hρ)
    exact hΦY _ hq
  · intro p hp t ht
    exact hasDerivAt_sourceTransportFlow_projectedPhaseGeometry (Φ := Φ) (p := p) (t := t)
      hU hV hF hrank hS
      row col time e hρ (hΦU _ ht _ hp) (hvelocity _ hp _ ht)
  · intro x hx z hz
    have hxR : x ∈ Metric.ball (0 : Euclidean n) R := Metric.closedBall_subset_ball hrR hx
    have hwB : (x, z) ∈ Metric.ball (0 : Euclidean n) R ×ˢ V := ⟨hxR, hz⟩
    have hwD : coordinates e (ρ • x, z) ∈ D := hbuffer hwB
    have hw : (ρ • x, z) ∈ U ×ˢ V :=
      by simpa only [(coordinates e).symm_apply_apply] using
        hDU (x := coordinates e (ρ • x, z)) hwD
    have hpos : 0 < α (ρ • x, z) := by
      rw [hαeq]
      exact transportFromFootpoint_pos _ _ _ _ _ zero_lt_one
    have ht : ρ * (coordinates e (x, z)).1 ∈ I := by
      change (transportCoordinateDilation ρ (coordinates e (x, z))).1 ∈ I
      rw [← coordinates_source_dilation]
      exact (hYU (x := coordinates e (ρ • x, z)) hwD).1
    have hp : Y (transportCoordinateDilation ρ (coordinates e (x, z))) ∈ A := by
      rw [← coordinates_source_dilation]
      exact (hYU (x := coordinates e (ρ • x, z)) hwD).2
    have hf := sourceAmplitude_eq_actual_characteristic_solution (Φ := Φ) (Y := Y)
      hU hV hF hflat hrank
      hS hξ row col time e hI h0 hΦU hρ (coordinates e (x, z)) ht hp
    dsimp only at hf
    rw [← hαeq, (coordinates e).symm_apply_apply] at hf
    have hwΩ : (ρ • x, z) ∈ coordinates e ⁻¹' D := hwD
    have hαpoint : DifferentiableAt ℝ α (ρ • x, z) :=
      (hα.contDiffAt ((hD.preimage (coordinates e).continuous).mem_nhds hwΩ)).differentiableAt
        (by simp)
    obtain ⟨hd, ha, hn, hP, hk, hl, htime⟩ :=
      sourceAmplitude_positive_null_transport (α := α) (w := (x, z))
        hU hV hF hflat hrank hS hξ
        row col time hρ hw hαpoint hpos
        (hchar (ρ • x, z) hwΩ) (hminor (ρ • x, z) hwΩ)
        (hroot (ρ • x, z) hwΩ) (hpde (ρ • x, z) hwΩ)
    exact ⟨hf, hd, ha, hn, hP, hk, hl, htime,
      (he _).trans (Geometry.direction_time _ htime)⟩

end JanetCartan.NormalizedBackground.SourceGeometry
