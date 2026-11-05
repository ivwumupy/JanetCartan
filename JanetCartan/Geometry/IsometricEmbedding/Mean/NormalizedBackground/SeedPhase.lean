module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.CarrierData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.NormalizedTransport

/-!
# Normalization of the retained seed phase

The phases below are those of `PatchQuantitativeFamily.currentChart`, used by
`FrozenModel.normalizedCarrierData`. The centered Cauchy value and nonzero
physical covector are proved from that chart. One buffer works for every mixed
derivative of the phase, covector and canonical footpoint, through scale zero
(`app:ch_background:prop:bg-normalized`). No new Hamilton or transport family
is selected, and the canonical footpoint is never replaced by the density's
ODE footpoint. The positive scalar/null amplitude remains a separate input
to the final mean construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground
open ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase SourceGeometry
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumNormal.FrozenModel
open ContinuumNormal.CarrierVariation.FamilyInputs

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The actual retained carrier has the centered Cauchy value required by
`SourceGeometry.exists_sourcePrincipalMean_and_phase_bounds`, on the doubled
patch (`app:ch_background:eq:bg-Nsigma`). -/
theorem retained_carrier_phase_zero {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) : T.carrier Q 0 z = 0 := by
  exact seedHamiltonPhase_zero (T.currentChart Q)
    (T.current_section_source Q (by simpa using T.reference.radius_pos) hz)

/-- Nonvanishing is supplied by the punctured domain of the literal determinant
Hamiltonian. No positive covector bound is assumed
(`app:ch_background:prop:bg-normalized`, zero-scale normal argument). -/
theorem retained_carrierGradient_ne_zero {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball 0 T.physicalRadius)
    (hz : z ∈ parameterInterior (2 * P.radius)) : T.carrierGradient Q x z ≠ 0 := by
  exact (carrierPhase_gradient_mem_domain (T.currentChart Q) T.reference.spatialPatch
    (T.reference.target_contains x hx z hz)).2

/-- The physical covector of the existing normalized phase is the actual
retained carrier gradient pulled back by source dilation, including at zero.
The centered phase premise is discharged from its Cauchy section
(`app:ch_background:eq:bg-Nsigma`). -/
theorem normalizedCovector_eq_retainedCarrierGradient {c C : ℝ} (hP : P.IsValid c C)
    {σ : ℝ} {x : Euclidean n} {z : CarrierParameter}
    (hx : σ • x ∈ ball 0 T.physicalRadius)
    (hz : parameter z ∈ parameterInterior (2 * P.radius)) :
    normalizedCovector T Q σ x z = T.carrierGradient Q (σ • x) (parameter z) := by
  by_cases hσ : σ = 0
  · subst σ
    simpa only [zero_smul] using (normalizedCovector_zero T Q x z).trans
      (seedCovector_spatialPatch T Q z)
  have hS := T.carrier_smooth hP Q
  have he : (fun y ↦ normalizedPhase T Q σ y (T.reference.spatialPatch (parameter z))) =
      fun y ↦ sourcePhaseExtension
        (fun p : Euclidean n × Euclidean 3 ↦ T.carrier Q p.1 p.2)
        (σ, (y, parameter z)) := rfl
  unfold normalizedCovector
  rw [he]
  exact gradient_sourcePhaseExtension_position isOpen_ball (convex_ball _ _) hS
    (fun a ha ↦ retained_carrier_phase_zero T Q (fun i ↦ (ha i).le))
    (mem_ball_self T.physicalRadius_pos) hσ hx hz

/-- One common buffer, chosen before the derivative order, for the actual
normalized phase, physical covector, and canonical footpoint used by
`normalizedCarrierData`. The compact carrier set is in the original Euclidean
labels; no measure or density footpoint is changed
(`app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_phase_normalization_bounds {c C : ℝ} (hP : P.IsValid c C)
    {D : Set (Euclidean n)} (hD : IsCompact D)
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hKW : K ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let W := parameter ⁻¹' parameterInterior (3 * P.radius / 2)
    let J := fun q : ℝ × (Euclidean n × CarrierParameter) ↦
      (normalizedPhase T Q q.1 q.2.1 (T.reference.spatialPatch (parameter q.2.2)),
        normalizedCovector T Q q.1 q.2.1 q.2.2,
        normalizedTransportPosition T Q q.1 q.2)
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ContDiffOn ℝ ∞ J (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) ∧
      (∀ σ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B, σ • x ∈ ball 0 T.physicalRadius) ∧
      (∀ σ ∈ Ioc (0 : ℝ) r, ∀ x ∈ B, ∀ z ∈ W,
        normalizedPhase T Q σ x (T.reference.spatialPatch (parameter z)) =
          σ⁻¹ * T.carrier Q (σ • x) (parameter z) ∧
        normalizedCovector T Q σ x z = T.carrierGradient Q (σ • x) (parameter z) ∧
        normalizedCovector T Q σ x z ≠ 0) ∧
      ∀ s : ℕ, ∃ M > 0, ∀ σ ∈ Icc (0 : ℝ) r, ∀ x ∈ D, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ s J (σ, (x, z))‖ ≤ M := by
  let W := parameter ⁻¹' parameterInterior (3 * P.radius / 2)
  let J := fun q : ℝ × (Euclidean n × CarrierParameter) ↦
    (normalizedPhase T Q q.1 q.2.1 (T.reference.spatialPatch (parameter q.2.2)),
      normalizedCovector T Q q.1 q.2.1 q.2.2,
      normalizedTransportPosition T Q q.1 q.2)
  have hW : IsOpen W := (isOpen_parameterInterior _).preimage parameter.continuous
  have hmiddle : ∀ z ∈ W, parameter z ∈ parameterInterior (2 * P.radius) := by
    intro z hz i
    exact (hz i).trans (by linarith [hP.1])
  obtain ⟨B, hB, hDB, r₀, hr₀, hseg₀⟩ := exists_source_phase_buffer
    isOpen_ball (mem_ball_self T.physicalRadius_pos) hD
  let r := min r₀ 1
  have hr : 0 < r := lt_min hr₀ zero_lt_one
  have hseg : ∀ σ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B,
      ∀ t ∈ Ioo (-1 : ℝ) 2, (t * σ) • x ∈ ball 0 T.physicalRadius := by
    intro σ hσ x hx t ht
    exact hseg₀ σ ⟨by linarith [hσ.1, min_le_left r₀ 1],
      by linarith [hσ.2, min_le_left r₀ 1]⟩ x hx t ht
  have hmaps (σ) (hσ : σ ∈ Ioo (-2 * r) (2 * r)) (x) (hx : x ∈ B) :
      σ • x ∈ ball 0 T.physicalRadius := by
    simpa using hseg σ hσ x hx 1 ⟨by norm_num, by norm_num⟩
  have hS : ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦ T.carrier Q p.1 (parameter p.2))
      (ball 0 T.physicalRadius ×ˢ W) :=
    (T.carrier_smooth hP Q).comp
      (contDiffOn_fst.prodMk (parameter.contDiff.comp_contDiffOn contDiffOn_snd))
      (fun p hp ↦ ⟨hp.1, hmiddle p.2 hp.2⟩)
  have hIW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hphase : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean n × CarrierParameter) ↦
        normalizedPhase T Q q.1 q.2.1 (T.reference.spatialPatch (parameter q.2.2)))
      (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) := by
    have hh := contDiffOn_sourcePhaseExtension isOpen_ball hW
      (isOpen_Ioo.prod (hB.prod hW)) isOpen_Ioo hIW hS
      (fun q hq t ht ↦ ⟨hseg q.1 hq.1 q.2.1 hq.2.1 t ht, hq.2.2⟩)
    have he : (fun q : ℝ × (Euclidean n × CarrierParameter) ↦
        normalizedPhase T Q q.1 q.2.1 (T.reference.spatialPatch (parameter q.2.2))) =
        sourcePhaseExtension
          (fun p : Euclidean n × CarrierParameter ↦ T.carrier Q p.1 (parameter p.2)) := by
      funext q
      rfl
    rw [he]
    exact hh
  have hcov : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean n × CarrierParameter) ↦
        normalizedCovector T Q q.1 q.2.1 q.2.2)
      (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) := by
    apply ((T.carrierGradient_smooth hP Q).comp
      ((contDiffOn_fst.smul contDiffOn_snd.fst).prodMk
        (parameter.contDiff.comp_contDiffOn contDiffOn_snd.snd))
      (fun q hq ↦ ⟨hmaps q.1 hq.1 q.2.1 hq.2.1, hmiddle q.2.2 hq.2.2⟩)).congr
    intro q hq
    exact normalizedCovector_eq_retainedCarrierGradient T Q hP
      (hmaps q.1 hq.1 q.2.1 hq.2.1) (hmiddle q.2.2 hq.2.2)
  have hζ : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦ T.reference.spatialPatch (parameter z)) W :=
    (T.reference.spatialPatch_smooth hP).comp parameter.contDiff.contDiffOn hmiddle
  have hpr : T.physicalRadius ≤ T.family.radius := by
    have hh := min_le_left T.family.radius (3 * T.family.sourceRadius)
    have hp := T.physicalRadius_pos
    dsimp [PatchQuantitativeFamily.physicalRadius] at hp ⊢
    linarith
  have htransport : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean n × CarrierParameter) ↦ normalizedTransportPosition T Q q.1 q.2)
      (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) :=
    contDiffOn_sourceTransportPosition isOpen_ball hB isOpen_ball
      (zeroEnergyPhase_smooth T Q) hζ
      (fun z hz ↦ spatialPatch_mem_phaseBuffer T hP (fun i ↦ (hz i).le))
      (fun σ hσ x hx t ht ↦ ball_subset_ball hpr (hseg σ hσ x hx t ht))
  have hJ : ContDiffOn ℝ ∞ J (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) :=
    hphase.prodMk (hcov.prodMk htransport)
  refine ⟨B, hB, hDB, r, hr, min_le_right _ _, hJ, hmaps, ?_, ?_⟩
  · intro σ hσ x hx z hz
    have hσ' : σ ∈ Ioo (-2 * r) (2 * r) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hscaled := hmaps σ hσ' x hx
    have hξ := normalizedCovector_eq_retainedCarrierGradient T Q hP hscaled (hmiddle z hz)
    refine ⟨?_, hξ, ?_⟩
    swap
    · rw [hξ]
      exact retained_carrierGradient_ne_zero T Q hscaled (hmiddle z hz)
    exact (sourcePhase_eq_extension isOpen_ball (convex_ball _ _)
      ((hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hz⟩)).of_le (by simp))
      (retained_carrier_phase_zero T Q (fun i ↦ (hmiddle z hz i).le))
      (mem_ball_self T.physicalRadius_pos) hscaled hσ.1.ne').symm
  · intro s
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod (hD.prod hK)).exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hJ
        (isOpen_Ioo.prod (hB.prod hW)) (by simp)).mono
        (show Icc (0 : ℝ) r ×ˢ D ×ˢ K ⊆ Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W from by
          intro q hq
          exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hDB hq.2.1, hKW hq.2.2⟩))
    exact ⟨|M| + 1, by positivity, fun σ hσ x hx z hz ↦
      (hM (σ, (x, z)) ⟨hσ, hx, hz⟩).trans ((le_abs_self M).trans (by linarith))⟩

end JanetCartan.NormalizedBackground
