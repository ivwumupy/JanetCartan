module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.PhaseProfiles
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-!
# Actual Hamilton-position profiles on the retained primitive chart

The position in the full reflected amplitude is the covector derivative of
the normalized seed phase, not the inverse ODE density footpoint. Its entire
profile on the supplied primitive chart follows from the existing joint
seed-phase construction. The common scale interval is chosen before every
derivative order. This discharges the Hamilton-position input of
`exists_normalizedCarrierData_density_reflected_bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedCarrierProfiles
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier
open ContinuumNormal.FrozenModel ContinuumNormalReduction.TransportSymbol

/-- Uniform bounds for the literal normalized Hamilton position, including
scale zero, on the SAME primitive chart. The supplied spatial region need
only lie in a fixed ball; the seed-phase producer chooses a common scale
cap and all derivative constants before the scale. No position estimate,
inverse-flow identification, or amplitude estimate is assumed
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_normalizedTransportPosition_profiles
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    {R : ℝ} (hD : D.region ⊆ ball (0 : Euclidean n) R ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2))) :
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧ ∃ H : ℕ → ℝ, (∀ p, 0 < H p) ∧
      ∀ σ ∈ Icc (0 : ℝ) σ₀,
        ContDiffOn ℝ ∞ (normalizedTransportPosition T Q₀ σ) D.region ∧
        ∀ p, cNorm D.carrier p (normalizedTransportPosition T Q₀ σ) ≤ H p := by
  let W := parameter ⁻¹' parameterInterior (3 * P.radius / 2)
  let K := Prod.snd '' D.carrier
  have hK : IsCompact D.carrier := isCompact_closedBall ..
  have hKW : K ⊆ W := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hD (D.ball_subset hp)).2
  obtain ⟨B, hB, hDB, σ₀, hσ₀, hσ₁, κ, _, A, hA, hJ, _, _, hb, _⟩ :=
    ContinuumAdjoint.Canonical.NormalizedFamily.exists_normalized_phase_compact_profiles
      T Q₀ hP (isCompact_closedBall (0 : Euclidean n) R)
      (hK.image continuous_snd) hKW
  let J := fun q : ℝ × (Euclidean n × CarrierParameter) ↦
    (normalizedPhase T Q₀ q.1 q.2.1 (T.reference.spatialPatch (parameter q.2.2)),
      normalizedCovector T Q₀ q.1 q.2.1 q.2.2,
      normalizedTransportPosition T Q₀ q.1 q.2)
  let L : (ℝ × (Euclidean n × Euclidean (n - 1))) →L[ℝ] Euclidean (n - 1) :=
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean (n - 1))).comp
      (ContinuousLinearMap.snd ℝ ℝ (Euclidean n × Euclidean (n - 1)))
  have hBW : IsOpen (B ×ˢ W) :=
    hB.prod ((isOpen_parameterInterior _).preimage parameter.continuous)
  have hregion : D.region ⊆ B ×ˢ W := fun p hp ↦
    ⟨hDB (ball_subset_closedBall (hD hp).1), (hD hp).2⟩
  refine ⟨σ₀, hσ₀, hσ₁, fun p ↦ ‖L‖ * (∑ j ∈ Finset.range (p + 1), A j) + 1,
    fun p ↦ by
      have hsum : 0 ≤ ∑ j ∈ Finset.range (p + 1), A j :=
        Finset.sum_nonneg (fun j _ ↦ (hA j).le)
      positivity, ?_⟩
  intro σ hσ
  have hscale : σ ∈ Ioo (-2 * σ₀) (2 * σ₀) := by
    constructor <;> linarith [hσ.1, hσ.2]
  have hslice : ContDiffOn ℝ ∞ (fun p ↦ J (σ, p)) (B ×ˢ W) :=
    hJ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨hscale, hp⟩)
  refine ⟨hslice.snd.snd.mono hregion, ?_⟩
  intro p
  have hproj := FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on hK p L
    (fun q hq ↦ (hslice.contDiffAt
      (hBW.mem_nhds (hregion (D.ball_subset hq)))).of_le (by simp))
  have hsliceBound : cNorm D.carrier p (fun q ↦ J (σ, q)) ≤
      ∑ j ∈ Finset.range (p + 1), A j := by
    apply cNorm_le_sum_of_bounds (fun j _ ↦ (hA j).le)
    intro j _ q hq
    exact (hb j σ hσ q.1 (ball_subset_closedBall (hD (D.ball_subset hq)).1)
      q.2 ⟨q, hq, rfl⟩).2
  change cNorm D.carrier p (normalizedTransportPosition T Q₀ σ) ≤
    ‖L‖ * cNorm D.carrier p (fun q ↦ J (σ, q)) at hproj
  exact (hproj.trans (mul_le_mul_of_nonneg_left hsliceBound (norm_nonneg L))).trans
    (le_add_of_nonneg_right zero_le_one)

end JanetCartan.ContinuumRow.NormalizedCarrierProfiles
