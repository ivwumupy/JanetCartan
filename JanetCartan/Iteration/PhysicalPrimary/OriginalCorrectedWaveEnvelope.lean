module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveJets
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponse
public import JanetCartan.Iteration.PhysicalPrimary.OriginalActualInitialSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointProfiles
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalWorkingProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEvent
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate

/-!
# The same corrected displacement envelope before sharp spatial remodulation

The actual native-row application below uses the retained raw coefficient
profiles on the ORIGINAL parent cell, before the optional restriction to the
smaller sampling ball. The original physical cutoff chart and every whole-wave
shifted closed parameter cell fit this parent cell. Neither the wave, its scalar,
the source inverse, nor a physical cutoff is replaced
(`app:ch_response:eq:current-atomic-amplitudes`, `main:eq:primary-fixed-scales`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
  RawPrimary RawPrimary.AmplitudeGrades

/-- The original parent compact, unlike its smaller sampling sub-ball, contains
all the whole-wave shifted parameters. It lies in the SAME uncut response region. -/
theorem parent_compact_in_response {n d : ℕ} {c : Euclidean 3 × Euclidean d}
    {σ : ℝ} (hσ : 0 < σ)
    {O : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    {W : Set (Euclidean 3 × Euclidean d)}
    (hO : closedBall ((0 : Euclidean n),c) (2*σ) ⊆ O)
    (hW : closedBall c σ ⊆ W) :
    closedBall ((0 : Euclidean n),c) σ ⊆ O ∩ (univ ×ˢ W) := by
  intro q hq
  refine ⟨hO (closedBall_subset_closedBall (by linarith only [hσ]) hq), mem_univ _, ?_⟩
  rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hq
  exact hW hq.2

/-- Full response regularity on univ times the doubled parameter window
restricts to the original doubled parent ball without a source-chart premise. -/
theorem parent_ball_in_parameter_window {n d : ℕ} (c : Euclidean 3 × Euclidean d) (σ : ℝ) :
    ball ((0 : Euclidean n),c) (2*σ) ⊆ univ ×ˢ ball c (2*σ) := by
  intro q hq
  rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq
  exact ⟨mem_univ _,hq.2⟩

/-- The old physical cutoff chart and the full closed parameter cell already
fit the retained raw compact. No smaller sampling radius is asserted here. -/
theorem cutoff_chart_product_in_parent {n d : ℕ} {c : Euclidean 3 × Euclidean d}
    {σ : ℝ} {X : Set (Euclidean n)} (hX : X ⊆ ball (0 : Euclidean n) σ) :
    X ×ˢ closedBall c σ ⊆ closedBall ((0 : Euclidean n),c) σ := by
  intro q hq
  rw [mem_closedBall, Prod.dist_eq, max_le_iff]
  exact ⟨(hX hq.1).le,hq.2⟩

/-- The corrected displacement cost combines the existing raw polynomial
budget with the original response cost. The response constant itself excludes
size; the genuine native size σ is inserted here once and only once. -/
def correctedDisplacementCost (A B D : ℕ → ℝ) (σ : ℝ) (j : ℕ) : ℝ :=
  Polynomial.displacementProfile A B A B j + σ * D j

theorem correctedDisplacementCost_nonneg {A B D : ℕ → ℝ} {σ : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hD : ∀ j, 0 ≤ D j)
    (hσ : 0 ≤ σ) (j : ℕ) : 0 ≤ correctedDisplacementCost A B D σ j := by
  exact add_nonneg (add_nonneg (add_nonneg (hA j) (add_nonneg (hA j) (hB j)))
    (hB j)) (mul_nonneg hσ (hD j))

/-- Literal rearrangement of the response producer's τ²-size bound into the
existing corrected-atom displacement theorem, with no change of source size. -/
theorem response_displacement_weight {bound C σ τ K : ℝ} {j r : ℕ}
    (h : bound ≤ C * (τ^2*σ) * K^(j-r)) :
    bound ≤ τ^2 * (σ*C) * K^(j-r) := by
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

/-- The raw spatial phase loses no constant in passing from its literal
Euclidean gradient to its next derivative (`app:ch_waves:eq:graded-phase`). -/
theorem phase_succ_norm_eq_gradient {n : ℕ} (f : Euclidean n → ℝ) (j : ℕ)
    (x : Euclidean n) :
    ‖iteratedFDeriv ℝ (j+1) f x‖ = ‖iteratedFDeriv ℝ j (gradient f) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv, ← toDual_comp_gradient]
  exact (InnerProductSpace.toDual ℝ (Euclidean n)).norm_iteratedFDeriv_comp_left (gradient f) x j

/-- Sharp physical phase jets from the SAME retained joint gradient profile.
Only the physical slice and natural-exponent monotonicity are used; neither a
new phase extension nor an equality outside its true domain is required. -/
theorem phase_spatial_jets_of_retained_profile
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {J Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    {rpar : ℕ} {L : ℝ} (hL : 1 ≤ L) {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hp : HasDerivativeProfile J
      (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar+3) L C)
    (j : ℕ) (w : Euclidean n × (Euclidean 3 × Euclidean (n-1))) (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ (j+1) (fun y ↦ phase T Q y w.2.2) w.1‖ ≤ C j * L^j := by
  have hg : ContDiffOn ℝ ∞ (fun q ↦ phaseGradient T Q q.1 q.2.2) Ω :=
    (phaseGradient_smooth T Q).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  rw [phase_succ_norm_eq_gradient]
  change ‖iteratedFDeriv ℝ j (fun y ↦ phaseGradient T Q y w.2.2) w.1‖ ≤ _
  exact (norm_iteratedFDeriv_physical_slice_le hΩ hg (hJΩ hw) j).trans
    ((norm_iteratedFDeriv_le_profile hJ hΩ hJΩ hg hp j hw).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.sub_le _ _)) (hC j)))

end JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

publish_original_corrected_envelope_raw
