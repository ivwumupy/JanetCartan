module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponse
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
public import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveEnvelope
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfilesTemplate

/-!
# Corrected derivative profiles on the entire original parent cell

The positive scalar has a nonzero constant tail. Its background therefore uses
`fullCorrectedDerivativeAmplitude` on the original parent σ-cover, not the
root-local coefficient cutoff or an extended inner carrier. These estimates
feed the weighted outer Hermitian baseline (`app:ch_waves:eq:background-quadrature`,
`app:ch_response:eq:current-atomic-amplitudes`). The raw coefficients and the
full response are consumed before any working-radius restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
  RawPrimary RawPrimary.AmplitudeGrades CorrectedAtoms

/-- The original doubled parent ball, intersected only with the prescribed
open comparison window of the uncut source response. -/
def parentOpen {n d : ℕ} (c : Euclidean 3 × Euclidean d) (σ : ℝ)
    (W : Set (Euclidean 3 × Euclidean d)) :
    Set (Euclidean n × (Euclidean 3 × Euclidean d)) :=
  ball ((0 : Euclidean n),c) (2*σ) ∩ (univ ×ˢ W)

/-- The parent compact and its neighborhood are fixed before the current
history; only the prescribed static comparison window is used. -/
theorem parent_static_geometry {n d : ℕ} {c : Euclidean 3 × Euclidean d} {σ : ℝ}
    (hσ : 0 < σ) {W : Set (Euclidean 3 × Euclidean d)}
    (hW : IsOpen W) (hcell : closedBall c σ ⊆ W) :
    IsCompact (closedBall ((0 : Euclidean n),c) σ) ∧
    IsOpen (parentOpen (n := n) c σ W) ∧
    closedBall ((0 : Euclidean n),c) σ ⊆ parentOpen c σ W := by
  refine ⟨isCompact_closedBall _ _,isOpen_ball.inter (isOpen_univ.prod hW),?_⟩
  intro q hq
  refine ⟨closedBall_subset_ball (by linarith only [hσ]) hq,mem_univ _,?_⟩
  rw [mem_closedBall,Prod.dist_eq,max_le_iff] at hq
  exact hcell hq.2

/-- The entire closed parent cell has an open neighborhood inside the actual
full-response region. Neither its radius nor its parameter set is shrunk. -/
theorem parent_geometry {n d : ℕ} {c : Euclidean 3 × Euclidean d} {σ : ℝ}
    (hσ : 0 < σ) {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    {W : Set (Euclidean 3 × Euclidean d)}
    (hΩ : closedBall ((0 : Euclidean n),c) (2*σ) ⊆ Ω)
    (hW : IsOpen W) (hcell : closedBall c σ ⊆ W) :
    IsCompact (closedBall ((0 : Euclidean n),c) σ) ∧
    IsOpen (parentOpen (n := n) c σ W) ∧
    closedBall ((0 : Euclidean n),c) σ ⊆ parentOpen c σ W ∧
    parentOpen (n := n) c σ W ⊆ ball ((0 : Euclidean n),c) (2*σ) ∧
    parentOpen (n := n) c σ W ⊆ Ω ∩ (univ ×ˢ W) := by
  refine ⟨isCompact_closedBall _ _,isOpen_ball.inter (isOpen_univ.prod hW),?_,
    inter_subset_left,?_⟩
  · intro q hq
    refine ⟨closedBall_subset_ball (by linarith only [hσ]) hq,mem_univ _,?_⟩
    rw [mem_closedBall,Prod.dist_eq,max_le_iff] at hq
    exact hcell hq.2
  · intro q hq
    exact ⟨hΩ (ball_subset_closedBall hq.1),hq.2⟩

/-- The response producer excludes source size from `Cresp`. The actual size
σ is multiplied exactly once; the raw retained polynomial is unchanged. -/
def correctedCost (n N : ℕ) (Pξ Clead Ccorr Cresp : ℕ → ℝ) (σ : ℝ) (j : ℕ) : ℝ :=
  Polynomial.derivativeProfile n N Pξ Clead Ccorr Clead Ccorr j + σ*Cresp j

theorem correctedCost_nonneg (n N : ℕ) {Pξ Clead Ccorr Cresp : ℕ → ℝ} {σ : ℝ}
    (hPξ : ∀ j, 0 ≤ Pξ j) (hClead : ∀ j, 0 ≤ Clead j)
    (hCcorr : ∀ j, 0 ≤ Ccorr j) (hCresp : ∀ j, 0 ≤ Cresp j) (hσ : 0 ≤ σ) (j : ℕ) :
    0 ≤ correctedCost n N Pξ Clead Ccorr Cresp σ j :=
  add_nonneg
    (Polynomial.polynomialProfiles_nonneg n N hPξ hClead hCcorr hClead hCcorr j).2.2.2.2
    (mul_nonneg hσ (hCresp j))

/-- Reassociate the genuine original linear-response grade without absorbing
or repeating the source size (`app:ch_response:eq:response-graded-derivative`). -/
theorem response_derivative_weight {bound C σ τ K : ℝ} {j r : ℕ}
    (h : bound ≤ C*(τ*σ)*K^(j-r)) :
    bound ≤ τ*(σ*C)*K^(j-r) := by
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

/-- Smoothness follows from the four actual uncontracted raw coefficients and
the SAME full response. No Hermitian or inner-cutoff profile is substituted. -/
theorem corrected_smooth_of_coefficients
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (χ : Euclidean n → ℝ) (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))} (hΩ : IsOpen Ω)
    (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (Polynomial.fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (Polynomial.fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {τ : ℝ} (hτ : τ ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω) :
    ContDiffOn ℝ ∞ (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) Ω := by
  exact (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ).2.sub
    (contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
      hΩ hphase χ B τ hresponse)

end JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles

-- Each field is checked separately at the unchanged default resource limits.
-- The actual event supplies every rate, reserve, raw coefficient and response.
publish_original_parent_static 0
publish_original_parent_static 1
publish_original_parent_static 2
publish_original_parent_static 3
publish_original_parent_static 4
publish_original_parent_static 5
publish_original_parent_static 6
publish_original_parent_dynamic 0
publish_original_parent_dynamic 1
publish_original_parent_dynamic 2
publish_original_parent_dynamic 3
end
