module

public import JanetCartan.Iteration.PhysicalPrimary.LeadingSource
public import JanetCartan.Iteration.PhysicalInitialization.CurrentInverse
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfilesTemplate

/-!
# The original current reduced source and its actual small supports

The finite-word construction uses the true source factor eta, not the larger
raw-primary cutoff, and preserves the closed support of the SAME parameter
cutoff theta. The current/leading specialization below will retain the original
Q/Phi/Y and all scalar budgets; no source or response estimate is assumed.
Consumers: the actual complete residual word and its reserved Fourier datum
(`app:ch_response:eq:response-graded-source`, `app:ch_regular:lem:finite-chain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius Topology
namespace JanetCartan.PhysicalPrimary.OriginalSourceProfiles
open ResponsePrimarySources Sampling.BackgroundModulation PhysicalSeed PhysicalInitialization
open ActualCarriers FrozenMenu CurrentFullPhase RawPrimary ResponseSourceExtension

/-- The actual original-cell parameter cutoff is fixed before any source scale,
history or sample: inner radius three halves and outer radius seven quarters
of the SAME comparison radius. Its plateau has a neighborhood of the whole
closed original cell (`app:ch_response:eq:response-graded-source`). -/
def parameterCutoff {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (cell : OriginalBoundary.centers hn a) :
    ContDiffBump (cell.1.1, (OriginalBoundary.T hn a).reference.spatialPatch cell.1.1) where
  rIn := 3 * OriginalBoundary.σcover hn a cell / 2
  rOut := 7 * OriginalBoundary.σcover hn a cell / 4
  rIn_pos := by
    have hσ := (OriginalBoundary.comparison_pos hn a cell).2.2.2.2.2.2.2.2
    positivity
  rIn_lt_rOut := by
    have hσ := (OriginalBoundary.comparison_pos hn a cell).2.2.2.2.2.2.2.2
    linarith

/-- The SAME parameter mask has closed support strictly inside the doubled
original cell and equals one as a germ on every point of the closed original
cell. This preserves all parameter jets, not only pointwise values. -/
theorem parameterCutoff_spec {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (cell : OriginalBoundary.centers hn a) :
    let θ := parameterCutoff hn a cell
    let center := (cell.1.1, (OriginalBoundary.T hn a).reference.spatialPatch cell.1.1)
    let σ := OriginalBoundary.σcover hn a cell
    ContDiff ℝ ∞ (θ : Euclidean 3 × Euclidean (n-1) → ℝ) ∧
      HasCompactSupport (θ : Euclidean 3 × Euclidean (n-1) → ℝ) ∧
      tsupport (θ : Euclidean 3 × Euclidean (n-1) → ℝ) ⊆ ball center (2*σ) ∧
      ∀ c ∈ closedBall center σ, (θ : Euclidean 3 × Euclidean (n-1) → ℝ) =ᶠ[𝓝 c] 1 := by
  intro θ center σ
  have hσ : 0 < σ := (OriginalBoundary.comparison_pos hn a cell).2.2.2.2.2.2.2.2
  refine ⟨θ.contDiff, θ.hasCompactSupport, ?_, ?_⟩
  · rw [θ.tsupport_eq]
    apply closedBall_subset_ball
    change 7*σ/4 < 2*σ
    linarith
  · intro c hc
    apply θ.eventuallyEq_one_of_mem_ball
    apply closedBall_subset_ball (show σ < θ.rIn from ?_) hc
    change σ < 3*σ/2
    linarith

/-- The strengthened original cap yields a genuine nonempty scalar interval,
with exactly the current leading upper and lower budgets. -/
theorem scalar_budget_gap {σ C : ℝ} (hσ : 0 < σ) (hC : 1 ≤ C) :
    σ*Real.sqrt (1/2) < σ*C := by
  have hs : Real.sqrt (1/2) < (1 : ℝ) := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)
    nlinarith [Real.sqrt_nonneg (1/2 : ℝ)]
  exact mul_lt_mul_of_pos_left (hs.trans_le hC) hσ


/-- The literal reduced source retains both the small physical source factor
and the original parameter cutoff. The full raw strain inside the contraction
is unchanged; no support condition is imposed on the broader chiSrc. -/
theorem reducedSource_zero_off_cutoffs {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n)
    (astrain : Euclidean n × (Euclidean 3 × Euclidean (n-1)) →
      Matrix (Fin n) (Fin n) ℂ)
    (χsrc η : Euclidean n → ℝ)
    (θ : Euclidean 3 × Euclidean (n-1) → ℝ) :
    let a := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
      θ w.2 • (χsrc w.1 • (η w.1 •
        ((1/2 : ℝ) • complexStressContraction (Q w.1) (astrain w))))
    (∀ w, w.1 ∉ tsupport η → a w = 0) ∧
      (∀ w, w.2 ∉ tsupport θ → a w = 0) := by
  intro a
  constructor
  · intro w hw
    have hz : η w.1 = 0 := image_eq_zero_of_notMem_tsupport hw
    simp only [a, hz, zero_smul, smul_zero]
  · intro w hw
    have hz : θ w.2 = 0 := image_eq_zero_of_notMem_tsupport hw
    simp only [a, hz, zero_smul]

/-- Closed physical/parameter support for the SAME literal full-strain datum.
In particular the finite-word parameter source is `tsupport theta`, not the
larger protected union of doubled original cells. -/
theorem reducedSource_tsupport_subset {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n)
    (astrain : Euclidean n × (Euclidean 3 × Euclidean (n-1)) →
      Matrix (Fin n) (Fin n) ℂ)
    (χsrc η : Euclidean n → ℝ)
    (θ : Euclidean 3 × Euclidean (n-1) → ℝ) :
    tsupport (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
      θ w.2 • (χsrc w.1 • (η w.1 •
        ((1/2 : ℝ) • complexStressContraction (Q w.1) (astrain w))))) ⊆
      tsupport η ×ˢ tsupport θ := by
  obtain ⟨hphysical, hparameter⟩ := reducedSource_zero_off_cutoffs Q astrain χsrc η θ
  apply closure_minimal _ ((isClosed_tsupport η).prod (isClosed_tsupport θ))
  intro w hw
  exact ⟨by_contra (fun h ↦ hw (hphysical w h)),
    by_contra (fun h ↦ hw (hparameter w h))⟩

/-- The two original plateaus reduce the literal full-strain datum to the
small source eta. This is the equality needed to instantiate the actual
corrected atom with source chi2, while keeping the separate large output mask.
No plateau of eta on the broad measured source support is required. -/
theorem reducedSource_mask_normalization {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n)
    (astrain : Euclidean n × (Euclidean 3 × Euclidean (n-1)) →
      Matrix (Fin n) (Fin n) ℂ)
    (χsrc η χenv : Euclidean n → ℝ)
    (θ : Euclidean 3 × Euclidean (n-1) → ℝ)
    (hsource : ∀ x, χsrc x * η x = η x)
    (henv : ∀ x ∈ tsupport η, χenv x = 1) :
    (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
      θ w.2 • (χsrc w.1 • (η w.1 • ((1/2 : ℝ) •
        complexStressContraction (Q w.1) (χenv w.1 • astrain w))))) =
    (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
      θ w.2 • (η w.1 • ((1/2 : ℝ) • complexStressContraction (Q w.1) (astrain w)))) := by
  funext w
  by_cases hzero : η w.1 = 0
  · simp only [hzero, zero_smul, smul_zero]
  · have hplateau := henv w.1 (subset_tsupport η hzero)
    rw [hplateau, one_smul]
    have hmul : χsrc w.1 • (η w.1 •
        ((1/2 : ℝ) • complexStressContraction (Q w.1) (astrain w))) =
        η w.1 • ((1/2 : ℝ) • complexStressContraction (Q w.1) (astrain w)) := by
      rw [smul_smul, hsource]
    exact congrArg (fun v : EuclideanSpace ℂ (Fin n) ↦ θ w.2 • v) hmul

/-- The full native source estimate transfers without loss to the literal
small-cutoff raw-strain datum. This internal implication is applied below to
the actual original source producer; it is not an extra response hypothesis
(`app:ch_response:eq:response-graded-source`). -/
theorem normalize_full_source_fourier
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}}
    {F : Euclidean n → Euclidean N} {row col : Fin n}
    {Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))}
    {scalar : Euclidean (n-1) × Euclidean 3 → ℝ}
    {core chart : Set (Euclidean n)} {χenv : OutputCutoff core chart}
    {τ : ℝ} {χsrc η : Euclidean n → ℝ}
    {θ : Euclidean 3 × Euclidean (n-1) → ℝ}
    {C : ℕ → ℕ → ℝ} {size K : ℝ} {reserve : ℕ}
    (hsource : ∀ x, χsrc x * η x = η x)
    (henv : ∀ x ∈ tsupport η, χenv.toFun x = 1)
    (hbound : LeadingReducedSourceFourierBounds
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
        θ w.2 • (χsrc w.1 • (η w.1 • ((1/2 : ℝ) •
          complexStressContraction (Q.1 w.1)
            (fullStrainEnvelope T Q F row col Φ Y scalar χenv τ w.2 w.1)))))
      χenv.toFun C size K reserve) :
    let a := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
      θ w.2 • (η w.1 • ((1/2 : ℝ) • complexStressContraction (Q.1 w.1)
        (fullPrimaryStrainAmplitude T Q F row col Φ Y scalar τ w)))
    LeadingReducedSourceFourierBounds a η C size K reserve ∧
      ∀ w, w.2 ∉ tsupport θ → a w = 0 := by
  have heq :
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
        θ w.2 • (χsrc w.1 • (η w.1 • ((1/2 : ℝ) •
          complexStressContraction (Q.1 w.1)
            (fullStrainEnvelope T Q F row col Φ Y scalar χenv τ w.2 w.1))))) =
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
        θ w.2 • (η w.1 • ((1/2 : ℝ) • complexStressContraction (Q.1 w.1)
          (fullPrimaryStrainAmplitude T Q F row col Φ Y scalar τ w)))) := by
    simpa only [fullStrainEnvelope_eq] using
      reducedSource_mask_normalization Q.1
        (fullPrimaryStrainAmplitude T Q F row col Φ Y scalar τ) χsrc η χenv.toFun θ hsource henv
  rw [heq] at hbound
  refine ⟨⟨hbound.1, ?_, hbound.2.2⟩, ?_⟩
  · intro w hw
    simp only [image_eq_zero_of_notMem_tsupport hw, zero_smul, smul_zero]
  · intro w hw
    simp only [image_eq_zero_of_notMem_tsupport hw, zero_smul]

end JanetCartan.PhysicalPrimary.OriginalSourceProfiles

apply_original_current_reduced_source
apply_actual_original_source_masks
prove_actual_original_source_normalization
