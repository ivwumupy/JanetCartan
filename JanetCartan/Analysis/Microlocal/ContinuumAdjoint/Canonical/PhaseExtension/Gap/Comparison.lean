module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Gap.Frozen
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhaseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.ReferenceJoint

/-!
# Actual transported-position comparison from the primitive frame threshold

The covector gradient of the current phase and its physical derivative are
controlled by the joint phase `C²` error. Orthogonal physical coordinates and
covector extraction are contractions, so the estimates hold throughout the
fixed extension domain. The phase-comparison producer chooses the threshold
before the current frame; frame-order monotonicity gives the required `C⁶`
neighborhood.

These are the value and derivative inputs to
`transverseGap_affineExtension_of_comparison`. Cutoff selection and the final
global gap assembly remain with that theorem's caller.

Source: `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

private def covectorDifferentialExtraction (n : ℕ) :
    ((WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) →L[ℝ] ℝ) →L[ℝ]
      Euclidean (n - 1) :=
  (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℝ (Euclidean (n - 1))
      (WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) ℝ).flip
        (ContinuousLinearMap.inr ℝ _ _))

private theorem norm_covectorDifferentialExtraction_le (n : ℕ) :
    ‖covectorDifferentialExtraction n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖(InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm
    (L.comp (ContinuousLinearMap.inr ℝ _ _))‖ ≤ 1 * ‖L‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  simpa using L.le_opNorm (0, v)

private theorem gradient_eq_covectorDifferentialExtraction {n : ℕ}
    {S : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) → ℝ}
    {q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)}
    (hS : DifferentiableAt ℝ S q) :
    gradient (fun ζ ↦ S (q.1, ζ)) q.2 =
      covectorDifferentialExtraction n (fderiv ℝ S q) := by
  have hi : HasFDerivAt (fun ζ : Euclidean (n - 1) ↦ (q.1, ζ))
      (ContinuousLinearMap.inr ℝ _ _) q.2 := by
    simpa using ((ContinuousLinearMap.inr ℝ
      (WithLp 2 (ℝ × Euclidean (n - 1))) (Euclidean (n - 1))).hasFDerivAt
        (x := q.2)).const_add (q.1, 0)
  exact congrArg (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm
    (hS.hasFDerivAt.comp q.2 hi).fderiv

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private theorem referencePhase_contDiffAt
    {q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)}
    (hq : q ∈ ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius)) :
    ContDiffAt ℝ ∞ (Comparison.referencePhase (ActualPhase.dispersion T)) q := by
  have hs : ContDiffOn ℝ ∞ (Comparison.referencePhase (ActualPhase.dispersion T))
      (ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius)) :=
    Comparison.contDiffOn_referencePhase (ActualPhase.dispersion_smooth T)
      (fun _ h ↦ (mem_ball.mp h).trans_le' (le_max_right _ _))
  exact hs.contDiffAt (isOpen_ball.mem_nhds hq)

private theorem phasePoint_mem_ball {c C : ℝ} (hP : P.IsValid c C)
    {p : Euclidean n × CarrierParameter} (hp : p ∈ extensionDomain T) :
    (CanonicalCarrier.physicalCoordinates T p.1,
      T.reference.spatialPatch (CanonicalCarrier.parameter p.2)) ∈
        ball (0, ActualPhase.covectorCenter T) T.family.radius := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · have hr : T.physicalRadius ≤ T.family.radius := by
      have hpos := T.physicalRadius_pos
      dsimp [PatchQuantitativeFamily.physicalRadius] at hpos ⊢
      linarith [min_le_left T.family.radius (3 * T.family.sourceRadius)]
    simpa using (mem_ball.mp hp.1).trans_le hr
  · obtain ⟨ε, hε, hshift⟩ := ActualPhase.exists_covector_shift_buffer T hP
      (by norm_num : (0 : ℝ) < 1)
    have hh := hshift (CanonicalCarrier.parameter p.2) (fun i ↦ (hp.2 i).le)
      0 (by simp) 0 (by simpa using hε.le) 0 (by constructor <;> norm_num)
    simpa only [zero_mul, zero_smul, add_zero, mem_ball] using hh

private theorem transportPosition_error_eq_extraction {c C : ℝ} (hP : P.IsValid c C)
    (Q : _) {p : Euclidean n × CarrierParameter} (hp : p ∈ extensionDomain T) :
    CanonicalCarrier.transportPosition T Q p - frozenSpatialReference T p.2 p.1 =
      covectorDifferentialExtraction n
        (fderiv ℝ (ActualPhase.current T Q - Comparison.referencePhase (ActualPhase.dispersion T))
          (CanonicalCarrier.physicalCoordinates T p.1,
            T.reference.spatialPatch (CanonicalCarrier.parameter p.2))) := by
  have hq := ball_subset_ball (by linarith [T.family.radius_pos] :
    T.family.radius ≤ 2 * T.family.radius) (phasePoint_mem_ball T hP hp)
  have hS := ((ActualPhase.current_smooth T Q).contDiffAt
    (isOpen_ball.mem_nhds hq)).differentiableAt (by simp)
  have hR := (referencePhase_contDiffAt T hq).differentiableAt (by simp)
  rw [fderiv_sub hS hR, map_sub, CanonicalCarrier.transportPosition,
    frozenSpatialReference_eq_gradient T _
      ((mem_ball.mp hq).trans_le' (le_max_right _ _)),
    gradient_eq_covectorDifferentialExtraction hS, gradient_eq_covectorDifferentialExtraction hR]

/-- The actual value and spatial differential errors are bounded by the joint
phase `C²` error. This supplies the comparison input to
`transverseGap_affineExtension_of_comparison`
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem transportPosition_comparison_le_phase_cNorm_two {c C : ℝ} (hP : P.IsValid c C)
    (Q : _) {p : Euclidean n × CarrierParameter} (hp : p ∈ extensionDomain T) :
    ‖CanonicalCarrier.transportPosition T Q p - frozenSpatialReference T p.2 p.1‖ ≤
        cNorm (closedBall (0, ActualPhase.covectorCenter T) T.family.radius) 2
          (ActualPhase.current T Q - Comparison.referencePhase (ActualPhase.dispersion T)) ∧
      ‖fderiv ℝ (fun x ↦ CanonicalCarrier.transportPosition T Q (x, p.2)) p.1 -
        frozenSpatialReference T p.2‖ ≤
        cNorm (closedBall (0, ActualPhase.covectorCenter T) T.family.radius) 2
          (ActualPhase.current T Q - Comparison.referencePhase (ActualPhase.dispersion T)) := by
  let f := ActualPhase.current T Q - Comparison.referencePhase (ActualPhase.dispersion T)
  let q := (CanonicalCarrier.physicalCoordinates T p.1,
    T.reference.spatialPatch (CanonicalCarrier.parameter p.2))
  let K := closedBall ((0 : WithLp 2 (ℝ × Euclidean (n - 1))),
    ActualPhase.covectorCenter T) T.family.radius
  have hq : q ∈ K := ball_subset_closedBall (phasePoint_mem_ball T hP hp)
  have hf : ∀ w ∈ K, ContDiffAt ℝ ∞ f w := by
    intro w hw
    have hw' := closedBall_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius < 2 * T.family.radius) hw
    exact ((ActualPhase.current_smooth T Q).contDiffAt (isOpen_ball.mem_nhds hw')).sub
      (referencePhase_contDiffAt T hw')
  have hjet (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j f q‖ ≤ cNorm K 2 f :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun w hw ↦ (hf w hw).of_le (by simp)) hq hj
  have hE (L) : ‖covectorDifferentialExtraction n L‖ ≤ ‖L‖ :=
    ((covectorDifferentialExtraction n).le_opNorm L).trans
      ((mul_le_mul_of_nonneg_right (norm_covectorDifferentialExtraction_le n)
        (norm_nonneg L)).trans_eq (one_mul _))
  constructor
  · rw [transportPosition_error_eq_extraction T hP Q hp]
    exact (hE _).trans (by simpa only [norm_iteratedFDeriv_one] using hjet 1 (by omega))
  · let ψ := fun x ↦ (CanonicalCarrier.physicalCoordinates T x,
        T.reference.spatialPatch (CanonicalCarrier.parameter p.2))
    let D := (CanonicalCarrier.physicalCoordinates T).toContinuousLinearMap.prod
      (0 : Euclidean n →L[ℝ] Euclidean (n - 1))
    have hψ : HasFDerivAt ψ D p.1 :=
      (CanonicalCarrier.physicalCoordinates T).toContinuousLinearMap.hasFDerivAt.prodMk
        (hasFDerivAt_const _ _)
    have hdf := ((hf q hq).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hd := (covectorDifferentialExtraction n).hasFDerivAt.comp p.1
      (hdf.hasFDerivAt.comp p.1 hψ)
    have he : (fun x ↦ CanonicalCarrier.transportPosition T Q (x, p.2) -
        frozenSpatialReference T p.2 x) =ᶠ[𝓝 p.1]
        (fun x ↦ covectorDifferentialExtraction n (fderiv ℝ f (ψ x))) :=
      eventuallyEq_of_mem (isOpen_ball.mem_nhds hp.1) fun x hx ↦
        transportPosition_error_eq_extraction T hP Q ⟨hx, hp.2⟩
    have hY : DifferentiableAt ℝ
        (fun x ↦ CanonicalCarrier.transportPosition T Q (x, p.2)) p.1 :=
      (((transportPosition_contDiffOn_extensionDomain T hP Q).contDiffAt
        ((extensionDomain_open T).mem_nhds hp)).comp p.1
          (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have he' := he.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ ((fun x ↦ CanonicalCarrier.transportPosition T Q (x, p.2)) -
      ⇑(frozenSpatialReference T p.2)) p.1 =
        fderiv ℝ (covectorDifferentialExtraction n ∘ fderiv ℝ f ∘ ψ) p.1 at he'
    rw [fderiv_sub hY (frozenSpatialReference T p.2).differentiableAt,
      ContinuousLinearMap.fderiv, hd.fderiv] at he'
    rw [he']
    have hb : ‖(covectorDifferentialExtraction n).comp
        ((fderiv ℝ (fderiv ℝ f) q).comp D)‖ ≤ ‖fderiv ℝ (fderiv ℝ f) q‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _
        (norm_nonneg (fderiv ℝ (fderiv ℝ f) q))
      intro v
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) q (D v)‖ := hE _
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) q‖ * ‖D v‖ := ContinuousLinearMap.le_opNorm _ _
        _ = _ := by simp [D]
    apply hb.trans
    have hh := hjet 2 (by omega)
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hh
    exact hh

/-- One primitive frame `C⁶` threshold gives both transport comparisons on
the entire fixed extension domain, before choosing the current frame.
The phase producer is invoked only at order two. Consumer:
`transverseGap_affineExtension_of_comparison`
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem exists_transportPosition_uniform_comparison_threshold
    {c C : ℝ} (hP : P.IsValid c C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ p ∈ extensionDomain T,
        ‖CanonicalCarrier.transportPosition T Q p - frozenSpatialReference T p.2 p.1‖ < ε ∧
          ‖fderiv ℝ (fun x ↦ CanonicalCarrier.transportPosition T Q (x, p.2)) p.1 -
            frozenSpatialReference T p.2‖ < ε := by
  obtain ⟨δ, hδ, hphase⟩ := ActualPhase.exists_current_comparison_threshold T 2 hε
  refine ⟨δ, hδ, fun Q hQ p hp ↦ ?_⟩
  have hb := hphase Q
    ((cNorm_mono_order (by norm_num : 2 + 1 ≤ 6)).trans_lt hQ) _ Subset.rfl
  have he := transportPosition_comparison_le_phase_cNorm_two T hP Q hp
  exact ⟨he.1.trans_lt hb, he.2.trans_lt hb⟩

/-- Compact-support specialization of the actual transport comparison, for
assembling the global affine-extension gap. The threshold precedes the frame
and controls both the value and the spatial derivative on the same set.
Consumer: `transverseGap_affineExtension_of_comparison`
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem exists_transportPosition_comparison_threshold
    {c C : ℝ} (hP : P.IsValid c C)
    {L : Set (Euclidean n × CarrierParameter)} (_hL : IsCompact L)
    (hLO : L ⊆ extensionDomain T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ p ∈ L,
        ‖CanonicalCarrier.transportPosition T Q p - frozenSpatialReference T p.2 p.1‖ < ε ∧
          ‖fderiv ℝ (fun x ↦ CanonicalCarrier.transportPosition T Q (x, p.2)) p.1 -
            frozenSpatialReference T p.2‖ < ε := by
  obtain ⟨δ, hδ, hcompare⟩ := exists_transportPosition_uniform_comparison_threshold T hP hε
  exact ⟨δ, hδ, fun Q hQ p hp ↦ hcompare Q hQ p (hLO hp)⟩

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
