module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.ActiveInactiveGeometry
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.NormalizedIncidence

/-!
# Inactive angular separation from the final supplied incidence capture

The positive-source capture retained by the actual terminal family suffices to
construct a fixed smooth cutoff in its unchanged parameter domain. Evaluate
that same capture at the cube field, identify its momentum by the original
comparison theorem, and use compact separation. The original uniform momentum
comparison then gives the gap for every sufficiently close current field.
No smaller support, new sector mask, or new incidence domain is substituted.

Consumer: the active/inactive characteristic factor split in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes

open ActualCarriers CurrentFullPhase HamiltonPhase FrozenMenu
open LeadingWave.FullModulation RegularSector.FiniteMasks NormedSpace

variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Coeff" => Fin (d+1) → MetricTensor (d+1)

private theorem full_source_cube_gradient
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : E → Coeff // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
    (hQ₀ : Q₀.1 = fun _ ↦ cubeStress (d+1))
    {y : E} {ζ : Euclidean d} (hy : (y,ζ) ∈ phaseDomain T) :
    phaseGradient T Q₀ y ζ = T.reference.covector (0,ζ) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  by_contra hnot
  have hpos : 0 < ‖phaseGradient T Q₀ y ζ - T.reference.covector (0,ζ)‖ :=
    lt_of_not_ge hnot
  obtain ⟨δ,hδ,hcompare⟩ := T.exists_full_source_covector_comparison hpos
  have hz : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
      (Q₀.1 - fun _ ↦ cubeStress (d+1)) < δ := by
    rw [hQ₀,sub_self,cNorm_zero]
    exact hδ
  exact (lt_irrefl _) (hcompare Q₀ hz (y,ζ) hy)

/-- The final same-family source capture constructs an active cutoff and a
uniform complementary angular gap. Only the original source coefficient
margin is reduced; the supplied mask and incident domain are unchanged. The
actual history constructor attains the new margin by increasing its common
initial threshold (`app:ch_response:eq:response-whole-source-partition`). -/
theorem exists_full_source_incidence_cutoff_and_gap
    (T : PatchQuantitativeFamily P U hU)
    {X : Set E} {Csrc V : Set Par}
    (hX : IsCompact X) (hXne : X.Nonempty) (hCsrc : IsCompact Csrc)
    (hsource : X ×ˢ Csrc ⊆ domain T) (hV : IsOpen V)
    (mask : E → ℝ) {margin : ℝ} (hmargin : 0 < margin)
    (hcapture : ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < margin →
      ∀ y ∈ X, ∀ c ∈ Csrc, ∀ scale : ℝ, 0 < scale →
        scale • phaseGradient T Q y c.2 ∈ tsupport (conicMask mask) → c ∈ V) :
    ∃ χ : Par → ℝ, ContDiff ℝ ∞ χ ∧ (∀ c, χ c ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ margin ∧ δ ≤ T.family.threshold ∧
    ∃ gap : ℝ, 0 < gap ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
      ∀ y ∈ X, ∀ c ∈ Csrc, c ∈ tsupport (fun c ↦ 1 - χ c) →
      ∀ η ∈ tsupport (conicMask mask),
        gap ≤ dist (normalize (phaseGradient T Q y c.2)) (normalize η) := by
  obtain ⟨x₀,hx₀⟩ := hXne
  let Q₀ : {Q : E → Coeff // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold} :=
    ⟨fun _ ↦ cubeStress (d+1),contDiffOn_const,by simpa using T.family.threshold_pos⟩
  let frozen : Par → E := fun c ↦ T.reference.covector (0,c.2)
  have hfrozen : ContinuousOn frozen Csrc :=
    T.continuousOn_frozen_full_source_pair.snd.comp
      (f := fun c ↦ (x₀,c)) (continuousOn_const.prodMk continuousOn_id)
      (fun c hc ↦ hsource ⟨hx₀,hc⟩)
  have hne c (hc : c ∈ Csrc) : frozen c ≠ 0 := by
    have hdom := hsource (show (x₀,c) ∈ X ×ˢ Csrc from ⟨hx₀,hc⟩)
    have hcball : c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius := by
      change dist (x₀,c.2) (0,FullPhaseCharts.ActualPhase.covectorCenter T) < T.family.radius at hdom
      rw [Prod.dist_eq] at hdom
      exact (max_lt_iff.mp hdom).2
    exact (T.full_source_frozen_covector_regular hcball).1
  have hcaptured c (hc : c ∈ Csrc)
      (hsection : (3 : ℝ) • normalize (frozen c) ∈ tsupport (conicMask mask)) : c ∈ V := by
    have he := full_source_cube_gradient T Q₀ rfl
      (hsource (show (x₀,c) ∈ X ×ˢ Csrc from ⟨hx₀,hc⟩))
    change phaseGradient T Q₀ x₀ c.2 = frozen c at he
    have hnorm : 0 < ‖frozen c‖ := norm_pos_iff.mpr (hne c hc)
    apply hcapture Q₀ (by simpa only [Q₀,sub_self,cNorm_zero] using hmargin)
      x₀ hx₀ c hc (3 * ‖frozen c‖⁻¹) (by positivity)
    rw [he]
    simpa only [NormedSpace.normalize,smul_smul] using hsection
  obtain ⟨χ,hχ,hrange,hcompact,hsχ,_,gap,hgap,hseparate⟩ :=
    exists_incidence_parameter_cutoff_and_gap hCsrc hV frozen hfrozen hne mask hcaptured
  obtain ⟨δ,hδ,hδT,hcompare⟩ :=
    T.exists_uniform_full_source_normalized_covector_comparison (hX.prod hCsrc) hsource hgap
  refine ⟨χ,hχ,hrange,hcompact,hsχ,min δ margin,lt_min hδ hmargin,
    min_le_right _ _,(min_le_left _ _).trans hδT,gap,hgap,?_⟩
  intro Q hQ y hy c hc hinactive η hη
  exact hseparate c hc hinactive (phaseGradient T Q y c.2)
    (hcompare Q (hQ.trans_le (min_le_left _ _)) (y,c) ⟨hy,hc⟩).2 η hη


/-- The supplied negative-source capture gives its own fixed active cutoff
and complementary angular gap. The graph operator is unchanged: this uses
minus the original full-source momentum, not a literal-adjoint momentum.
The source margin is fixed before histories and derivative orders
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem exists_negative_full_source_incidence_cutoff_and_gap
    (T : PatchQuantitativeFamily P U hU)
    {X : Set E} {Csrc V : Set Par}
    (hX : IsCompact X) (hXne : X.Nonempty) (hCsrc : IsCompact Csrc)
    (hsource : X ×ˢ Csrc ⊆ domain T) (hV : IsOpen V)
    (mask : E → ℝ) {margin : ℝ} (hmargin : 0 < margin)
    (hcapture : ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < margin →
      ∀ y ∈ X, ∀ c ∈ Csrc, ∀ scale : ℝ, 0 < scale →
        scale • (-phaseGradient T Q y c.2) ∈ tsupport (conicMask mask) → c ∈ V) :
    ∃ χ : Par → ℝ, ContDiff ℝ ∞ χ ∧ (∀ c, χ c ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ margin ∧ δ ≤ T.family.threshold ∧
    ∃ gap : ℝ, 0 < gap ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
      ∀ y ∈ X, ∀ c ∈ Csrc, c ∈ tsupport (fun c ↦ 1 - χ c) →
      ∀ η ∈ tsupport (conicMask mask),
        gap ≤ dist (normalize (-phaseGradient T Q y c.2)) (normalize η) := by
  obtain ⟨x₀,hx₀⟩ := hXne
  let Q₀ : {Q : E → Coeff // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold} :=
    ⟨fun _ ↦ cubeStress (d+1),contDiffOn_const,by simpa using T.family.threshold_pos⟩
  let frozen : Par → E := fun c ↦ -T.reference.covector (0,c.2)
  have hfrozen : ContinuousOn frozen Csrc :=
    (T.continuousOn_frozen_full_source_pair.snd.comp
      (f := fun c ↦ (x₀,c)) (continuousOn_const.prodMk continuousOn_id)
      (fun c hc ↦ hsource ⟨hx₀,hc⟩)).neg
  have hne c (hc : c ∈ Csrc) : frozen c ≠ 0 := by
    have hdom := hsource (show (x₀,c) ∈ X ×ˢ Csrc from ⟨hx₀,hc⟩)
    have hcball : c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius := by
      change dist (x₀,c.2) (0,FullPhaseCharts.ActualPhase.covectorCenter T) < T.family.radius at hdom
      rw [Prod.dist_eq] at hdom
      exact (max_lt_iff.mp hdom).2
    exact neg_ne_zero.mpr (T.full_source_frozen_covector_regular hcball).1
  have hcaptured c (hc : c ∈ Csrc)
      (hsection : (3 : ℝ) • normalize (frozen c) ∈ tsupport (conicMask mask)) : c ∈ V := by
    have hp := full_source_cube_gradient T Q₀ rfl
      (hsource (show (x₀,c) ∈ X ×ˢ Csrc from ⟨hx₀,hc⟩))
    have he : -phaseGradient T Q₀ x₀ c.2 = frozen c := congrArg Neg.neg hp
    have hnorm : 0 < ‖frozen c‖ := norm_pos_iff.mpr (hne c hc)
    apply hcapture Q₀ (by simpa only [Q₀,sub_self,cNorm_zero] using hmargin)
      x₀ hx₀ c hc (3 * ‖frozen c‖⁻¹) (by positivity)
    rw [he]
    simpa only [NormedSpace.normalize,smul_smul] using hsection
  obtain ⟨χ,hχ,hrange,hcompact,hsχ,_,gap,hgap,hseparate⟩ :=
    exists_incidence_parameter_cutoff_and_gap hCsrc hV frozen hfrozen hne mask hcaptured
  obtain ⟨δ,hδ,hδT,hcompare⟩ :=
    T.exists_uniform_full_source_normalized_covector_comparison (hX.prod hCsrc) hsource hgap
  refine ⟨χ,hχ,hrange,hcompact,hsχ,min δ margin,lt_min hδ hmargin,
    min_le_right _ _,(min_le_left _ _).trans hδT,gap,hgap,?_⟩
  intro Q hQ y hy c hc hinactive η hη
  apply hseparate c hc hinactive (-phaseGradient T Q y c.2) _ η hη
  have hh := (hcompare Q (hQ.trans_le (min_le_left _ _)) (y,c) ⟨hy,hc⟩).2
  simpa only [frozen,NormedSpace.normalize,norm_neg,smul_neg,dist_neg_neg] using hh

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
