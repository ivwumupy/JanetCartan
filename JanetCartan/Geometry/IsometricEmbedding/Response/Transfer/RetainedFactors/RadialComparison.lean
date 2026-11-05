module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CompleteFrequencyJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.PrimitiveInputs

/-!
# Frequency comparison on the same capped retained chart

The original spatial mixed half-gap gives the averaged determinant gap on
the whole cone. The retained phase's third coefficient norm bounds its mixed
derivative before choosing a source annulus. Euler's identity then gives
both radial inequalities, uniformly before varying the chart and history.
Germ agreement transfers the inequalities to the actual smooth representative.
Consumers: `hradial` and the whole-image inputs of both integrated-envelope
endpoints (`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral
open SymbolBudgets FourierIntegral WholeImageGeometry NormalComparison
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

private theorem norm_averagedGradient_diagonal (S : E → E → ℝ) (x ξ : E) :
    ‖averagedGradient S x x ξ‖ = ‖fderiv ℝ (fun y ↦ S y ξ) x‖ := by
  simp [averagedGradient, averagedPhaseDifferential]

/-- The whole retained cone has uniform mixed, averaged-inverse and radial
bounds from the SAME chart's original half-gap and coefficient budget.
The constants precede the coefficient field, flow, chart, elapsed time and
frequency. The coefficient order is three, below the constructor's order ten
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_retained_elapsed_frequency_comparison
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε b aperture : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε ≤ b)
    (phaseCost : ℕ → ℝ) (hcost : ∀ j, 0 < phaseCost j) (M : ℝ) :
    ∃ gap > (0 : ℝ), ∃ Bmix > (0 : ℝ),
    ∃ m > (0 : ℝ), m ≤ 1 ∧ ∃ Mfreq : ℝ, 1 ≤ Mfreq ∧
    ∀ (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1)),
      cNorm KQ 3 Q ≤ M →
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      closedBall (z.1, z) b ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ q ∈ C.target,
        HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      (∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) →
      (∀ j, cNorm (closedBall (z.1, z) b) j (twoTimePhase C) ≤
        phaseCost j * (1 + cNorm KQ (j + 1) Q)) →
    ∀ t ∈ Icc (0 : ℝ) ε,
      let S := elapsedPhase (curriedPhase ℓ C) t
      let X := elapsedPhysicalBox z (ε / 2)
      let D := retainedFrequencyDomain ℓ z ε aperture (1 / 2)
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) ∧
      (∀ x ∈ X, ∀ ξ ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun y ↦ S y v) x) ξ‖ ≤ Bmix) ∧
      (∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D ∧
        ∀ ξ ∈ D, gap ≤ |(averagedJacobian S x y ξ).det|) ∧
      (∀ x ∈ X, ∀ y ∈ X, ∀ ξ ∈ D,
        m * ‖ξ‖ ≤ ‖averagedGradient S x y ξ‖ ∧
          ‖averagedGradient S x y ξ‖ ≤ Mfreq * ‖ξ‖) ∧
      ∀ x ∈ X, ∀ ξ ∈ D,
        m * ‖ξ‖ ≤ ‖fderiv ℝ (fun y ↦ S y ξ) x‖ ∧
          ‖fderiv ℝ (fun y ↦ S y ξ) x‖ ≤ Mfreq * ‖ξ‖ := by
  obtain ⟨gap, hgap, hgeom⟩ := exists_conic_elapsed_averaged_geometry d
  let Bmix := 1 + retainedPhaseCost ℓ z ε (1 / 2) 2 phaseCost 2 * (1 + |M|)
  have hBmix : 0 < Bmix := by
    have := retainedPhaseCost_pos ℓ z ε (1 / 2) 2 hcost 2
    dsimp only [Bmix]
    positivity
  obtain ⟨F, hF, Cinv, hCinv, hcompare⟩ :=
    exists_frequency_comparison_of_mixed_bound (n := d + 1) Bmix hgap
  refine ⟨gap, hgap, Bmix, hBmix, min 1 Cinv⁻¹,
    lt_min zero_lt_one (inv_pos.mpr hCinv), min_le_left _ _, max 1 F, le_max_left _ _, ?_⟩
  intro KQ Q hQ h Φ C hbuffer hs hdiff hnear hphase t ht S X D
  have hbuffer' : closedBall (z.1, z) (2 * ε) ⊆ C.target :=
    (closedBall_subset_closedBall hεb).trans hbuffer
  have hx : X ⊆ elapsedPhysicalBox z ε := fun _ hv ↦
    ⟨ball_subset_ball (by linarith) hv.1, ball_subset_ball (by linarith) hv.2⟩
  have hξ : D ⊆ spatialPart ⁻¹' angularCone ℓ z.2.2 ε := fun _ hv ↦
    ⟨hv.1.1.1, ball_subset_ball (by linarith) hv.1.1.2⟩
  have hξhalf : D ⊆ spatialPart ⁻¹' angularCone ℓ z.2.2 (ε / 2) := fun _ hv ↦
    ⟨hv.1.1.1, ball_subset_ball (by linarith) hv.1.1.2⟩
  have hX : IsOpen X := isOpen_elapsedPhysicalBox _ _
  have hD : IsOpen D := isOpen_retainedFrequencyDomain _ _ _ _ _
  have hcX : Convex ℝ X := convex_elapsedPhysicalBox _ _
  have hs' : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) :=
    (elapsedPhase_contDiffOn (curriedPhase ℓ C) t
      (fun _ hv _ hη ↦ contDiffAt_curriedPhase_elapsed ℓ hε hbuffer' hs ht hv hη)).mono
        (Set.prod_mono hx hξ)
  have hmix : ∀ x ∈ X, ∀ ξ ∈ D,
      ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun y ↦ S y v) x) ξ‖ ≤ Bmix := by
    intro x hxx ξ hξξ
    have hraw η (hη : η ∈ angularCone ℓ z.2.2 ε) :
        ContDiffAt ℝ ∞ (jointPhase (curriedPhase ℓ C))
          ((x 0, x 0 - t, spatialPart x), η) :=
      (contDiffOn_retained_product ℓ hε hεb hbuffer hs).contDiffAt
        ((isOpen_ball.prod (isOpen_angularCone _ _ _)).mem_nhds
          ⟨elapsed_mem_bufferedBase hε ht (hx hxx), hη⟩)
    apply (norm_elapsedPhase_mixed_fderiv_le (curriedPhase ℓ C) t x ξ
      (isOpen_angularCone _ _ _) (hξ hξξ) hraw).trans
    change 1 + _ ≤ 1 + _
    apply add_le_add le_rfl
    apply (retained_mixed_coefficient_bound ℓ hε hεb hbuffer hs KQ Q phaseCost
      hphase ht (hx hxx) (hξhalf hξξ)).trans
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hQ.trans (le_abs_self M)))
      (retainedPhaseCost_pos ℓ z ε (1 / 2) 2 hcost 2).le
  have hg := hgeom ℓ h Φ C z ε hε hbuffer' hs hdiff
    (fun q hq ↦ hnear q (closedBall_subset_closedBall hεb hq)) t ht
  have hgeom' : ∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D ∧
      ∀ ξ ∈ D, gap ≤ |(averagedJacobian S x y ξ).det| := by
    intro x hxx y hyy
    exact ⟨(hg x (hx hxx) y (hx hyy)).1.mono hξ,
      fun ξ hξξ ↦ (hg x (hx hxx) y (hx hyy)).2 ξ (hξ hξξ)⟩
  have hcomp := hcompare S X D hX hD hcX hs'
    (fun x _ ξ _ a ha _ ↦ elapsedPhase_smul (curriedPhase ℓ C) t a x ξ
      (extend_smul ℓ (twoTimePhase C) (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ha))
    hmix (fun x hxx y hyy ξ hξξ ↦ (hgeom' x hxx y hyy).2 ξ hξξ)
  have hcomp' : ∀ x ∈ X, ∀ y ∈ X, ∀ ξ ∈ D,
      min 1 Cinv⁻¹ * ‖ξ‖ ≤ ‖averagedGradient S x y ξ‖ ∧
        ‖averagedGradient S x y ξ‖ ≤ max 1 F * ‖ξ‖ := by
    intro x hxx y hyy ξ hξξ
    have hc := hcomp x hxx y hyy ξ hξξ
    constructor
    · calc
        _ ≤ Cinv⁻¹ * ‖ξ‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ ≤ ‖averagedGradient S x y ξ‖ := by
          rw [inv_mul_le_iff₀ hCinv]
          exact hc.2
    · exact hc.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine ⟨hs', hmix, hgeom', hcomp', ?_⟩
  intro x hxx ξ hξξ
  simpa only [norm_averagedGradient_diagonal] using hcomp' x hxx x hxx ξ hξξ

/-- The smooth representative agrees on the ENTIRE original physical box
and collared cone throughout the complete capped interval. This supplies
whole-segment equality for `bufferedNormalDomain_phase_congr`; the assertion
does not restrict frequencies to the annular part of the multiplier
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem capped_elapsed_representative_eqOn
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε src aperture : ℝ}
    (hε : 0 < ε) (hsrc : src ≤ ε)
    (C : OpenPartialHomeomorph TC TC) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {χ : TC → ℝ}
    (hχ : ∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) :
    EqOn (Function.uncurry (elapsedPhase
      (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t))
      (Function.uncurry (elapsedPhase (curriedPhase ℓ C) t))
      (elapsedPhysicalBox z (ε / 2) ×ˢ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) := by
  intro p hp
  exact (SmoothRepresentative.elapsed_representative_eventuallyEq ℓ C hδ hχ
    (capped_elapsedPoint_mem_phase_plateau ℓ z hε hsrc ht hp.1 hp.2)
    (hδhalf.trans hp.2.2.le)).eq_of_nhds

/-- The whole averaged-gradient image, including every unbounded normal
shell, is the SAME for the smooth representative of the capped factor.
No independent chart target replaces this domain
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem capped_representative_bufferedNormalDomain_eq
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε src aperture : ℝ}
    (hε : 0 < ε) (hsrc : src ≤ ε)
    (C : OpenPartialHomeomorph TC TC) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {χ : TC → ℝ}
    (hχ : ∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) :
    LowBounds.bufferedNormalDomain (elapsedPhysicalBox z (ε / 2))
      (retainedFrequencyDomain ℓ z ε aperture (1 / 2))
      (elapsedPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t) =
    LowBounds.bufferedNormalDomain (elapsedPhysicalBox z (ε / 2))
      (retainedFrequencyDomain ℓ z ε aperture (1 / 2))
      (elapsedPhase (curriedPhase ℓ C) t) :=
  bufferedNormalDomain_phase_congr (isOpen_elapsedPhysicalBox _ _)
    (convex_elapsedPhysicalBox _ _)
    (capped_elapsed_representative_eqOn ℓ z hε hsrc C hδ hδhalf hχ ht)

end JanetCartan.ResponseTransfer.RetainedFactors
