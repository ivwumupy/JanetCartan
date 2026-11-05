module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.FrozenInverse

/-!
# Global inverse estimate for the selected current conic phase

For the complete complement in `app:ch_response:thm:response-literal-transfer`,
the error from the frozen momentum map has a uniformly small derivative on
the entire convex active cone. The mean value estimate and the explicit
frozen inverse therefore give the global inverse estimate, without inferring
global injectivity from pointwise mixed invertibility.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- A full derivative comparison gives the mixed momentum comparison with
constant one for the actual canonical product norm. This is the local input
to `exists_conicSectionEnergyPhase_inverse_bound`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem exists_sectionEnergy_mixed_comparison_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ z ∈ T.target,
        ‖(T.currentChart Q).mixedMomentumDerivative z -
          T.reference.chart.mixedMomentumDerivative z‖ ≤ ε := by
  obtain ⟨δ, hδ, hcomp⟩ := T.family.exists_momentum_comparison_threshold hε
  refine ⟨δ, hδ, fun Q hQ z hz ↦ ?_⟩
  have hc := (hcomp Q hQ z (ball_subset_closedBall hz)).2.le
  rw [(T.currentChart Q).mixedMomentumDerivative_eq (T.family.momentum_smooth Q)
    (T.current_coordinates_smooth Q) hz,
    T.reference.chart.mixedMomentumDerivative_eq T.reference.momentum_smooth
      T.reference.coordinates_smooth hz]
  apply ContinuousLinearMap.opNorm_le_bound _ hε.le
  intro v
  have hh := ((fderiv ℝ (T.currentChart Q).chartMomentum z -
    fderiv ℝ T.reference.chart.chartMomentum z).le_opNorm ((0 : Euclidean n), v)).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  simpa only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.inr_apply,
    Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg v)] using hh

/-- Joint smoothness of the actual conic momentum on the full active cone
(`app:ch_response:thm:response-literal-transfer`, complete complement). -/
theorem conicSectionEnergyPhase_gradient_smooth
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _) :
    ContDiffOn ℝ ∞ (fun z : Euclidean n × (ℝ × Euclidean (n - 1)) ↦
      gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y z.2) z.1)
      (ball 0 T.physicalRadius ×ˢ T.sectionEnergyCone ℓ r) := by
  apply ((T.currentChart Q).contDiffOn_gradient_conicPhase ℓ
    (T.family.momentum_smooth Q) (T.current_coordinates_smooth Q)).mono
  rintro ⟨x, η⟩ ⟨hx, hη⟩
  exact ⟨hη.1, T.sectionEnergyDomain_subset_target Q hx (ball_subset_ball hr hη.2)⟩

set_option maxHeartbeats 1000000 in
/-- The required global inverse estimate on every pair of covectors in the
entire active cone, for the literal current phase. The positive low threshold
is produced by the family's full momentum comparison, and all constants are
chosen before the frame, frequencies, and samples
(`app:ch_response:thm:response-literal-transfer`, complete complement). -/
theorem exists_conicSectionEnergyPhase_inverse_bound
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) :
    ∃ L > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ ball 0 T.physicalRadius, ∀ η ∈ T.sectionEnergyCone ℓ r,
      ∀ θ ∈ T.sectionEnergyCone ℓ r,
        ‖η - θ‖ ≤ L * ‖gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x -
          gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y θ) x‖ := by
  obtain ⟨L, hL, hLbound⟩ := T.exists_reference_conic_inverse_bound
  let ε := (2 * L)⁻¹
  have hε : 0 < ε := inv_pos.mpr (mul_pos (by norm_num) hL)
  have hεL : L * ε = 1 / 2 := by dsimp [ε]; field_simp
  obtain ⟨δ, hδ, hcomp⟩ := T.exists_sectionEnergy_mixed_comparison_threshold hε
  refine ⟨2 * L, by positivity, δ, hδ, ?_⟩
  intro Q hQ x hx η hη θ hθ
  let F := fun ζ ↦ gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y ζ) x
  let F₀ := fun ζ ↦ gradient (fun y ↦ T.reference.chart.conicPhase ℓ (y, ζ)) x
  let B := ball (0 : Euclidean n) T.physicalRadius
  let V := T.sectionEnergyDomain
  have hsub : B ×ˢ V ⊆ T.target := by
    rintro ⟨y, ζ⟩ ⟨hy, hζ⟩
    exact T.sectionEnergyDomain_subset_target Q hy hζ
  have hconic (ζ : ℝ × Euclidean (n - 1)) (hζ : ζ ∈ T.sectionEnergyCone ℓ r) :
      (x, ζ) ∈ CharacteristicRoot.conicDomain ℓ (B ×ˢ V) :=
    ⟨hζ.1, hx, ball_subset_ball hr hζ.2⟩
  have htarget (ζ : ℝ × Euclidean (n - 1)) (hζ : ζ ∈ T.sectionEnergyCone ℓ r) :
      (x, ζ) ∈ CharacteristicRoot.conicDomain ℓ T.target :=
    ⟨hζ.1, hsub (hconic ζ hζ).2⟩
  have hdiff : ∀ ζ ∈ T.sectionEnergyCone ℓ r, DifferentiableAt ℝ F ζ := by
    intro ζ hζ
    have hopen : IsOpen (B ×ˢ T.sectionEnergyCone ℓ r) :=
      isOpen_ball.prod (T.sectionEnergyCone_isOpen ℓ r)
    have hz : (x, ζ) ∈ B ×ˢ T.sectionEnergyCone ℓ r := ⟨hx, hζ⟩
    have hs := (T.conicSectionEnergyPhase_gradient_smooth ℓ hr Q).contDiffAt
      (x := (x, ζ)) (hopen.mem_nhds hz)
    exact (hs.differentiableAt (by simp)).comp ζ
      (hasFDerivAt_prodMk_right x ζ).differentiableAt
  have hdiff₀ : ∀ ζ ∈ T.sectionEnergyCone ℓ r, DifferentiableAt ℝ F₀ ζ := by
    intro ζ hζ
    have hopen := CharacteristicRoot.isOpen_conicDomain ℓ T.reference.chart.isOpen_target
    have hs := (T.reference.chart.contDiffOn_gradient_conicPhase ℓ T.reference.momentum_smooth
      T.reference.coordinates_smooth).contDiffAt (x := (x, ζ)) (hopen.mem_nhds (htarget ζ hζ))
    exact (hs.differentiableAt (by simp)).comp ζ
      (hasFDerivAt_prodMk_right x ζ).differentiableAt
  have hderiv : ∀ ζ ∈ T.sectionEnergyCone ℓ r, ‖fderiv ℝ (F - F₀) ζ‖ ≤ ε := by
    intro ζ hζ
    rw [fderiv_sub (hdiff ζ hζ) (hdiff₀ ζ hζ)]
    have he := (T.currentChart Q).fderiv_gradient_conicPhase_eq_normalized ℓ
      (T.family.momentum_smooth Q) (T.current_coordinates_smooth Q)
      (B := B) (P := V) (z := (x, ζ)) isOpen_ball isOpen_ball (convex_ball _ _) hsub (hconic ζ hζ)
    have he₀ := T.reference.chart.fderiv_gradient_conicPhase_eq_normalized ℓ
      T.reference.momentum_smooth T.reference.coordinates_smooth
      (B := B) (P := V) (z := (x, ζ)) isOpen_ball isOpen_ball (convex_ball _ _) hsub (hconic ζ hζ)
    change fderiv ℝ F ζ = _ at he
    change fderiv ℝ F₀ ζ = _ at he₀
    rw [he, he₀]
    exact hcomp Q hQ _ (hsub (hconic ζ hζ).2)
  have herr := (T.sectionEnergyCone_convex ℓ r).norm_image_sub_le_of_norm_fderiv_le
    (fun ζ hζ ↦ (hdiff ζ hζ).sub (hdiff₀ ζ hζ)) hderiv hη hθ
  rw [norm_sub_rev ((F - F₀) θ), norm_sub_rev θ] at herr
  have hbase := hLbound ℓ x η θ (htarget η hη) (htarget θ hθ)
  have he : F₀ η - F₀ θ = (F η - F θ) - ((F - F₀) η - (F - F₀) θ) := by
    simp only [Pi.sub_apply]
    abel
  have hnorm := norm_sub_le (F η - F θ) ((F - F₀) η - (F - F₀) θ)
  rw [← he] at hnorm
  have hh : ‖F₀ η - F₀ θ‖ ≤ ‖F η - F θ‖ + ε * ‖η - θ‖ := by
    linarith
  have hh' := mul_le_mul_of_nonneg_left hh hL.le
  change ‖η - θ‖ ≤ 2 * L * ‖F η - F θ‖
  change ‖η - θ‖ ≤ L * ‖F₀ η - F₀ θ‖ at hbase
  rw [mul_add, ← mul_assoc, hεL] at hh'
  linarith

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
