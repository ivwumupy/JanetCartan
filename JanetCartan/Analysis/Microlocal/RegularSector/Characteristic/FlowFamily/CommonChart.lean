module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.CommonChart.InverseDifferential
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.CommonChart.MixedIdentity

/-!
# Common two-time charts and the spatial phase half-gap

From the fixed scalar `C³` root budget and any actual smooth Hamilton flow,
choose source and target radii before the root and flow. The inverse chart
has the literal two-time projection as its global forward map. For locally
degree-one roots its actual phase satisfies the spatial mixed half-gap in
the Frobenius norm. These are the low geometric inputs for `AmplitudeBounds`
and `EvolutionIntegral.SymbolBudgets`, from
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`.

The flow hypothesis is produced by `exists_common_rootHamiltonFlow`.
No projection, inverse, or phase estimate is assumed of that flow.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic
variable {d : ℕ}

/-- Actual common projection charts and the spatial mixed half-gap. The
dimension constant is the norm of the fixed spatial block extraction into
Frobenius matrices; it is absorbed when choosing the source radius, before
the root or flow. The inverse Lipschitz estimate holds on the whole target.
Local degree-one homogeneity is used only for the actual phase identity,
via the Liouville theorem for this same ODE
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_common_twoTimePhaseChart
    (z : RootState (Euclidean d)) (hz : z.2.2 ≠ 0) {R T M : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hM : 0 ≤ M)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) :
    ∃ ρ > (0 : ℝ), ∃ ε > (0 : ℝ),
      2 * ρ ≤ R / 4 ∧ 2 * ρ ≤ T / 4 ∧ 2 * ε < ‖z.2.2‖ ∧
      closedBall (z.1, z) (2 * ρ) ⊆ twoTimeDomain z (R / 2) T ∧
      ∀ (h : RootState (Euclidean d) → ℝ)
        (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)),
        ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
        ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ →
        ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
          (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
          C.source = ball (z.1, z) ρ ∧
          ContDiffOn ℝ ∞ C.symm C.target ∧
          closedBall (z.1, z) (2 * ε) ⊆ C.target ∧
          (∀ q ∈ closedBall (z.1, z) ρ,
            ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap.comp
              (fderiv ℝ (twoTimeProjection Φ) q) -
                ContinuousLinearMap.id ℝ (TwoTimePoint (Euclidean d))‖ ≤ 1 / 2) ∧
          (∀ q ∈ C.target, ∀ q' ∈ C.target,
            ‖C.symm q - C.symm q'‖ ≤ (2 * (1 + 2 * M)) * ‖q - q'‖) ∧
          ((∀ w ∈ D, ∀ᶠ a : ℝ in 𝓝 1, h (w.1, (w.2.1, a • w.2.2)) = a * h w) →
            ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) := by
  let κ := (twoTimeInverseMixedExtraction (d := d)).opNorm
  let L := 1 + 2 * M
  have hκ : 0 ≤ κ := twoTimeInverseMixedExtraction.opNorm_nonneg
  have hL : 0 < L := by dsimp [L]; positivity
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  let δ := 1 / (4 * (κ + 1) * L)
  have hden : 0 < 4 * (κ + 1) * L := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδhalf : δ ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    have := mul_le_mul_of_nonneg_left hLone (show 0 ≤ κ + 1 by positivity)
    nlinarith
  have hδden : δ * (4 * (κ + 1) * L) = 1 := one_div_mul_cancel (ne_of_gt hden)
  have hsmall : κ * (δ * (2 * L)) ≤ 1 / 2 := by
    nlinarith [mul_nonneg hδ.le hL.le]
  obtain ⟨ρ, hρ, ε, hε, hρR, hρT, hεη, hdomain, hcharts⟩ :=
    exists_common_twoTimeProjectionChart z hz hR hT hM hδ hδhalf hD hRD
  refine ⟨ρ, hρ, ε, hε, hρR, hρT, hεη, hdomain, ?_⟩
  intro h Φ hh hlow hΦ
  obtain ⟨C, hC, hsource, hinv, hbuffer, hgap, hlip⟩ := hcharts h Φ hh hlow hΦ
  have hsourceDomain : C.source ⊆ twoTimeDomain z (R / 2) T := by
    rw [hsource]
    exact ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hdomain)
  refine ⟨C, hC, hsource, hinv, hbuffer,
    (fun q hq ↦ (hgap q hq).trans hδhalf), hlip, ?_⟩
  intro hhom q hq
  have hqC := hbuffer hq
  have hphase (w) (hw : w ∈ C.target) := rootFlow_hasFDerivAt_twoTimePhase hD hRD hh hhom hΦ hT
    hC hsourceDomain hinv hw
  rw [twoTimePhaseMixed_eq_inverseMixedExtraction hinv hphase hqC,
    ← twoTimeInverseMixedExtraction_shear (-rootMomentumGradient h z), ← map_sub]
  have hi := norm_fderiv_twoTimeChart_symm_sub_shear_le hδ.le
    (by positivity : 0 ≤ 2 * L) hΦ hC hsourceDomain hinv
    (fun w hw ↦ hgap w (ball_subset_closedBall (hsource ▸ hw))) hlip hqC
  calc
    _ ≤ κ * ‖fderiv ℝ C.symm q -
        (twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap‖ :=
      twoTimeInverseMixedExtraction.le_opNorm _
    _ ≤ κ * (δ * (2 * L)) := mul_le_mul_of_nonneg_left hi hκ
    _ ≤ 1 / 2 := hsmall

end JanetCartan.RegularSector.Characteristic
