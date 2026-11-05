module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.CommonChart
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.InversePhaseBounds

/-!
# Uniform construction of the two-time Hamilton phase

Assemble the actual flow, common inverse chart, and single-high estimates for
`paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`. The only analytic inputs are the
scalar root's smoothness, local degree-one homogeneity, and fixed `C³` bound.
The time and both chart radii, together with the entire constant sequence,
precede the root. One flow and one chart serve every derivative order.

The root is supplied by `Characteristic/RootFamily`. The consumers are the
signed transport in `Characteristic/AmplitudeBounds` and the phase inputs of
`EvolutionIntegral.SymbolBudgets`, after the separate conic extension. This
construction does not assert the finite-sector or operator estimates.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic

variable {d : ℕ}

/-- Construct the common two-time Hamilton flow and inverse projection, with
the literal phase and all its quantitative inputs. The full phase differential
retains both Hamilton--Jacobi time terms. Both orientations of the entire time
segment stay in the prescribed root-state ball, also after inverse projection.
The same flow, inverse and phase have single-high joint bounds with reserve one;
their only fixed low root order is three. No flow, inverse, phase gap, or jet
estimate is assumed (`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_common_twoTimeHamiltonPhase
    (z : RootState (Euclidean d)) (hz : z.2.2 ≠ 0) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) :
    ∃ T > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ B : ℕ → ℝ,
      (∀ n, 0 < B n) ∧ 2 * ρ ≤ R / 4 ∧ 2 * ρ ≤ T / 4 ∧ 2 * ε < ‖z.2.2‖ ∧
      closedBall (z.1, z) (2 * ρ) ⊆ twoTimeDomain z (R / 2) T ∧
      ∀ h : RootState (Euclidean d) → ℝ,
        ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
        (∀ w ∈ D, ∀ᶠ a : ℝ in 𝓝 1, h (w.1, (w.2.1, a • w.2.2)) = a * h w) →
        ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
        ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
          ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ ∧
          ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z (R / 2) T) ∧
          ContDiffOn ℝ ∞ (twoTimeProjection Φ) (twoTimeDomain z (R / 2) T) ∧
          (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
          C.source = ball (z.1, z) ρ ∧ C.source ⊆ twoTimeDomain z (R / 2) T ∧
          ContDiffOn ℝ ∞ C C.source ∧ ContDiffOn ℝ ∞ C.symm C.target ∧
          closedBall (z.1, z) (2 * ε) ⊆ C.target ∧
          (∀ q ∈ twoTimeDomain z (R / 2) T,
            HasDerivAt (fun t ↦ twoTimeState Φ (t, q.2))
              (rootHamiltonField h (twoTimeState Φ q)) q.1) ∧
          (∀ q ∈ twoTimeDomain z (R / 2) T, ∀ v ∈ uIcc q.2.1 q.1,
            (v, q.2) ∈ twoTimeDomain z (R / 2) T ∧
              twoTimeState Φ (v, q.2) ∈ closedBall z R ∧
              (twoTimeState Φ (v, q.2)).1 = v) ∧
          (∀ q ∈ C.target,
            (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
              (C.symm q).2.2.2 = q.2.2.2 ∧
              (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
          (∀ q ∈ C.target, ∀ v ∈ uIcc q.2.1 q.1,
            (v, (C.symm q).2) ∈ twoTimeDomain z (R / 2) T ∧
              twoTimeState Φ (v, (C.symm q).2) ∈ closedBall z R ∧
              (twoTimeState Φ (v, (C.symm q).2)).1 = v) ∧
          (∀ w ∈ ball z ρ,
            (w.1, w) ∈ C.source ∧ (w.1, w) ∈ C.target ∧
              twoTimeState Φ (w.1, w) = w ∧ twoTimeProjection Φ (w.1, w) = (w.1, w) ∧
              C.symm (w.1, w) = (w.1, w) ∧
              twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
          ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
          (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
          (∀ q ∈ closedBall (z.1, z) ρ,
            ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap.comp
              (fderiv ℝ (twoTimeProjection Φ) q) -
                ContinuousLinearMap.id ℝ (TwoTimePoint (Euclidean d))‖ ≤ 1 / 2) ∧
          (∀ q ∈ C.target, ∀ q' ∈ C.target,
            ‖C.symm q - C.symm q'‖ ≤ (2 * (1 + 2 * M)) * ‖q - q'‖) ∧
          (∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
          ∀ n, cNorm (closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ +
            (cNorm (closedBall (z.1, z) ρ) n (twoTimeState Φ) +
              cNorm (closedBall (z.1, z) ρ) n (twoTimeProjection Φ)) +
            (cNorm (closedBall (z.1, z) (2 * ε)) n C.symm +
              cNorm (closedBall (z.1, z) (2 * ε)) n (twoTimePhase C)) ≤
                B n * (1 + cNorm (closedBall z R) (n + 1) h) := by
  obtain ⟨T, hT, A, hA, hflow⟩ := exists_common_rootHamiltonFlow z hR hM hD hRD
  obtain ⟨ρ, hρ, ε, hε, hρR, hρT, hεη, hdomain, hchart⟩ :=
    exists_common_twoTimePhaseChart z hz hR hT hM hD hRD
  choose P hP hforward using fun n ↦
    exists_rootFlow_twoTime_cNorm_bound z hR hT hM hρR hρT hD hRD n
  obtain ⟨I, hI, hinverse⟩ := exists_rootFlow_twoTime_inverse_phase_cNorm_bound
    z hR hT hρ (by positivity : 0 < 2 * ε) hM hρR hρT hD hRD
  refine ⟨T, hT, ρ, hρ, ε, hε, (fun n ↦ A n + P n + I n),
    (fun n ↦ add_pos (add_pos (hA n) (hP n)) (hI n)), hρR, hρT, hεη, hdomain, ?_⟩
  intro h hh hlow hhom
  obtain ⟨Φ, hΦ, hΦbound⟩ := hflow h hh hlow
  obtain ⟨C, hC, hsource, hCsmooth, hbuffer, hgap, hlip, hmixed⟩ :=
    hchart h Φ hh hlow hΦ
  have hsub : C.source ⊆ twoTimeDomain z (R / 2) T := by
    rw [hsource]
    exact ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hdomain)
  have hproj := rootFlow_twoTimeProjection_smooth hΦ
  have hforwardSmooth : ContDiffOn ℝ ∞ C C.source := by
    rw [hC]
    exact hproj.mono hsub
  have hcoords (q) (hq : q ∈ C.target) := twoTimeChart_inverse_coordinates hC hq
  refine ⟨Φ, C, hΦ, rootFlow_twoTimeState_smooth hΦ, hproj, hC, hsource, hsub,
    hforwardSmooth, hCsmooth, hbuffer,
    (fun _ hq ↦ rootFlow_twoTimeState_hasDerivAt hΦ hq),
    (fun _ hq _ hv ↦ rootFlow_twoTimeState_segment hΦ hT hq hv), hcoords, ?_, ?_,
    contDiffOn_twoTimePhase hCsmooth,
    (fun _ hq ↦ rootFlow_hasFDerivAt_twoTimePhase hD hRD hh hhom hΦ hT hC hsub hCsmooth hq),
    hgap, hlip, hmixed hhom, ?_⟩
  · intro q hq v hv
    apply rootFlow_twoTimeState_segment hΦ hT (hsub (C.map_target hq))
    simpa only [(hcoords q hq).1, (hcoords q hq).2.1] using hv
  · intro w hw
    have hwR : w ∈ closedBall z (R / 2) :=
      ball_subset_closedBall (ball_subset_ball (by linarith : ρ ≤ R / 2) hw)
    have hws : (w.1, w) ∈ C.source := by
      rw [hsource]
      exact max_lt ((le_max_left (dist w.1 z.1) (dist w.2 z.2)).trans_lt hw) hw
    obtain ⟨hstate, hprojection⟩ := rootFlow_twoTime_diagonal hΦ hwR
    have hwt : (w.1, w) ∈ C.target := by
      simpa only [hC, hprojection] using C.map_source hws
    have hinv : C.symm (w.1, w) = (w.1, w) := by
      simpa only [hC, hprojection] using C.left_inv hws
    exact ⟨hws, hwt, hstate, hprojection, hinv,
      twoTimePhase_diagonal hC (hΦ.initial w hwR) hws⟩
  · intro n
    exact (add_le_add
      (add_le_add (hΦbound n) (hforward n h Φ hh hlow hΦ))
      (hinverse h Φ C hh hlow hΦ hC hsource hCsmooth hbuffer hgap n)).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic
