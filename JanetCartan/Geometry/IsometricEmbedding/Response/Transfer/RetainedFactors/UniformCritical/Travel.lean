module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CriticalValue
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.Triangular

/-!
# Uniform travel bounds for the retained root evolution

The first primitive root jet bounds the speed of the original flow. Its
physical lift has an explicit Lipschitz bound on the original convex state
ball. Consequently one elapsed radius, fixed before the root and flow,
controls both orientations and every intermediate time. No continuity
argument chooses a field-dependent radius.

Consumer: the whole-trajectory buffers for the uniform primary critical maps
in `app:ch_response:eq:response-exact-phase` and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open CompatibleResponse ArbitraryAccuracy EvolutionLocalization
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}
local notation "Z" => RootState (Euclidean d)

private theorem root_fderiv_le_budget
    {h : Z → ℝ} {D : Set Z} (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    {z : Z} {R B : ℝ} (hRD : closedBall z R ⊆ D)
    (hlow : cNorm (closedBall z R) 1 h ≤ B) {w : Z} (hw : w ∈ closedBall z R) :
    ‖fderiv ℝ h w‖ ≤ B := by
  have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z R)
    (fun v hv ↦ ((hh.contDiffAt (hD.mem_nhds (hRD hv))).of_le
      (by simp : (1 : ℕ∞ω) ≤ ∞))) hw (show 1 ≤ 1 from le_rfl)
  simpa only [norm_iteratedFDeriv_one] using hb.trans hlow

/-- The original retained flow moves by at most its explicit primitive
first-jet speed times elapsed time, for either time sign and including closed
endpoints. The original root budget from `RetainedEvolution` supplies `hlow`
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_root_flow_travel
    {h : Z → ℝ} {D : Set Z} (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    {z : Z} {R r time B : ℝ} (htime : 0 < time)
    (hRD : closedBall z R ⊆ D) (hlow : cNorm (closedBall z R) 1 h ≤ B)
    {Φ : Z × ℝ → Z} (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r time Φ)
    {w : Z} (hw : w ∈ closedBall z r) {t : ℝ} (ht : t ∈ Icc (-time) time) :
    ‖Φ (w, t) - w‖ ≤ (1 + B) * |t| := by
  have hfield (v : Z) (hv : v ∈ closedBall z R) : ‖rootHamiltonField h v‖ ≤ 1 + B := by
    have hb : ‖rootHamiltonField h v‖ ≤ 1 + ‖fderiv ℝ h v‖ := by
      simpa using norm_iteratedFDeriv_rootHamiltonField_le (n := 0) hD
        (hh.of_le (by simp)) (hRD hv)
    exact hb.trans (add_le_add_right (root_fderiv_le_budget hD hh hRD hlow hv) 1)
  have hb := (convex_Icc (-time) time).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu ↦ hΦ.ode w hw u hu)
    (fun u hu ↦ hfield _ (hΦ.range w hw u hu))
    (show (0 : ℝ) ∈ Icc (-time) time by constructor <;> linarith) ht
  simpa only [hΦ.initial w hw, sub_zero, Real.norm_eq_abs] using hb

/-- On the original convex root ball, the physical lift is Lipschitz with
an explicit constant from the same first root jet. This controls the temporal
covector as well as the spatial state, as required by primary conservation
(`app:ch_response:eq:response-exact-phase`). -/
theorem norm_retained_root_lift_sub_le
    {h : Z → ℝ} {D : Set Z} (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    {z : Z} {R B : ℝ} (hB : 0 ≤ B) (hRD : closedBall z R ⊆ D)
    (hlow : cNorm (closedBall z R) 1 h ≤ B)
    {v w : Z} (hv : v ∈ closedBall z R) (hw : w ∈ closedBall z R) :
    ‖rootSuspensionState h 0 v - rootSuspensionState h 0 w‖ ≤
      2 * (1 + B) * ‖v - w‖ := by
  have hdiff := (convex_closedBall z R).norm_image_sub_le_of_norm_fderiv_le
    (fun p hp ↦ (hh.contDiffAt (hD.mem_nhds (hRD hp))).differentiableAt (by simp))
    (fun p hp ↦ root_fderiv_le_budget hD hh hRD hlow hp) hw hv
  have ht : |v.1 - w.1| ≤ ‖v - w‖ := by
    simpa only [Prod.fst_sub, Real.norm_eq_abs] using norm_fst_le (v - w)
  have hx : ‖v.2.1 - w.2.1‖ ≤ ‖v - w‖ :=
    (norm_fst_le (v.2 - w.2)).trans (norm_snd_le (v - w))
  have hp : ‖v.2.2 - w.2.2‖ ≤ ‖v - w‖ :=
    (norm_snd_le (v.2 - w.2)).trans (norm_snd_le (v - w))
  change max ‖timeSpacePoint v.1 v.2.1 - timeSpacePoint w.1 w.2.1‖
    ‖timeSpacePoint (0 + h v) v.2.2 - timeSpacePoint (0 + h w) w.2.2‖ ≤ _
  simp only [zero_add, timeSpacePoint_sub]
  apply max_le
  · exact (norm_timeSpacePoint_le _ _).trans (by nlinarith [norm_nonneg (v - w)])
  · have hh' : |h v - h w| ≤ B * ‖v - w‖ := hdiff
    exact (norm_timeSpacePoint_le _ _).trans (by nlinarith [norm_nonneg (v - w)])

/-- One explicit positive elapsed radius controls the entire retained flow
and its physical lift on every unoriented segment. It is chosen from the
primitive first-root budget and the requested fixed margin BEFORE the root,
field and flow. The margin may be that of a larger integration carrier;
source-mask support is not used as critical-point containment.

The actual producer is the first-order instance of the retained `rootCost`
budget, specialized below to the original coefficient low bound. This is the
uniform replacement for the continuity step in
`exists_retained_flow_lift_buffer`
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_uniform_retained_flow_lift_buffer
    (z : Z) {R r time B margin : ℝ} (hrR : r ≤ R)
    (htime : 0 < time) (hB : 0 ≤ B) (hm : 0 < margin) :
    ∃ τ > (0 : ℝ), τ ≤ time / 2 ∧
      ∀ (h : Z → ℝ) (D : Set Z), IsOpen D → ContDiffOn ℝ ∞ h D →
        closedBall z R ⊆ D → cNorm (closedBall z R) 1 h ≤ B →
      ∀ Φ : Z × ℝ → Z, ODE.IsSmoothFlowOn (rootHamiltonField h) z R r time Φ →
      ∀ w ∈ closedBall z r, Φ (w, 0) = w ∧
        ∀ t : ℝ, |t| ≤ τ → ∀ u ∈ uIcc 0 t,
          HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u ∧
          Φ (w, u) ∈ closedBall z R ∧
          ‖Φ (w, u) - w‖ ≤ margin / 2 ∧
          ‖rootSuspensionState h 0 (Φ (w, u)) - rootSuspensionState h 0 w‖ ≤ margin / 2 := by
  let A := 2 * (1 + B) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hspeed : 1 + B ≤ A := by dsimp [A]; nlinarith
  let τ := min (time / 2) (margin / (2 * A))
  have hτ : 0 < τ := lt_min (half_pos htime) (by positivity)
  refine ⟨τ, hτ, min_le_left _ _, ?_⟩
  intro h D hD hh hRD hlow Φ hΦ w hw
  refine ⟨hΦ.initial w hw, ?_⟩
  intro t ht u hu
  have huabs : |u| ≤ τ := by
    have hb := abs_sub_left_of_mem_uIcc hu
    simp only [sub_zero] at hb
    exact hb.trans ht
  have huopen : u ∈ Ioo (-time) time := by
    have hb := huabs.trans (min_le_left _ _)
    exact ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩
  have hurange := hΦ.range w hw u (Ioo_subset_Icc_self huopen)
  have htravel := retained_root_flow_travel hD hh htime hRD hlow hΦ hw
    (Ioo_subset_Icc_self huopen)
  have hsmall : A * |u| ≤ margin / 2 := by
    calc
      _ ≤ A * (margin / (2 * A)) := mul_le_mul_of_nonneg_left
        (huabs.trans (min_le_right _ _)) hA.le
      _ = margin / 2 := by field_simp
  refine ⟨hΦ.hasDerivAt hw huopen, hurange,
    htravel.trans ((mul_le_mul_of_nonneg_right hspeed (abs_nonneg _)).trans hsmall), ?_⟩
  calc
    _ ≤ 2 * (1 + B) * ‖Φ (w, u) - w‖ :=
      norm_retained_root_lift_sub_le hD hh hB hRD hlow hurange
        (closedBall_subset_closedBall hrR hw)
    _ ≤ 2 * (1 + B) * ((1 + B) * |u|) :=
      mul_le_mul_of_nonneg_left htravel (by positivity)
    _ = A * |u| := by dsimp [A]; ring
    _ ≤ margin / 2 := hsmall

/-- Instantiate the uniform travel radius with the ORIGINAL retained
coefficient-to-root estimate and the producer's order-ten coefficient bound.
No separate low-root hypothesis is needed: monotonicity of the original
coefficient seminorm discharges it. The same `fieldRoot`, flow and full
unoriented segments are retained. All constants precede the coefficient
field and hence every history, frequency and accuracy.

`hroot` is exactly the `m = 1` projection of the `rootCost` estimate exported
by `exists_uniform_supported_conic_pencilAmplitudes_with_retained_evolution`;
its smoothness, root-ball inclusion and flow premises are projections of
that same witness (`app:ch_response:eq:response-exact-phase`). -/
theorem exists_retained_coefficient_flow_lift_buffer
    (i : Fin (d + 1))
    (H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ)
    (z : Z) (KQ : Set (Euclidean (d + 1)))
    {R r time rootCost M margin : ℝ} (hrR : r ≤ R)
    (htime : 0 < time) (hrootCost : 0 < rootCost) (hM : 0 ≤ M) (hm : 0 < margin) :
    ∃ τ > (0 : ℝ), τ ≤ time / 2 ∧
      ∀ Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1),
        cNorm KQ 10 Q ≤ M →
        let h := fieldRoot (coordinateSplit i) Q H
        ∀ D : Set Z, IsOpen D → ContDiffOn ℝ ∞ h D → closedBall z R ⊆ D →
          cNorm (closedBall z R) 1 h ≤ rootCost * (1 + cNorm KQ 1 Q) →
        ∀ Φ : Z × ℝ → Z, ODE.IsSmoothFlowOn (rootHamiltonField h) z R r time Φ →
        ∀ w ∈ closedBall z r, Φ (w, 0) = w ∧
          ∀ t : ℝ, |t| ≤ τ → ∀ u ∈ uIcc 0 t,
            HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u ∧
            Φ (w, u) ∈ closedBall z R ∧
            ‖Φ (w, u) - w‖ ≤ margin / 2 ∧
            ‖rootSuspensionState h 0 (Φ (w, u)) - rootSuspensionState h 0 w‖ ≤ margin / 2 := by
  obtain ⟨τ, hτ, hτtime, hb⟩ := exists_uniform_retained_flow_lift_buffer z hrR htime
    (show 0 ≤ rootCost * (1 + M) by positivity) hm
  refine ⟨τ, hτ, hτtime, ?_⟩
  intro Q hQ h D hD hh hRD hroot Φ hΦ w hw
  have hfirst : cNorm KQ 1 Q ≤ M :=
    (cNorm_mono_order (f := Q) (s := KQ) (by norm_num : 1 ≤ 10)).trans hQ
  exact hb h D hD hh hRD (hroot.trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hfirst 1) hrootCost.le)) Φ hΦ w hw

end JanetCartan.ResponseTransfer.RetainedFactors
