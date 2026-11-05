module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.RootBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.TwoTimeCritical

/-!
# Actual local two-time compatibility of the selected primary phase

For `paper-v2.tex`, `app:ch_response:lem:energy-carrier-jets`, instantiate the
root eikonal and graph-preservation deductions on the SAME selected primary
phase. The actual pencil root and two-time phase constructors produce the
objects. Shrinking the open root domain enforces the entire physical/covector
flow buffer; no flowout containment or phase matching is assumed.

The last theorem is a local construction from the published primary chart.
It does not supply uniform choices over the full compact signed patch and
current-frame neighborhood, critical-point existence or Hessian bounds, or
any solver/residual estimate. Those remain obligations of the full response.
-/

open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.CompatibleResponse
open ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- Construct the two-time phase inside a prescribed physical/covector
buffer and prove zero critical value for every member of the SAME primary
family. The flow is built on the open part of the root domain whose zero-energy
lift lies in the buffer, so whole-segment containment is a conclusion.
Both orientations follow from the entire unordered interval `uIcc 0 r`.

Consumer: `exists_primary_local_twoTime_compatibility` discharges all these
root, eikonal and compact-buffer inputs for the literal primary chart. This
lemma does not assume graph preservation, a flow, or critical-value equality
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem exists_local_twoTime_critical_value
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {Ω W Y P B : Set (Euclidean (d + 1))} {K : Set (Euclidean 3)}
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ a : ℝ in 𝓝 1, h (z.1, (z.2.1, a • z.2.2)) = a * h z)
    (hΩ : IsOpen Ω) (hφ : ∀ c ∈ K, ContDiffOn ℝ ∞ (fun x ↦ φ x c) Ω)
    (hW : IsOpen W) (hB : IsOpen B) (hY : IsCompact Y) (hP : IsCompact P)
    (hWY : W ⊆ Y) (hYΩ : Y ⊆ Ω) (hBP : B ⊆ P)
    (hprod : MapsTo spacetimeRootState (Y ×ˢ P) D)
    (hgP : ∀ c ∈ K, MapsTo (gradient (fun x ↦ φ x c)) W P)
    (he : ∀ c ∈ K, ∀ x ∈ W, rootSuspension h (x, gradient (fun y ↦ φ y c) x) = 0)
    {z₀ : RootState (Euclidean d)} (hz₀ : z₀ ∈ D)
    (hzW : (rootSuspensionState h 0 z₀).1 ∈ W)
    (hzB : (rootSuspensionState h 0 z₀).2 ∈ B) :
    ∃ R > (0 : ℝ), ∃ ε > (0 : ℝ),
    ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
    ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
      C.source ⊆ twoTimeDomain z₀ R ε ∧ (z₀.1, z₀) ∈ C.target ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      ContDiffOn ℝ ∞ Φ (ball z₀ R ×ˢ Ioo (-ε) ε) ∧
      ContDiffOn ℝ ∞ C.symm C.target ∧
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
      (∀ w ∈ ball z₀ R, Φ (w, 0) = w) ∧
      (∀ w ∈ ball z₀ R, ∀ u ∈ Ioo (-ε) ε,
        HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u ∧
        Φ (w, u) ∈ D ∧ (rootSuspensionState h 0 (Φ (w, u))).1 ∈ W ∧
          (rootSuspensionState h 0 (Φ (w, u))).2 ∈ B) ∧
      ∀ c ∈ K, ∀ r x z θ, z ∈ W → elapsedChartPoint r x θ ∈ C.target →
        fderiv ℝ (elapsedModulatedPhase C r (fun y ↦ φ y c) x) (z, θ) = 0 →
        FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r)
          z θ x (gradient (fun y ↦ φ y c) x) ∧
        elapsedModulatedPhase C r (fun y ↦ φ y c) x (z, θ) = 0 := by
  have hlift : ContinuousOn (rootSuspensionState h 0) D := by
    have hx : Continuous (fun z : RootState (Euclidean d) ↦ timeSpacePoint z.1 z.2.1) :=
      timeSpacePointCLM.continuous.comp (continuous_fst.prodMk continuous_snd.fst)
    have hp : ContinuousOn (fun z : RootState (Euclidean d) ↦ (0 + h z, z.2.2)) D :=
      (continuousOn_const.add hh.continuousOn).prodMk continuousOn_snd.snd
    have hp' : ContinuousOn
        (timeSpacePointCLM ∘ fun z : RootState (Euclidean d) ↦ (0 + h z, z.2.2)) D :=
      timeSpacePointCLM.continuous.comp_continuousOn hp
    exact hx.continuousOn.prodMk hp'
  let D' := D ∩ rootSuspensionState h 0 ⁻¹' (W ×ˢ B)
  have hD' : IsOpen D' := hlift.isOpen_inter_preimage hD (hW.prod hB)
  obtain ⟨R, hR, ε, hε, Φ, C, hΦsmooth, hi, hd, hm, _, hclock, hC, hsource,
    _, htarget, _, hinverse, hsmooth, hphase, _⟩ :=
    exists_localTwoTimeHamiltonPhase hD' (hh.mono inter_subset_left)
      (fun z hz ↦ hhom z hz.1) (show z₀ ∈ D' from ⟨hz₀, hzW, hzB⟩)
  refine ⟨R, hR, ε, hε, Φ, C, hC, hsource, htarget, hsmooth,
    hΦsmooth, hinverse, hphase, hi, ?_, ?_⟩
  · intro w hw u hu
    exact ⟨hd w hw u hu, (hm w hw u hu).1, (hm w hw u hu).2⟩
  · intro c hc r x z θ hz hq hstat
    have hph := hphase _ hq
    have hφz := ((hφ c hc).contDiffAt (hΩ.mem_nhds (hYΩ (hWY hz)))).differentiableAt (by simp)
    have hbase := (elapsedModulatedPhase_stationary_iff hph hφz).mp hstat |>.2
    obtain ⟨ht, hs, hη, _⟩ := twoTimeChart_inverse_coordinates hC hq
    have hinit : (C.symm (elapsedChartPoint r x θ)).2 = spacetimeRootState (z, θ) := by
      rw [hbase]
      apply Prod.ext
      · simpa [spacetimeRootState, elapsedInputBase, elapsedChartPoint] using hs
      · apply Prod.ext
        · simp [spacetimeRootState, elapsedInputBase]
        · simpa [spacetimeRootState, elapsedChartPoint] using hη
    have hstart := hsource (C.map_target hq)
    have hw : spacetimeRootState (z, θ) ∈ ball z₀ R := hinit ▸ hstart.1
    have hr : r ∈ Ioo (-ε) ε := by
      have hs' := hstart.2
      rw [ht, hs] at hs'
      simpa [elapsedChartPoint] using hs'
    have hsegment : uIcc 0 r ⊆ Ioo (-ε) ε := by
      intro u hu
      rcases le_total 0 r with hrpos | hrneg
      · rw [uIcc_of_le hrpos] at hu
        exact ⟨lt_of_lt_of_le (by linarith) hu.1, lt_of_le_of_lt hu.2 hr.2⟩
      · rw [uIcc_of_ge hrneg] at hu
        exact ⟨lt_of_lt_of_le hr.1 hu.1, lt_of_le_of_lt hu.2 hε⟩
    apply elapsedModulatedPhase_critical_value hD hh hhom hΩ (hφ c hc) hW hY hP
      hWY hYΩ hprod (hgP c hc) (he c hc) hC hz hq
      ((hclock _ hstart).trans ht) hph (hi _ hw)
      (fun u hu ↦ hd _ hw u (hsegment hu))
      (fun u hu ↦ (hm _ hw u (hsegment hu)).2.1)
      (fun u hu ↦ hBP (hm _ hw u (hsegment hu)).2.2) hstat

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open FrozenMenu CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

set_option backward.isDefEq.respectTransparency true in
/-- Construct a direct two-time root flow and phase compatible with the
literal `T.currentChart Q` primary phase on a common local parameter patch.
The transverse coordinate, smooth homogeneous root, original eikonal equation,
physical/parameter/covector buffers, whole-segment containment, flow and inverse
smoothness, and exact phase differential are all constructed. At every critical
point the output covector is the same primary gradient and the critical value
is exactly zero. The flow and chart precede the varying nearby parameters and
both signs of elapsed time; there are no frequencies or samples.

This is local progress for `app:ch_response:lem:energy-carrier-jets`, not the
full `app:ch_response:thm:response-compatible-choice`. The choices may depend
on the current frame and base point. Common choices over the full compact
signed family and coefficient neighborhood, critical-point existence and
uniqueness/Hessian gaps, and the actual fixed response remain to be proved. -/
theorem exists_primary_local_twoTime_compatibility {c C : ℝ} (hP : P.IsValid c C)
    (Q : _) {x₀ : Euclidean (d + 1)} {z₀ : Euclidean 3}
    (hx₀ : x₀ ∈ ball 0 T.physicalRadius) (hz₀ : z₀ ∈ parameterInterior (2 * P.radius)) :
    ∃ i : Fin (d + 1), ∃ D : Set (RootState (Euclidean d)),
    ∃ h : RootState (Euclidean d) → ℝ, ∃ ρ > (0 : ℝ), ∃ s > (0 : ℝ),
    ∃ R > (0 : ℝ), ∃ ε > (0 : ℝ),
    ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
    ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      let x := primaryCoordinateChange i x₀
      let p := gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y z₀) x
      let w₀ := spacetimeRootState (x, p)
      IsOpen D ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ U ∧ w.2.2 ≠ 0 ∧
        determinant (Q.1 ((coordinateSplit i).symm (w.1, w.2.1)))
          ((coordinateSplit i).symm (h w, w.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q.1 ((coordinateSplit i).symm (w.1, w.2.1))))
          ((coordinateSplit i).symm (h w, w.2.2)) ((coordinateSplit i).symm (1, 0)) ≠ 0) ∧
      (∀ w ∈ D, ∀ a : ℝ, 0 < a →
        (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
      (∀ q ∈ closedBall x (4 * ρ) ×ˢ closedBall z₀ (4 * ρ),
        (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
          q.2 ∈ parameterInterior (2 * P.radius)) ∧
      ContDiffOn ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦
        T.primaryPhaseInCoordinates i Q q.1 q.2)
        (closedBall x (4 * ρ) ×ˢ closedBall z₀ (4 * ρ)) ∧
      (∀ c ∈ ball z₀ ρ, ∀ y ∈ ball x (2 * ρ),
        rootSuspension h (y, gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y c) y) = 0) ∧
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
      C.source ⊆ twoTimeDomain w₀ R ε ∧ (w₀.1, w₀) ∈ C.target ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      ContDiffOn ℝ ∞ Φ (ball w₀ R ×ˢ Ioo (-ε) ε) ∧
      ContDiffOn ℝ ∞ C.symm C.target ∧
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
      (∀ w ∈ ball w₀ R, Φ (w, 0) = w) ∧
      (∀ w ∈ ball w₀ R, ∀ u ∈ Ioo (-ε) ε,
        HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u ∧
        Φ (w, u) ∈ D ∧ (rootSuspensionState h 0 (Φ (w, u))).1 ∈ ball x (2 * ρ) ∧
          (rootSuspensionState h 0 (Φ (w, u))).2 ∈ ball p s) ∧
      ∀ c ∈ ball z₀ ρ, ∀ r y z θ, z ∈ ball x (2 * ρ) →
        elapsedChartPoint r y θ ∈ C.target →
        fderiv ℝ (elapsedModulatedPhase C r (fun y ↦ T.primaryPhaseInCoordinates i Q y c) y)
          (z, θ) = 0 →
        FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r)
          z θ y (gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y c) y) ∧
        elapsedModulatedPhase C r (fun y ↦ T.primaryPhaseInCoordinates i Q y c) y (z, θ) = 0 := by
  obtain ⟨i, D, h, ρ, hρ, s, hs, hD, hh, hroot, hscale, hcontain, hφ, _, he, hg, hprod⟩ :=
    T.exists_buffered_primary_root hP Q hx₀ hz₀
  let x := primaryCoordinateChange i x₀
  let g := fun q : Euclidean (d + 1) × Euclidean 3 ↦
    gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y q.2) q.1
  let p := g (x, z₀)
  let w₀ := spacetimeRootState (x, p)
  have hbase : (x, z₀) ∈ closedBall x (4 * ρ) ×ˢ closedBall z₀ (4 * ρ) :=
    ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  have he₀ : rootSuspension h (x, p) = 0 := (he (x, z₀) hbase).2
  have hlift : rootSuspensionState h 0 w₀ = (x, p) := by
    have hh₀ : h w₀ = p 0 := (sub_eq_zero.mp he₀).symm
    apply Prod.ext
    · exact timeSpacePoint_coordinates x
    · change timeSpacePoint (0 + h w₀) (spatialPart p) = p
      rw [zero_add, hh₀]
      exact timeSpacePoint_coordinates p
  have hmem {c : Euclidean 3} (hc : c ∈ ball z₀ ρ) {y : Euclidean (d + 1)}
      (hy : y ∈ ball x (4 * ρ)) :
      (y, c) ∈ closedBall x (4 * ρ) ×ˢ closedBall z₀ (4 * ρ) :=
    ⟨ball_subset_closedBall hy,
      closedBall_subset_closedBall (by linarith : ρ ≤ 4 * ρ) (ball_subset_closedBall hc)⟩
  have hφ' c (hc : c ∈ ball z₀ ρ) :
      ContDiffOn ℝ ∞ (fun y ↦ T.primaryPhaseInCoordinates i Q y c) (ball x (4 * ρ)) :=
    hφ.comp (f := fun y : Euclidean (d + 1) ↦ (y, c))
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ hmem hc hy)
  have hWY : ball x (2 * ρ) ⊆ closedBall x (3 * ρ) :=
    fun _ hy ↦ closedBall_subset_closedBall (by linarith : 2 * ρ ≤ 3 * ρ) (ball_subset_closedBall hy)
  have hYΩ : closedBall x (3 * ρ) ⊆ ball x (4 * ρ) := closedBall_subset_ball (by linarith)
  have hg' c (hc : c ∈ ball z₀ ρ) :
      MapsTo (gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y c)) (ball x (2 * ρ))
        (closedBall p s) := by
    intro y hy
    change dist (g (y, c)) p ≤ s
    have hgb : dist (g (y, c)) p < s / 2 :=
      hg (x := (y, c)) (hmem hc (hYΩ (hWY hy)))
    exact hgb.le.trans (by linarith)
  have he' c (hc : c ∈ ball z₀ ρ) y (hy : y ∈ ball x (2 * ρ)) :
      rootSuspension h (y, gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y c) y) = 0 :=
    (he (y, c) (hmem hc (hYΩ (hWY hy)))).2
  have hhom z (hz : z ∈ D) :
      ∀ᶠ a : ℝ in 𝓝 1, h (z.1, (z.2.1, a • z.2.2)) = a * h z := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    exact (hscale z hz a ha).2
  obtain ⟨R, hR, ε, hε, Φ, C, hC, hsource, htarget, hsmooth,
    hΦsmooth, hinverse, hphase, hi, hflow, hcrit⟩ :=
    exists_local_twoTime_critical_value (h := h) (D := D) (Ω := ball x (4 * ρ))
      (W := ball x (2 * ρ)) (Y := closedBall x (3 * ρ)) (P := closedBall p s)
      (B := ball p s) (K := ball z₀ ρ)
      (φ := fun y c ↦ T.primaryPhaseInCoordinates i Q y c) (z₀ := w₀)
      hD hh hhom isOpen_ball hφ'
      isOpen_ball isOpen_ball (isCompact_closedBall x (3 * ρ)) (isCompact_closedBall p s)
      hWY hYΩ ball_subset_closedBall
      (fun q hq ↦ hprod ⟨closedBall_subset_closedBall (by linarith : 3 * ρ ≤ 4 * ρ) hq.1, hq.2⟩) hg' he'
      (he (x, z₀) hbase).1 (by rw [hlift]; exact mem_ball_self (by positivity))
      (by rw [hlift]; exact mem_ball_self hs)
  exact ⟨i, D, h, ρ, hρ, s, hs, R, hR, ε, hε, Φ, C, hD, hh, hroot,
    hscale, hcontain, hφ, he', hC, hsource, htarget, hsmooth,
    hΦsmooth, hinverse, hphase, hi, hflow, hcrit⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
