module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.ZeroTime
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationarySystem
public import JanetCartan.Analysis.Operator.InverseStability

/-!
# Full-source averaged Hessians on complete segments

The zero-time block structure survives averaging along the entire original
source/covector segment. The third joint phase jet controls elapsed variation
with those same endpoints. Consumer: the actual history inverse bound in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.FullSourceStationary
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open ResponseTransfer.DirectEvolution ResponseTransfer.RetainedFactors

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- The exact averaged block inverse for either orientation of the full
source, on the whole normalized conic domain and whole integration segment.
Only the actual joint second phase seminorm controls its norm; no inverse gap
is assumed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem full_source_conic_zeroTime_averagedHessian_bound
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph TC TC}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    {φ : E → Param → ℝ} {Ω : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {KP : Set (E × Param)} (hKP : IsCompact KP) (hKPΩ : KP ⊆ Ω)
    (κ : E × Param → W) (q : E × Param) (w : W)
    (hprimary : ∀ t ∈ Icc (0 : ℝ) 1, ((κ q + t • (w - κ q)).fst, q.2) ∈ KP)
    (hgraph : ∀ o : Bool, ∀ t ∈ Icc (0 : ℝ) 1,
      fullSourceGraphPoint o ((0, q), κ q + t • (w - κ q)) ∈ domain ℓ C.target) :
    let H := averagedPhaseHessian
      (fun p v ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ ((0, p), v)) κ q w
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    IsUnit H ∧ ‖Ring.inverse H‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      (1 + cNorm KP 2 (Function.uncurry φ)) * ‖e.toContinuousLinearMap‖ := by
  let seg := fun t : ℝ ↦ κ q + t • (w - κ q)
  let A := fun t : ℝ ↦ fderiv ℝ (gradient (fun y ↦ φ y q.2)) (seg t).fst
  have hseg : Continuous (fun t : ℝ ↦ (seg t).fst) := by dsimp [seg]; fun_prop
  have hAs : ContinuousOn A (uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hg : ContDiffAt ℝ ∞ (gradient (fun y ↦ φ y q.2)) (seg t).fst :=
      ((contDiffOn_full_source_gradient hΩ hφ).contDiffAt
        (hΩ.mem_nhds (hKPΩ (hprimary t ht')))).comp
          (f := fun y : E ↦ (y, q.2)) (seg t).fst (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hg.fderiv_right (m := ∞) (by simp)).continuousAt.comp
      (x := t) hseg.continuousAt).continuousWithinAt
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 1 := hAs.intervalIntegrable
  have heq : averagedPhaseHessian
      (fun p v ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ ((0, p), v)) κ q w =
      (retainedDiagonalHessianEquiv (∫ t in (0 : ℝ)..1, A t)).toContinuousLinearMap := by
    rw [← integral_retainedDiagonalHessian A hAi]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact full_source_conic_zeroTime_hessian adj ℓ hC hsource hi hΩ hφ q
      (hKPΩ (hprimary t ht')) (hgraph false t ht') (hgraph true t ht')
  have hbound : ‖∫ t in (0 : ℝ)..1, A t‖ ≤ cNorm KP 2 (Function.uncurry φ) := by
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (fun t ht ↦ (norm_full_source_spatialHessian_le_joint hΩ hφ
          (hKPΩ (hprimary t (by simpa using (uIoc_subset_uIcc ht))))).trans
            (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKP
              (fun p hp ↦ (hφ.contDiffAt (hΩ.mem_nhds (hKPΩ hp))).of_le (by norm_num))
              (hprimary t (by simpa using (uIoc_subset_uIcc ht))) le_rfl))
  dsimp only
  rw [heq]
  refine ⟨(retainedDiagonalHessianEquiv _).toUnit.isUnit,
    (norm_inverse_retainedDiagonalHessian_le _).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hbound) (norm_nonneg _)) (norm_nonneg _)

/-- The full-source Hessian varies by at most the third joint phase seminorm
times elapsed time on either signed time segment. No source parameter or
integration variable is moved in this comparison
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_full_source_hessian_sub_zero_le
    {f : FullSourcePoint d → ℝ} {V K : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) (hf : ContDiffOn ℝ ∞ f V)
    (t : ℝ) (q : E × Param) (w : W)
    (hsegment : ∀ u ∈ uIcc (0 : ℝ) t, ((u, q), w) ∈ K) :
    ‖fderiv ℝ (gradient (fun v ↦ f ((t, q), v))) w -
      fderiv ℝ (gradient (fun v ↦ f ((0, q), v))) w‖ ≤ cNorm K 3 f * |t| := by
  let H := fun p : FullSourcePoint d ↦ fderiv ℝ (gradient (fun v ↦ f (p.1, v))) p.2
  let L : ℝ →L[ℝ] FullSourcePoint d := ((ContinuousLinearMap.id ℝ ℝ).prod 0).prod 0
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun u ↦ by simp [L, Prod.norm_def])
  have hc u : HasFDerivAt (fun u : ℝ ↦ ((u, q), w)) L u := by
    simpa [L] using ((hasFDerivAt_id (𝕜 := ℝ) u).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) q u)).prodMk (hasFDerivAt_const (𝕜 := ℝ) w u)
  have hs u (hu : u ∈ uIcc (0 : ℝ) t) :=
    full_source_stationaryHessian_local_jet hV hf (hKV (hsegment u hu))
  have hn u (hu : u ∈ uIcc (0 : ℝ) t) :
      ‖(fderiv ℝ H ((u, q), w)).comp L‖ ≤ cNorm K 3 f := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_of_le_one_right (norm_nonneg _) hL).trans
    exact (hs u hu).2.trans (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun v hv ↦ (hf.contDiffAt (hV.mem_nhds (hKV hv))).of_le (by norm_num))
      (hsegment u hu) le_rfl)
  have hb := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u hu ↦ (((hs u hu).1.differentiableAt (by simp)).hasFDerivAt.comp u
      (hc u)).hasFDerivWithinAt) hn left_mem_uIcc right_mem_uIcc
  simpa only [sub_zero, Real.norm_eq_abs, Function.comp_apply] using hb

/-- The SAME full segment average obeys the elapsed Hessian bound, with
both integration endpoints held fixed. The original third phase jet pays for
the whole time/source/covector segment
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_full_source_averagedHessian_sub_zero_le
    {f : FullSourcePoint d → ℝ} {V K : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) (hf : ContDiffOn ℝ ∞ f V)
    (t : ℝ) (q : E × Param) (a w : W)
    (hsegments : ∀ u ∈ uIcc (0 : ℝ) t, ∀ s ∈ Icc (0 : ℝ) 1,
      ((u, q), a + s • (w - a)) ∈ K) :
    ‖averagedPhaseHessian (fun p v ↦ f ((t, p), v)) (fun _ ↦ a) q w -
      averagedPhaseHessian (fun p v ↦ f ((0, p), v)) (fun _ ↦ a) q w‖ ≤ cNorm K 3 f * |t| := by
  let seg := fun s : ℝ ↦ a + s • (w - a)
  let H := fun u s ↦ fderiv ℝ (gradient (fun v ↦ f ((u, q), v))) (seg s)
  have hc (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) t) :
      ContinuousOn (H u) (uIcc (0 : ℝ) 1) := by
    intro s hs
    have hp : Continuous (fun s : ℝ ↦ ((u, q), seg s)) := by dsimp [seg]; fun_prop
    have hm := hKV (hsegments u hu s (by simpa using hs))
    exact ((full_source_stationaryHessian_local_jet hV hf hm).1.continuousAt.comp
      (x := s) hp.continuousAt).continuousWithinAt
  have ht : IntervalIntegrable (H t) MeasureTheory.volume 0 1 := (hc t right_mem_uIcc).intervalIntegrable
  have h0 : IntervalIntegrable (H 0) MeasureTheory.volume 0 1 := (hc 0 left_mem_uIcc).intervalIntegrable
  change ‖(∫ s in (0 : ℝ)..1, H t s) - ∫ s in (0 : ℝ)..1, H 0 s‖ ≤ _
  rw [← intervalIntegral.integral_sub ht h0]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (fun s hs ↦ norm_full_source_hessian_sub_zero_le hV hK hKV hf t q (seg s)
      (fun u hu ↦ hsegments u hu s (by simpa using uIoc_subset_uIcc hs)))
  simpa only [sub_zero, abs_one, mul_one] using hb

end JanetCartan.FullSourceStationary
