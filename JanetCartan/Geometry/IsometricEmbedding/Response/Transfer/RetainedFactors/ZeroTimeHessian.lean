module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CriticalGeometry
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback
/-!
# Quantitative zero-time Hessians of the retained conic phase

The original retained flow proves the literal stationary block formula at
all source/covector points in the conic overlap. Segment averaging preserves
this block structure exactly, even for a varying primary Hessian. Its inverse
is bounded by the original joint primary C² seminorm, with the actual Hilbert
and product norm conversions retained.

This gives the uniform zero-time reference for the small-elapsed-time gap in
`app:ch_response:eq:direct-envelope-profile`. Positive elapsed-time stability
and the common supported-carrier construction remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.RetainedFactors
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open DirectEvolution EvolutionIntegral.KernelIdentification
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "W" => CarrierVariables (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- The diagonal stationary block has an explicit inverse norm bound, with
no smallness assumption on the primary Hessian
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_stationaryDiagonalEquiv_symm_le (A : E →L[ℝ] E) :
    ‖(stationaryDiagonalEquiv A).symm.toContinuousLinearMap‖ ≤ 1 + ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change max ‖-w.2‖ ‖-A w.2 - w.1‖ ≤ _
  have h1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
  have ha := A.le_opNorm w.2
  have hmul := mul_le_mul_of_nonneg_left h2 (norm_nonneg A)
  rw [norm_neg]
  refine max_le ?_ ?_
  · nlinarith only [h2, norm_nonneg A, norm_nonneg w]
  · apply (norm_sub_le _ _).trans
    rw [norm_neg]
    nlinarith only [ha, hmul, h1]

/-- The explicit diagonal Hessian in the ACTUAL Hilbert integration variables.
The product equivalence is retained, so the maximum and Hilbert norms are not
silently identified (`app:ch_response:eq:direct-envelope-profile`). -/
def retainedDiagonalHessianEquiv (A : E →L[ℝ] E) : W ≃L[ℝ] W :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  (e.trans (stationaryDiagonalEquiv A)).trans e.symm

/-- A fixed dimension-only norm conversion and the primary Hessian norm
control the inverse of the actual diagonal Hessian
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_inverse_retainedDiagonalHessian_le (A : E →L[ℝ] E) :
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    ‖Ring.inverse (retainedDiagonalHessianEquiv A).toContinuousLinearMap‖ ≤
      ‖e.symm.toContinuousLinearMap‖ * (1 + ‖A‖) * ‖e.toContinuousLinearMap‖ := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse, ContinuousLinearMap.inverse_equiv]
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  change ‖e.symm.toContinuousLinearMap ∘L
    ((stationaryDiagonalEquiv A).symm.toContinuousLinearMap ∘L e.toContinuousLinearMap)‖ ≤ _
  calc
    _ ≤ ‖e.symm.toContinuousLinearMap‖ *
        (‖(stationaryDiagonalEquiv A).symm.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ((1 + ‖A‖) * ‖e.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (norm_stationaryDiagonalEquiv_symm_le A) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- At zero elapsed time, the Hessian of the SAME retained conic phase is
the explicit stationary block at EVERY supported source/covector point.
This is stronger than a diagonal-point invertibility assertion: no equality
between the physical source and output is required. The retained flow's
initial condition and the actual local conic overlap prove the formula
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_conic_zeroTime_hessian
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a b : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ w ∈ ball z a, Φ (w, 0) = w)
    (hphase : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C p) p)
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {x : E} {c : Euclidean 3} {w : W} (hw : (w.fst, c) ∈ Ω)
    (hbase : elapsedChartPoint 0 x w.snd ∈
      localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b) ∩
        domain ℓ (localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b))) :
    fderiv ℝ (gradient (elapsedCarrierPhase (curriedPhase ℓ C) 0 φ (x, c))) w =
      (retainedDiagonalHessianEquiv (fderiv ℝ (gradient (fun y ↦ φ y c)) w.fst)).toContinuousLinearMap := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  have he := retained_conic_carrier_germ ℓ hphase hbuffer φ (q := (0, (x, c))) (w := w) hbase
  have he' : elapsedCarrierPhase (curriedPhase ℓ C) 0 φ (x, c) =ᶠ[𝓝 w]
      elapsedCarrierPhase (chartPhase C) 0 φ (x, c) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto.eventually he
  rw [he'.gradient.fderiv_eq]
  have hq : elapsedChartPoint 0 x w.snd ∈ C.target := by
    apply hbuffer
    apply ball_subset_closedBall
    simpa only [localPatch, mem_ofPred_eq, mem_ball, Prod.dist_eq, max_lt_iff,
      and_assoc] using hbase.1
  have hs : ContinuousAt (fun v : W ↦ (v.fst, c)) w := by fun_prop
  have hc : ContinuousAt (fun v : W ↦ elapsedChartPoint 0 x v.snd) w := by
    exact continuousAt_const.prodMk (continuousAt_const.prodMk
      (continuousAt_const.prodMk (spatialPartCLM.continuous.continuousAt.comp
        (WithLp.continuous_snd 2 E E).continuousAt)))
  have hgradient : gradient (elapsedCarrierPhase (chartPhase C) 0 φ (x, c)) =ᶠ[𝓝 w]
      fun v ↦ e.symm (gradient (fun y ↦ φ y c) v.fst - v.snd, x - v.fst) := by
    filter_upwards [hs.preimage_mem_nhds (hΩ.mem_nhds hw),
      hc.preimage_mem_nhds (C.open_target.mem_nhds hq)] with v hv hvq
    rw [gradient_elapsedCarrierPhase (φ := φ) (c := c) (x := x) (w := v) (hphase _ hvq)
      (((hφ.contDiffAt (hΩ.mem_nhds hv)).comp v.fst
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))]
    change e.symm (gradient (fun y ↦ φ y c) v.fst - v.snd,
      elapsedInputBase C 0 x v.snd - v.fst) = _
    rw [elapsedInputBase_zero hC (retained_source_subset_twoTimeDomain hsource) hi hvq]
  have hg : DifferentiableAt ℝ (gradient (fun y ↦ φ y c)) w.fst :=
    (((contDiffOn_joint_primaryGradient hΩ hφ).contDiffAt (hΩ.mem_nhds hw)).comp
      w.fst (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hd := e.symm.hasFDerivAt.comp w
    (((hg.hasFDerivAt.comp w (WithLp.fstL 2 ℝ E E).hasFDerivAt).sub
      (WithLp.sndL 2 ℝ E E).hasFDerivAt).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) x w).sub (WithLp.fstL 2 ℝ E E).hasFDerivAt))
  rw [(hd.congr_of_eventuallyEq hgradient).fderiv]
  ext v
  simp [retainedDiagonalHessianEquiv, stationaryDiagonalEquiv, e]

private def primaryHessianInsertion : (E →L[ℝ] E) →L[ℝ] (W →L[ℝ] W) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  (ContinuousLinearMap.compL ℝ W E W
    (e.symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ E E)).comp
      ((ContinuousLinearMap.compL ℝ W E E).flip (WithLp.fstL 2 ℝ E E))

private theorem retainedDiagonalHessian_affine (A : E →L[ℝ] E) :
    (retainedDiagonalHessianEquiv A).toContinuousLinearMap =
      primaryHessianInsertion A + (retainedDiagonalHessianEquiv (0 : E →L[ℝ] E)).toContinuousLinearMap := by
  ext v
  simp [primaryHessianInsertion, retainedDiagonalHessianEquiv, stationaryDiagonalEquiv,
    sub_eq_add_neg, WithLp.prodContinuousLinearEquiv]
  rw [← map_add]
  congr 1
  ext <;> simp

/-- Averaging the zero-time stationary Hessians keeps the EXACT block
structure, even when the primary Hessian varies along the entire segment.
Invertibility therefore does not require that primary Hessians be close to a
single matrix (`app:ch_response:eq:direct-envelope-profile`). -/
theorem integral_retainedDiagonalHessian (A : ℝ → E →L[ℝ] E)
    (hA : IntervalIntegrable A MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..1, (retainedDiagonalHessianEquiv (A t)).toContinuousLinearMap) =
      (retainedDiagonalHessianEquiv (∫ t in (0 : ℝ)..1, A t)).toContinuousLinearMap := by
  calc
    _ = ∫ t in (0 : ℝ)..1, primaryHessianInsertion (A t) +
        (retainedDiagonalHessianEquiv (0 : E →L[ℝ] E)).toContinuousLinearMap :=
      intervalIntegral.integral_congr (fun t _ ↦ retainedDiagonalHessian_affine (A t))
    _ = primaryHessianInsertion (∫ t in (0 : ℝ)..1, A t) +
        (retainedDiagonalHessianEquiv (0 : E →L[ℝ] E)).toContinuousLinearMap := by
      rw [intervalIntegral.integral_add (intervalIntegrable_iff.mpr (primaryHessianInsertion.integrable_comp hA.def'))
        intervalIntegrable_const, primaryHessianInsertion.intervalIntegral_comp_comm hA]
      simp
    _ = _ := (retainedDiagonalHessian_affine _).symm

/-- The primary spatial Hessian is controlled by the ORIGINAL second joint
phase jet, with constant one and the actual product/Hilbert conventions.
This supplies a uniform low bound from the already proved primary history
profile (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_primary_spatialHessian_le_joint
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {x : E} {c : Euclidean 3} (hx : (x, c) ∈ Ω) :
    ‖fderiv ℝ (gradient (fun y ↦ φ y c)) x‖ ≤
      ‖iteratedFDeriv ℝ 2 (Function.uncurry φ) (x, c)‖ := by
  have hn := (InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left
    (fderiv ℝ (fun y ↦ φ y c)) x 1
  have he : ‖fderiv ℝ (gradient (fun y ↦ φ y c)) x‖ =
      ‖iteratedFDeriv ℝ 2 (fun y ↦ φ y c) x‖ := by
    calc
      _ = ‖iteratedFDeriv ℝ 1 ((InnerProductSpace.toDual ℝ E).symm ∘
          fderiv ℝ (fun y ↦ φ y c)) x‖ := by rw [norm_iteratedFDeriv_one]; rfl
      _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun y ↦ φ y c)) x‖ := hn
      _ = _ := norm_iteratedFDeriv_fderiv
  rw [he]
  let L : E →L[ℝ] E × Euclidean 3 := (ContinuousLinearMap.id ℝ E).prod 0
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun y ↦ by simp [L, Prod.norm_def])
  have hb := SymbolBudgets.norm_iteratedFDeriv_preAffine_le L (0, c) hΩ hφ
    (x := x) (by simpa [L] using hx) 2
  have hp := pow_le_one₀ (norm_nonneg L) hL (n := 2)
  have hb' := hb.trans (mul_le_of_le_one_right (norm_nonneg _) hp)
  simpa [L, Function.uncurry] using hb'

/-- The SAME retained conic phase has a uniform inverse bound for EVERY
zero-time segment-averaged Hessian in the supplied full carriers. The primary
Hessian may vary along the segment: the exact block average is inverted and
its norm is bounded by the original joint primary `C²` seminorm. That seminorm
is supplied uniformly over histories by `HistoryPrimaryPhaseJets` when the
reserve is at least two. No averaged inverse or Hessian gap is assumed.
Positive elapsed-time stability is a separate remaining obligation
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_conic_zeroTime_averagedHessian_bound
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a b : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ w ∈ ball z a, Φ (w, 0) = w)
    (hphase : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C p) p)
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {KP : Set (E × Euclidean 3)} (hKP : IsCompact KP) (hKPΩ : KP ⊆ Ω)
    (κ : E × Euclidean 3 → W) (x : E) (c : Euclidean 3) (w : W)
    (hprimary : ∀ t ∈ Icc (0 : ℝ) 1,
      ((κ (x, c) + t • (w - κ (x, c))).fst, c) ∈ KP)
    (hbase : ∀ t ∈ Icc (0 : ℝ) 1,
      elapsedChartPoint 0 x (κ (x, c) + t • (w - κ (x, c))).snd ∈
        localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b) ∩
          domain ℓ (localPatch (ball (z.1, (z.1, z.2.1)) b) (ball z.2.2 b))) :
    let H := averagedPhaseHessian (elapsedCarrierPhase (curriedPhase ℓ C) 0 φ) κ (x, c) w
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    IsUnit H ∧ ‖Ring.inverse H‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      (1 + cNorm KP 2 (Function.uncurry φ)) * ‖e.toContinuousLinearMap‖ := by
  let seg := fun t : ℝ ↦ κ (x, c) + t • (w - κ (x, c))
  let A := fun t : ℝ ↦ fderiv ℝ (gradient (fun y ↦ φ y c)) (seg t).fst
  have hseg : Continuous (fun t : ℝ ↦ (seg t).fst) := by
    dsimp [seg]
    fun_prop
  have hAs : ContinuousOn A (uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hg : ContDiffAt ℝ ∞ (gradient (fun y ↦ φ y c)) (seg t).fst :=
      ((contDiffOn_joint_primaryGradient hΩ hφ).contDiffAt
        (hΩ.mem_nhds (hKPΩ (hprimary t ht')))).comp
          (f := fun y : E ↦ (y, c)) (seg t).fst (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hg.fderiv_right (m := ∞) (by simp)).continuousAt.comp
      (x := t) hseg.continuousAt).continuousWithinAt
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 1 := hAs.intervalIntegrable
  have heq : averagedPhaseHessian (elapsedCarrierPhase (curriedPhase ℓ C) 0 φ) κ (x, c) w =
      (retainedDiagonalHessianEquiv (∫ t in (0 : ℝ)..1, A t)).toContinuousLinearMap := by
    rw [← integral_retainedDiagonalHessian A hAi]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact retained_conic_zeroTime_hessian ℓ hC hsource hi hphase hbuffer hΩ hφ
      (hKPΩ (hprimary t ht')) (hbase t ht')
  have hbound : ‖∫ t in (0 : ℝ)..1, A t‖ ≤ cNorm KP 2 (Function.uncurry φ) := by
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (fun t ht ↦ (norm_primary_spatialHessian_le_joint hΩ hφ
          (hKPΩ (hprimary t (by simpa using (uIoc_subset_uIcc ht))))).trans
            (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKP
              (fun q hq ↦ (hφ.contDiffAt (hΩ.mem_nhds (hKPΩ hq))).of_le (by norm_num))
              (hprimary t (by simpa using (uIoc_subset_uIcc ht))) le_rfl))
  dsimp only
  rw [heq]
  refine ⟨(retainedDiagonalHessianEquiv _).toUnit.isUnit,
    (norm_inverse_retainedDiagonalHessian_le _).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hbound) (norm_nonneg _)) (norm_nonneg _)

end JanetCartan.ResponseTransfer.RetainedFactors
