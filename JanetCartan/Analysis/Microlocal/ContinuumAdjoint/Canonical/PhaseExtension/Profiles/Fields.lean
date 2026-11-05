module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.FieldJets
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.Interpolation
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.JointJets

/-!
# Global primitive profiles for the literal derivative-trade fields

The fields are rational functions of the first jet of the same affine extension.
Their one-high estimates lose five immersion derivatives, and interpolation uses
the fixed baseline `2(n+1)`. Off the compact correction the fields are constant.
The global transverse gap is an explicit geometric premise, produced separately
by `jc-adjoint-phase-extension-gap`; no downstream profile is a premise.
Source: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow DerivativeKernels ActualCarriers FrozenMenu CurrentFullPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual extended fields satisfy the global finite-low/high profiles in
the exact symbol variables of the scalar-transport endpoint. All constants
precede `F`, and the only high budget is `1 + ‖F‖_{C^{s+2(n+1)+5}}`.
The list merely selects the finitely many directional fields to be bounded.
This conditional deduction does not construct the global transverse gap.
Consumer: `hcoeff` of `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_projected_affineField_profile {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ extensionDomain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κ δ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) (hδ : 0 < δ) (s : ℕ) :
    ∃ D : List (InitialCarrierDerivative n) → ℕ → ℝ, (∀ ds i, 0 ≤ D ds i) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K (2*(n+1)+5) F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let Y := affineExtension A χ (CanonicalCarrier.transportPosition T Q)
        (∀ p : Euclidean n × CarrierParameter, TransverseGap δ (spatialMatrix Y p.2 p.1)) →
        ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
          ∀ p : AdjointSymbolPoint n, ∀ e ∈ ds, ∀ j i, i ≤ ds.length+2*(n+1) →
            ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
              branchField (initialField Y) (carrierField Y) e j p.1) p‖ ≤
              D ds i * (1 + cNorm K (s+2*(n+1)+5) F) ^
                (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  classical
  obtain ⟨R, hR, hsupport⟩ := hc.isBounded.subset_closedBall_lt
    0 (0 : Euclidean n × CarrierParameter)
  let J := closedBall (0 : Euclidean n × CarrierParameter) R
  obtain ⟨E, hE, he⟩ := exists_projected_affineExtension_bound T (N := N) hP A hχ hc hs
    (isCompact_closedBall (0 : Euclidean n × CarrierParameter) R) hK hKU hball M hκmet hκ
  let Mjet := E 1 * (1+M)
  choose C hC hb using fun e j m ↦ exists_cNorm_branchField_le_firstJet
    (0 : Euclidean n × CarrierParameter) hR Mjet hδ e j m
  let G := fun e j m ↦ C e j m * (1+E (m+1))
  have hG e j m : 0 < G e j m := mul_pos (hC e j m) (by linarith [hE (m+1)])
  let b := 2*(n+1)
  choose B hB hprofile using fun e j ↦ exists_closedBall_reserve_profile
    (F := ℂ) (0 : Euclidean n × CarrierParameter) hR b s
      (G e j b * (1+M)) (G e j (b+s))
  let Aref := A.comp (ContinuousLinearMap.fst ℝ (Euclidean n) CarrierParameter)
  let Bglobal := fun e j i ↦ B e j i + ‖firstJetBranch e j Aref‖
  have hBg e j i : 0 ≤ Bglobal e j i := add_nonneg (hB e j i) (norm_nonneg _)
  let D := fun (ds : List (InitialCarrierDerivative n)) i ↦ ∑ e ∈ ds.toFinset, ∑ j, Bglobal e j i
  have hD ds i : 0 ≤ D ds i := Finset.sum_nonneg fun e _ ↦
    Finset.sum_nonneg fun j _ ↦ hBg e j i
  refine ⟨D, hD, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  let Y := affineExtension A χ (CanonicalCarrier.transportPosition T Q)
  have hY : ContDiff ℝ ∞ Y := affineExtension_contDiff A (extensionDomain_open T) hχ
    (transportPosition_contDiffOn_extensionDomain T hP Q) hs
  have hfour : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hbound (m) : cNorm J m Y ≤ E m * (1 + cNorm K (m+4) F) :=
    he F hF hi hrank hfour hmet hnormal hlow m
  intro hgap
  have hjetRange (p) (hp : p ∈ J) :
      ‖fderiv ℝ Y p‖ ≤ Mjet ∧ TransverseGap δ (spatialMatrix Y p.2 p.1) := by
    refine ⟨?_, hgap p⟩
    have hnorm := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
      (hY.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hp (le_refl 1)
    rw [norm_iteratedFDeriv_one] at hnorm
    have hlow5 : cNorm K (1+4) F ≤ M := (cNorm_mono_order (by omega)).trans hFM
    exact (hnorm.trans (hbound 1)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (hE 1).le)
  let f := fun e j (p : Euclidean n × CarrierParameter) ↦
    branchField (initialField Y) (carrierField Y) e j (p.2,p.1)
  have hf e j : ContDiff ℝ ∞ (f e j) :=
    (branchField_contDiff_of_gap hY hδ hgap e j).comp (contDiff_snd.prodMk contDiff_fst)
  have hfield e j m : cNorm J m (f e j) ≤ G e j m * (1 + cNorm K (m+5) F) := by
    have hh := hb e j m Y hY hjetRange
    apply hh.trans
    dsimp [G]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hC e j m).le
    have hp := hbound (m+1)
    rw [show m+1+4 = m+5 by omega] at hp
    nlinarith [cNorm_nonneg K (m+5) F]
  let H := 1 + cNorm K (s+2*(n+1)+5) F
  have hH : 1 ≤ H := by dsimp [H]; linarith [cNorm_nonneg K (s+2*(n+1)+5) F]
  have hglobal e j i (hi : i ≤ b+s) (p : Euclidean n × CarrierParameter) :
      ‖iteratedFDeriv ℝ i (f e j) p‖ ≤
        Bglobal e j i * H ^ (((i-b : ℕ) : ℝ) / (max s 1 : ℕ)) := by
    by_cases hp : p ∈ J
    · have hlo : cNorm J b (f e j) ≤ G e j b * (1+M) :=
        (hfield e j b).trans (mul_le_mul_of_nonneg_left (by dsimp [b]; linarith) (hG e j b).le)
      have hhi : cNorm J (b+s) (f e j) ≤ G e j (b+s) * H := by
        simpa only [H, b, show 2*(n+1)+s+5 = s+2*(n+1)+5 by omega] using hfield e j (b+s)
      exact (hprofile e j (f e j) (hf e j) hlo H hH hhi i hi p hp).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _))
          (Real.rpow_nonneg (zero_le_one.trans hH) _))
    · have hnot : p ∉ tsupport χ := fun hh ↦ hp (hsupport hh)
      have heq : f e j =ᶠ[𝓝 p] (fun _ ↦ firstJetBranch e j Aref) := by
        have hd := (affineExtension_eventuallyEq_reference A
          (CanonicalCarrier.transportPosition T Q) hnot).fderiv (𝕜 := ℝ)
        filter_upwards [hd] with q hq
        change branchField (initialField Y) (carrierField Y) e j (q.2,q.1) = _
        rw [← firstJetBranch_fderiv (hY.differentiable (by simp)).differentiableAt e j]
        have ha : fderiv ℝ (fun q : Euclidean n × CarrierParameter ↦ A q.1) q = Aref :=
          Aref.fderiv
        rw [hq, ha]
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
      have hconst : ‖iteratedFDeriv ℝ i (fun _ : Euclidean n × CarrierParameter ↦
          firstJetBranch e j Aref) p‖ ≤ ‖firstJetBranch e j Aref‖ := by
        cases i with
        | zero => simp
        | succ i => simp [iteratedFDeriv_succ_const]
      apply hconst.trans
      have hpw : 1 ≤ H ^ (((i-b : ℕ) : ℝ) / (max s 1 : ℕ)) := Real.one_le_rpow hH (by positivity)
      dsimp [Bglobal]
      nlinarith [hB e j i, norm_nonneg (firstJetBranch e j Aref)]
  intro ds hds p e heds j i hi
  have hsmall : i ≤ b+s := by dsimp [b]; omega
  have hraw := hglobal e j i hsmall (p.1.2,p.1.1)
  have hswap := (LinearIsometryEquiv.prodComm ℝ CarrierParameter (Euclidean n)).norm_iteratedFDeriv_comp_right (f e j) p.1 i
  change ‖iteratedFDeriv ℝ i
      (branchField (initialField Y) (carrierField Y) e j) p.1‖ =
    ‖iteratedFDeriv ℝ i (f e j) (p.1.2,p.1.1)‖ at hswap
  have htotal : Bglobal e j i ≤ D ds i := by
    apply (Finset.single_le_sum (fun k _ ↦ hBg e k i) (Finset.mem_univ j)).trans
    exact Finset.single_le_sum (fun e _ ↦ Finset.sum_nonneg fun j _ ↦ hBg e j i)
      (List.mem_toFinset.mpr heds)
  apply (adjoint_spatial_jet_lift_bound _ (branchField_contDiff_of_gap hY hδ hgap e j) i p).trans
  rw [hswap]
  exact hraw.trans (mul_le_mul_of_nonneg_right htotal
    (Real.rpow_nonneg (zero_le_one.trans hH) _))

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
