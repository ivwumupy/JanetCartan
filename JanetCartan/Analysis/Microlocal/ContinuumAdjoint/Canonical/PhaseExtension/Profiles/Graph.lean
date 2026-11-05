module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.ExtensionBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.Interpolation

/-!
# Global positive-order profiles of the actual affine graph

The graph is unbounded, but outside the fixed compact correction it is linear.
Its positive jets therefore satisfy the global profile required by
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Source: `app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts.InverseEstimates
open ActualCarriers.ConstructedCarrierJets

variable {n : ℕ}

private theorem norm_iteratedFDeriv_linear_pos_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (i : ℕ) (hi : 1 ≤ i) (p : E) :
    ‖iteratedFDeriv ℝ i L p‖ ≤ ‖L‖ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ ↦ L := funext fun _ ↦ L.fderiv
  rw [he]
  cases j with
  | zero => simp
  | succ j => simp [iteratedFDeriv_succ_const]

/-- A compact-set graph bound from the actual extended position, with constants
depending only on the fixed compact set and coordinate swap. Consumer: the graph
interpolation endpoints in `app:ch_background:prop:bg-adjoint`. -/
theorem exists_cNorm_affineGraph_le
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    {O : Set (Euclidean n × CarrierParameter)} (hO : IsOpen O)
    {L : Set (CarrierParameter × Euclidean n)} (hL : IsCompact L)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ Y : Euclidean n × CarrierParameter → Euclidean (n - 1),
        ContDiffOn ℝ ∞ Y O → ∀ m,
        cNorm L m (fun p ↦ (p.1, affineExtension A χ Y (p.2,p.1))) ≤
          C m * (1 + cNorm (tsupport χ) m Y) := by
  obtain ⟨D, hD, hd⟩ := exists_cNorm_affineExtension_le A hO
    (hL.image continuous_swap) hχ hc hs
  obtain ⟨B, hB, hb⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean (n-1))
    hL (hL.image continuous_swap) (fun _ _ ↦ (contDiff_snd.prodMk contDiff_fst).contDiffAt)
    (fun p hp ↦ mem_image_of_mem Prod.swap hp)
  refine ⟨fun m ↦ cNorm L m (Prod.fst : CarrierParameter × Euclidean n → CarrierParameter) +
      B m * D m, fun m ↦ by
        have := cNorm_nonneg L m (Prod.fst : CarrierParameter × Euclidean n → CarrierParameter)
        have := mul_pos (hB m) (hD m)
        positivity, ?_⟩
  intro Y hY m
  have hext := affineExtension_contDiff A hO hχ hY hs
  have hpair := cNorm_prodMk_le_on L hL m
    (fun _ _ ↦ (contDiff_fst (n := ∞)).contDiffAt.of_le (by simp))
    (fun _ _ ↦ (hext.comp (contDiff_snd.prodMk contDiff_fst)).contDiffAt.of_le (by simp))
  have hh := (hb _ (fun _ _ ↦ hext.contDiffAt) m).trans
    (mul_le_mul_of_nonneg_left (hd Y hY m) (hB m).le)
  change cNorm L m (fun p ↦ affineExtension A χ Y (p.2,p.1)) ≤ _ at hh
  simp only [Function.comp_def] at hpair
  dsimp only
  nlinarith [mul_nonneg (cNorm_nonneg L m
    (Prod.fst : CarrierParameter × Euclidean n → CarrierParameter))
      (cNorm_nonneg (tsupport χ) m Y)]

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Global positive graph jets of the SAME projected-stress affine extension.
The fixed primitive reserve is `2(n+1)+5`; the one high norm is shared with the
field profiles. Constants precede the immersion. Natural subtraction preserves
the endpoint exponent, including `s = 0`.
Consumer: `hYB` in `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_projected_affineGraph_profile {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ extensionDomain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) (s : ℕ) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
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
        ∀ p : CarrierParameter × Euclidean n, ∀ i, 1 ≤ i → i ≤ s+2*(n+1) →
          ‖iteratedFDeriv ℝ i (fun p : CarrierParameter × Euclidean n ↦
            (p.1, Y (p.2,p.1))) p‖ ≤
            B i * (1 + cNorm K (s+2*(n+1)+5) F) ^
              (((i-1-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  obtain ⟨R, hR, hsupport⟩ := (hc.image continuous_swap).isBounded.subset_closedBall_lt
    0 (0 : CarrierParameter × Euclidean n)
  let J := closedBall (0 : CarrierParameter × Euclidean n) R
  have hs' : tsupport χ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    have hh := hs hp
    refine ⟨hh.1, fun i ↦ ?_⟩
    have hh' := hh.2 i
    linarith [hP.1]
  obtain ⟨D, hD, hd⟩ := CanonicalCarrier.exists_projected_transportPosition_bound
    T (N := N) hP hc hs' hK hKU hball M hκmet hκ
  obtain ⟨E, hE, he⟩ := exists_cNorm_affineGraph_le A (extensionDomain_open T)
    (isCompact_closedBall (0 : CarrierParameter × Euclidean n) R) hχ hc hs
  let G := fun m ↦ E m * (1 + D m)
  have hG m : 0 < G m := mul_pos (hE m) (by linarith [hD m])
  let b := 2*(n+1)+1
  obtain ⟨B, hB, hb⟩ := exists_closedBall_reserve_profile
    (F := CarrierParameter × Euclidean (n-1)) (0 : CarrierParameter × Euclidean n)
    hR b s (G b * (1+M)) (G (b+s))
  let L : (CarrierParameter × Euclidean n) →L[ℝ] CarrierParameter × Euclidean (n-1) :=
    (ContinuousLinearMap.fst ℝ CarrierParameter (Euclidean n)).prod
      (A.comp (ContinuousLinearMap.snd ℝ CarrierParameter (Euclidean n)))
  refine ⟨fun i ↦ B i + ‖L‖, fun i ↦ add_nonneg (hB i) (norm_nonneg _), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
    contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  let Y := affineExtension A χ (CanonicalCarrier.transportPosition T Q)
  let f := fun p : CarrierParameter × Euclidean n ↦ (p.1, Y (p.2,p.1))
  have hY := transportPosition_contDiffOn_extensionDomain T hP Q
  have hf : ContDiff ℝ ∞ f := graph_contDiff
    (affineExtension_contDiff A (extensionDomain_open T) hχ hY hs)
  have hfour : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hbound (m) : cNorm J m f ≤ G m * (1 + cNorm K (m+4) F) := by
    have hh := hd F hF hi hrank hfour hmet hnormal hlow m
    apply (he _ hY m).trans
    dsimp [G]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hE m).le
    nlinarith [cNorm_nonneg K (m+4) F]
  have hlow' : cNorm J b f ≤ G b * (1+M) :=
    (hbound b).trans (mul_le_mul_of_nonneg_left (by dsimp [b]; linarith) (hG b).le)
  let H := 1 + cNorm K (s+2*(n+1)+5) F
  have hH : 1 ≤ H := by dsimp [H]; linarith [cNorm_nonneg K (s+2*(n+1)+5) F]
  have hhigh : cNorm J (b+s) f ≤ G (b+s) * H := by
    simpa only [H, b, show 2*(n+1)+1+s+4 = s+2*(n+1)+5 by omega] using hbound (b+s)
  intro p i hi₁ his
  have hexc : i-b = i-1-2*(n+1) := by dsimp [b]; omega
  by_cases hp : p ∈ J
  · have hjet := hb f hf hlow' H hH hhigh i (by dsimp [b]; omega) p hp
    rw [hexc] at hjet
    exact hjet.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg L))
      (Real.rpow_nonneg (zero_le_one.trans hH) _))
  · have hnot : (p.2,p.1) ∉ tsupport χ := fun hh ↦ hp
      (hsupport (mem_image_of_mem Prod.swap hh))
    have heq : f =ᶠ[𝓝 p] L := by
      have hh := (affineExtension_eventuallyEq_reference A
        (CanonicalCarrier.transportPosition T Q) hnot).comp_tendsto continuous_swap.continuousAt
      filter_upwards [hh] with q hq
      exact congrArg (Prod.mk q.1) hq
    rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
    apply (norm_iteratedFDeriv_linear_pos_le L i hi₁ p).trans
    have hpw : 1 ≤ H ^ (((i-1-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) :=
      Real.one_le_rpow hH (by positivity)
    nlinarith [hB i, norm_nonneg L]

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
