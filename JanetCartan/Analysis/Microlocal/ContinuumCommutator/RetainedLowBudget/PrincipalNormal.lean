module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction

/-!
# The principal normal without the reconstruction derivative

The carrier in `app:ch_background:eq:bg-T` uses the principal normal only.
Its finite-jet expression does not use the derivative of the null amplitude.
The joint reconstruction estimate also estimates the lower-order correction,
which does use that derivative. Keeping the principal expression alone saves
one derivative in the input to the retained commutator baseline.

Consumer: the retained carrier coefficient bound at order `2*(n+1)+1`
in `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.ContinuumCommutator.RetainedLowBudget
open GeometricProfile AmbientResponse LeadingWave LeadingWave.JointReconstruction

private def principalJet {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : Euclidean n → Euclidean N) (b ξ : Euclidean n × Z → Euclidean n)
    (p : Euclidean n × Z) : JointJet n N :=
  ((secondJet F p.1, b p, 0), ξ p)

private theorem norm_iteratedFDeriv_comp_right_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (L : G →L[ℝ] E) (hL : ‖L‖ ≤ 1) {x : G} (hx : L x ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  have hpre := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen j hpre hx,
    iteratedFDerivWithin_of_isOpen j hU hx] at he
  rw [he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL)
    _ = _ := mul_one _

private theorem cNorm_principalJet_le {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) (ρ : ℝ)
    {U : Set (Euclidean n)} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hKU : Metric.closedBall a.1 ρ ⊆ U) (hKV : Metric.closedBall a.2 ρ ⊆ V)
    {F : Euclidean n → Euclidean N} {b ξ : Euclidean n × Z → Euclidean n}
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V)) (r : ℕ) :
    cNorm (Metric.closedBall a ρ) r (principalJet F b ξ) ≤ (r + 1 : ℝ) *
      (cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
        cNorm (Metric.closedBall a ρ) r b + cNorm (Metric.closedBall a ρ) r ξ) := by
  have hKUV : Metric.closedBall a ρ ⊆ U ×ˢ V := by
    rw [← closedBall_prod_same a.1 a.2 ρ]
    exact Set.prod_mono hKU hKV
  have hFat (x) (hx : x ∈ Metric.closedBall a.1 ρ) := hF.contDiffAt (hU.mem_nhds (hKU hx))
  have hbat (p) (hp : p ∈ Metric.closedBall a ρ) :=
    hb.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))
  have hξat (p) (hp : p ∈ Metric.closedBall a ρ) :=
    hξ.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))
  have hdF : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hddF : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) U :=
    hdF.fderiv_of_isOpen hU (by simp)
  have hJF : ContDiffOn ℝ ∞ (secondJet F) U := hdF.prodMk hddF
  have h := cNorm_le_sum_of_bounds (s := Metric.closedBall a ρ) (r := r)
    (f := principalJet F b ξ)
    (C := fun _ ↦ cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
      cNorm (Metric.closedBall a ρ) r b + cNorm (Metric.closedBall a ρ) r ξ)
    (fun _ _ ↦ add_nonneg (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..))
      (cNorm_nonneg ..)) (by
      intro j hj p hp
      have hpx : p.1 ∈ Metric.closedBall a.1 ρ := by
        have := hp
        rw [← closedBall_prod_same a.1 a.2 ρ] at this
        exact this.1
      have hFp := hFat p.1 hpx
      have hbp := hbat p hp
      have hξp := hξat p hp
      have hJFp : ContDiffAt ℝ ∞ (fun q : Euclidean n × Z ↦ secondJet F q.1) p :=
        (hJF.contDiffAt (hU.mem_nhds (hKU hpx))).comp p contDiffAt_fst
      have hjet : ‖iteratedFDeriv ℝ j (fun q : Euclidean n × Z ↦ secondJet F q.1) p‖ ≤
          cNorm (Metric.closedBall a.1 ρ) (r + 2) F := by
        apply (norm_iteratedFDeriv_comp_right_le hU hJF
          (ContinuousLinearMap.fst ℝ (Euclidean n) Z)
          (ContinuousLinearMap.norm_fst_le ..) (hKU hpx) j).trans
        change ‖iteratedFDeriv ℝ j (fun x ↦ (fderiv ℝ F x,
          fderiv ℝ (fderiv ℝ F) x)) p.1‖ ≤ _
        rw [iteratedFDeriv_prodMk (hFp.fderiv_right (show ∞ + 1 ≤ ∞ by simp))
          ((hFp.fderiv_right (show ∞ + 1 ≤ ∞ by simp)).fderiv_right (show ∞ + 1 ≤ ∞ by simp)) (by simp),
          ContinuousMultilinearMap.opNorm_prod]
        simp only [norm_iteratedFDeriv_fderiv]
        apply max_le
        · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
            (fun x hx ↦ (hFat x hx).of_le (by simp)) hpx (by omega)
        · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
            (fun x hx ↦ (hFat x hx).of_le (by simp)) hpx (by omega)
      have hb0 : ‖iteratedFDeriv ℝ j b p‖ ≤ cNorm (Metric.closedBall a ρ) r b :=
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
          (fun q hq ↦ (hbat q hq).of_le (by simp)) hp (by omega)
      have hb1 : ‖iteratedFDeriv ℝ j
          (fun _ : Euclidean n × Z ↦ (0 : Euclidean n →L[ℝ] Euclidean n)) p‖ ≤
            cNorm (Metric.closedBall a ρ) r b := by
        simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        exact cNorm_nonneg ..
      have hξ0 : ‖iteratedFDeriv ℝ j ξ p‖ ≤ cNorm (Metric.closedBall a ρ) r ξ :=
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
          (fun q hq ↦ (hξat q hq).of_le (by simp)) hp hj
      have hdbp : ContDiffAt ℝ ∞
          (fun _ : Euclidean n × Z ↦ (0 : Euclidean n →L[ℝ] Euclidean n)) p :=
        contDiffAt_const
      unfold principalJet
      rw [iteratedFDeriv_prodMk (hJFp.prodMk (hbp.prodMk hdbp)) hξp (by simp),
        ContinuousMultilinearMap.opNorm_prod,
        iteratedFDeriv_prodMk hJFp (hbp.prodMk hdbp) (by simp),
        ContinuousMultilinearMap.opNorm_prod,
        iteratedFDeriv_prodMk hbp hdbp (by simp), ContinuousMultilinearMap.opNorm_prod]
      have hFn := cNorm_nonneg (Metric.closedBall a.1 ρ) (r + 2) F
      have hbn := cNorm_nonneg (Metric.closedBall a ρ) r b
      have hξn := cNorm_nonneg (Metric.closedBall a ρ) r ξ
      exact max_le (max_le (by linarith) (max_le (by linarith) (by linarith))) (by linarith))
  simpa [mul_add] using h


private theorem exists_cNorm_principalNormal_le_of_compact_range
    {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {T : Set (SecondJet (Euclidean n) (Euclidean N))} (hT : IsCompact T)
    (hTi : ∀ J ∈ T, Function.Injective J.1)
    (hTr : ∀ J ∈ T, Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N))) (M : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (Euclidean n)) (V : Set Z), IsOpen U → IsOpen V →
      Metric.closedBall a.1 ρ ⊆ U → Metric.closedBall a.2 ρ ⊆ V →
      ∀ (F : Euclidean n → Euclidean N) (b ξ : Euclidean n × Z → Euclidean n),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞ b (U ×ˢ V) → ContDiffOn ℝ ∞ ξ (U ×ˢ V) →
      MapsTo (secondJet F) (Metric.closedBall a.1 ρ) T →
      cNorm (Metric.closedBall a ρ) 1 b ≤ M → cNorm (Metric.closedBall a ρ) 1 ξ ≤ M →
      cNorm (Metric.closedBall a ρ) r
          (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) ≤
        C * (1 + cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
          cNorm (Metric.closedBall a ρ) r b + cNorm (Metric.closedBall a ρ) r ξ) := by
  have ht := isCompact_jointJetRange hT (max M 0)
  obtain ⟨Cn, hCn, hnormal⟩ :=
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ ht (le_refl r)
      (fun q hq ↦ (contDiffAt_principalNormalValue
        (hTi q.1.1 hq.1.1) (hTr q.1.1 hq.1.1)).of_le (by simp))
  refine ⟨Cn * (r + 1), by positivity, ?_⟩
  intro U V hU hV hKU hKV F b ξ hF hFi hFr hb hξ hFT hbM hξM
  have hKUV : Metric.closedBall a ρ ⊆ U ×ˢ V := by
    rw [← closedBall_prod_same a.1 a.2 ρ]
    exact Set.prod_mono hKU hKV
  have hjt : MapsTo (principalJet F b ξ) (Metric.closedBall a ρ)
      (jointJetRange T (max M 0)) := by
    intro p hp
    have h := mapsTo_jointJet_range a ρ hFT
      (fun p hp ↦ (hb.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp))
      (fun p hp ↦ (hξ.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp))
      (hbM.trans (le_max_left M 0)) (hξM.trans (le_max_left M 0)) hp
    exact ⟨⟨h.1.1, h.1.2.1, by
      simpa only [principalJet, Metric.mem_closedBall, dist_self] using (le_max_right M 0)⟩, h.2⟩
  have hdF := hF.fderiv_of_isOpen hU (by simp : ∞ + 1 ≤ ∞)
  have hddF := hdF.fderiv_of_isOpen hU (by simp : ∞ + 1 ≤ ∞)
  have hj : ContDiffOn ℝ ∞ (principalJet F b ξ) (U ×ˢ V) :=
    (((hdF.prodMk hddF).comp contDiffOn_fst (fun _ hp ↦ hp.1)).prodMk
      (hb.prodMk contDiffOn_const)).prodMk hξ
  have hn := hnormal (U ×ˢ V) (hU.prod hV) hKUV (principalJet F b ξ) hj hjt
  have hen : cNorm (Metric.closedBall a ρ) r
      (principalNormalValue ∘ principalJet F b ξ) = cNorm (Metric.closedBall a ρ) r
      (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ r
    intro p hp
    exact (jointJet_fields_eventuallyEq ξ hU hV hF hb hFi hFr (hKUV hp)).1
  rw [hen] at hn
  have hjet := cNorm_principalJet_le a ρ hU hV hKU hKV hF hb hξ r
  have hhigh : 1 + cNorm (Metric.closedBall a ρ) r (principalJet F b ξ) ≤
      (r + 1 : ℝ) * (1 + cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
        cNorm (Metric.closedBall a ρ) r b + cNorm (Metric.closedBall a ρ) r ξ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  exact hn.trans ((mul_le_mul_of_nonneg_left hhigh hCn.le).trans_eq (by ring))

private theorem norm_secondJet_le_cNorm_four {n N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) {F : Euclidean n → Euclidean N}
    (hF : ∀ x ∈ K, ContDiffAt ℝ 4 F x) {x : Euclidean n} (hx : x ∈ K) :
    ‖secondJet F x‖ ≤ cNorm K 4 F := by
  change max ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ _
  apply max_le
  · have h := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hF hx (by omega : 1 ≤ 4)
    simpa only [norm_iteratedFDeriv_one] using h
  · have h := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hF hx (by omega : 2 ≤ 4)
    simpa only [show 2 = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using h

/-- The actual principal normal costs two immersion derivatives and no
null-amplitude derivative. The compact second-jet range is constructed from
the fixed C4 budget and the original metric and normal-pairing gaps. Constants
precede the varying fields. This removes the extra derivative introduced by
estimating the lower-order reconstruction simultaneously, for the carrier
baseline in `app:ch_background:eq:bg-commutator` and `app:ch_waves:eq:joint-tame`.
The scalar transport and supported-symbol inputs remain separate obligations. -/
theorem exists_cNorm_principalNormal_le_of_primitive_bounds
    {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {M γ κ : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hκ : 0 < κ) (B : ℝ) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ (U : Set (Euclidean n)) (V : Set Z), IsOpen U → IsOpen V →
      Metric.closedBall a.1 ρ ⊆ U → Metric.closedBall a.2 ρ ⊆ V →
      ∀ (F : Euclidean n → Euclidean N) (b ξ : Euclidean n × Z → Euclidean n),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞ b (U ×ˢ V) → ContDiffOn ℝ ∞ ξ (U ×ˢ V) →
      cNorm (Metric.closedBall a.1 ρ) 4 F ≤ M →
      (∀ x ∈ Metric.closedBall a.1 ρ, ∀ v,
        γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Metric.closedBall a.1 ρ, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (Metric.closedBall a ρ) 1 b ≤ B → cNorm (Metric.closedBall a ρ) 1 ξ ≤ B →
      ∀ r : ℕ,
      cNorm (Metric.closedBall a ρ) r
          (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) ≤
        C r * (1 + cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
          cNorm (Metric.closedBall a ρ) r b + cNorm (Metric.closedBall a ρ) r ξ) := by
  obtain ⟨T, hT, hTi, hTr, hmem⟩ :=
    exists_compact_secondJet_range (n := n) (N := N) hM hγ hκ
  choose C hC hbound using fun r ↦
    exists_cNorm_principalNormal_le_of_compact_range a hρ hT hTi hTr B r
  refine ⟨C, hC, ?_⟩
  intro U V hU hV hKU hKV F b ξ hF hi hrank hb hξ hFM hmetric hnormal hbB hξB r
  apply hbound r U V hU hV hKU hKV F b ξ hF hi hrank hb hξ _ hbB hξB
  intro x hx
  have hFat (y) (hy : y ∈ Metric.closedBall a.1 ρ) :=
    hF.contDiffAt (hU.mem_nhds (hKU hy))
  exact hmem F x ((hFat x hx).of_le (by simp)) (hi x (hKU hx)) (hrank x (hKU hx))
    ((norm_secondJet_le_cNorm_four (isCompact_closedBall ..)
      (fun y hy ↦ (hFat y hy).of_le (by simp)) hx).trans hFM)
    (hmetric x hx) (hnormal x hx)

end JanetCartan.ContinuumCommutator.RetainedLowBudget
