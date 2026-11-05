module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.LocalIdentity
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Joint derivative bounds for the reconstruction jet

For `app:ch_waves:eq:joint-tame`, physical projection and restriction of the
joint differential have norm at most one. Thus the shared joint jet costs
only two derivatives of the immersion and one of the covector. These bounds
are consumed by the compact-range composition estimate in `Estimates`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.LeadingWave.JointReconstruction

set_option maxSynthPendingDepth 5

open GeometricProfile AmbientResponse

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

/-- Restricting the joint covector differential to physical directions costs
one derivative with no additional high-norm factor (`app:ch_waves:eq:joint-tame`). -/
theorem norm_iteratedFDeriv_physical_fderiv_le {n : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {b : Euclidean n × Z → Euclidean n} {p : Euclidean n × Z}
    (hb : ContDiffAt ℝ ∞ b p) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q ↦
      (fderiv ℝ b q).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z)) p‖ ≤
        ‖iteratedFDeriv ℝ (j + 1) b p‖ := by
  let L : ((Euclidean n × Z) →L[ℝ] Euclidean n) →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean n) :=
    (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n × Z) (Euclidean n)).flip
      (ContinuousLinearMap.inl ℝ (Euclidean n) Z)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro A
    change ‖A.comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z)‖ ≤ 1 * ‖A‖
    calc
      _ ≤ ‖A‖ * ‖ContinuousLinearMap.inl ℝ (Euclidean n) Z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ..) (norm_nonneg _)
      _ = _ := by ring
  have h := L.norm_iteratedFDeriv_comp_left
    (hb.fderiv_right (show ∞ + 1 ≤ ∞ by simp)) (by simp : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j (fun q ↦
    (fderiv ℝ b q).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z)) p‖ ≤ _ at h
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans (by
    simpa using mul_le_mul_of_nonneg_right hL
      (norm_nonneg (iteratedFDeriv ℝ (j + 1) b p)))

/-- The literal joint jet has a sum of single high norms on the product-norm
ball (`app:ch_waves:eq:joint-tame`). Smoothness is required only on the open
physical and parameter charts. The losses are respectively two, one and zero. -/
theorem cNorm_jointJet_le {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) (ρ : ℝ)
    {U : Set (Euclidean n)} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hKU : Metric.closedBall a.1 ρ ⊆ U) (hKV : Metric.closedBall a.2 ρ ⊆ V)
    {F : Euclidean n → Euclidean N} {b ξ : Euclidean n × Z → Euclidean n}
    (hF : ContDiffOn ℝ ∞ F U) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V)) (r : ℕ) :
    cNorm (Metric.closedBall a ρ) r (jointJet F b ξ) ≤ (r + 1 : ℝ) *
      (cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
        cNorm (Metric.closedBall a ρ) (r + 1) b + cNorm (Metric.closedBall a ρ) r ξ) := by
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
    (f := jointJet F b ξ)
    (C := fun _ ↦ cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
      cNorm (Metric.closedBall a ρ) (r + 1) b + cNorm (Metric.closedBall a ρ) r ξ)
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
      have hdbp : ContDiffAt ℝ ∞ (fun q ↦
          (fderiv ℝ b q).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z)) p :=
        (hbp.fderiv_right (by simp)).clm_comp contDiffAt_const
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
      have hb0 : ‖iteratedFDeriv ℝ j b p‖ ≤ cNorm (Metric.closedBall a ρ) (r + 1) b :=
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
          (fun q hq ↦ (hbat q hq).of_le (by simp)) hp (by omega)
      have hb1 : ‖iteratedFDeriv ℝ j (fun q ↦
          (fderiv ℝ b q).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z)) p‖ ≤
            cNorm (Metric.closedBall a ρ) (r + 1) b :=
        (norm_iteratedFDeriv_physical_fderiv_le hbp j).trans
          (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
            (fun q hq ↦ (hbat q hq).of_le (by simp)) hp (by omega))
      have hξ0 : ‖iteratedFDeriv ℝ j ξ p‖ ≤ cNorm (Metric.closedBall a ρ) r ξ :=
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
          (fun q hq ↦ (hξat q hq).of_le (by simp)) hp hj
      unfold jointJet
      rw [iteratedFDeriv_prodMk (hJFp.prodMk (hbp.prodMk hdbp)) hξp (by simp),
        ContinuousMultilinearMap.opNorm_prod,
        iteratedFDeriv_prodMk hJFp (hbp.prodMk hdbp) (by simp),
        ContinuousMultilinearMap.opNorm_prod,
        iteratedFDeriv_prodMk hbp hdbp (by simp), ContinuousMultilinearMap.opNorm_prod]
      have hFn := cNorm_nonneg (Metric.closedBall a.1 ρ) (r + 2) F
      have hbn := cNorm_nonneg (Metric.closedBall a ρ) (r + 1) b
      have hξn := cNorm_nonneg (Metric.closedBall a ρ) r ξ
      exact max_le (max_le (by linarith) (max_le (by linarith) (by linarith))) (by linarith))
  simpa [mul_add] using h

end JanetCartan.LeadingWave.JointReconstruction
