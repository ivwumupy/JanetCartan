module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Averaging
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.TameComposition
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local norm operations for the carrier substitution

These operations supply the primitive carrier and product estimates in
`app:ch_seed:eq:seed-quotient-integral`. Smoothness is only required on the
specified open neighborhoods. The consumer is `QuotientJets`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {A B D F : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pairing preserves additive high norms for the carrier substitution in
`app:ch_seed:eq:seed-quotient-integral`. -/
theorem cNorm_prodMk_le_on (K : Set A) (hK : IsCompact K) (k : ℕ)
    {f : A → B} {g : A → D}
    (hf : ∀ x ∈ K, ContDiffAt ℝ k f x)
    (hg : ∀ x ∈ K, ContDiffAt ℝ k g x) :
    cNorm K k (fun x ↦ (f x, g x)) ≤ cNorm K k f + cNorm K k g := by
  let a := fun j ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' K)
  let b := fun j ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ j g x‖) '' K)
  have ha j : 0 ≤ a j := sSup_norm_iteratedFDeriv_nonneg K j f
  have hb j : 0 ≤ b j := sSup_norm_iteratedFDeriv_nonneg K j g
  apply (cNorm_le_sum_of_bounds (C := fun j ↦ a j + b j)
    (fun j _ ↦ add_nonneg (ha j) (hb j)) ?_).trans_eq
  · simp only [Finset.sum_add_distrib, cNorm, a, b]
  · intro j hj x hx
    rw [iteratedFDeriv_prodMk (hf x hx) (hg x hx) (by exact_mod_cast hj)]
    rw [ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hf hj)
        (mem_image_of_mem _ hx)).trans (le_add_of_nonneg_right (hb j))
    · exact (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hg hj)
        (mem_image_of_mem _ hx)).trans (le_add_of_nonneg_left (ha j))

/-- Restriction along a contraction bounds every carrier jet without derivative
loss (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem cNorm_comp_contraction_le_on (L : A →L[ℝ] B) (hL : ‖L‖ ≤ 1)
    {K : Set A} {J V : Set B} (hJ : IsCompact J) (hV : IsOpen V)
    (hJV : J ⊆ V) {f : B → F} (hf : ContDiffOn ℝ ∞ f V)
    (hmap : MapsTo L K J) (k : ℕ) :
    cNorm K k (f ∘ L) ≤ (k + 1 : ℝ) * cNorm J k f := by
  have hb : ∀ j ≤ k, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ cNorm J k f := by
    intro j hj x hx
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le L hV hf
      (hJV (hmap hx)) j).trans
    calc
      _ ≤ cNorm J k f * 1 := mul_le_mul
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
          (fun y hy ↦ (hf.contDiffAt (hV.mem_nhds (hJV hy))).of_le (by simp))
          (hmap hx) hj)
        (pow_le_one₀ (norm_nonneg _) hL) (by positivity) (cNorm_nonneg _ _ _)
      _ = _ := mul_one _
  simpa using cNorm_le_sum_of_bounds (fun _ _ ↦ cNorm_nonneg J k f) hb

/-- Local bilinear bound with one fixed factor. It is used for epsilon times
carrier, before interpolation of the varying phase/carrier product
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem cNorm_bilinear_le_on (b : B →L[ℝ] D →L[ℝ] F)
    {K U : Set A} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : A → B} {g : A → D} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U) (k : ℕ) :
    cNorm K k (fun x ↦ b (f x) (g x)) ≤
      (∑ j ∈ Finset.range (k + 1), ‖b‖ *
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * cNorm K k f * cNorm K k g := by
  have hb : ∀ j ≤ k, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun x ↦ b (f x) (g x)) x‖ ≤
        (‖b‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
          cNorm K k f * cNorm K k g := by
    intro j hj x hx
    have h := b.norm_iteratedFDerivWithin_le_of_bilinear hf hg
      hU.uniqueDiffOn (hKU hx) (n := j) (by simp)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)] at h
    apply h.trans
    calc
      _ ≤ ‖b‖ * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * cNorm K k f * cNorm K k g := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg b)
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
            (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp)) hx
            (by have := Finset.mem_range.mp hi; omega)
        · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
            (fun y hy ↦ (hg.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp)) hx
            ((Nat.sub_le _ _).trans hj)
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _)
      _ = _ := by simp only [← Finset.sum_mul, mul_assoc]
  simpa only [Finset.sum_mul] using cNorm_le_sum_of_bounds (C := fun j ↦
    (‖b‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
      cNorm K k f * cNorm K k g) (fun _ _ ↦ mul_nonneg
        (mul_nonneg (mul_nonneg (norm_nonneg b)
          (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))) (cNorm_nonneg _ _ _))
        (cNorm_nonneg _ _ _)) hb

/-- Additive one-high bilinear estimate, derived by tame composition with the
fixed bilinear map on a fixed ball. The constant precedes both varying inputs.
This is the gradient/carrier product in `app:ch_seed:eq:seed-quotient-integral`. -/
theorem exists_cNorm_bilinear_le_additive_oneHigh
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ D]
    (b : B →L[ℝ] D →L[ℝ] F) (a : A) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set A} (hU : IsOpen U) (hball : Metric.closedBall a ρ ⊆ U)
    {k : ℕ} (hk : 2 ≤ k) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > (0 : ℝ), ∀ (f : A → B) (g : A → D),
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      cNorm (Metric.closedBall a ρ) 1 f ≤ M →
      cNorm (Metric.closedBall a ρ) 1 g ≤ N →
      cNorm (Metric.closedBall a ρ) k (fun x ↦ b (f x) (g x)) ≤
        C * (1 + cNorm (Metric.closedBall a ρ) k f + cNorm (Metric.closedBall a ρ) k g) := by
  let K := Metric.closedBall a ρ
  let J := Metric.closedBall (0 : B × D) (1 + M + N)
  let H : B × D → F := fun w ↦ b w.1 w.2
  have hH : ContDiff ℝ ∞ H := b.isBoundedBilinearMap.contDiff
  obtain ⟨C, hC, hc⟩ := exists_cNorm_comp_le_additive_oneHigh (F := F)
    a (0 : B × D) hρ (show 0 < 1 + M + N by positivity)
    hU isOpen_univ hball (subset_univ _) hk (add_nonneg hM hN)
    (cNorm_nonneg J 1 H)
  have hhk := cNorm_nonneg J k H
  refine ⟨C * (1 + cNorm J k H), mul_pos hC (by linarith), ?_⟩
  intro f g hf hg hfM hgN
  have hfl (j : ℕ) : ∀ x ∈ K, ContDiffAt ℝ j f x :=
    fun x hx ↦ (hf.contDiffAt (hU.mem_nhds (hball hx))).of_le (by simp)
  have hgl (j : ℕ) : ∀ x ∈ K, ContDiffAt ℝ j g x :=
    fun x hx ↦ (hg.contDiffAt (hU.mem_nhds (hball hx))).of_le (by simp)
  have hp j := cNorm_prodMk_le_on K (isCompact_closedBall a ρ) j (hfl j) (hgl j)
  have hm : MapsTo (fun x ↦ (f x, g x)) K J := by
    intro x hx
    simp only [J, Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    apply max_le
    · have hf0 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (isCompact_closedBall a ρ) (hfl 1) hx (Nat.zero_le 1)
      simp only [norm_iteratedFDeriv_zero] at hf0
      linarith
    · have hg0 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (isCompact_closedBall a ρ) (hgl 1) hx (Nat.zero_le 1)
      simp only [norm_iteratedFDeriv_zero] at hg0
      linarith
  have hh := hc (fun x ↦ (f x, g x)) H (hf.prodMk hg) hH.contDiffOn hm
    ((hp 1).trans (add_le_add hfM hgN)) le_rfl
  apply hh.trans
  have hpk := hp k
  have hfk := cNorm_nonneg K k f
  have hgk := cNorm_nonneg K k g
  change C * (1 + cNorm K k (fun x ↦ (f x, g x)) + cNorm J k H) ≤
    C * (1 + cNorm J k H) * (1 + cNorm K k f + cNorm K k g)
  nlinarith [mul_nonneg hhk (add_nonneg hfk hgk)]

end JanetCartan.FullPhaseCharts.InverseEstimates
