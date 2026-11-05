module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.PhysicalInverse

/-!
# Joint profiles after substituting the original first coefficient jet

The complete physical inverse action depends on `Q`, `fderiv Q`, `B`, and
the normalized full covector. One derivative of reserve absorbs the first
jet, leaving zero slow-scale offset. This is the composition step for
`coefficientConicPhysicalAction` in the branch-three comparable grade.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers CompositionBounds
open RegularSector.Characteristic.ResidualCoordinates
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
local notation "Jet" => Coeff × ((E →L[ℝ] Coeff) × Mat)

private theorem linear_jet_bound (T : E × E →L[ℝ] E) (p : E × E)
    {k : ℕ} (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k T p‖ ≤ ‖T‖ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ T = fun _ ↦ T := funext fun _ ↦ T.fderiv
  rw [he]
  by_cases hj : j = 0
  · subst j; simp only [norm_iteratedFDeriv_zero, le_refl]
  · simp [iteratedFDeriv_const_of_ne hj]

/-- A smooth function of the original coefficient first jet has a joint
`C_k L^k` profile on its retained compact domain. This specialized composition
lemma is consumed by `coefficientConicPhysicalAction`: its smoothness is proved
from the actual inverse domain, not a symbol-grade hypothesis. The original
reserve is unchanged, subject only to `1 ≤ Rstar`; the fixed offset is zero
(`app:ch_regular:eq:initial-coefficient-profile`, `high-amplitude`). -/
theorem exists_coefficientFirstJet_joint_profile
    (i : Fin (d+1)) (G : Jet × E → CMat)
    {S : Set (Jet × E)} (hS : IsCompact S)
    (hG : ∀ z ∈ S, ContDiffAt ℝ ∞ G z)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (x : E) (RQ : ℝ) (Ω : Set E), IsOpen Ω → closedBall x RQ ⊆ Ω →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ A k * L ^ (k - Rstar)) →
      ∀ v : E × E, physicalCoordinates i v.1 ∈ closedBall x RQ →
        ((Q (physicalCoordinates i v.1),
          (fderiv ℝ Q (physicalCoordinates i v.1), B (physicalCoordinates i v.1))), v.2) ∈ S →
      ∀ k, ‖iteratedFDeriv ℝ k (fun w : E × E ↦
        G ((Q (physicalCoordinates i w.1),
          (fderiv ℝ Q (physicalCoordinates i w.1), B (physicalCoordinates i w.1))), w.2)) v‖ ≤
        C k * L ^ k := by
  let P : E × E →L[ℝ] E := (physicalCoordinates i).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ E E)
  let T := ContinuousLinearMap.snd ℝ E E
  let D := fun k ↦ A k * ‖P‖ ^ k
  let H := fun k ↦ A (k+1) * ‖P‖ ^ k
  let J := fun k ↦ max (max (D k) (max (H k) (D k))) ‖T‖
  have hJ k : 0 ≤ J k := (norm_nonneg T).trans (le_max_right _ _)
  let C := fun k ↦ ∑ part : OrderedFinpartition k,
    cNorm S part.length G * ∏ j, J (part.partSize j)
  refine ⟨C, fun k ↦ Finset.sum_nonneg (fun part _ ↦
    mul_nonneg (cNorm_nonneg _ _ _) (Finset.prod_nonneg (fun _ _ ↦ hJ _))), ?_⟩
  intro Rstar hR L hL x RQ Ω hΩ hball Q B hQ hB hQp hBp v hv hmem k
  let F : E × E → Jet × E := fun w ↦ ((Q (P w), (fderiv ℝ Q (P w), B (P w))), w.2)
  have hq := hQ.contDiffAt (hΩ.mem_nhds (hball hv))
  have hb := hB.contDiffAt (hΩ.mem_nhds (hball hv))
  have hd := hq.fderiv_right (m := ∞) (by simp)
  have hF : ContDiffAt ℝ ∞ F v :=
    ((hq.comp v P.contDiff.contDiffAt).prodMk
      ((hd.comp v P.contDiff.contDiffAt).prodMk (hb.comp v P.contDiff.contDiffAt))).prodMk contDiffAt_snd
  have houter j : ‖iteratedFDeriv ℝ j G (F v)‖ ≤ cNorm S j G :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
      (fun z hz ↦ (hG z hz).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) hmem le_rfl
  have hbound {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : E → W) (hf : ContDiffOn ℝ ∞ f Ω)
      (hp : ∀ j, cNorm (closedBall x RQ) j f ≤ A j * L ^ (j-Rstar)) (j : ℕ) :
      ‖iteratedFDeriv ℝ j f (P v)‖ ≤ A j * L ^ (j-Rstar) :=
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun y hy ↦ (hf.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
        (show (j : ℕ∞ω) ≤ ∞ by simp)) hv le_rfl).trans (hp j)
  have hinner j (hj : 1 ≤ j) : ‖iteratedFDeriv ℝ j F v‖ ≤ J j * L ^ j := by
    have hqj : ‖iteratedFDeriv ℝ j (Q ∘ P) v‖ ≤ D j * L ^ j := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hΩ hQ (hball hv) j).trans
      have hh : ‖iteratedFDeriv ℝ j Q (P v)‖ ≤ A j * L ^ j :=
        (hbound (W := Coeff) Q hQ hQp j).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (Nat.sub_le j Rstar)) (hA j))
      exact (mul_le_mul_of_nonneg_right hh
        (pow_nonneg (norm_nonneg P) j)).trans_eq (by dsimp [D]; ring)
    have hbj : ‖iteratedFDeriv ℝ j (B ∘ P) v‖ ≤ D j * L ^ j := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hΩ hB (hball hv) j).trans
      have hh : ‖iteratedFDeriv ℝ j B (P v)‖ ≤ A j * L ^ j :=
        (hbound (W := Mat) B hB hBp j).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (Nat.sub_le j Rstar)) (hA j))
      exact (mul_le_mul_of_nonneg_right hh
        (pow_nonneg (norm_nonneg P) j)).trans_eq (by dsimp [D]; ring)
    have hdj : ‖iteratedFDeriv ℝ j ((fderiv ℝ Q) ∘ P) v‖ ≤ H j * L ^ j := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hΩ
        (hQ.fderiv_of_isOpen hΩ (m := ∞) (by simp)) (hball hv) j).trans
      rw [norm_iteratedFDeriv_fderiv]
      have hh : ‖iteratedFDeriv ℝ (j+1) Q (P v)‖ ≤ A (j+1) * L ^ j :=
        (hbound (W := Coeff) Q hQ hQp (j+1)).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (by omega : j+1-Rstar ≤ j)) (hA (j+1)))
      exact (mul_le_mul_of_nonneg_right hh
        (pow_nonneg (norm_nonneg P) j)).trans_eq (by dsimp [H]; ring)
    have htj : ‖iteratedFDeriv ℝ j T v‖ ≤ ‖T‖ * L ^ j :=
      (linear_jet_bound T v hj).trans
        (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hL))
    change ‖iteratedFDeriv ℝ j
      (fun w ↦ (((Q ∘ P) w, (((fderiv ℝ Q) ∘ P) w, (B ∘ P) w)), T w)) v‖ ≤ _
    rw [iteratedFDeriv_prodMk
      ((hq.comp v P.contDiff.contDiffAt).prodMk
        ((hd.comp v P.contDiff.contDiffAt).prodMk (hb.comp v P.contDiff.contDiffAt)))
      T.contDiff.contDiffAt (by simp), ContinuousMultilinearMap.opNorm_prod,
      iteratedFDeriv_prodMk (hq.comp v P.contDiff.contDiffAt)
        ((hd.comp v P.contDiff.contDiffAt).prodMk (hb.comp v P.contDiff.contDiffAt)) (by simp),
      ContinuousMultilinearMap.opNorm_prod,
      iteratedFDeriv_prodMk (hd.comp v P.contDiff.contDiffAt) (hb.comp v P.contDiff.contDiffAt) (by simp),
      ContinuousMultilinearMap.opNorm_prod]
    exact (max_le_max (max_le_max hqj (max_le_max hdj hbj)) htj).trans_eq (by
      simp only [J, max_mul_of_nonneg _ _ (pow_nonneg (zero_le_one.trans hL) j)])
  change ‖iteratedFDeriv ℝ k (G ∘ F) v‖ ≤ _
  have hGv : ContDiffAt ℝ ∞ G (F v) := hG _ hmem
  apply (norm_iteratedFDeriv_comp_le_partition_sum (hGv.of_le (by simp))
    (hF.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) le_rfl).trans
  dsimp only [C]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro part _
  calc
    _ ≤ cNorm S part.length G * ∏ j, J (part.partSize j) * L ^ part.partSize j :=
      mul_le_mul (houter _) (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun j _ ↦ hinner _ (part.partSize_pos j)))
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (cNorm_nonneg _ _ _)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_partSize, mul_assoc]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
