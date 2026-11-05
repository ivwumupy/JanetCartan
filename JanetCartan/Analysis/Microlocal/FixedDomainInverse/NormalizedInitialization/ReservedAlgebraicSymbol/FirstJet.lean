module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.FirstJetProfile
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus

/-!
# Preserve the original coefficient reserve through its first jet

The complete algebraic residual depends on `Q`, `fderiv Q`, `B`, and the
normalized covector. The first jet spends one coefficient derivative. The
finite composition rule retains every remaining natural subtraction reserve,
instead of replacing the inner powers by `L^j`.

Consumer: the SAME `coefficientConicPhysicalAction` in the algebraic diagonal
letter of `app:ch_response:eq:direct-envelope-profile`, with coefficient
profiles from `app:ch_regular:eq:initial-coefficient-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol

open ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers CompositionBounds
open RegularSector.Characteristic.ResidualCoordinates
open ResponseTransfer.GradedPrimitives

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
  · subst j
    simp only [norm_iteratedFDeriv_zero, le_refl]
  · simp [iteratedFDeriv_const_of_ne hj]

/-- Applying a fixed smooth coefficient operation to the ORIGINAL first jet
retains `L^(k+1-Rstar)`. The compact outer inverse domain is fixed before the
varying fields and scale. The chain rule uses
`GradedPrimitives.partition_sub_reserve_le` through its proved composition
estimate; no symbol estimate is an input
(`app:ch_regular:eq:initial-coefficient-profile`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_coefficientFirstJet_reserved_joint_profile
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
        C k * L ^ (k + 1 - Rstar) := by
  let P : E × E →L[ℝ] E := (physicalCoordinates i).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ E E)
  let T := ContinuousLinearMap.snd ℝ E E
  let D := fun k ↦ A k * ‖P‖ ^ k
  let H := fun k ↦ A (k+1) * ‖P‖ ^ k
  let J := fun k ↦ max (max (D k) (max (H k) (D k))) ‖T‖
  have hJ k : 0 ≤ J k := (norm_nonneg T).trans (le_max_right _ _)
  let C := compositionConstant (fun j ↦ cNorm S j G) J
  refine ⟨C, compositionConstant_nonneg (fun _ ↦ cNorm_nonneg _ _ _) hJ, ?_⟩
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
      (g : E → W) (hg : ContDiffOn ℝ ∞ g Ω)
      (hp : ∀ j, cNorm (closedBall x RQ) j g ≤ A j * L ^ (j-Rstar)) (j : ℕ) :
      ‖iteratedFDeriv ℝ j g (P v)‖ ≤ A j * L ^ (j-Rstar) :=
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun y hy ↦ (hg.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
        (show (j : ℕ∞ω) ≤ ∞ by simp)) hv le_rfl).trans (hp j)
  have hinner j (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ j F v‖ ≤ J j * L ^ (j + 1 - Rstar) := by
    have hqj : ‖iteratedFDeriv ℝ j (Q ∘ P) v‖ ≤ D j * L ^ (j + 1 - Rstar) := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hΩ hQ (hball hv) j).trans
      have hh : ‖iteratedFDeriv ℝ j Q (P v)‖ ≤ A j * L ^ (j + 1 - Rstar) :=
        (hbound (W := Coeff) Q hQ hQp j).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (by omega)) (hA j))
      exact (mul_le_mul_of_nonneg_right hh
        (pow_nonneg (norm_nonneg P) j)).trans_eq (by dsimp [D]; ring)
    have hbj : ‖iteratedFDeriv ℝ j (B ∘ P) v‖ ≤ D j * L ^ (j + 1 - Rstar) := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hΩ hB (hball hv) j).trans
      have hh : ‖iteratedFDeriv ℝ j B (P v)‖ ≤ A j * L ^ (j + 1 - Rstar) :=
        (hbound (W := Mat) B hB hBp j).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (by omega)) (hA j))
      exact (mul_le_mul_of_nonneg_right hh
        (pow_nonneg (norm_nonneg P) j)).trans_eq (by dsimp [D]; ring)
    have hdj : ‖iteratedFDeriv ℝ j ((fderiv ℝ Q) ∘ P) v‖ ≤ H j * L ^ (j + 1 - Rstar) := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hΩ
        (hQ.fderiv_of_isOpen hΩ (m := ∞) (by simp)) (hball hv) j).trans
      rw [norm_iteratedFDeriv_fderiv]
      exact (mul_le_mul_of_nonneg_right (hbound (W := Coeff) Q hQ hQp (j+1))
        (pow_nonneg (norm_nonneg P) j)).trans_eq (by dsimp [H]; ring)
    have htj : ‖iteratedFDeriv ℝ j T v‖ ≤ ‖T‖ * L ^ (j + 1 - Rstar) :=
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
      simp only [J, max_mul_of_nonneg _ _ (pow_nonneg (zero_le_one.trans hL) _)])
  change ‖iteratedFDeriv ℝ k (G ∘ F) v‖ ≤ _
  have hGv : ContDiffAt ℝ ∞ G (F v) := hG _ hmem
  have hcomp := norm_jet_comp_fixed_outer_le
    (hF.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hGv.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) (le_refl k)
    (fun j ↦ cNorm S j G) J (fun _ ↦ cNorm_nonneg _ _ _) hJ hL (Rstar-1)
    (fun j _ ↦ houter j) (fun j hj _ ↦ by
      simpa only [show j - (Rstar-1) = j + 1 - Rstar by omega] using hinner j hj)
  simpa only [C, show k - (Rstar-1) = k + 1 - Rstar by omega] using hcomp

end JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol
