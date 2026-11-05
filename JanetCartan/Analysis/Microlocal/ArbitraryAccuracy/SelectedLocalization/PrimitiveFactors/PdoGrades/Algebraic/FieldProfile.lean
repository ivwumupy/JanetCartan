module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.ConicInverse

/-!
# Joint inverse grades from the original coefficient profile

This substitutes the original field into the compact joint inverse. The
Faà di Bruno products have total derivative order `k`, so their slow-scale
cost is `L^k`. The reserve is zero at this inverse step; differentiating the
whole source-inverse product in the complete residual is a further step.
Consumer: the branch-three joint grade in `CompleteFactor`, with source
`app:ch_regular:eq:initial-coefficient-profile` and `high-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers CompositionBounds
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat

private theorem norm_iteratedFDeriv_linear_pos
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (p : V) {k : ℕ} (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k T p‖ ≤ ‖T‖ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ T = fun _ ↦ T := funext fun _ ↦ T.fderiv
  rw [he]
  by_cases hj : j = 0
  · subst j
    simp only [norm_iteratedFDeriv_zero, le_refl]
  · simp [iteratedFDeriv_const_of_ne hj]

/-- Original coefficient profiles give joint physical/normalized-covariable
grades for the literal `conicBminus` on a fixed retained compact carrier.
The constants precede `Rstar,Q,L,ρ`; the inverse step uses zero reserve.
`hH` is supplied by the selected `RootBuffer`, and `hdomain` by its normalized
spectral/complement certificate. They are geometric inputs, not symbol-jet
assumptions. The derivative is of `v ↦ b(v.1,ρ • v.2)`, so normalized
covariable derivatives are included and order minus one is preserved.
This is the inverse prerequisite for
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-amplitude`). -/
theorem exists_conicBminus_fieldRoot_joint_profile
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ)
    {S : Set (Coeff × E)} (hS : IsCompact S)
    (hpos : ∀ p ∈ S, ℓ (spatialPart p.2) ≠ 0)
    (hH : ∀ p ∈ S, ContDiffAt ℝ ∞ H
      (p.1, spatialPart (normalizeCovector ℓ p.2)))
    (hdomain : ∀ p ∈ S,
      ((coefficientRootPencil (coordinateSplit i) H
          (p.1, spatialPart (normalizeCovector ℓ p.2)),
        pencil p.1 ((coordinateSplit i).symm (1, 0))),
          normalizeCovector ℓ p.2 0 - H (p.1, spatialPart (normalizeCovector ℓ p.2))) ∈
        minorComplementDomain r c)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (Rstar : ℕ) (L ρ : ℝ), 1 ≤ L → 0 < ρ →
      ∀ (x : E) (RQ : ℝ) (Ω : Set E), IsOpen Ω → closedBall x RQ ⊆ Ω →
      ∀ Q : E → Coeff, ContDiffOn ℝ ∞ Q Ω →
      (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
      ∀ p : E × E, physicalCoordinates i p.1 ∈ closedBall x RQ →
        (Q (physicalCoordinates i p.1), p.2) ∈ S → ∀ k,
        ‖iteratedFDeriv ℝ k (fun v : E × E ↦
          conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c v.1 (ρ • v.2)) p‖ ≤
            ρ⁻¹ * C k * L ^ k := by
  classical
  obtain ⟨D, hD, hs, hb⟩ := exists_coefficientConicBminus_joint_bounds
    ℓ i r c H hS hpos hH hdomain
  let P : E × E →L[ℝ] E := (physicalCoordinates i).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ E E)
  let T := ContinuousLinearMap.snd ℝ E E
  let J : ℕ → ℝ := fun k ↦ A k * ‖P‖ ^ k + ‖T‖
  have hJ k : 0 ≤ J k := add_nonneg (mul_nonneg (hA k) (pow_nonneg (norm_nonneg P) k))
    (norm_nonneg T)
  let C : ℕ → ℝ := fun k ↦ ∑ part : OrderedFinpartition k,
    D part.length * ∏ j, J (part.partSize j)
  have hC k : 0 ≤ C k := Finset.sum_nonneg fun part _ ↦
    mul_nonneg (hD _).le (Finset.prod_nonneg fun j _ ↦ hJ _)
  refine ⟨C, hC, ?_⟩
  intro Rstar L ρ hL hρ x RQ Ω hΩ hball Q hQ hprofile p hp hmem k
  let F : E × E → Coeff × E := fun v ↦ (Q (P v), v.2)
  let G := coefficientConicBminus ℓ i r c H
  have hQp : ContDiffAt ℝ ∞ Q (P p) := hQ.contDiffAt (hΩ.mem_nhds (hball hp))
  have hF : ContDiffAt ℝ ∞ F p := (hQp.comp p P.contDiff.contDiffAt).prodMk contDiffAt_snd
  have hG : ContDiffAt ℝ ∞ G (F p) := hs _ hmem
  have houter j : ‖iteratedFDeriv ℝ j G (F p)‖ ≤ D j := by
    simpa only [one_smul, inv_one, one_mul] using hb 1 zero_lt_one j (F p) hmem
  have hinner j (hj : 1 ≤ j) : ‖iteratedFDeriv ℝ j F p‖ ≤ J j * L ^ j := by
    have hq : ‖iteratedFDeriv ℝ j (Q ∘ P) p‖ ≤ (A j * ‖P‖ ^ j) * L ^ j := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hΩ hQ
        (hball hp) j).trans
      have hv : ‖iteratedFDeriv ℝ j Q (P p)‖ ≤ A j * L ^ j :=
        ((norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
          (fun y hy ↦ (hQ.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
            (show (j : ℕ∞ω) ≤ ∞ by simp)) hp le_rfl).trans (hprofile j)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.sub_le j Rstar)) (hA j))
      exact (mul_le_mul_of_nonneg_right hv (pow_nonneg (norm_nonneg P) j)).trans_eq (by ring)
    have ht : ‖iteratedFDeriv ℝ j T p‖ ≤ ‖T‖ * L ^ j :=
      (norm_iteratedFDeriv_linear_pos T p hj).trans
        (le_mul_of_one_le_right (norm_nonneg T) (one_le_pow₀ hL))
    change ‖iteratedFDeriv ℝ j (fun v ↦ ((Q ∘ P) v, T v)) p‖ ≤ _
    rw [iteratedFDeriv_prodMk (hQp.comp p P.contDiff.contDiffAt) T.contDiff.contDiffAt (by simp),
      ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact hq.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (norm_nonneg T)) (pow_nonneg (zero_le_one.trans hL) j))
    · exact ht.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (mul_nonneg (hA j) (pow_nonneg (norm_nonneg P) j)))
        (pow_nonneg (zero_le_one.trans hL) j))
  have hcomp : ‖iteratedFDeriv ℝ k (G ∘ F) p‖ ≤ C k * L ^ k := by
    apply (norm_iteratedFDeriv_comp_le_partition_sum (hG.of_le (by simp))
      (hF.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) le_rfl).trans
    dsimp only [C]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro part _
    calc
      _ ≤ D part.length * ∏ j, J (part.partSize j) * L ^ part.partSize j :=
        mul_le_mul (houter _) (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          (fun j _ ↦ hinner _ (part.partSize_pos j)))
          (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (hD _).le
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_partSize, mul_assoc]
  have he : (fun v : E × E ↦
      conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c v.1 (ρ • v.2)) =
        ρ⁻¹ • (G ∘ F) := by
    funext v
    exact coefficientConicBminus_smul ℓ i r c H hρ.ne' (Q (P v)) v.2
  rw [he, iteratedFDeriv_const_smul_apply
    ((hG.comp p hF).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  exact (mul_le_mul_of_nonneg_left hcomp (inv_pos.mpr hρ).le).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
