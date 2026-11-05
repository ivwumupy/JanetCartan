module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalAmplitude.Recovery
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalAmplitude.Masks

/-!
# Physical joint derivatives from the retained conic seminorm

Recover a high-radius germ and apply the linear chain rule and Leibniz rule.
The only matrix estimates are the original retained seminorms. Consumer:
`CompleteFactor.hauxAmplitudeGrades` (`app:ch_regular:eq:high-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
open RegularSector RegularSector.Characteristic
open ConicAmplitude AmplitudeBounds EvolutionIntegral EvolutionIntegral.SymbolBudgets
open EvolutionIntegral.KernelIdentification FourierIntegral.PrimitiveProfiles
variable {d q : ℕ}
local notation "J" => SymbolBudgets.TwoTimePoint d
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "E" => Euclidean (d+1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The fixed finite Leibniz sum in the physical residual grade. Its inputs
are the actual mask profile and the original retained symbol profile
(`app:ch_regular:eq:high-amplitude`). -/
def transferProfile (H D : ℕ → ℝ) (C : ℝ) (k : ℕ) : ℝ :=
  C * ∑ i ∈ Finset.range (k+1),
    (k.choose i : ℝ) * H i * (D (k-i) * (max 1 C) ^ (k-i))

/-- Nonnegativity of the fixed transfer constant
(`app:ch_regular:eq:high-amplitude`). -/
theorem transferProfile_nonneg {H D : ℕ → ℝ} (hH : ∀ k, 0 ≤ H k)
    (hD : ∀ k, 0 ≤ D k) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ transferProfile H D C k := by
  apply mul_nonneg hC
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH i))
    (mul_nonneg (hD _) (pow_nonneg (le_max_of_le_left zero_le_one) _))

/-- Original negative-order seminorms imply physical joint grades after the
actual output mask. The geometric dilation is supplied by
`physical_covector_dilation_bounds`, and the fixed mask jets are supplied by
`exists_residualMask_profile`. No local amplitude cNorm or new-band seminorm
is an input (`app:ch_regular:eq:high-amplitude`). -/
theorem physical_joint_grade_of_retained_seminorm
    (ℓ : Euclidean d →L[ℝ] ℝ) (angular : Euclidean d → ℝ) (F : T → Mat)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (H D : ℕ → ℝ) (hH : ∀ i, 0 ≤ H i) (hD : ∀ i, 0 ≤ D i)
    (hmask : ∀ i w, ‖iteratedFDeriv ℝ i (residualMask χ) w‖ ≤ H i)
    {K : Set J} (hK : IsCompact K) {L C t : ℝ}
    (hL : 1 ≤ L) (ht : 0 < t) (htC : t ≤ C)
    {w : J} (hw : w.2 ≠ 0) (hweight : t * (1 + ‖w.2‖) ≤ C)
    (hmem : covectorDilation t w ∈ K)
    (hsmooth : ContDiff ℝ ∞
      (jointAmplitude (curryCharacteristicMatrix (collared ℓ 1 angular F))))
    (hbudget : ∀ j, BoundedTwoTimeOrderSeminorm 1 K j
        (curryCharacteristicMatrix (collared ℓ 1 angular F)) ∧
      twoTimeOrderSeminorm 1 K j (curryCharacteristicMatrix (collared ℓ 1 angular F)) ≤
        D j * L ^ j) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun v : J ↦ χ (timeSpacePoint v.1.1 v.1.2.2) •
      jointAmplitude (curryCharacteristicMatrix (collared ℓ 1 angular F)) v) w‖ ≤
        (1 + ‖w.2‖) ^ (-1 : ℝ) * transferProfile H D C k * L ^ k := by
  let b := curryCharacteristicMatrix (collared ℓ 1 angular F)
  obtain ⟨R, hR, hgerm⟩ := exists_collared_recovery_germ ℓ angular F ht hw
  let g := fun v ↦ t • twoTimeOrderField 1 R b (covectorDilation t v)
  have hfield : ContDiff ℝ ∞ (twoTimeOrderField 1 R b) :=
    (hsmooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))).const_smul (R ^ 1)
  have hg : ContDiff ℝ ∞ g := (hfield.comp (covectorDilation t).contDiff).const_smul t
  have he : (fun v : J ↦ χ (timeSpacePoint v.1.1 v.1.2.2) • jointAmplitude b v) =ᶠ[𝓝 w]
      (fun v ↦ residualMask χ v • g v) := by
    filter_upwards [hgerm] with v hv
    dsimp only [b] at *
    rw [hv]
    exact (mul_smul _ _ _).symm
  have hgBound j : ‖iteratedFDeriv ℝ j g w‖ ≤
      t * (D j * (max 1 C) ^ j) * L ^ j := by
    have hchain := norm_iteratedFDeriv_preAffine_le (x := w) (covectorDilation t) 0
      isOpen_univ hfield.contDiffOn (mem_univ _) j
    simp only [add_zero] at hchain
    have hjet := (norm_iteratedFDeriv_le_cNorm hK (hfield.of_le (by simp)) hmem le_rfl).trans
      ((cNorm_twoTimeOrderField_le (hbudget j).1 hR).trans (hbudget j).2)
    have hT := norm_covectorDilation_le (d := d) ht.le (le_max_left 1 C)
      (htC.trans (le_max_right 1 C))
    have hcomp := hchain.trans (mul_le_mul hjet
      (pow_le_pow_left₀ (norm_nonneg _) hT j) (by positivity)
      (mul_nonneg (hD j) (pow_nonneg (zero_le_one.trans hL) _)))
    change ‖iteratedFDeriv ℝ j (t • (twoTimeOrderField 1 R b ∘ covectorDilation t)) w‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (a := t) (i := j) (x := w)
      ((hfield.comp (covectorDilation t).contDiff).contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_of_nonneg ht.le]
    exact (mul_le_mul_of_nonneg_left hcomp ht.le).trans_eq (by ring)
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  have hleib := norm_iteratedFDeriv_smul_le (contDiff_residualMask hχ) hg w (n := k) (by simp)
  apply hleib.trans
  have hsum : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (residualMask χ) w‖ * ‖iteratedFDeriv ℝ (k-i) g w‖) ≤
      t * (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * H i *
        (D (k-i) * (max 1 C) ^ (k-i))) * L ^ k := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hm := mul_le_mul
      (mul_le_mul_of_nonneg_left (hmask i w) (Nat.cast_nonneg (k.choose i))) (hgBound (k-i))
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg (k.choose i)) (hH i))
    apply hm.trans
    calc
      _ = t * ((k.choose i : ℝ) * H i * (D (k-i) * (max 1 C) ^ (k-i))) * L ^ (k-i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.sub_le k i))
        (mul_nonneg ht.le (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH i))
          (mul_nonneg (hD _) (pow_nonneg (le_max_of_le_left zero_le_one) _))))
  apply hsum.trans
  have htweight : t ≤ (1 + ‖w.2‖)⁻¹ * C := by
    apply (le_inv_mul_iff₀ (by positivity : 0 < 1 + ‖w.2‖)).mpr
    simpa only [mul_comm] using hweight
  rw [Real.rpow_neg_one, transferProfile]
  have hsnon : 0 ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * H i *
      (D (k-i) * (max 1 C) ^ (k-i)) := Finset.sum_nonneg (fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH i))
      (mul_nonneg (hD _) (pow_nonneg (le_max_of_le_left zero_le_one) _)))
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htweight hsnon)
    (pow_nonneg (zero_le_one.trans hL) k)).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
