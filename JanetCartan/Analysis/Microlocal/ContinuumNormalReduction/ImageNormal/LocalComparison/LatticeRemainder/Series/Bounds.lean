module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.Localization
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Summable bounds for the Bessel lattice jets

For `app:ch_background:prop:bg-frame`, Step 1, these deductions use only
smoothness off the origin and rapid decay of every kernel derivative there.
Their consumer is the termwise differentiation in `LatticeRemainder.Series`.
The heat-integral estimates supplying the two hypotheses remain separate.
-/

@[expose] public noncomputable section
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The literal nonzero-translate summand of the remainder in
`app:ch_background:prop:bg-frame`, Step 1. -/
def imageBesselLatticeTerm (k : Fin d → ℤ) (p : E × E) : ℝ :=
  if k = 0 then 0 else imageBesselKernel (p.1 - p.2 + integerTranslation k)

private def differenceMap : E × E →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E

private theorem norm_jet_comp_difference
    (hK : ContDiffOn ℝ ∞ (imageBesselKernel (d := d)) {x | x ≠ 0})
    (a : E) (p : E × E) (hp : p.1 - p.2 + a ≠ 0) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q : E × E ↦ imageBesselKernel (q.1 - q.2 + a)) p‖ ≤
      ‖iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2 + a)‖ *
        ‖differenceMap (d := d)‖ ^ n := by
  let s : Set E := {z | z + a ≠ 0}
  have hs : IsOpen s := isOpen_ne.preimage (continuous_id.add continuous_const)
  have hf : ContDiffOn ℝ ∞ (fun z : E ↦ imageBesselKernel (z + a)) s :=
    hK.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ h ↦ h)
  let hg := differenceMap (d := d)
  have hmem : hg p ∈ s := hp
  have hpre : IsOpen (hg ⁻¹' s) := hs.preimage hg.continuous
  have he := hg.iteratedFDerivWithin_comp_right hf hs.uniqueDiffOn hpre.uniqueDiffOn
    (x := p) hmem (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hpre hmem,
    iteratedFDerivWithin_of_isOpen n hs hmem, iteratedFDeriv_comp_add_right] at he
  change iteratedFDeriv ℝ n (fun q : E × E ↦ imageBesselKernel (q.1 - q.2 + a)) p = _ at he
  rw [he]
  simpa [hg, differenceMap] using (iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2 + a)).norm_compContinuousLinearMap_le
    (fun _ : Fin n ↦ hg)

/-- Each individual nonzero translate is smooth throughout the comparison
cube (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiffOn_imageBesselLatticeTerm
    (hK : ContDiffOn ℝ ∞ (imageBesselKernel (d := d)) {x | x ≠ 0})
    (k : Fin d → ℤ) : ContDiffOn ℝ ∞ (imageBesselLatticeTerm k)
      (imageBesselComparisonDomain d) := by
  classical
  unfold imageBesselLatticeTerm
  by_cases hk : k = 0
  · simp only [hk, ite_true]
    exact contDiffOn_const
  · simp only [ite_eq_right hk]
    apply hK.comp ((contDiff_fst.sub contDiff_snd).add contDiff_const).contDiffOn
    intro p hp
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    have hone : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    intro hz
    have he : p.1 i - p.2 i + (k i : ℝ) = 0 := congrArg (fun z : E ↦ z i) hz
    have hb := abs_sub (p.2 i) (p.1 i)
    have hid : (k i : ℝ) = p.2 i - p.1 i := by linarith
    rw [← hid] at hb
    have h1 := hp.1 i
    have h2 := hp.2 i
    linarith

/-- A common nonnegative summable majorant for all joint derivatives up to
any finite order on a closed comparison cube. This is the convergence input
for `app:ch_background:prop:bg-frame`, Step 1, with the actual gap `1 - 2r`. -/
theorem exists_summable_imageBesselLatticeTerm_jet_majorant
    (hK : ContDiffOn ℝ ∞ (imageBesselKernel (d := d)) {x | x ≠ 0})
    (hdecay : ∀ δ : ℝ, 0 < δ → ∀ n m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : E, δ ≤ ‖x‖ → (1 + ‖x‖)^m * ‖iteratedFDeriv ℝ n imageBesselKernel x‖ ≤ C)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2) (N : ℕ) :
    ∃ u : (Fin d → ℤ) → ℝ, Summable u ∧ (∀ k, 0 ≤ u k) ∧
      ∀ n ≤ N, ∀ k, ∀ p : E × E,
        (∀ i, |p.1 i| ≤ r) → (∀ i, |p.2 i| ≤ r) →
        ‖iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p‖ ≤ u k := by
  classical
  let S : Set E := (WithLp.toLp 2) '' Set.Icc (fun _ : Fin d ↦ -r) (fun _ ↦ r)
  have hS : IsCompact S := isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ))
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  have hmem (x : E) (hx : ∀ i, |x i| ≤ r) : x ∈ S :=
    ⟨WithLp.ofLp x, ⟨fun i ↦ (abs_le.mp (hx i)).1, fun i ↦ (abs_le.mp (hx i)).2⟩, rfl⟩
  have hR₀ : 0 ≤ R := by simpa using hR 0 (hmem 0 (by simpa using fun _ : Fin d ↦ hr₀))
  let A : ℝ := 1 + 2 * Real.pi + 2 * Real.pi * (2 * R)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  choose C hC₀ hC using hdecay (1 - 2 * r) (by linarith)
  let B (n : ℕ) := A ^ (d + 1) * C n (d + 1) * ‖differenceMap (d := d)‖ ^ n
  have hB (n : ℕ) : 0 ≤ B n := by dsimp [B]; exact mul_nonneg (mul_nonneg (pow_nonneg hA _) (hC₀ _ _)) (pow_nonneg (norm_nonneg _) _)
  let D := ∑ n ∈ Finset.range (N + 1), B n
  have hD : 0 ≤ D := Finset.sum_nonneg (fun n _ ↦ hB n)
  refine ⟨fun k ↦ D * ((1 + frequencyNorm k) ^ (d + 1))⁻¹,
    (summable_one_add_frequencyNorm_inv_pow d).mul_left D, fun k ↦ mul_nonneg hD (inv_nonneg.mpr (pow_nonneg (by linarith [frequencyNorm_nonneg k]) _)), ?_⟩
  intro n hn k p hx hy
  have hwpos : 0 < 1 + frequencyNorm k := by linarith [frequencyNorm_nonneg k]
  by_cases hk : k = 0
  · have he : imageBesselLatticeTerm k = (fun _ : E × E ↦ (0 : ℝ)) := by
      funext q; simp [imageBesselLatticeTerm, hk]
    rw [he]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg hD (inv_nonneg.mpr (pow_nonneg hwpos.le _))
  have hgap := norm_sub_add_integerTranslation_ge hx hy hk
  have hne := sub_add_integerTranslation_ne_zero hr hx hy hk
  have hz : ‖(integerTranslation k : E)‖ ≤ ‖p.1 - p.2 + integerTranslation k‖ + 2 * R := by
    have ht := norm_add_le (p.1 - p.2 + integerTranslation k) (p.2 - p.1)
    rw [show p.1 - p.2 + integerTranslation k + (p.2 - p.1) = integerTranslation k by abel] at ht
    have hd := norm_sub_le p.2 p.1
    linarith [hR p.1 (hmem _ hx), hR p.2 (hmem _ hy)]
  have hw : 1 + frequencyNorm k ≤ A * (1 + ‖p.1 - p.2 + integerTranslation k‖) := by
    change 1 + 2 * Real.pi * ‖(integerTranslation k : E)‖ ≤ _
    have hb := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2 * Real.pi)
    dsimp [A]
    nlinarith [norm_nonneg (p.1 - p.2 + integerTranslation k), Real.pi_pos,
      mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (by positivity : 0 ≤ 2 * R))
        (norm_nonneg (p.1 - p.2 + integerTranslation k))]
  have hweighted : (1 + frequencyNorm k) ^ (d + 1) *
      ‖iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2 + integerTranslation k)‖ ≤
        A ^ (d + 1) * C n (d + 1) := by
    calc
      _ ≤ (A * (1 + ‖p.1 - p.2 + integerTranslation k‖)) ^ (d + 1) *
          ‖iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2 + integerTranslation k)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwpos.le hw _) (norm_nonneg _)
      _ = A ^ (d + 1) * ((1 + ‖p.1 - p.2 + integerTranslation k‖) ^ (d + 1) *
          ‖iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2 + integerTranslation k)‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC n (d + 1) _ hgap) (by positivity)
  have hb : ‖iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p‖ ≤
      B n * ((1 + frequencyNorm k) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have hc := norm_jet_comp_difference hK (integerTranslation k) p hne n
    unfold imageBesselLatticeTerm
    simp only [ite_eq_right hk]
    calc
      _ ≤ (‖iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2 + integerTranslation k)‖ *
          ‖differenceMap (d := d)‖ ^ n) * (1 + frequencyNorm k) ^ (d + 1) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ((1 + frequencyNorm k) ^ (d + 1) *
          ‖iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2 + integerTranslation k)‖) *
          ‖differenceMap (d := d)‖ ^ n := by ring
      _ ≤ B n := mul_le_mul_of_nonneg_right hweighted (by positivity)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ ↦ hB j) (Finset.mem_range.mpr (by omega))) (by positivity))

end JanetCartan.ContinuumNormalReduction.ImageNormal
