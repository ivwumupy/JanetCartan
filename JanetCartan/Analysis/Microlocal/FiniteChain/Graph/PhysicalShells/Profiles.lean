module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Regimes

/-!
# Instantiating the comparable cutoff profiles

These bounds are on the literal complex-valued factors of the normalized
joint amplitude. They follow from the fixed bump, the actual dyadic radii,
and the exhaustive comparable regime. In particular they are independent
of both shell indices and of the requested accuracy
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open Noncomparable KernelEstimates.NoncomparableGeometry
variable {n : ℕ}

/-- A fixed derivative profile shared by the graph branches and the output
family on comparable pairs (`app:ch_regular:eq:chain-tail`). -/
def comparableCutoffProfile (n : ℕ) (H : ℝ) (m : ℕ) : ℝ :=
  (2 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m * (2 * H) ^ m

/-- Nonnegativity for the actual cutoff profile
(`app:ch_regular:eq:chain-tail`). -/
theorem comparableCutoffProfile_nonneg {H : ℝ} (hH : 0 ≤ H) (m : ℕ) :
    0 ≤ comparableCutoffProfile n H m := by
  unfold comparableCutoffProfile
  exact mul_nonneg (mul_nonneg (by positivity) (frequencyBumpDerivativeBound_nonneg n m))
    (pow_nonneg (by positivity) _)

/-- The two graph branches have a common normalized derivative profile
whenever their inverse relative radius is bounded
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_rescaled_graphBranchCutoff_le
    {ρ H : ℝ} (hρ : 0 < ρ) (hH : 0 ≤ H) (low : Bool) (j m : ℕ)
    (hscale : ρ / branchRadius low j ≤ H) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (fun η => graphBranchCutoff low j (ρ • η)) ξ‖ ≤
      comparableCutoffProfile n H m := by
  have hB := frequencyBumpDerivativeBound_nonneg n m
  have hpow := pow_le_pow_left₀ (div_nonneg hρ.le (branchRadius_pos low j).le)
    (hscale.trans (by linarith : H ≤ 2 * H)) m
  cases low
  · have hh := norm_iteratedFDeriv_rescaled_highGraphCutoff_le j m ρ ξ
    simp only [branchRadius, Bool.false_eq_true, ↓reduceIte, div_eq_mul_inv,
      mul_pow] at hpow
    apply hh.trans
    rw [abs_of_pos hρ]
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * frequencyBumpDerivativeBound n m
      from mul_nonneg (by norm_num) hB)
    have hc := mul_le_mul_of_nonneg_right
      (show 2 * frequencyBumpDerivativeBound n m ≤
        (2 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m])
      (pow_nonneg (by positivity : 0 ≤ 2 * H) m)
    simp only [mul_pow] at hc ⊢
    dsimp [comparableCutoffProfile]
    rw [mul_pow]
    nlinarith [hp.trans hc]
  · have hh := norm_iteratedFDeriv_rescaled_lowGraphCutoff_le j m ρ ξ
    simp only [branchRadius, ↓reduceIte, div_eq_mul_inv, inv_inv, mul_pow] at hpow
    apply hh.trans
    rw [abs_of_pos hρ]
    have hp := mul_le_mul_of_nonneg_left hpow (show
      0 ≤ (1 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m by positivity)
    have hc := mul_le_mul_of_nonneg_right
      (show (1 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m ≤
        (2 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m by nlinarith)
      (pow_nonneg (by positivity : 0 ≤ 2 * H) m)
    simp only [mul_pow] at hc ⊢
    dsimp [comparableCutoffProfile]
    rw [mul_pow]
    nlinarith [hp.trans hc]

/-- Output derivatives use the same profile, including the bounded-frequency
cutoff at index zero (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_rescaled_outputCutoff_le_profile
    {ρ H : ℝ} (hρ : 0 < ρ) (hH : 0 ≤ H) (k m : ℕ)
    (hscale : ρ / (2 : ℝ) ^ k ≤ H) (ζ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (fun η => outputCutoff k (ρ • η)) ζ‖ ≤
      comparableCutoffProfile n H m := by
  have hB := frequencyBumpDerivativeBound_nonneg n m
  have hs : ρ * ((2 : ℝ) ^ (k - 1))⁻¹ ≤ 2 * H := by
    cases k with
    | zero => simp only [pow_zero, div_one] at hscale; simpa using (show ρ ≤ 2 * H by linarith)
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ, div_eq_mul_inv, mul_inv_rev] at hscale
      norm_num at hscale
      nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ρ * ((2 : ℝ) ^ (k - 1))⁻¹) hs m
  rw [mul_pow] at hp
  have hh := norm_iteratedFDeriv_rescaled_outputCutoff_le k m ρ ζ
  apply hh.trans
  rw [abs_of_pos hρ]
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
  have hc := mul_le_mul_of_nonneg_right
    (show 2 * frequencyBumpDerivativeBound n m ≤
      (2 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m])
    (pow_nonneg (by positivity : 0 ≤ 2 * H) m)
  dsimp [comparableCutoffProfile]
  nlinarith [hm.trans hc]

private theorem norm_iteratedFDeriv_complex_projection_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (π : E →L[ℝ] Euclidean n) (hπ : ‖π‖ ≤ 1)
    (f : Euclidean n → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) (p : E) :
    ‖iteratedFDeriv ℝ m (fun x => (f (π x) : ℂ)) p‖ ≤
      ‖iteratedFDeriv ℝ m f (π p)‖ := by
  change ‖iteratedFDeriv ℝ m (Complex.ofRealLI ∘ (f ∘ π)) p‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hf.comp π.contDiff).contDiffAt
    (by simp), π.iteratedFDeriv_comp_right hf p (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg π) hπ) (norm_nonneg _)).trans_eq
    (mul_one _)

/-- Comparable geometry supplies the uniform inverse-relative-radius bound
for both independent cutoffs (`app:ch_regular:eq:chain-tail`). -/
theorem comparablePair_inverse_radius_bounds {c C a b ρ : ℝ} (ha : 0 < a)
    (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (h : IsComparablePair c C a b ρ low j k) :
    ρ / branchRadius low j ≤ (8 * annulusFactor c C) / a ∧
      ρ / (2 : ℝ) ^ k ≤ (8 * annulusFactor c C) / a := by
  have hF : 0 < 8 * annulusFactor c C := by
    have := two_le_annulusFactor c C
    positivity
  have hb := comparablePair_radius_bounds hρ h
  have hg := (div_le_iff₀ hF).mp (by simpa only [div_mul_eq_mul_div] using hb.1)
  have ho := (div_le_iff₀ hF).mp (by simpa only [div_mul_eq_mul_div] using hb.2.2.1)
  constructor
  · apply (div_le_div_iff₀ (branchRadius_pos low j) ha).mpr
    nlinarith
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k) ha).mpr
    nlinarith

/-- The literal complex graph-cutoff factor in the joint amplitude has a
fixed profile on every comparable pair. No factor-derivative premise remains
for this cutoff (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_joint_graphCutoff_le {c C a b ρ : ℝ}
    (ha : 0 < a) (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (h : IsComparablePair c C a b ρ low j k) (m : ℕ)
    (p : JointVariables (Euclidean n)) :
    ‖iteratedFDeriv ℝ m (fun p : JointVariables (Euclidean n) =>
      (graphBranchCutoff low j (ρ • p.2.1) : ℂ)) p‖ ≤
        comparableCutoffProfile n ((8 * annulusFactor c C) / a) m := by
  let π : JointVariables (Euclidean n) →L[ℝ] Euclidean n :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  have hπ : ‖π‖ ≤ 1 := π.opNorm_le_bound zero_le_one (by
    intro p
    change ‖p.2.1‖ ≤ 1 * ‖p‖
    simpa only [one_mul] using (norm_fst_le p.2).trans (norm_snd_le p))
  have hh := norm_iteratedFDeriv_complex_projection_le π hπ
    (fun ξ => graphBranchCutoff low j (ρ • ξ))
    ((contDiff_graphBranchCutoff low j).comp (contDiff_id.const_smul ρ)) m p
  apply hh.trans
  apply norm_iteratedFDeriv_rescaled_graphBranchCutoff_le (zero_lt_one.trans_le hρ)
    (by have := two_le_annulusFactor c C; positivity)
  exact (comparablePair_inverse_radius_bounds ha hρ h).1

/-- The literal complex output-cutoff factor has the same fixed profile,
also for index zero (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_joint_outputCutoff_le {c C a b ρ : ℝ}
    (ha : 0 < a) (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (h : IsComparablePair c C a b ρ low j k) (m : ℕ)
    (p : JointVariables (Euclidean n)) :
    ‖iteratedFDeriv ℝ m (fun p : JointVariables (Euclidean n) =>
      (outputCutoff k (ρ • p.2.2.2) : ℂ)) p‖ ≤
        comparableCutoffProfile n ((8 * annulusFactor c C) / a) m := by
  let π : JointVariables (Euclidean n) →L[ℝ] Euclidean n :=
    (ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  have hπ : ‖π‖ ≤ 1 := π.opNorm_le_bound zero_le_one (by
    intro p
    change ‖p.2.2.2‖ ≤ 1 * ‖p‖
    simpa only [one_mul] using ((norm_snd_le p.2.2).trans (norm_snd_le p.2)).trans
      (norm_snd_le p))
  have hh := norm_iteratedFDeriv_complex_projection_le π hπ
    (fun ζ => outputCutoff k (ρ • ζ))
    ((contDiff_outputCutoff k).comp (contDiff_id.const_smul ρ)) m p
  apply hh.trans
  apply norm_iteratedFDeriv_rescaled_outputCutoff_le_profile (zero_lt_one.trans_le hρ)
    (by have := two_le_annulusFactor c C; positivity)
  exact (comparablePair_inverse_radius_bounds ha hρ h).2

end JanetCartan.FiniteChain.Graph.PhysicalShells
