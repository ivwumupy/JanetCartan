module

public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot
public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Finite-jet stability of positive amplitudes

The square-root step of `app:ch_mean_pairs:eq:mean-density-lipschitz`.
The domain may include both carrier and initial variables. Constants depend on
only the fixed order and bounded class, with no carrier frequency or mesh.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.DensityDiscrepancy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private def sqrtDividedDifference (z : ℝ × ℝ) : ℝ :=
  (Real.sqrt (1 + z.1) + Real.sqrt (1 + z.2))⁻¹

private theorem contDiffAt_sqrtDividedDifference (k : ℕ) {z : ℝ × ℝ}
    (hz₁ : 0 < 1 + z.1) (hz₂ : 0 < 1 + z.2) :
    ContDiffAt ℝ k sqrtDividedDifference z := by
  apply ContDiffAt.inv
    (((contDiffAt_const.add contDiffAt_fst).sqrt hz₁.ne').add
      ((contDiffAt_const.add contDiffAt_snd).sqrt hz₂.ne'))
  exact (add_pos (Real.sqrt_pos.mpr hz₁) (Real.sqrt_pos.mpr hz₂)).ne'

private theorem cNorm_pair_le {s : Set X} (hs : IsCompact s) (k : ℕ)
    {v w : X → ℝ} (hv : ContDiff ℝ k v) (hw : ContDiff ℝ k w) :
    cNorm s k (fun x ↦ (v x, w x)) ≤ cNorm s k v + cNorm s k w := by
  simp only [cNorm, ← Finset.sum_add_distrib]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ add_nonneg (sSup_norm_iteratedFDeriv_nonneg s j v)
      (sSup_norm_iteratedFDeriv_nonneg s j w))
  intro j hj x hx
  rw [iteratedFDeriv_prodMk hv.contDiffAt hw.contDiffAt (by exact_mod_cast hj),
    ContinuousMultilinearMap.opNorm_prod]
  have hv' := le_csSup (bddAbove_norm_iteratedFDeriv hs hv hj) (Set.mem_image_of_mem _ hx)
  have hw' := le_csSup (bddAbove_norm_iteratedFDeriv hs hw hj) (Set.mem_image_of_mem _ hx)
  exact max_le (by linarith [sSup_norm_iteratedFDeriv_nonneg s j w])
    (by linarith [sSup_norm_iteratedFDeriv_nonneg s j v])

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: uniform finite-jet Lipschitz
stability of `a sqrt(1+v)` on a bounded positive class. Positivity on the ambient
domain ensures smoothness of the displayed functions; the quantitative interval
and jet bounds are required only on `s`. The order is unchanged. -/
theorem exists_positiveAmplitude_cNorm_lipschitz {s : Set X} (hs : IsCompact s)
    (k : ℕ) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a v w : X → ℝ,
      ContDiff ℝ k a → ContDiff ℝ k v → ContDiff ℝ k w →
      cNorm s k a ≤ R → cNorm s k v ≤ M → cNorm s k w ≤ M →
      (∀ x, 0 < 1 + v x) → (∀ x, 0 < 1 + w x) →
      (∀ x ∈ s, 1 + v x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ x ∈ s, 1 + w x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm s k (fun x ↦ positiveDensityAmplitude (a x) (v x) -
        positiveDensityAmplitude (a x) (w x)) ≤ C * cNorm s k (v - w) := by
  let t : Set (ℝ × ℝ) := Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
    Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  have ht : IsCompact t := isCompact_Icc.prod isCompact_Icc
  have hg (z : ℝ × ℝ) (hz : z ∈ t) : ContDiffAt ℝ k sqrtDividedDifference z :=
    contDiffAt_sqrtDividedDifference k (by dsimp [t] at hz; linarith [hz.1.1])
      (by dsimp [t] at hz; linarith [hz.2.1])
  let B := cNorm t k sqrtDividedDifference
  let K := compositionMultiplicity k * B * (1 + 2 * M) ^ k
  have hK : 0 ≤ K := by
    dsimp [K, B, compositionMultiplicity]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
      (cNorm_nonneg _ _ _)) (pow_nonneg (by linarith) _)
  let C := (2 : ℝ) ^ k * R * ((2 : ℝ) ^ k * K)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1 + C, by positivity, ?_⟩
  intro a v w ha hv hw haR hvM hwM hvpos hwpos hvi hwi
  let f : X → ℝ × ℝ := fun x ↦ (v x, w x)
  have hf : ContDiff ℝ k f := hv.prodMk hw
  have hft : Set.MapsTo f s t := by
    intro x hx
    obtain ⟨hv₁, hv₂⟩ := hvi x hx
    obtain ⟨hw₁, hw₂⟩ := hwi x hx
    exact ⟨⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩,
      ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩⟩
  have hcomp : cNorm s k (sqrtDividedDifference ∘ f) ≤ K := by
    apply (cNorm_comp_le_polynomial (fun _ _ ↦ hf.contDiffAt)
      (fun x hx ↦ hg (f x) (hft hx))
      (fun j hj ↦ bddAbove_norm_iteratedFDeriv hs hf hj) (cNorm_nonneg t k sqrtDividedDifference) ?_).trans
    · dsimp [K, B]
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)) (cNorm_nonneg _ _ _))
      apply pow_le_pow_left₀ (by linarith [cNorm_nonneg s k f])
      have hh := cNorm_pair_le hs k hv hw
      dsimp [f] at *
      linarith
    · intro j hj x hx
      exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt ht hg (hft hx) hj
  have hgc : ContDiff ℝ k (sqrtDividedDifference ∘ f) :=
    contDiff_iff_contDiffAt.mpr fun x ↦
      (contDiffAt_sqrtDividedDifference k (hvpos x) (hwpos x)).comp x hf.contDiffAt
  have heq : (fun x ↦ positiveDensityAmplitude (a x) (v x) -
      positiveDensityAmplitude (a x) (w x)) =
      (fun x ↦ a x * ((v x - w x) * (sqrtDividedDifference ∘ f) x)) := by
    funext x
    rw [positiveDensityAmplitude, positiveDensityAmplitude, ← mul_sub,
      sqrt_sub_sqrt_eq_div (hvpos x) (hwpos x)]
    simp [sqrtDividedDifference, f, div_eq_mul_inv]
  rw [heq]
  calc
    _ ≤ (2 : ℝ) ^ k * cNorm s k a *
        cNorm s k (fun x ↦ (v x - w x) * (sqrtDividedDifference ∘ f) x) :=
      cNorm_mul_le hs ha ((hv.sub hw).mul hgc)
    _ ≤ (2 : ℝ) ^ k * R * ((2 : ℝ) ^ k * cNorm s k (v - w) * K) := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left haR (by positivity)) _ (cNorm_nonneg _ _ _) (by positivity)
      exact (cNorm_mul_le hs (hv.sub hw) hgc).trans
        (mul_le_mul_of_nonneg_left hcomp (mul_nonneg (by positivity) (cNorm_nonneg _ _ _)))
    _ = C * cNorm s k (v - w) := by dsimp [C]; ring
    _ ≤ (1 + C) * cNorm s k (v - w) :=
      mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: one constant controls
both the amplitude class and its Lipschitz dependence. This supplies the
bounded factors in the Hermitian polarization, rather than assuming them. -/
theorem exists_positiveAmplitude_cNorm_bounds {s : Set X} (hs : IsCompact s)
    (k : ℕ) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a v w : X → ℝ,
      ContDiff ℝ k a → ContDiff ℝ k v → ContDiff ℝ k w →
      cNorm s k a ≤ R → cNorm s k v ≤ M → cNorm s k w ≤ M →
      (∀ x, 0 < 1 + v x) → (∀ x, 0 < 1 + w x) →
      (∀ x ∈ s, 1 + v x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ x ∈ s, 1 + w x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm s k (fun x ↦ positiveDensityAmplitude (a x) (v x)) ≤ R + C * M ∧
      cNorm s k (fun x ↦ positiveDensityAmplitude (a x) (w x)) ≤ R + C * M ∧
      cNorm s k (fun x ↦ positiveDensityAmplitude (a x) (v x) -
        positiveDensityAmplitude (a x) (w x)) ≤ C * cNorm s k (v - w) := by
  obtain ⟨C, hC, hbound⟩ := exists_positiveAmplitude_cNorm_lipschitz hs k hM hR
  refine ⟨C, hC, ?_⟩
  intro a v w ha hv hw haR hvM hwM hvpos hwpos hvi hwi
  have hsingle (v : X → ℝ) (hv : ContDiff ℝ k v) (hvM : cNorm s k v ≤ M)
      (hvpos : ∀ x, 0 < 1 + v x)
      (hvi : ∀ x ∈ s, 1 + v x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
      cNorm s k (fun x ↦ positiveDensityAmplitude (a x) (v x)) ≤ R + C * M := by
    have hd := hbound a v 0 ha hv contDiff_const haR hvM
      (by simpa using hM) hvpos (by intro x; norm_num) hvi
      (by intro x hx; norm_num)
    simp only [Pi.zero_apply, positiveDensityAmplitude_zero, sub_zero] at hd
    have hamp : ContDiff ℝ k (fun x ↦ positiveDensityAmplitude (a x) (v x)) :=
      ha.mul ((contDiff_const.add hv).sqrt (fun x ↦ (hvpos x).ne'))
    have ht := cNorm_add_le hs (hamp.sub ha) ha
    have heq : (fun x ↦ positiveDensityAmplitude (a x) (v x) - a x) + a =
        (fun x ↦ positiveDensityAmplitude (a x) (v x)) := by ext x; simp
    rw [heq] at ht
    exact ht.trans (by linarith [mul_le_mul_of_nonneg_left hvM hC.le])
  exact ⟨hsingle v hv hvM hvpos hvi, hsingle w hw hwM hwpos hwi,
    hbound a v w ha hv hw haR hvM hwM hvpos hwpos hvi hwi⟩

end JanetCartan.DensityDiscrepancy
