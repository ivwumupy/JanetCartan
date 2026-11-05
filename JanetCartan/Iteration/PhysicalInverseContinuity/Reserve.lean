module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedProfiles
public import JanetCartan.Analysis.Operator.CoerciveInverse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.InputScale

/-!
# Prehistory finite-order budgets for the actual zero-density inverse

At fixed final contraction the initial scalars are fixed. On the original
carrier/image balls the retained coefficient profile is bounded by an ordinary
finite physical jet neighborhood. The current zero-density inverse estimate
has **zero** history exponent at the reserved high grade. This supplies a
uniform `X^(m+1)` budget *before* taking the low-norm tolerance in
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumCommutator ContinuumRow CarrierSobolev

/-- A single original immersion jet bound controls the actual retained
coefficient profile at every smaller order on its two original norm sets.
The unchanged initial scalar contribution is kept exactly. -/
theorem retainedCoefficientProfile_le_of_physical_jet_near
    {n N : ℕ} {ι : Type*} [Fintype ι] {K Kimage Kbig : Set (Euclidean n)}
    (hKbig : IsCompact Kbig) (hK : K ⊆ Kbig) (himage : Kimage ⊆ Kbig)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
    {F G : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {s M : ℕ} (hs : s ≤ M) (hnear : cNorm Kbig M (F - G) ≤ 1) :
    retainedCoefficientProfile K Kimage Kin F initial s ≤
      2 * (1 + cNorm Kbig s G) + ∑ i, cNorm (Kin i) s (initial i) := by
  have hFs : ContDiff ℝ s F := hF.of_le (by simp)
  have hGs : ContDiff ℝ s G := hG.of_le (by simp)
  have hsub : cNorm Kbig s (F - G) ≤ 1 := (cNorm_mono_order hs).trans hnear
  have hb : cNorm Kbig s F ≤ 1 + cNorm Kbig s G := by
    have h := cNorm_add_le hKbig (hFs.sub hGs) hGs
    change cNorm Kbig s ((F - G) + G) ≤ cNorm Kbig s (F - G) + cNorm Kbig s G at h
    rw [sub_add_cancel] at h
    exact h.trans (add_le_add hsub le_rfl)
  have h₁ := (cNorm_mono_set_of_contDiffAt hK hKbig (fun _ _ ↦ hFs.contDiffAt)).trans hb
  have h₂ := (cNorm_mono_set_of_contDiffAt himage hKbig (fun _ _ ↦ hFs.contDiffAt)).trans hb
  unfold retainedCoefficientProfile
  linarith only [h₁, h₂]

/-- The precise current zero-density estimate becomes history-independent at
the preselected reserved grade. In particular this proof never interpolates a
qualitative low-norm neighborhood against a growing high norm. The input
`hcurrent` is the zero branch of `StrongCurrent.source_continuation`; `hseed`
is the actual reference raw level, not a second chosen inverse. -/
theorem raw_sub_gradeNorm_le_of_fixed_reserve
    {n : ℕ} {ι : Type*} [Fintype ι] (A A₀ : AugmentedInput n ι →L[ℝ] OutputL2 n)
    (e e₀ : OutputL2 n) {m rStar Bcan : ℕ} (hreserve : m + 1 + Bcan ≤ rStar)
    {Czero Be T : ℝ} (hCzero : 0 ≤ Czero)
    (he : e ∈ (periodicSobolevScale n (Euclidean n)).level (m + 1))
    (hBe : (periodicSobolevScale n (Euclidean n)).gradeNorm (m + 1) e ≤ Be)
    (hraw : CoerciveInverse.rightInverse A e ∈ (augmentedInputSobolevScale n ι).level (m + 1))
    (hseed : CoerciveInverse.rightInverse A₀ e₀ ∈ (augmentedInputSobolevScale n ι).level (m + 1))
    (hcurrent : (periodicSobolevScale n (Euclidean n)).gradeNorm (m + 1)
        ((CoerciveInverse.normalOperator A).inverse e) +
      (augmentedInputSobolevScale n ι).gradeNorm (m + 1) (CoerciveInverse.rightInverse A e) ≤
      Czero * ((periodicSobolevScale n (Euclidean n)).gradeNorm (m + 1) e +
        T ^ ((m + 1) - (rStar - Bcan)) * ‖e‖)) :
    CoerciveInverse.rightInverse A e - CoerciveInverse.rightInverse A₀ e₀ ∈
        (augmentedInputSobolevScale n ι).level (m + 1) ∧
      (augmentedInputSobolevScale n ι).gradeNorm (m + 1)
          (CoerciveInverse.rightInverse A e - CoerciveInverse.rightInverse A₀ e₀) ≤
        Czero * (Be + Be) + (augmentedInputSobolevScale n ι).gradeNorm (m + 1)
          (CoerciveInverse.rightInverse A₀ e₀) := by
  let S := periodicSobolevScale n (Euclidean n)
  let X := augmentedInputSobolevScale n ι
  have hz : m + 1 - (rStar - Bcan) = 0 := by omega
  rw [hz, pow_zero, one_mul] at hcurrent
  have hb : X.gradeNorm (m + 1) (CoerciveInverse.rightInverse A e) ≤ Czero * (Be + Be) :=
    (le_add_of_nonneg_left (S.gradeNorm_nonneg _ _)).trans (hcurrent.trans
      (mul_le_mul_of_nonneg_left (add_le_add hBe ((S.norm_le_gradeNorm he).trans hBe)) hCzero))
  exact ⟨(X.level _).sub_mem hraw hseed, (X.gradeNorm_sub_le hraw hseed).trans (add_le_add hb le_rfl)⟩

end JanetCartan.PhysicalInverseContinuity
