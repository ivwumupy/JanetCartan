module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.Concentration

/-!
# Concentration using row bounds on the patch support

For `app:ch_waves:thm:sampling`, zero patch weights erase the corresponding
normal operators. The sharp row bound is therefore needed only where the
original patch weight is nonzero. This supplies the concentration step for
`exists_threshold_refinedKernelPrefix_realization_of_support`.

An auxiliary continuous radial clipping lets us reuse the whole-output
Bernstein theorem, including its zero-variance case. The weighted sample and
mean operators are proved equal before applying that theorem. Neither the
weights nor the shift law is changed.
-/

@[expose] public noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling
open SeparatedSampling Realization

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Rows agreeing wherever the original patch weight is nonzero have exactly
the same sampled normal (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem patchSampleNormal_congr_on_support {p : ℕ} (B : ℝ)
    (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T S : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (heq : ∀ c z, ψ z ≠ 0 → T c z = S c z) (U : Lattice → Point) :
    patchSampleNormal p B ψ w h T U = patchSampleNormal p B ψ w h S U := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases hz : ψ (node h U a) = 0
  · simp [weight, hz]
  · rw [heq _ _ hz]

/-- Rows agreeing wherever the original patch weight is nonzero have exactly
the same continuum normal (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem patchMeanNormal_congr_on_support {p : ℕ} (B : ℝ)
    (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T S : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (heq : ∀ c z, ψ z ≠ 0 → T c z = S c z) :
    patchMeanNormal p B ψ w h T = patchMeanNormal p B ψ w h S := by
  apply Finset.sum_congr rfl
  intro q _
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : ψ z = 0
  · simp [hz]
  · rw [heq _ _ hz]

/-- The literal weighted block bound only uses the row bound on the original
patch support (`app:ch_waves:eq:sampling-operator-bounds`). Zero row bounds and
zero patch weights are allowed. -/
theorem norm_atomicBlock_le_of_support {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h M : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (hM : 0 ≤ M)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c z, ψ z ≠ 0 → ‖T c z‖ ^ 2 ≤ M) (q : Lattice) (u : Point) :
    ‖atomicBlock p ψ w h T q u‖ ≤
      (nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) * M := by
  have hP := (hψ.nonneg 0).trans (hψ.le_bound 0)
  have hW := (hw.nonneg 0).trans (hw.le_bound 0)
  calc
    _ ≤ ∑ m ∈ integerCube (p + 2), ‖weight ψ w h (fun _ ↦ u) (q, m) •
        atomNormal (T (color p q) (node h (fun _ ↦ u) (q, m)))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ integerCube (p + 2), (h ^ 3 * (P * W ^ 3)) * M := by
      apply Finset.sum_le_sum
      intro m _
      by_cases hz : ψ (node h (fun _ ↦ u) (q, m)) = 0
      · simp only [weight, hz, mul_zero, zero_mul, zero_smul, norm_zero]
        positivity
      · rw [norm_smul, Real.norm_of_nonneg (weight_nonneg hw hψ hh _), norm_atomNormal]
        exact mul_le_mul (weight_le hw hψ hh _) (hT _ _ hz) (sq_nonneg _) (by positivity)
    _ = _ := by simp [card_integerCube, nodesPerBlock, mul_assoc]

private def clippedRow (M : ℝ) (T : E →L[ℂ] H) : E →L[ℂ] H :=
  if M = 0 then 0 else (Real.sqrt M / max (Real.sqrt M) ‖T‖) • T

omit [CompleteSpace E] [CompleteSpace H] in
private theorem clippedRow_eq {M : ℝ} (T : E →L[ℂ] H) (hT : ‖T‖ ^ 2 ≤ M) :
    clippedRow M T = T := by
  by_cases hM : M = 0
  · have hzero : T = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg T])
    simp [clippedRow, hM, hzero]
  · have hMpos : 0 < M := lt_of_le_of_ne ((sq_nonneg _).trans hT) (Ne.symm hM)
    have hnorm : ‖T‖ ≤ Real.sqrt M := (Real.le_sqrt (norm_nonneg _) hMpos.le).mpr hT
    simp [clippedRow, hM, max_eq_left hnorm, (Real.sqrt_pos.mpr hMpos).ne']

omit [CompleteSpace E] [CompleteSpace H] in
private theorem norm_clippedRow_sq_le {M : ℝ} (hM : 0 ≤ M) (T : E →L[ℂ] H) :
    ‖clippedRow M T‖ ^ 2 ≤ M := by
  by_cases hzero : M = 0
  · simp [clippedRow, hzero]
  have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hpos
  have hmax : 0 < max (Real.sqrt M) ‖T‖ := hsqrt.trans_le (le_max_left _ _)
  have hn : ‖clippedRow M T‖ ≤ Real.sqrt M := by
    rw [clippedRow, ite_eq_right hzero, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.sqrt M / max (Real.sqrt M) ‖T‖) * max (Real.sqrt M) ‖T‖ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ = _ := div_mul_cancel₀ _ hmax.ne'
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hM)

omit [CompleteSpace E] [CompleteSpace H] in
private theorem continuous_clippedRow {M : ℝ} (hM : 0 ≤ M) :
    Continuous (clippedRow (E := E) (H := H) M) := by
  change Continuous (fun T : E →L[ℂ] H ↦ clippedRow M T)
  by_cases hzero : M = 0
  · simpa [clippedRow, hzero] using (continuous_const : Continuous fun _ : E →L[ℂ] H ↦
      (0 : E →L[ℂ] H))
  have hpos : 0 < Real.sqrt M := Real.sqrt_pos.mpr (lt_of_le_of_ne hM (Ne.symm hzero))
  simp only [clippedRow, ite_eq_right hzero]
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun T ↦ (hpos.trans_le (le_max_left _ ‖T‖)).ne')).smul continuous_id

omit [CompleteSpace E] [CompleteSpace H] in
private theorem isCompactOperator_clippedRow (M : ℝ) (T : E →L[ℂ] H)
    (hT : IsCompactOperator T) : IsCompactOperator (clippedRow M T) := by
  by_cases hzero : M = 0
  · simpa [clippedRow, hzero] using hT.smul (0 : ℝ)
  · simpa [clippedRow, hzero] using hT.smul (Real.sqrt M / max (Real.sqrt M) ‖T‖)

/-- Whole-output Bernstein with the sharp bound required only on the original
patch support (`app:ch_waves:eq:sampling-all-prefixes`). The auxiliary clipped
rows have exactly the original sampled and mean normals. This reuses the
independent atomic-block proof and its treatment of zero actual variance. -/
theorem operatorBernstein_familyDeviation_of_support
    {A : Type*} [Fintype A] [SeparableSpace H]
    {p : ℕ} {B W h M R C D t : ℝ} {P : A → ℝ}
    {ψ : A → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w) (hh : 0 < h)
    (T : A → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hTc : ∀ a c, Continuous (T a c)) (hcompact : ∀ a c z, IsCompactOperator (T a c z))
    (hM : 0 ≤ M) (hT : ∀ a c z, ψ a z ≠ 0 → ‖T a c z‖ ^ 2 ≤ M)
    (hblock : ∀ a, (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * W ^ 3)) * M ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h (T a)‖ ≤ C)
    (htrace : ∀ (m : ℕ) (e : Fin m → H), Orthonormal ℂ e →
      ∑ k, Complex.re ⟪e k, (∑ a, patchMeanNormal p B (ψ a) w h (T a)) (e k)⟫_ℂ ≤ D)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2) :
    familyShiftLaw A p B h {ω | t < ‖familyDeviation p B ψ w h T ω‖} ≤
      OperatorCompression.bernsteinTail R (R * C) (R * D) t := by
  let S a c z := clippedRow M (T a c z)
  have heq a c z (hz : ψ a z ≠ 0) : S a c z = T a c z :=
    clippedRow_eq _ (hT a c z hz)
  have hsample a U : patchSampleNormal p B (ψ a) w h (S a) U =
      patchSampleNormal p B (ψ a) w h (T a) U :=
    patchSampleNormal_congr_on_support B (ψ a) w h (S a) (T a) (heq a) U
  have hmean_eq a : patchMeanNormal p B (ψ a) w h (S a) =
      patchMeanNormal p B (ψ a) w h (T a) :=
    patchMeanNormal_congr_on_support B (ψ a) w h (S a) (T a) (heq a)
  have hdev : familyDeviation p B ψ w h S = familyDeviation p B ψ w h T := by
    funext ω
    simp only [familyDeviation, hsample, hmean_eq]
  have hb := operatorBernstein_familyDeviation hw hψ hψc hwc hh S
    (fun a c ↦ (continuous_clippedRow hM).comp (hTc a c))
    (fun a c z ↦ isCompactOperator_clippedRow M _ (hcompact a c z))
    (fun a c z ↦ norm_clippedRow_sq_le hM (T a c z)) hblock hR hC
    (by simpa only [hmean_eq] using hmean)
    (by simpa only [hmean_eq] using htrace) ht hthreshold
  simpa only [hdev] using hb

end JanetCartan.Sampling
