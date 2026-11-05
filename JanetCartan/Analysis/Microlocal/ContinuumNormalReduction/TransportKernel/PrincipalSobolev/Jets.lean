module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.Kernel
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Fixed-cutoff jets of the diagonal correction

The bounded-frequency term following `app:ch_background:eq:bg-real-symbol`
has joint physical jets controlled by one high norm. The cutoffs contribute
only their fixed finite seminorm; reversing the literal kernel uses the
exchanged cutoff seminorm and the same primitive jet estimates.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n N : ℕ}

/-- The fixed finite jet factor for localization of the diagonal correction
in `app:ch_background:eq:bg-real-symbol`. Absolute values avoid any auxiliary
sign requirements on the frequency radius. -/
def diagonalCorrectionLocalizedJetConstant (χ β : Euclidean n → ℝ)
    (s : ℕ) (R : ℝ) : ℝ :=
  (2 : ℝ) ^ s * cNorm (tsupport (diagonalCorrectionMask χ β)) s
    (diagonalCorrectionMask χ β) *
      ∑ l ∈ Finset.range (s + 1), |correctionKernelJetConstant n l R|

/-- Nonnegativity of the fixed cutoff factor
(`app:ch_background:eq:bg-real-symbol`). -/
theorem diagonalCorrectionLocalizedJetConstant_nonneg (χ β : Euclidean n → ℝ)
    (s : ℕ) (R : ℝ) : 0 ≤ diagonalCorrectionLocalizedJetConstant χ β s R := by
  unfold diagonalCorrectionLocalizedJetConstant
  exact mul_nonneg (mul_nonneg (by positivity) (cNorm_nonneg _ _ _))
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

private theorem localized_jet_bound
    (χ β : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β)
    (g : Euclidean n × Euclidean n → ℂ) (hg : ContDiff ℝ ∞ g)
    (s : ℕ) (R : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ p ∈ tsupport (diagonalCorrectionMask χ β), ∀ l ≤ s,
      ‖iteratedFDeriv ℝ l g p‖ ≤ correctionKernelJetConstant n l R * A)
    (r : ℕ) (hr : r ≤ s) (p : Euclidean n × Euclidean n) :
    ‖iteratedFDeriv ℝ r (fun q ↦ diagonalCorrectionMask χ β q * g q) p‖ ≤
      diagonalCorrectionLocalizedJetConstant χ β s R * A := by
  let m := diagonalCorrectionMask χ β
  have hm := diagonalCorrectionMask_contDiff hχ hβ
  have hms := diagonalCorrectionMask_hasCompactSupport hχs hβs
  by_cases hp : p ∈ tsupport m
  · let B := cNorm (tsupport m) s m
    let D := ∑ l ∈ Finset.range (s + 1), |correctionKernelJetConstant n l R|
    have hB : 0 ≤ B := cNorm_nonneg _ _ _
    have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hgb (l : ℕ) (hl : l ≤ s) : ‖iteratedFDeriv ℝ l g p‖ ≤ D * A := by
      apply (hb p hp l hl).trans
      apply mul_le_mul_of_nonneg_right _ hA
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun l ↦
        |correctionKernelJetConstant n l R|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl)))
    apply (norm_iteratedFDeriv_mul_le hm hg p (by simp : (r : ℕ∞ω) ≤ ∞)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * B * (D * A) := by
        apply Finset.sum_le_sum
        intro l hl
        have hls : l ≤ s := (Nat.le_of_lt_succ (Finset.mem_range.mp hl)).trans hr
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (JanetCartan.norm_iteratedFDeriv_le_cNorm hms (hm.of_le (by simp)) hp hls)
          (by positivity)) (hgb (r-l) ((Nat.sub_le _ _).trans hr))
          (norm_nonneg _) (mul_nonneg (by positivity) hB)
      _ = (2 : ℝ)^r * B * (D * A) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        simp
      _ ≤ (2 : ℝ)^s * B * (D * A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr) hB) (mul_nonneg hD hA)
      _ = _ := by unfold diagonalCorrectionLocalizedJetConstant; dsimp [B, D, m]; ring
  · have hz : iteratedFDeriv ℝ r (fun q ↦ m q * g q) p = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h ↦ hp (tsupport_mul_subset_left (tsupport_iteratedFDeriv_subset r h))
    rw [hz, norm_zero]
    exact mul_nonneg (diagonalCorrectionLocalizedJetConstant_nonneg χ β s R) hA

variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ β : Euclidean n → ℝ)
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β)

include he hone hC hcomparison hχ hβ hχs hβs

/-- The precise primitive kernel jets imply global localized jets, including
the fixed cutoff derivatives (`app:ch_background:eq:bg-real-symbol`). -/
theorem norm_iteratedFDeriv_localizedDiagonalCorrectionKernel_le
    (s : ℕ) {A : ℝ} (hA : 0 ≤ A) (i j : Fin n)
    (hb : ∀ p ∈ tsupport (diagonalCorrectionMask χ β), ∀ l ≤ s,
      ‖iteratedFDeriv ℝ l (fun q : Euclidean n × Euclidean n ↦
        diagonalCompletionErrorKernel a J u Ω K i j q.1 q.2) p‖ ≤
          correctionKernelJetConstant n l (max 2 (2 * C)) * A)
    (r : ℕ) (hr : r ≤ s) (p : Euclidean n × Euclidean n) :
    ‖iteratedFDeriv ℝ r (Function.uncurry
      (localizedDiagonalCorrectionKernel a J u Ω K χ β i j)) p‖ ≤
        diagonalCorrectionLocalizedJetConstant χ β s (max 2 (2 * C)) * A :=
  localized_jet_bound χ β hχ hβ hχs hβs _
    (diagonalCompletionErrorKernel_contDiff a J u Ω K he hone hC hcomparison i j)
    s _ hA hb r hr p

/-- The literal adjoint has the same finite-order bound with exchanged
fixed cutoffs (`app:ch_background:eq:bg-real-symbol`). -/
theorem norm_iteratedFDeriv_localizedDiagonalCorrectionAdjointKernel_le
    (s : ℕ) {A : ℝ} (hA : 0 ≤ A) (i j : Fin n)
    (hb : ∀ p ∈ tsupport (diagonalCorrectionMask β χ), ∀ l ≤ s,
      ‖iteratedFDeriv ℝ l (fun q : Euclidean n × Euclidean n ↦
        conj (diagonalCompletionErrorKernel a J u Ω K j i q.2 q.1)) p‖ ≤
          correctionKernelJetConstant n l (max 2 (2 * C)) * A)
    (r : ℕ) (hr : r ≤ s) (p : Euclidean n × Euclidean n) :
    ‖iteratedFDeriv ℝ r (Function.uncurry
      (localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j)) p‖ ≤
        diagonalCorrectionLocalizedJetConstant β χ s (max 2 (2 * C)) * A := by
  change ‖iteratedFDeriv ℝ r (fun q : Euclidean n × Euclidean n ↦
    localizedDiagonalCorrectionAdjointKernel a J u Ω K χ β i j q.1 q.2) p‖ ≤ _
  simp_rw [localizedDiagonalCorrectionAdjointKernel_eq]
  exact localized_jet_bound β χ hβ hχ hβs hχs _
    (diagonalCompletionErrorKernel_adjoint_contDiff a J u Ω K he hone hC hcomparison i j)
    s _ hA hb r hr p

end JanetCartan.ContinuumRow.TransportKernel
