module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Products in the derivative seminorms

The bilinear Leibniz estimate used in `app:lem:elementary-interpolation-jets` of
paper.tex, for the actual `cNorm` (sum of derivative suprema). The constants are
explicit: a continuous bilinear map has bound `2 ^ r * ‖B‖` at order `r`.
The matrix specialization uses Frobenius norms, including for rectangular matrices.

The fields are `C^r` on the ambient space. Compactness bounds the derivative images;
the empty compact set is allowed. These are product bounds, not the interpolation or tame
finite-jet assertions of the same source lemma.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem derivativeSup_nonneg (s : Set D) (f : D → E) (j : ℕ) :
    0 ≤ sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s) := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, rfl⟩
  exact norm_nonneg _

private theorem norm_iteratedFDeriv_le_sup {s : Set D} (hs : IsCompact s)
    {r j : ℕ} {f : D → E} (hf : ContDiff ℝ r f) (hj : j ≤ r)
    {x : D} (hx : x ∈ s) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ sSup ((fun y ↦ ‖iteratedFDeriv ℝ j f y‖) '' s) := by
  apply le_csSup _ (Set.mem_image_of_mem _ hx)
  exact hs.bddAbove_image ((hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm.continuousOn)

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the full bilinear Leibniz
bound, with the derivative orders and binomial coefficients retained. -/
theorem cNorm_bilinear_le_sum (B : E →L[ℝ] F →L[ℝ] G)
    {s : Set D} (hs : IsCompact s) {r : ℕ} {f : D → E} {g : D → F}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    cNorm s r (fun x ↦ B (f x) (g x)) ≤
      ‖B‖ * ∑ j ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * sSup ((fun x ↦ ‖iteratedFDeriv ℝ i f x‖) '' s) *
          sSup ((fun x ↦ ‖iteratedFDeriv ℝ (j - i) g x‖) '' s) := by
  rw [cNorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  apply Real.sSup_le
  · rintro _ ⟨x, hx, rfl⟩
    apply (B.norm_iteratedFDeriv_le_of_bilinear hf hg x (by exact_mod_cast hjr)).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
    apply Finset.sum_le_sum
    intro i hi
    have hir : i ≤ r := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hjr
    have hjir : j - i ≤ r := (Nat.sub_le j i).trans hjr
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_sup hs hf hir hx) (by positivity))
      (norm_iteratedFDeriv_le_sup hs hg hjir hx) (norm_nonneg _)
      (mul_nonneg (by positivity) (derivativeSup_nonneg s f i))
  · exact mul_nonneg (norm_nonneg B) (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (by positivity) (derivativeSup_nonneg s f i))
        (derivativeSup_nonneg s g (j - i)))

private theorem sum_leibniz_le (r : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ j ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * a i * b (j - i)) ≤
      (2 : ℝ) ^ r * (∑ i ∈ Finset.range (r + 1), a i) *
        ∑ i ∈ Finset.range (r + 1), b i := by
  calc
    _ ≤ ∑ j ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (j + 1),
        (2 : ℝ) ^ r * (a i * b (j - i)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i _
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hc : (j.choose i : ℝ) ≤ (2 : ℝ) ^ r := by
        exact_mod_cast (Nat.choose_le_two_pow j i).trans (Nat.pow_le_pow_right (by decide) hjr)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (mul_nonneg (ha i) (hb _))
    _ = (2 : ℝ) ^ r * ∑ j ∈ Finset.range (r + 1),
        ∑ i ∈ Finset.range (r + 1 - j), a j * b i := by
      rw [← Finset.sum_range_diag_flip (r + 1) (fun i j ↦ a i * b j)]
      simp_rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ r * ∑ j ∈ Finset.range (r + 1),
        ∑ i ∈ Finset.range (r + 1), a j * b i := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.sub_le _ _)) (fun i _ _ ↦ mul_nonneg (ha j) (hb i))
    _ = _ := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the bilinear product
estimate in the sum-of-suprema seminorm, with explicit constant `2 ^ r * ‖B‖`. -/
theorem cNorm_bilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    {s : Set D} (hs : IsCompact s) {r : ℕ} {f : D → E} {g : D → F}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    cNorm s r (fun x ↦ B (f x) (g x)) ≤
      (2 : ℝ) ^ r * ‖B‖ * cNorm s r f * cNorm s r g := by
  apply (cNorm_bilinear_le_sum B hs hf hg).trans
  have h := mul_le_mul_of_nonneg_left
    (sum_leibniz_le r
      (fun i ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ i f x‖) '' s))
      (fun i ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ i g x‖) '' s))
      (derivativeSup_nonneg s f) (derivativeSup_nonneg s g)) (norm_nonneg B)
  simpa only [cNorm, mul_assoc, mul_left_comm] using h

/-- Appendix B, `app:lem:elementary-interpolation-jets`: a prescribed operator
norm bound gives a concrete `C^r` product constant. -/
theorem cNorm_bilinear_le_of_opNorm_le (B : E →L[ℝ] F →L[ℝ] G)
    {s : Set D} (hs : IsCompact s) {r : ℕ} {f : D → E} {g : D → F}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) {C : ℝ} (hB : ‖B‖ ≤ C) :
    cNorm s r (fun x ↦ B (f x) (g x)) ≤
      (2 : ℝ) ^ r * C * cNorm s r f * cNorm s r g := by
  apply (cNorm_bilinear_le B hs hf hg).trans
  have hf0 : 0 ≤ cNorm s r f := Finset.sum_nonneg fun i _ ↦ derivativeSup_nonneg s f i
  have hg0 : 0 ≤ cNorm s r g := Finset.sum_nonneg fun i _ ↦ derivativeSup_nonneg s g i
  gcongr

/-- Appendix B, `app:lem:elementary-interpolation-jets`: ordered products in a
normed algebra, with constant `2 ^ r` and no derivative loss. -/
theorem cNorm_mul_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {s : Set D} (hs : IsCompact s) {r : ℕ} {f g : D → A}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    cNorm s r (fun x ↦ f x * g x) ≤ (2 : ℝ) ^ r * cNorm s r f * cNorm s r g := by
  simpa only [mul_one, ContinuousLinearMap.mul_apply'] using
    cNorm_bilinear_le_of_opNorm_le (ContinuousLinearMap.mul ℝ A) hs hf hg
      (ContinuousLinearMap.opNorm_mul_le ℝ A)

/-- Appendix B, `app:lem:elementary-interpolation-jets`: scalar multiplication
of vector-valued fields, with constant `2 ^ r`. -/
theorem cNorm_smul_le {s : Set D} (hs : IsCompact s) {r : ℕ}
    {f : D → ℝ} {g : D → E} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    cNorm s r (fun x ↦ f x • g x) ≤ (2 : ℝ) ^ r * cNorm s r f * cNorm s r g := by
  simpa only [mul_one, ContinuousLinearMap.lsmul_apply] using
    cNorm_bilinear_le_of_opNorm_le (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
      hs hf hg ContinuousLinearMap.opNorm_lsmul_le

/-- Appendix B, `app:lem:elementary-interpolation-jets`: rectangular matrix
multiplication as a continuous bilinear map for the Frobenius norms. -/
def matrixMulBilinear (l m n : Type*) [Fintype l] [Fintype m] [Fintype n] :
    Matrix l m ℝ →L[ℝ] Matrix m n ℝ →L[ℝ] Matrix l n ℝ :=
  (LinearMap.mk₂ ℝ (fun (A : Matrix l m ℝ) (B : Matrix m n ℝ) ↦ A * B)
    Matrix.add_mul Matrix.smul_mul Matrix.mul_add
    (fun c A B ↦ Matrix.mul_smul A c B)).mkContinuous₂ 1
    (fun A B ↦ by simpa only [LinearMap.mk₂_apply, one_mul] using Matrix.frobenius_norm_mul A B)

-- Unfold the matrix topology wrappers when synthesizing the operator norm instance.
set_option backward.isDefEq.respectTransparency false in
/-- Appendix B, `app:lem:elementary-interpolation-jets`: the Frobenius bilinear
multiplication map has operator norm at most one, independently of dimensions. -/
theorem norm_matrixMulBilinear_le (l m n : Type*) [Fintype l] [Fintype m] [Fintype n] :
    ‖matrixMulBilinear l m n‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Appendix B, `app:lem:elementary-interpolation-jets`: ordered rectangular
matrix products in Frobenius `C^r` seminorms, with constant `2 ^ r`. -/
theorem cNorm_matrix_mul_le {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    {s : Set D} (hs : IsCompact s) {r : ℕ}
    {f : D → Matrix l m ℝ} {g : D → Matrix m n ℝ}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    cNorm s r (fun x ↦ f x * g x) ≤ (2 : ℝ) ^ r * cNorm s r f * cNorm s r g := by
  simpa only [matrixMulBilinear, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply, mul_one] using
    cNorm_bilinear_le_of_opNorm_le (matrixMulBilinear l m n) hs hf hg
      (norm_matrixMulBilinear_le l m n)

end JanetCartan
