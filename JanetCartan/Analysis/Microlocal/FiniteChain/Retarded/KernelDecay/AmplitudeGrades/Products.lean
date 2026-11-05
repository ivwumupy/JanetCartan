module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Basic
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Grades
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Product profiles for the concrete retarded amplitude

These estimates supply `norm_iteratedFDeriv_normalizedAmplitude_le_scales` and its
output-derivative variants. The Leibniz convolution retains the fixed offsets
in `app:ch_regular:eq:high-amplitude`, without multiplying them by the
integration order in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace JanetCartan.FiniteChain.Retarded.KernelDecay

/-- Explicit Leibniz constants for the amplitude product
(`app:ch_regular:eq:high-amplitude`). -/
def derivativeConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A j * B (n - j)

/-- Nonnegativity of the constants supplied to the half-space estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem derivativeConvolution_nonneg {A B : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (n : ℕ) :
    0 ≤ derivativeConvolution A B n :=
  Finset.sum_nonneg fun j _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB _)

variable {V W F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual Leibniz estimate: frequency factors multiply, while grade
offsets add once (`app:ch_regular:eq:high-amplitude`). The hypotheses concern
the two factors, never the product. -/
theorem norm_iteratedFDeriv_mul_le_grades {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (_hB : ∀ j, 0 ≤ B j)
    {S T L : ℝ} (hS : 0 ≤ S) (_hT : 0 ≤ T) (hL : 0 ≤ L)
    (a b : ℕ) (x : V)
    (ha : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ S * A j * L ^ (j + a))
    (hb : ∀ j, ‖iteratedFDeriv ℝ j g x‖ ≤ T * B j * L ^ (j + b))
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      (S * T) * derivativeConvolution A B n * L ^ (n + (a + b)) := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (show (n : ℕ∞ω) ≤ ∞ by simp)).trans
  simp only [derivativeConvolution, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (n.choose j : ℝ) * (S * A j * L ^ (j + a)) *
        (T * B (n - j) * L ^ (n - j + b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (ha j) (Nat.cast_nonneg _))
        (hb _) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hS (hA j)) (pow_nonneg hL _)))
    _ = (S * T) * ((n.choose j : ℝ) * A j * B (n - j)) *
        (L ^ (j + a) * L ^ (n - j + b)) := by ring
    _ = _ := by rw [← pow_add]; congr 2; omega

/-- Linear coordinate extraction contributes at most `c^j`; in particular
the shifted weight contributes `2^j` (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_comp_linear_le_grades {f : W → F}
    (hf : ContDiff ℝ ∞ f) (p : V →L[ℝ] W) {c S L : ℝ}
    (_hc : 0 ≤ c) (hp : ‖p‖ ≤ c) {A : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hS : 0 ≤ S) (hL : 0 ≤ L) (b : ℕ)
    (x : V) (n : ℕ)
    (hb : ‖iteratedFDeriv ℝ n f (p x)‖ ≤ S * A n * L ^ (n + b)) :
    ‖iteratedFDeriv ℝ n (f ∘ p) x‖ ≤ S * (A n * c ^ n) * L ^ (n + b) := by
  rw [p.iteratedFDeriv_comp_right hf x (show (n : ℕ∞ω) ≤ ∞ by simp)]
  apply ((iteratedFDeriv ℝ n f (p x)).norm_compContinuousLinearMap_le
    (fun _ => p)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ (S * A n * L ^ (n + b)) * c ^ n :=
      mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hp _)
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg (mul_nonneg hS (hA n)) (pow_nonneg hL _))
    _ = _ := by ring

/-- The identity contribution of the complementary output symbol costs a
constant one at every order, not an extra frequency or grade exponent
(`app:ch_regular:lem:finite-chain`). -/
theorem norm_iteratedFDeriv_one_sub_le_grades {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) {A : ℕ → ℝ}
    {S L : ℝ} (hS : 1 ≤ S) (hL : 1 ≤ L) (b : ℕ) (x : V)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ S * A j * L ^ (j + b)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => 1 - f y) x‖ ≤
      S * (1 + A n) * L ^ (n + b) := by
  have h := HalfSpace.norm_iteratedFDeriv_one_sub_le hf hb n
  change ‖iteratedFDeriv ℝ n (fun y => 1 - f y) x‖ ≤ _ at h
  have h1 : 1 ≤ S * L ^ (n + b) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ S * L ^ (n + b) := mul_le_mul hS (one_le_pow₀ hL) zero_le_one (by linarith)
  have he : S * (1 + A n) * L ^ (n + b) =
      S * L ^ (n + b) + S * A n * L ^ (n + b) := by ring
  rw [he]
  linarith

/-- Freezing the external base contracts every derivative norm. This turns
joint normalized symbol profiles into the slice profiles used by the concrete
amplitude estimate (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_symbol_slice_le {f : V × W → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : V) (ξ : W) :
    ‖iteratedFDeriv ℝ n (fun η => f (x, η)) ξ‖ ≤
      ‖iteratedFDeriv ℝ n f (x, ξ)‖ := by
  let p : W →L[ℝ] V × W := (0 : W →L[ℝ] V).prod (ContinuousLinearMap.id ℝ W)
  let g : V × W → F := fun z => f ((x, 0) + z)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have hp : ‖p‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖((0 : V), y)‖ ≤ 1 * ‖y‖
    simp
  have he : (fun η => f (x, η)) = g ∘ p := by
    funext η
    simp [g, p]
  rw [he, p.iteratedFDeriv_comp_right hg ξ (show (n : ℕ∞ω) ≤ ∞ by simp)]
  apply ((iteratedFDeriv ℝ n g (p ξ)).norm_compContinuousLinearMap_le (fun _ => p)).trans
  have hprod : (∏ _ : Fin n, ‖p‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hp)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (p ξ)‖ := mul_le_of_le_one_right (norm_nonneg _) hprod
    _ = _ := by
      dsimp only [g]
      rw [iteratedFDeriv_comp_add_left]
      simp [p]

/-- The fixed normalized masks of `Localizers/Grades` supply the amplitude's
frequency-slice grades with the same constants, uniformly in the external
base (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_mask_slice_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : CanonicalPhase E → ℝ} (hm : ContDiff ℝ ∞ m)
    {C : ℝ} {n : ℕ} (hC : 0 ≤ C)
    (hb : ∀ p, ‖iteratedFDeriv ℝ n m p‖ ≤ C)
    {L : ℝ} (hL : 1 ≤ L) (x ξ : ℝ × E) :
    ‖iteratedFDeriv ℝ n (fun η => (m (x, η) : ℂ)) ξ‖ ≤ C * L ^ n := by
  have hs : ContDiff ℝ ∞ (fun η => m (x, η)) := hm.comp (contDiff_const.prodMk contDiff_id)
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ (fun η => m (x, η))) ξ‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hs.contDiffAt
    (show (n : ℕ∞ω) ≤ ∞ by simp)]
  exact (norm_iteratedFDeriv_symbol_slice_le hm n x ξ).trans (mask_derivative_grade hC hb hL _)

end JanetCartan.FiniteChain.Retarded.KernelDecay
