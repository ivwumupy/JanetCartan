module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplierBounds.Far
public import JanetCartan.Analysis.ContDiff.Norm.Composition.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Primitive partition bounds for the far source endpoints

The consumer is the differentiated far complement following
`app:ch_regular_base:eq:fixed-source-multiplication`. The partition sum keeps
each primitive derivative order, so interpolation need not multiply high norms.
The real phase exponential has unit norm at every derivative order.
-/

@[expose] public noncomputable section
open scoped ContDiff

namespace JanetCartan.FourierIntegral.SourceBounds

/-- Exact real derivatives of the physical exponential used in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem iteratedDeriv_physical_exp (k : ℕ) :
    (iteratedDeriv k (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ)))) =
      fun t : ℝ ↦ Complex.I ^ k * Complex.exp (Complex.I * (t : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have ho : HasDerivAt (fun a : ℝ ↦ (a : ℂ)) 1 t := by
      simpa using! Complex.ofRealCLM.hasDerivAt
    have h := (ho.const_mul Complex.I).cexp
    convert (h.const_mul (Complex.I ^ k)).deriv using 1
    ring

/-- No exponential growth is lost in differentiating the real phase in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem norm_iteratedFDeriv_physical_exp (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (fun a : ℝ ↦ Complex.exp (Complex.I * (a : ℂ))) t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_physical_exp]
  simp [norm_pow, Complex.norm_exp]

/-- The phase part of the primitive product budget in the far complement of
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourcePhasePartition (P : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ p : OrderedFinpartition s, ∏ i, P (p.partSize i)

/-- Positivity of the phase partition bound used in the source endpoint estimate. -/
theorem sourcePhasePartition_nonneg {P : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (s : ℕ) :
    0 ≤ sourcePhasePartition P s :=
  Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ hP _

/-- Only positive primitive orders through `s` enter a phase partition. -/
theorem sourcePhasePartition_mono {P Q : ℕ → ℝ} {s : ℕ}
    (hP : ∀ j, 0 ≤ P j) (hPQ : ∀ j, 1 ≤ j → j ≤ s → P j ≤ Q j) :
    sourcePhasePartition P s ≤ sourcePhasePartition Q s := by
  apply Finset.sum_le_sum
  intro p _
  exact Finset.prod_le_prod₀ (fun _ _ ↦ hP _)
    (fun i _ ↦ hPQ _ (p.partSize_pos i) (p.partSize_le i))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F

/-- The actual differentiated exponential is bounded by primitive real phase
jets, for the far complement in `app:ch_regular_base:eq:fixed-source-multiplication`.
This is a chain rule conclusion, not a hypothesis on differentiated endpoints. -/
theorem norm_iteratedFDeriv_exp_phase_le {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ s (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ))) z‖ ≤
      sourcePhasePartition (fun j ↦ ‖iteratedFDeriv ℝ j φ z‖) s := by
  have he : ContDiff ℝ s (fun a : ℝ ↦ Complex.exp (Complex.I * (a : ℂ))) := by
    have ho : ContDiff ℝ s (fun a : ℝ ↦ (a : ℂ)) := Complex.ofRealCLM.contDiff
    fun_prop
  simpa only [Function.comp_def, norm_iteratedFDeriv_physical_exp, one_mul,
    sourcePhasePartition] using
    CompositionBounds.norm_iteratedFDeriv_comp_le_partition_sum he.contDiffAt
      (hφ.of_le (show (s : ℕ∞ω) ≤ ∞ by simp)).contDiffAt (le_refl s)

/-- The complete Leibniz/partition budget for one endpoint in
`app:ch_regular_base:eq:fixed-source-multiplication`. Scalar multiplication
retains the amplitude as a whole, including its matrix order. -/
def sourceEndpointPartition (P A : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (s + 1),
    (s.choose i : ℝ) * sourcePhasePartition P i * A (s - i)

/-- Positivity of the complete endpoint budget. -/
theorem sourceEndpointPartition_nonneg {P A : ℕ → ℝ}
    (hP : ∀ j, 0 ≤ P j) (hA : ∀ j, 0 ≤ A j) (s : ℕ) :
    0 ≤ sourceEndpointPartition P A s := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (sourcePhasePartition_nonneg hP i)) (hA _)

/-- Monotonicity of the endpoint budget uses only the finite primitive reserve. -/
theorem sourceEndpointPartition_mono {P A Q B : ℕ → ℝ} {s : ℕ}
    (hP : ∀ j, 0 ≤ P j) (hA : ∀ j, 0 ≤ A j)
    (hPQ : ∀ j, 1 ≤ j → j ≤ s → P j ≤ Q j)
    (hAB : ∀ j ≤ s, A j ≤ B j) :
    sourceEndpointPartition P A s ≤ sourceEndpointPartition Q B s := by
  apply Finset.sum_le_sum
  intro i hi
  have his : i ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hp := sourcePhasePartition_mono hP (fun j hj hji ↦ hPQ j hj (hji.trans his))
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
    (hAB _ (Nat.sub_le _ _)) (hA _) (mul_nonneg (Nat.cast_nonneg _)
      ((sourcePhasePartition_nonneg hP i).trans hp))

/-- All joint derivatives of one literal oscillatory endpoint are bounded by
their primitive products (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem norm_iteratedFDeriv_exp_smul_le {φ : E → ℝ} {A : E → F}
    (hφ : ContDiff ℝ ∞ φ) (hA : ContDiff ℝ ∞ A) (s : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ s (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) • A y) z‖ ≤
      sourceEndpointPartition (fun j ↦ ‖iteratedFDeriv ℝ j φ z‖)
        (fun j ↦ ‖iteratedFDeriv ℝ j A z‖) s := by
  have he : ContDiff ℝ ∞ (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ))) := by
    have ho : ContDiff ℝ ∞ (fun a : ℝ ↦ (a : ℂ)) := Complex.ofRealCLM.contDiff
    fun_prop
  apply (norm_iteratedFDeriv_smul_le he hA z (show (s : ℕ∞ω) ≤ ∞ by simp)).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_exp_phase_le hφ i z)
      (Nat.cast_nonneg _)) (norm_nonneg _)

/-- Each differentiated linearized phase uses `j+1` derivatives of `S`.
With baseline one for `S`, the complete primitive excess is exactly `s`.
Thus the reserve is `s+1`, independent of Fourier moment order. Source:
`app:ch_regular_base:eq:joint-primitive-product` and the far source complement. -/
theorem sourceEndpointPartition_primitive_budget {s i : ℕ} (hi : i ≤ s)
    (p : OrderedFinpartition i) :
    (s - i) + ∑ a, (p.partSize a + 1 - 1) = s := by
  simp only [Nat.add_sub_cancel, CompositionBounds.sum_partSize]
  exact Nat.sub_add_cancel hi

end JanetCartan.FourierIntegral.SourceBounds
