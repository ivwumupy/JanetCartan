module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Matrices
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# One fixed source cutoff

The cutoff for the source expansion in `app:ch_regular_base:thm:actual-calculus`,
Step 1. It depends only on the original source box and the larger period box,
not on the amplitude, the Fourier mode, or the requested derivative order.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ}

/-- Primitive properties of the single source cutoff used by the source-series
assembly in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
structure SourceCutoff (n : ℕ) (R ℓ : ℝ) where
  toFun : Euclidean n → ℂ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  norm_le_one : ∀ y, ‖toFun y‖ ≤ 1
  cell : ∀ y, toFun y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n
  one : ∀ y, (∀ i, |y i| ≤ R) → toFun y = 1

set_option maxHeartbeats 800000 in
/-- Construct the fixed smooth cutoff, with a strict margin inside the enlarged
period box (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem nonempty_sourceCutoff {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) :
    Nonempty (SourceCutoff n R ℓ) := by
  let b := (R + ℓ / 2) / 2
  have hRb : R < b := by dsimp [b]; have := (div_lt_iff₀ hℓ).mp hR; linarith
  have hbℓ : b < ℓ / 2 := by dsimp [b]; have := (div_lt_iff₀ hℓ).mp hR; linarith
  let s : Set (Euclidean n) := {y | ∀ i, |y i| < b}
  let t : Set (Euclidean n) := {y | ∀ i, |y i| ≤ R}
  have hs : IsOpen s := by
    change IsOpen {y : Euclidean n | ∀ i, |y i| < b}
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const
  have ht : IsClosed t := by
    change IsClosed {y : Euclidean n | ∀ i, |y i| ≤ R}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
  obtain ⟨f, hf, hfr, hfs, hft⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hs ht (fun y hy i ↦ (hy i).trans_lt hRb)
  let K := (fun z : Euclidean n ↦ ℓ • z) '' fundamentalCell n
  have hK : IsCompact K := (isCompact_fundamentalCell n).image (by fun_prop)
  have hsK : s ⊆ K := by
    intro y hy
    refine ⟨ℓ⁻¹ • y, ?_, by simp [smul_smul, hℓ.ne']⟩
    intro i
    change -(1 / 2 : ℝ) ≤ ℓ⁻¹ * y i ∧ ℓ⁻¹ * y i ≤ 1 / 2
    apply abs_le.mp
    rw [abs_mul, abs_inv, abs_of_pos hℓ, ← div_eq_inv_mul]
    exact (div_le_iff₀ hℓ).mpr (by have := hy i; linarith)
  have hfc : HasCompactSupport f := by
    apply hK.of_isClosed_subset isClosed_closure
    exact closure_minimal (hfs ▸ hsK) hK.isClosed
  refine ⟨⟨fun y ↦ (f y : ℂ), Complex.ofRealCLM.contDiff.comp hf,
    hfc.comp_left (g := Complex.ofReal) (by simp), ?_, ?_, ?_⟩⟩
  · intro y
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfr ⟨y, rfl⟩).1]
    exact (hfr ⟨y, rfl⟩).2
  · intro y hy
    have hyf : y ∈ Function.support f := by simpa using hy
    have hyb := hfs ▸ hyf
    have hyK := hsK hyb
    rcases hyK with ⟨z, hz, rfl⟩
    simpa [smul_smul, hℓ.ne'] using hz
  · intro y hy
    simp [(hft y).mp hy]

/-- The same cutoff is one on every nonzero full-amplitude source fiber;
no source support is enlarged in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem SourceCutoff.one_on_amplitude {R ℓ : ℝ} (β : SourceCutoff n R ℓ)
    (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (x η y : Euclidean n) (hy : A x y η ≠ 0) : β.toFun y = 1 := by
  classical
  have he : ∃ i j, A x y η i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (by ext i j; exact h i j)
  obtain ⟨i, j, hij⟩ := he
  exact β.one y (hs x η i j y hij)

end JanetCartan.FourierIntegral.SourceExpansion
