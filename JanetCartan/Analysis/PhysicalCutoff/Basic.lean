module

public import JanetCartan.Analysis.PhysicalBernstein.Basic
public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Basic

/-!
# The physical smooth Fourier truncation

For paper-v2 §15 Steps 6–7, the fixed real-even symbol is one on the radian
ball of radius `R` and zero outside the radian ball of radius `2 * R`.
Both radii are fixed before the requested accuracy. The input and output
are the same whole-space real Euclidean-valued Schwartz fields, not periodic
surrogates. Reality, the exact Fourier identity, and contraction are proved
in the following leaf modules.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap ContDiff

namespace JanetCartan.PhysicalCutoff

variable {n N : ℕ}

/-- The fixed smooth symbol at the physical covector `(2π) • ξ`
(paper-v2 §15, Step 6). -/
def symbol (R : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fourierCutoff ((2 * Real.pi / R) • ξ)

/-- The multiplier is genuinely real and even (§15, Step 6). -/
@[simp] theorem symbol_neg (R : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    symbol R (-ξ) = symbol R ξ := by
  simp [symbol]

/-- The fixed multiplier takes values in `[0,1]` (§15, Step 6). -/
theorem symbol_mem_Icc (R : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    symbol R ξ ∈ Set.Icc (0 : ℝ) 1 := fourierCutoff_mem_Icc _

/-- Smoothness, with no accuracy parameter (§15, Step 6). -/
theorem contDiff_symbol (R : ℝ) :
    ContDiff ℝ ∞ (symbol (n := n) R) := by
  unfold symbol
  exact contDiff_fourierCutoff.comp (contDiff_id.const_smul _)

/-- The smooth multiplier acts on the actual Schwartz space (§15, Step 6). -/
theorem hasTemperateGrowth_symbol (R : ℝ) :
    Function.HasTemperateGrowth (symbol (n := n) R) := by
  exact (hasCompactSupport_fourierCutoff.hasTemperateGrowth
    contDiff_fourierCutoff).comp
    (((2 * Real.pi / R) • ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin n))).hasTemperateGrowth)

private theorem norm_scaled_frequency {R : ℝ} (hR : 0 < R)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖(2 * Real.pi / R) • ξ‖ = ‖(2 * Real.pi) • ξ‖ / R := by
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity), abs_of_pos (by positivity)]
  ring

/-- The plateau preserves every radian frequency at most `R` (§15, Step 6). -/
theorem symbol_eq_one {R : ℝ} (hR : 0 < R)
    {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖(2 * Real.pi) • ξ‖ ≤ R) :
    symbol R ξ = 1 := by
  apply fourierCutoff_eq_one
  rw [norm_scaled_frequency hR]
  exact (div_le_one hR).2 hξ

/-- Frequencies at least `2R` vanish, literally in the radian convention
(§15, Step 6). -/
theorem symbol_eq_zero {R : ℝ} (hR : 0 < R)
    {ξ : EuclideanSpace ℝ (Fin n)} (hξ : 2 * R ≤ ‖(2 * Real.pi) • ξ‖) :
    symbol R ξ = 0 := by
  apply fourierCutoff_eq_zero
  rw [norm_scaled_frequency hR]
  exact (le_div_iff₀ hR).2 hξ

/-- Norm-preserving complex inclusion of the original real Schwartz field
(§15, Step 6). -/
def complexify
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N))) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin N)) :=
  SchwartzMap.postcompCLM euclideanComplexInclusion u

/-- The inclusion is pointwise the shared inclusion used by physical band support. -/
@[simp] theorem complexify_apply
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N)))
    (x : EuclideanSpace ℝ (Fin n)) :
    complexify u x = euclideanComplexInclusion (u x) := rfl

/-- The actual filtered Fourier transform, not an assumed support condition
(§15, Step 6). -/
def filteredFourier (R : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N))) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin N)) :=
  SchwartzMap.smulLeftCLM _ (symbol R) (𝓕 (complexify u))

/-- The exact multiplier on the original Fourier transform (§15, Step 6). -/
@[simp] theorem filteredFourier_apply (R : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N)))
    (ξ : EuclideanSpace ℝ (Fin n)) :
    filteredFourier R u ξ = symbol R ξ • 𝓕 (complexify u) ξ :=
  SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_symbol R) _ _

/-- Inverse transform of the actual smooth truncated frequency field (§15, Step 6). -/
def complexTruncate (R : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N))) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin N)) :=
  𝓕⁻ (filteredFourier R u)

/-- The actual real Schwartz increment of §15, Steps 6–7. The subsequent
reality theorem proves that taking real part discards nothing. -/
def truncate (R : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N))) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N)) :=
  SchwartzMap.postcompCLM euclideanRealPart (complexTruncate R u)

/-- Fourier inversion gives the prescribed symbol before taking real part
(§15, Step 6). -/
theorem fourier_complexTruncate (R : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N))) :
    𝓕 (complexTruncate R u) = filteredFourier R u :=
  fourier_fourierInv_eq _

end JanetCartan.PhysicalCutoff
