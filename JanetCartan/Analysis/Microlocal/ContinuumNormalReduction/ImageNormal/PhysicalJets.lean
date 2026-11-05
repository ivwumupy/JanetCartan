module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.SourceCommutator
/-!
# Physical derivative bounds for the localized source commutator

For `app:ch_background:prop:bg-frame`, Step 1, every derivative in the two
physical positions of the actual Bessel/source-square diagonal remainder
retains order-minus-two decay. The fixed cutoffs give compact support to the
Taylor coefficient, so its derivative bounds follow from smoothness and
compactness, rather than from an assumed estimate for the remainder.

These are the physical budgets consumed by the integer Sobolev endpoint.
Frequency derivative estimates, the exact operator identification, and the
composition with `P_G`, the second `J`, and `P_G*` remain separate obligations.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The localized, two-position Taylor coefficient of the actual source
square (`app:ch_background:prop:bg-frame`, Step 1). -/
def localizedSourceSquareTaylor (α χ β : E → ℝ) (p : E × E) : E →L[ℝ] ℂ :=
  α p.1 • sourceTaylorCoefficient (fun y ↦ ((χ y)^2 : ℂ)) β p.1 p.2

/-- The fixed source-square Taylor coefficient is smooth in both physical
positions (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_localizedSourceSquareTaylor (α χ β : E → ℝ)
    (hα : ContDiff ℝ ∞ α) (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (localizedSourceSquareTaylor α χ β) := by
  have hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ ((χ p.2.1)^2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd.fst)).pow 2
  have ht := (contDiff_fullTaylorCoefficient_joint (fun _ y _ : E ↦ ((χ y)^2 : ℂ)) β hc hβ).comp
    (f := fun p : E × E ↦ (p.1, p.2, (0 : E))) (by fun_prop)
  exact (hα.comp contDiff_fst).smul ht

/-- The output and source masks retain compact support in both physical
positions (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_localizedSourceSquareTaylor (α χ β : E → ℝ)
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β) :
    HasCompactSupport (localizedSourceSquareTaylor α χ β) := by
  apply HasCompactSupport.intro (hα.isCompact.prod hβ.isCompact)
  intro p hp
  by_cases hx : p.1 ∈ tsupport α
  · have hy : p.2 ∉ tsupport β := fun hy ↦ hp ⟨hx, hy⟩
    simp [localizedSourceSquareTaylor, sourceTaylorCoefficient, image_eq_zero_of_notMem_tsupport hy]
  · simp [localizedSourceSquareTaylor, image_eq_zero_of_notMem_tsupport hx]

/-- Contract the actual frequency derivative of the Bessel symbol against a
source Taylor coefficient, with the unit-frequency normalization
(`app:ch_background:prop:bg-frame`, Step 1). -/
def imageBesselContraction (b : OrthonormalBasis (Fin d) ℝ E) (ξ : E) :
    (E →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ • ∑ j, (fderiv ℝ (imageBesselSymbol (d := d)) ξ (b j)) •
    ContinuousLinearMap.apply ℝ ℂ (b j)

/-- The contraction is the literal frequency-divergence product term
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselContraction_apply (b : OrthonormalBasis (Fin d) ℝ E)
    (ξ : E) (T : E →L[ℝ] ℂ) :
    imageBesselContraction b ξ T = frequencyCutoffError b imageBesselSymbol (fun _ ↦ T) ξ := by
  simp [imageBesselContraction, frequencyCutoffError]

/-- Order-minus-two decay of the contraction operator follows from the
actual Bessel derivative (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_imageBesselContraction_le (b : OrthonormalBasis (Fin d) ℝ E) (ξ : E) :
    ‖imageBesselContraction b ξ‖ ≤
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * d * (2 * Real.pi)) *
        (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro T
  rw [imageBesselContraction_apply]
  apply (norm_frequencyCutoffError_le b imageBesselSymbol (fun _ ↦ T) ξ).trans
  calc
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * d *
        ((2 * Real.pi) * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹) * ‖T‖ := by
      simp only [Fintype.card_fin]
      gcongr
      exact norm_fderiv_imageBesselSymbol_le ξ
    _ = _ := by ring

/-- The localized source-square diagonal remainder, retaining both physical
positions and the literal Bessel symbol (`app:ch_background:prop:bg-frame`,
Step 1). -/
def localizedSourceSquareRemainder (b : OrthonormalBasis (Fin d) ℝ E)
    (α χ β : E → ℝ) (ξ : E) (p : E × E) : ℂ :=
  α p.1 • diagonalRemainderAmplitude b
    (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β p.1 p.2 ξ

/-- Separate the actual Bessel frequency derivative from the fixed physical
Taylor coefficient (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedSourceSquareRemainder_eq_contraction
    (b : OrthonormalBasis (Fin d) ℝ E) (α χ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (ξ : E) :
    localizedSourceSquareRemainder b α χ β ξ =
      imageBesselContraction b ξ ∘ localizedSourceSquareTaylor α χ β := by
  funext p
  simp only [localizedSourceSquareRemainder, imageSourceSquare_remainder_eq b χ β hχ,
    Function.comp_apply, localizedSourceSquareTaylor, map_smul,
    imageBesselContraction_apply]

/-- Joint smoothness of the explicit localized remainder, for the integer
PDO realization in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem contDiff_localizedSourceSquareRemainder_joint
    (b : OrthonormalBasis (Fin d) ℝ E) (α χ β : E → ℝ)
    (hα : ContDiff ℝ ∞ α) (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun p : E × (E × E) ↦
      localizedSourceSquareRemainder b α χ β p.1 p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : E × E × E ↦
      imageBesselSymbol p.2.2 • ((χ p.2.1)^2 : ℂ)) :=
    (hasTemperateGrowth_imageBesselSymbol.1.comp contDiff_snd.snd).smul
      ((Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd.fst)).pow 2)
  exact (hα.comp contDiff_snd.fst).smul
    ((contDiff_diagonalRemainderAmplitude_joint b _ β hc hβ).comp
      (f := fun p : E × (E × E) ↦ (p.2.1, p.2.2, p.1)) (by fun_prop))

/-- Both physical supports remain compact in the explicit remainder; this
is the support input for `app:ch_background:prop:bg-frame`, Step 1. -/
theorem hasCompactSupport_localizedSourceSquareRemainder
    (b : OrthonormalBasis (Fin d) ℝ E) (α χ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hαc : HasCompactSupport α)
    (hβc : HasCompactSupport β) (ξ : E) :
    HasCompactSupport (localizedSourceSquareRemainder b α χ β ξ) := by
  rw [localizedSourceSquareRemainder_eq_contraction b α χ β hχ ξ]
  exact (hasCompactSupport_localizedSourceSquareTaylor α χ β hαc hβc).comp_left
    (map_zero (imageBesselContraction b ξ))

/-- Every physical derivative of the localized source-square remainder has
order-minus-two decay. The only hypotheses are smoothness and support of the
fixed cutoffs; no remainder estimate is assumed. The consuming estimate is the
image-normal error in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_localizedSourceSquareRemainder_physical_jet_bound
    (b : OrthonormalBasis (Fin d) ℝ E) (α χ β : E → ℝ)
    (hα : ContDiff ℝ ∞ α) (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (hαc : HasCompactSupport α) (hβc : HasCompactSupport β) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ p,
      ‖iteratedFDeriv ℝ n (localizedSourceSquareRemainder b α χ β ξ) p‖ ≤
        C * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ := by
  have ht := contDiff_localizedSourceSquareTaylor α χ β hα hχ hβ
  have htc := hasCompactSupport_localizedSourceSquareTaylor α χ β hαc hβc
  obtain ⟨K, hK⟩ := (htc.iteratedFDeriv n).exists_bound_of_continuous
    (ht.continuous_iteratedFDeriv (by simp))
  have hK₀ : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨(‖(2 * Real.pi * Complex.I)⁻¹‖ * d * (2 * Real.pi)) * K,
    by positivity, ?_⟩
  intro ξ p
  rw [localizedSourceSquareRemainder_eq_contraction b α χ β hχ ξ]
  apply ((imageBesselContraction b ξ).norm_iteratedFDeriv_comp_left
    ht.contDiffAt (by simp)).trans
  calc
    _ ≤ ((‖(2 * Real.pi * Complex.I)⁻¹‖ * d * (2 * Real.pi)) *
        (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹) * K :=
      mul_le_mul (norm_imageBesselContraction_le b ξ) (hK p) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A single constant controls any specified finite physical derivative
reserve of the actual source-square remainder. This supplies the fixed-low
budget in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_localizedSourceSquareRemainder_physical_budget
    (b : OrthonormalBasis (Fin d) ℝ E) (α χ β : E → ℝ)
    (hα : ContDiff ℝ ∞ α) (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (hαc : HasCompactSupport α) (hβc : HasCompactSupport β) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ ξ p,
      ‖iteratedFDeriv ℝ n (localizedSourceSquareRemainder b α χ β ξ) p‖ ≤
        C * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ := by
  have h (n : ℕ) := exists_localizedSourceSquareRemainder_physical_jet_bound
    b α χ β hα hχ hβ hαc hβc n
  choose C hC₀ hC using h
  refine ⟨∑ j ∈ Finset.range (N + 1), C j, Finset.sum_nonneg (fun j _ ↦ hC₀ j), ?_⟩
  intro n hn ξ p
  exact (hC n ξ p).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ ↦ hC₀ j) (Finset.mem_range.mpr (by omega)))
    (by positivity))

end JanetCartan.ContinuumNormalReduction.ImageNormal
