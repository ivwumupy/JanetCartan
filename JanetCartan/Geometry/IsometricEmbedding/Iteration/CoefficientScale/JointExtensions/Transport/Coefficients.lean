module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Transport.Basic

/-!
# Extending the six literal null-transport coefficients

The consumer is `exists_transport_extensions_before_geometry`. The denominator
is the actual polynomial in the projected frame and canonical carrier gradient;
its reciprocal is smooth on the nonzero gap produced by `LocalBounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport
open NullTransport.CoefficientBounds

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The literal adapted denominator is smooth on the actual input domain;
no denominator regularity is assumed (`app:ch_waves:eq:joint-tame`). -/
theorem contDiffOn_carrierAdaptedDenominator {c C : ℝ} (hP : P.IsValid c C)
    (row col : Fin n) {Ω : Set (Euclidean n × Euclidean 3)}
    (hΩ : Ω ⊆ inputDomain T) :
    ContDiffOn ℝ ∞ (carrierAdaptedDenominator T Q row col) Ω :=
  ((smooth_denominator T.data.adapted.normal row col).comp_contDiffOn
    (smooth_actualInput T hP Q)).mono hΩ

/-- The produced nonzero denominator gap gives reciprocal regularity
for the same actual coefficient (`app:ch_waves:eq:joint-tame`). -/
theorem contDiffOn_carrierReciprocalDenominator {c C : ℝ} (hP : P.IsValid c C)
    (row col : Fin n) {Ω : Set (Euclidean n × Euclidean 3)}
    (hΩ : Ω ⊆ inputDomain T)
    (hgap : ∀ w ∈ Ω, carrierAdaptedDenominator T Q row col w ≠ 0) :
    ContDiffOn ℝ ∞ (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) Ω :=
  (contDiffOn_carrierAdaptedDenominator T Q hP row col hΩ).inv hgap

/-- The sum of the global seminorms of the SIX actual fixed extensions,
including the denominator, its reciprocal and the full zeroth-order potential
(`app:eq:uniform-high-coeff`). -/
def extendedTransportCoefficientNorm (F : Euclidean n → Euclidean N) (row col : Fin n)
    (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) : ℝ :=
  cNorm univ m (extendTransportCoefficient a hρ (carrierNullvector T Q col)) +
    cNorm univ m (extendTransportCoefficient a hρ (carrierConullvector T Q row)) +
    cNorm univ m (extendTransportCoefficient a hρ (carrierAdaptedDenominator T Q row col)) +
    cNorm univ m (extendTransportCoefficient a hρ
      (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹)) +
    cNorm univ m (extendTransportCoefficient a hρ (carrierTransportDirection T Q row col)) +
    cNorm univ m (extendTransportCoefficient a hρ (carrierTransportPotential T Q F row col))

/-- First compare the summed global seminorm with the LITERAL
`currentTransportCoefficientNorm` on the larger original product ball at
the SAME order. The actual smoothness premises are discharged from
`LocalBounds` and the denominator formulas in the construction below
(`app:eq:uniform-high-coeff`). -/
theorem exists_extendedTransportCoefficientNorm_le
    (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ Q (F : Euclidean n → Euclidean N) (row col : Fin n),
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ (carrierNullvector T Q col) x) →
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ (carrierConullvector T Q row) x) →
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ (carrierAdaptedDenominator T Q row col) x) →
      (∀ x ∈ closedBall a ρ,
        ContDiffAt ℝ ∞ (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) x) →
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ (carrierTransportDirection T Q row col) x) →
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ (carrierTransportPotential T Q F row col) x) →
      extendedTransportCoefficientNorm T Q F row col a hρ m ≤
        C * currentTransportCoefficientNorm T Q F row col (closedBall a ρ) m := by
  obtain ⟨Cv, hCv, hv⟩ := exists_extendTransportCoefficient_cNorm_le (V := Euclidean n) a hρ m
  obtain ⟨Cl, hCl, hl⟩ := exists_extendTransportCoefficient_cNorm_le (V := Fin n → ℝ) a hρ m
  obtain ⟨Cs, hCs, hs⟩ := exists_extendTransportCoefficient_cNorm_le (V := ℝ) a hρ m
  let C := Cv + Cl + Cs
  have hCvC : Cv ≤ C := by dsimp [C]; linarith
  have hClC : Cl ≤ C := by dsimp [C]; linarith
  have hCsC : Cs ≤ C := by dsimp [C]; linarith
  have hv' (f : (Euclidean n × Euclidean 3) → Euclidean n)
      (hf : ∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ f x) :
      cNorm univ m (extendTransportCoefficient a hρ f) ≤ C * cNorm (closedBall a ρ) m f :=
    (hv f hf).trans (mul_le_mul_of_nonneg_right hCvC (cNorm_nonneg _ _ _))
  have hl' (f : (Euclidean n × Euclidean 3) → Fin n → ℝ)
      (hf : ∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ f x) :
      cNorm univ m (extendTransportCoefficient a hρ f) ≤ C * cNorm (closedBall a ρ) m f :=
    (hl f hf).trans (mul_le_mul_of_nonneg_right hClC (cNorm_nonneg _ _ _))
  have hs' (f : (Euclidean n × Euclidean 3) → ℝ)
      (hf : ∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ f x) :
      cNorm univ m (extendTransportCoefficient a hρ f) ≤ C * cNorm (closedBall a ρ) m f :=
    (hs f hf).trans (mul_le_mul_of_nonneg_right hCsC (cNorm_nonneg _ _ _))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Q F row col hk hl hd hi hv hp
  simpa only [extendedTransportCoefficientNorm, currentTransportCoefficientNorm, mul_add] using
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (hv' _ hk) (hl' _ hl)) (hs' _ hd)) (hs' _ hi)) (hv' _ hv)) (hs' _ hp)

end JanetCartan.CurrentCoefficientProfiles.JointExtensions
