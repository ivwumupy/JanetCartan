module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.SourceKernel

/-!
# The full forward source gap

The low-envelope part of `app:ch_response:thm:response-literal-transfer`.
Separation from the carrier and small input Fourier frequency imply a gap
proportional to `ρ + ‖η‖`, including unbounded frequencies. No conic or annular
restriction is used.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral JanetCartan.Localization
open scoped ContDiff Matrix.Norms.Frobenius

/-- Fixed gap constant for the forward complement in
`app:ch_response:thm:response-literal-transfer`. Here `Z` bounds the carrier norm. -/
def forwardGapConstant (c Z : ℝ) : ℝ := c / (2 * (c + 1 + Z))

/-- Positivity of the gap constant used by `norm_forwardSourceKernel_le`. -/
theorem forwardGapConstant_pos {c Z : ℝ} (hc : 0 < c) (hZ : 0 ≤ Z) :
    0 < forwardGapConstant c Z := by
  unfold forwardGapConstant
  positivity

/-- The elementary full forward gap in
`app:ch_response:thm:response-literal-transfer`, uniform over the entire
complement. The low envelope frequency `θ` is kept inside the source phase. -/
theorem forward_frequency_gap {n : ℕ} {c Z ρ : ℝ} {ζ η θ : Euclidean n}
    (hc : 0 < c) (hρ : 0 ≤ ρ) (hζ : ‖ζ‖ ≤ Z)
    (hη : c * ρ ≤ ‖η - ρ • ζ‖) (hθ : ‖θ‖ ≤ c * ρ / 2) :
    forwardGapConstant c Z * (ρ + ‖η‖) ≤ ‖η - ρ • ζ - θ‖ := by
  have hZ : 0 ≤ Z := (norm_nonneg ζ).trans hζ
  have htri : ‖η‖ ≤ ‖η - ρ • ζ‖ + ρ * Z := by
    calc
      ‖η‖ = ‖(η - ρ • ζ) + ρ • ζ‖ := by rw [sub_add_cancel]
      _ ≤ ‖η - ρ • ζ‖ + ‖ρ • ζ‖ := norm_add_le _ _
      _ ≤ ‖η - ρ • ζ‖ + ρ * Z := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hζ hρ)
  have hd : ‖η - ρ • ζ‖ ≤ 2 * ‖η - ρ • ζ - θ‖ := by
    have hh := norm_sub_norm_le (η - ρ • ζ) θ
    linarith
  unfold forwardGapConstant
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (c + 1 + Z))).mpr
  have h₁ := mul_le_mul_of_nonneg_left htri hc.le
  have h₂ := mul_le_mul_of_nonneg_left hη (by positivity : 0 ≤ 1 + Z)
  have h₃ := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ c + 1 + Z)
  nlinarith

/-- Exact source derivative of the full forward phase
(`app:ch_response:thm:response-literal-transfer`). -/
theorem fderiv_forwardSourcePhase {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (x η θ y : Euclidean n) :
    fderiv ℝ (forwardSourcePhase S ζ ρ x η θ) y =
      -(innerSL ℝ (η - ρ • ζ - θ)) := by
  exact ((innerSL ℝ (η - ρ • ζ - θ)).hasFDerivAt.const_sub (S x η)).fderiv

/-- The phase covector norm equals the actual signed frequency difference,
with no loss of physical normalization. -/
theorem norm_fderiv_forwardSourcePhase {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (x η θ y : Euclidean n) :
    ‖fderiv ℝ (forwardSourcePhase S ζ ρ x η θ) y‖ = ‖η - ρ • ζ - θ‖ := by
  rw [fderiv_forwardSourcePhase, norm_neg, innerSL_apply_norm]

/-- The source-gradient lower bound required by repeated integration by parts,
proved from separation rather than assumed for the forward graph. -/
theorem forwardSourcePhase_gap {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) {ζ η θ : Euclidean n} {ρ c Z : ℝ}
    (hc : 0 < c) (hρ : 0 ≤ ρ) (hζ : ‖ζ‖ ≤ Z)
    (hη : c * ρ ≤ ‖η - ρ • ζ‖) (hθ : ‖θ‖ ≤ c * ρ / 2)
    (x y : Euclidean n) :
    forwardGapConstant c Z * (ρ + ‖η‖) ≤
      ‖fderiv ℝ (forwardSourcePhase S ζ ρ x η θ) y‖ := by
  rw [norm_fderiv_forwardSourcePhase]
  exact forward_frequency_gap hc hρ hζ hη hθ

/-- The gap applies wherever the complete complementary amplitude is nonzero.
The sole selector assumption is its plateau near the carrier; original
physical cutoffs, bounded frequencies and shoulders remain in the amplitude
(`app:ch_response:thm:response-literal-transfer`). -/
theorem forwardSourcePhase_gap_of_complementaryAmplitude_ne_zero {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (χ : Euclidean n → ℂ) {ζ η θ : Euclidean n} {ρ c Z : ℝ}
    (hc : 0 < c) (hρ : 0 ≤ ρ) (hζ : ‖ζ‖ ≤ Z)
    (hχ : ∀ δ, ‖δ‖ < c * ρ → χ δ = 1)
    (hθ : ‖θ‖ ≤ c * ρ / 2) (x y : Euclidean n)
    (hne : complementaryAmplitude A ζ ρ χ x y η ≠ 0) :
    forwardGapConstant c Z * (ρ + ‖η‖) ≤
      ‖fderiv ℝ (forwardSourcePhase S ζ ρ x η θ) y‖ := by
  apply forwardSourcePhase_gap S hc hρ hζ ?_ hθ
  by_contra h
  exact hne (by simp [complementaryAmplitude, hχ _ (lt_of_not_ge h)])

/-- Higher source derivatives of the forward phase vanish exactly; thus no
phase profile loss is charged at large integration order in
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_forwardSourcePhase_eq_zero {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (x η θ y : Euclidean n) {j : ℕ} (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ (j + 1) (forwardSourcePhase S ζ ρ x η θ) y‖ = 0 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have heq : fderiv ℝ (forwardSourcePhase S ζ ρ x η θ) =
      fun _ ↦ -(innerSL ℝ (η - ρ • ζ - θ)) :=
    funext (fderiv_forwardSourcePhase S ζ ρ x η θ)
  rw [heq, iteratedFDeriv_const_of_ne (by omega : j ≠ 0), Pi.zero_apply, norm_zero]

/-- Upper source-gradient bound for the forward complement, needed to control
the actual reciprocal coefficients in repeated integration by parts. -/
theorem norm_fderiv_forwardSourcePhase_le {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) {ζ η θ : Euclidean n} {ρ c Z : ℝ}
    (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hζ : ‖ζ‖ ≤ Z)
    (hθ : ‖θ‖ ≤ c * ρ / 2) (x y : Euclidean n) :
    ‖fderiv ℝ (forwardSourcePhase S ζ ρ x η θ) y‖ ≤
      (1 + Z + c / 2) * (ρ + ‖η‖) := by
  rw [norm_fderiv_forwardSourcePhase]
  have hZ : 0 ≤ Z := (norm_nonneg ζ).trans hζ
  have htri := (norm_sub_le (η - ρ • ζ) θ).trans
    (add_le_add (norm_sub_le η (ρ • ζ)) le_rfl)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ] at htri
  have hz := mul_le_mul_of_nonneg_left hζ hρ
  nlinarith [mul_nonneg hZ (norm_nonneg η), mul_nonneg hc (norm_nonneg η)]

/-- The forward source-integral decay in
`app:ch_response:thm:response-literal-transfer`, directly from carrier
separation, low input Fourier support and the full amplitude's source grades.
This is the kernel step, before output derivatives and radial integration.
The constants contain no scale-dependent phase profile. -/
theorem norm_forwardSourceKernel_le {n r : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (S : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ x η θ : Euclidean n) (q : ℕ)
    (ha : ContDiffOn ℝ ∞ (fun y ↦ A x y η) Ω)
    (hs : tsupport (fun y ↦ A x y η) ⊆ Ω)
    (hcompact : HasCompactSupport (fun y ↦ A x y η))
    {c Z a L ρ : ℝ} (hc : 0 < c) (ha0 : 0 ≤ a) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hζ : ‖ζ‖ ≤ Z) (hη : c * ρ ≤ ‖η - ρ • ζ‖)
    (hθ : ‖θ‖ ≤ c * ρ / 2) {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (ha_bound : ∀ y ∈ tsupport (fun y ↦ A x y η), ∀ j,
      ‖iteratedFDeriv ℝ j (fun z ↦ A x z η) y‖ ≤ C j * (a * L ^ j)) :
    ‖sourceKernel (forwardSourcePhase S ζ ρ x η θ) A x η‖ ≤
      (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          ((forwardGapConstant c Z) ^ 2) (1 + Z + c / 2) (fun _ ↦ 0)) C q 0 *
        (a * (L / (ρ + ‖η‖)) ^ q)) *
        MeasureTheory.volume.real (tsupport (fun y ↦ A x y η)) := by
  apply norm_sourceKernel_le hΩ (forwardSourcePhase S ζ ρ x η θ) A x η q
    (contDiff_const.sub (innerSL ℝ (η - ρ • ζ - θ)).contDiff).contDiffOn
    ha hs hcompact (forwardGapConstant_pos hc ((norm_nonneg ζ).trans hζ))
    ha0 hL hρ ?_ ?_ hC ?_ ha_bound
  · intro y _
    exact forwardSourcePhase_gap S hc hρ.le hζ hη hθ x y
  · intro y _
    exact norm_fderiv_forwardSourcePhase_le S hc.le hρ.le hζ hθ x y
  · intro y _ j hj
    simp only [norm_iteratedFDeriv_forwardSourcePhase_eq_zero S ζ ρ x η θ y hj,
      zero_mul, le_refl]

/-- The source-kernel estimate for the actual complete complementary amplitude
in `app:ch_response:thm:response-literal-transfer`. Only the selector plateau
is used to obtain separation; the zero-amplitude case is included. All source
derivative assumptions concern the full complementary amplitude with its
original physical and frequency cutoffs. -/
theorem norm_complementary_forwardSourceKernel_le {n r : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (S : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (χ : Euclidean n → ℂ)
    (ζ x η θ : Euclidean n) (q : ℕ)
    {c Z a L ρ : ℝ}
    (ha : ContDiffOn ℝ ∞ (fun y ↦ complementaryAmplitude A ζ ρ χ x y η) Ω)
    (hs : tsupport (fun y ↦ complementaryAmplitude A ζ ρ χ x y η) ⊆ Ω)
    (hcompact : HasCompactSupport (fun y ↦ complementaryAmplitude A ζ ρ χ x y η))
    (hc : 0 < c) (ha0 : 0 ≤ a) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hζ : ‖ζ‖ ≤ Z) (hχ : ∀ δ, ‖δ‖ < c * ρ → χ δ = 1)
    (hθ : ‖θ‖ ≤ c * ρ / 2) {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (ha_bound : ∀ y ∈ tsupport (fun y ↦ complementaryAmplitude A ζ ρ χ x y η), ∀ j,
      ‖iteratedFDeriv ℝ j (fun z ↦ complementaryAmplitude A ζ ρ χ x z η) y‖ ≤ C j * (a * L ^ j)) :
    ‖sourceKernel (forwardSourcePhase S ζ ρ x η θ) (complementaryAmplitude A ζ ρ χ) x η‖ ≤
      (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          ((forwardGapConstant c Z) ^ 2) (1 + Z + c / 2) (fun _ ↦ 0)) C q 0 *
        (a * (L / (ρ + ‖η‖)) ^ q)) *
        MeasureTheory.volume.real (tsupport (fun y ↦ complementaryAmplitude A ζ ρ χ x y η)) := by
  by_cases hχeq : χ (η - ρ • ζ) = 1
  · simp [sourceKernel, complementaryAmplitude, hχeq]
  · have hη : c * ρ ≤ ‖η - ρ • ζ‖ := by
      by_contra h
      exact hχeq (hχ _ (lt_of_not_ge h))
    exact norm_forwardSourceKernel_le hΩ S (complementaryAmplitude A ζ ρ χ)
      ζ x η θ q ha hs hcompact hc ha0 hL hρ hζ hη hθ hC ha_bound

end JanetCartan.ResponseTransfer.LowEnvelope
