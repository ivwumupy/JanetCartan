module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Differential

/-!
# The literal Euclidean source commutator normal on Schwartz tests

For `app:ch_background:prop:bg-frame`, Step 1, construct `μ P [J,χ²] J P* μ`
and prove its literal formal adjoint is `-μ P J [J,χ²] P* μ`. Intermediate
localization is an exact split with the entire tail retained. The construction
is on Schwartz space; its bounded L² extension and order-minus-one amplitude
are separate analytic obligations, not hypotheses of these identities.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped SchwartzMap ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)

/-- Insert a scalar Schwartz operator between the actual two differential
factors of the image error (`app:ch_background:prop:bg-frame`, Step 1).
This is a construction on tests, with no analytic order or norm premise. -/
def coefficientSchwartzSandwich
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ)
    (T : S →L[ℂ] S) : (I → S) →L[ℂ] (I → S) :=
  (maskedCoefficientSchwartzCLM A Z μ).comp
    ((ContinuousLinearMap.pi fun j ↦ T.comp (ContinuousLinearMap.proj j)).comp
      (maskedCoefficientAdjointSchwartzCLM A Z μ))

/-- The actual source commutator error `μ P [J,χ²] J P* μ` on tests
(`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientSourceCommutatorSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ) :
    (I → S) →L[ℂ] (I → S) :=
  coefficientSchwartzSandwich A Z μ ((imageSourceSquareCommutator χ).comp imageBesselSchwartzCLM)

/-- The literal reversed expression, including the negative sign and the
reversed order of `J` and the commutator
(`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientSourceCommutatorFormalAdjointSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ) :
    (I → S) →L[ℂ] (I → S) :=
  -coefficientSchwartzSandwich A Z μ (imageBesselSchwartzCLM.comp (imageSourceSquareCommutator χ))

/-- The compactly localized composition to which the exact diagonal and
primitive composition APIs apply (`app:ch_background:prop:bg-frame`, Step 1).
It is only one summand of the actual commutator normal. -/
def coefficientSourceCommutatorLocalizedSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ) :
    (I → S) →L[ℂ] (I → S) :=
  coefficientSchwartzSandwich A Z μ ((imageSourceSquareCommutator χ).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ))).comp imageBesselSchwartzCLM))

/-- The complete intermediate-localization tail `μ P χ² J (1-β) J P* μ`.
It is subtracted from the localized composition, and no mask commutes across
`J` (`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientSourceCommutatorTailSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ) :
    (I → S) →L[ℂ] (I → S) :=
  coefficientSchwartzSandwich A Z μ
    ((SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))).comp
      (imageBesselSchwartzCLM.comp
        (((ContinuousLinearMap.id ℂ S) - SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ))).comp
          imageBesselSchwartzCLM)))

/-- Pointwise evaluation of the actual error. `q` is precisely the compact
Schwartz realization of `coefficientFormalAdjoint A Z (μ v)` by
`maskedCoefficientAdjointSchwartzCLM_apply`; the other factors are the literal
Fourier multipliers (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorSchwartz_apply
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : I → S) (x : E) (i : I) :
    coefficientSourceCommutatorSchwartz A Z χ μ v i x =
      (μ x : ℂ) * coefficientOperator A Z (fun y j ↦
        imageSourceSquareCommutator χ
          (imageBesselSchwartzCLM (maskedCoefficientAdjointSchwartzCLM A Z μ v j)) y) x i :=
  maskedCoefficientSchwartzCLM_apply A Z μ hA hZ hμ hμc _ x i

/-- The exact split, with no intermediate compact localization silently
inserted (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorSchwartz_localization
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hχ : χ.HasTemperateGrowth) (hβ : β.HasTemperateGrowth)
    (hplateau : ∀ y, χ y ≠ 0 → β y = 1) :
    coefficientSourceCommutatorSchwartz A Z χ μ =
      coefficientSourceCommutatorLocalizedSchwartz A Z χ μ β -
        coefficientSourceCommutatorTailSchwartz A Z χ μ β := by
  ext1 v
  change maskedCoefficientSchwartzCLM A Z μ _ =
    maskedCoefficientSchwartzCLM A Z μ _ - maskedCoefficientSchwartzCLM A Z μ _
  rw [← map_sub]
  congr 1
  funext j
  exact imageSourceSquareCommutator_localization χ β hχ hβ hplateau
    (imageBesselSchwartzCLM (maskedCoefficientAdjointSchwartzCLM A Z μ v j))

private theorem pairing_neg_right (u v : S) :
    imageSchwartzPairing u (-v) = -imageSchwartzPairing u v := by
  change inner ℂ (u.toLp 2) ((SchwartzMap.toLpCLM ℂ ℂ 2) (-v)) = _
  rw [map_neg, inner_neg_right]
  rfl

private theorem pairing_star (u v : S) :
    star (imageSchwartzPairing u v) = imageSchwartzPairing v u := by
  exact inner_conj_symm _ _

/-- The literal differential sandwich has precisely the reversed formal
adjoint on Euclidean Lebesgue tests; the proof uses the actual coefficient
integration-by-parts formula and the real Bessel symbol
(`app:ch_background:prop:bg-frame`, Step 1). This is a test identity, not yet
the bounded L² adjoint endpoint. -/
theorem coefficientSourceCommutatorSchwartz_pairing
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (u v : I → S) :
    (∑ i, imageSchwartzPairing (coefficientSourceCommutatorSchwartz A Z χ μ u i) (v i)) =
      ∑ i, imageSchwartzPairing (u i) (coefficientSourceCommutatorFormalAdjointSchwartz A Z χ μ v i) := by
  let q := maskedCoefficientAdjointSchwartzCLM A Z μ
  let t := fun j ↦ imageBesselSchwartzCLM (imageSourceSquareCommutator χ (q v j))
  have hr := congrArg star (maskedCoefficientSchwartzCLM_pairing A Z μ hA hZ hμ hμc t u)
  simp only [star_sum, pairing_star] at hr
  change (∑ i, imageSchwartzPairing
    (maskedCoefficientSchwartzCLM A Z μ
      (fun j ↦ imageSourceSquareCommutator χ (imageBesselSchwartzCLM (q u j))) i) (v i)) =
      ∑ i, imageSchwartzPairing (u i) (-(maskedCoefficientSchwartzCLM A Z μ t i))
  rw [maskedCoefficientSchwartzCLM_pairing A Z μ hA hZ hμ hμc]
  simp_rw [imageSourceSquareCommutator_rightBessel_pairing χ (hχc.hasTemperateGrowth hχ),
    pairing_neg_right]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  exact congrArg Neg.neg hr.symm

end JanetCartan.ContinuumNormalReduction.ImageNormal
