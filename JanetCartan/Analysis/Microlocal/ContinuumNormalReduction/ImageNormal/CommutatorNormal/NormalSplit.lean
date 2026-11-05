module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.TestOperator

/-!
# Exact source-square split of the literal Euclidean image normal

The parent construction in `app:ch_background:prop:bg-frame`, Step 1, consumes
this identity: `μ P J χ² J P* μ` is the already computed full differential
amplitude plus the literal source commutator. Every coefficient, source mask,
and measurement mask is retained. No estimate for the commutator is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped SchwartzMap ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)

/-- The literal image normal `μ P J χ² J P* μ` on Schwartz tests, before
moving the source square (`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientSourceSquaredImageSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ) :
    (I → S) →L[ℂ] (I → S) :=
  coefficientSchwartzSandwich A Z μ (imageBesselSchwartzCLM.comp
    ((SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))).comp imageBesselSchwartzCLM))

/-- The term `μ P χ² J² P* μ` after source-square commutation
(`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientCommutedImageSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ) :
    (I → S) →L[ℂ] (I → S) :=
  coefficientSchwartzSandwich A Z μ
    ((SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))).comp
      (imageBesselSchwartzCLM.comp imageBesselSchwartzCLM))

/-- Exact algebraic source-square commutation, preserving the order of
both inverse multipliers (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceSquaredImageSchwartz_eq_commuted_add_commutator
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ) :
    coefficientSourceSquaredImageSchwartz A Z χ μ =
      coefficientCommutedImageSchwartz A Z χ μ + coefficientSourceCommutatorSchwartz A Z χ μ := by
  ext1 v
  change maskedCoefficientSchwartzCLM A Z μ _ =
    maskedCoefficientSchwartzCLM A Z μ _ + maskedCoefficientSchwartzCLM A Z μ _
  rw [← map_add]
  congr 1
  funext j
  let q := maskedCoefficientAdjointSchwartzCLM A Z μ v j
  let M := SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))
  change imageBesselSchwartzCLM (M (imageBesselSchwartzCLM q)) =
    M (imageBesselSchwartzCLM (imageBesselSchwartzCLM q)) +
      (imageBesselSchwartzCLM (M (imageBesselSchwartzCLM q)) -
        M (imageBesselSchwartzCLM (imageBesselSchwartzCLM q)))
  abel

/-- Identification with the shared differential-factor construction, using
its exact divergence-form input (`app:ch_background:prop:bg-frame`, Step 1).
The existing full-amplitude theorem therefore applies without introducing a
second coefficient expansion. -/
theorem coefficientCommutedImageSchwartz_eq_coefficientImageNormal
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : I → S) (x : E) (i : I) :
    coefficientCommutedImageSchwartz A Z χ μ v i x =
      coefficientImageNormal A Z χ μ (fun y l ↦ v l y) hA hZ hμ hμc
        (fun l ↦ (v l).smooth ⊤) x i := by
  let w := fun y l ↦ (μ y : ℂ) * v l y
  have hw l : ContDiff ℝ ∞ (fun y ↦ w y l) :=
    (Complex.ofRealCLM.contDiff.comp hμ).mul ((v l).smooth ⊤)
  have hwc l : HasCompactSupport (fun y ↦ w y l) :=
    (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right
  have he (j : J) : maskedCoefficientAdjointSchwartzCLM A Z μ v j =
      coefficientAdjointSchwartz A Z w hA hZ hw hwc j := by
    ext y
    exact maskedCoefficientAdjointSchwartzCLM_apply A Z μ hA hZ hμ hμc v y j
  have hχt := hχc.hasTemperateGrowth hχ
  have hs : (fun y ↦ ((χ y)^2 : ℂ)).HasTemperateGrowth := by fun_prop
  change maskedCoefficientSchwartzCLM A Z μ _ i x = _
  rw [maskedCoefficientSchwartzCLM_apply A Z μ hA hZ hμ hμc]
  change (μ x : ℂ) * coefficientOperator A Z (fun y j ↦
    SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))
      (imageBesselSchwartzCLM (imageBesselSchwartzCLM
        (maskedCoefficientAdjointSchwartzCLM A Z μ v j))) y) x i = _
  simp only [he, SchwartzMap.smulLeftCLM_apply_apply hs, smul_eq_mul,
    imageBesselSchwartzCLM_apply, coefficientImageNormal, Complex.ofReal_pow]
  rfl


/-- Exact connection of the original normal with the already proved full
matrix amplitude and the literal commutator. This is the algebraic input to
the parent's order-minus-one reduction (`app:ch_background:prop:bg-frame`,
Step 1); the commutator endpoint remains a separate analytic obligation. -/
theorem coefficientSourceSquaredImageSchwartz_eq_fullAmplitude_add_commutator
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : Fin d → S) (x : E) (i : Fin d) :
    coefficientSourceSquaredImageSchwartz A Z χ μ v i x =
      matrixFullAmplitudeOperator (differentialFullAmplitude A Z (fun y ↦ χ y^2) μ)
        (fun y l ↦ v l y) x i + coefficientSourceCommutatorSchwartz A Z χ μ v i x := by
  have hs := coefficientSourceSquaredImageSchwartz_eq_commuted_add_commutator A Z χ μ
  have h₁ := coefficientCommutedImageSchwartz_eq_coefficientImageNormal A Z χ μ
    hA hZ hχ hχc hμ hμc v x i
  have h₂ := coefficientImageNormal_eq_fullAmplitude A Z χ μ
    (fun y l ↦ v l y) hA hZ hχ hμ hμc (fun l ↦ (v l).smooth ⊤) x i
  calc
    _ = coefficientCommutedImageSchwartz A Z χ μ v i x +
        coefficientSourceCommutatorSchwartz A Z χ μ v i x :=
      congrArg (fun T : (Fin d → S) →L[ℂ] (Fin d → S) ↦ T v i x) hs
    _ = _ := congrArg (fun z : ℂ ↦ z + coefficientSourceCommutatorSchwartz A Z χ μ v i x)
      (h₁.trans h₂)

end JanetCartan.ContinuumNormalReduction.ImageNormal
