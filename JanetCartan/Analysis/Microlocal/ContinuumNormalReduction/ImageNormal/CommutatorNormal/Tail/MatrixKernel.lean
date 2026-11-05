module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.ScalarAction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Action

/-!
# The literal differentiated tail kernel

The two-factor integration-by-parts formula in `app:ch_background:prop:bg-frame`,
Step 1, applies to the compact scalar kernel and the compact test `μv`.
The resulting matrix kernel includes both measurement masks, the source-square
derivatives, and all zeroth-order coefficients. The derivatives of `μ` and `A`
in `P* (μv)` are retained until the proved integration by parts is applied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)

/-- The literal real matrix kernel after both differential factors of the
intermediate-localization tail (`app:ch_background:prop:bg-frame`, Step 1).
`imageNormalTwoFactorKernel` differentiates the entire localized scalar kernel. -/
def coefficientSourceCommutatorTailKernel
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (i k : I) (p : E × E) : ℝ :=
  μ p.1 * μ p.2 * imageNormalTwoFactorKernel (localizedImageCommutatorTailKernel χ β) A Z i k p

omit [Fintype I] in
/-- Smoothness of the actual matrix tail from the primitive smooth arrays,
cutoffs, and plateau gap (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_coefficientSourceCommutatorTailKernel
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) (i k : I) :
    ContDiff ℝ ∞ (coefficientSourceCommutatorTailKernel A Z χ μ β i k) :=
  ((hμ.comp contDiff_fst).mul (hμ.comp contDiff_snd)).mul
    (contDiff_imageNormalTwoFactorKernel _ A Z
      (contDiff_localizedImageCommutatorTailKernel χ β hχ hχc hβ hβc hδ hplateau) hA hZ i k)

omit [Fintype I] in
/-- Joint compact support for each matrix entry follows from the literal
scalar kernel; no global coefficient bounds are needed
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_coefficientSourceCommutatorTailKernel
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hχc : HasCompactSupport χ) (hβc : HasCompactSupport β) (i k : I) :
    HasCompactSupport (coefficientSourceCommutatorTailKernel A Z χ μ β i k) :=
  (hasCompactSupport_imageNormalTwoFactorKernel _ A Z
    (hasCompactSupport_localizedImageCommutatorTailKernel χ β hχc hβc) i k).mul_left

omit [Fintype J] in
/-- The divergence-form source factor vanishes off the measurement support,
including every coefficient and measurement-cutoff derivative
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem maskedCoefficientAdjointSchwartzCLM_eq_zero_off_tsupport
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : I → S) (y : E) (hy : y ∉ tsupport μ) (j : J) :
    maskedCoefficientAdjointSchwartzCLM A Z μ v j y = 0 := by
  rw [maskedCoefficientAdjointSchwartzCLM_apply A Z μ hA hZ hμ hμc]
  have hn : μ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy
  have hd (a : Fin d) (i : I) : partialDeriv
      (fun z ↦ (A z a i j : ℂ) * ((μ z : ℂ) * v i z)) y a = 0 := by
    have he : (fun z ↦ (A z a i j : ℂ) * ((μ z : ℂ) * v i z)) =ᶠ[𝓝 y] 0 := by
      filter_upwards [hn] with z hz
      simp [show μ z = 0 from hz]
    rw [partialDeriv, he.fderiv_eq]
    simp
  simp only [coefficientFormalAdjoint, hd, Finset.sum_const_zero, neg_zero,
    image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]

/-- The published Schwartz tail equals integration against the literal
smooth compact matrix kernel. This discharges the test-action identity,
including all source and output differentiation
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailSchwartz_eq_integral
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (hβμ : ∀ y ∈ tsupport μ, β y = 1) (v : I → S) (x : E) (i : I) :
    coefficientSourceCommutatorTailSchwartz A Z χ μ β v i x =
      ∑ k, ∫ y, (coefficientSourceCommutatorTailKernel A Z χ μ β i k (x, y) : ℂ) * v k y := by
  let q := maskedCoefficientAdjointSchwartzCLM A Z μ v
  let K := localizedImageCommutatorTailKernel χ β
  have hK : ContDiff ℝ ∞ K :=
    contDiff_localizedImageCommutatorTailKernel χ β hχ hχc hβ hβc hδ hplateau
  have hKc : HasCompactSupport K :=
    hasCompactSupport_localizedImageCommutatorTailKernel χ β hχc hβc
  have hq (j : J) (y : E) (hy : q j y ≠ 0) : β y = 1 := by
    apply hβμ
    by_contra hn
    exact hy (maskedCoefficientAdjointSchwartzCLM_eq_zero_off_tsupport
      A Z μ hA hZ hμ hμc v y hn j)
  have he (j : J) :
      (fun z ↦ SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y) ^ 2 : ℂ))
        (imageBesselSchwartzCLM (imageBesselSchwartzCLM (q j) -
          SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) (imageBesselSchwartzCLM (q j)))) z) =
      fun z ↦ ∫ y, (K (z, y) : ℂ) *
        coefficientFormalAdjoint A Z (fun y k ↦ (μ y : ℂ) * v k y) y j := by
    funext z
    rw [localizedImageCommutatorTailKernel_schwartz_action χ β hχ hχc hβ hβc hδ hplateau
      (q j) (hq j)]
    apply integral_congr_ae
    exact ae_of_all _ fun y ↦ congrArg (fun w : ℂ ↦ (K (z, y) : ℂ) * w)
      (maskedCoefficientAdjointSchwartzCLM_apply A Z μ hA hZ hμ hμc v y j)
  change maskedCoefficientSchwartzCLM A Z μ _ i x = _
  rw [maskedCoefficientSchwartzCLM_apply A Z μ hA hZ hμ hμc]
  have he' : (fun z j ↦ SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y) ^ 2 : ℂ))
        (imageBesselSchwartzCLM (imageBesselSchwartzCLM (q j) -
          SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) (imageBesselSchwartzCLM (q j)))) z) =
      fun z j ↦ ∫ y, (K (z, y) : ℂ) *
        coefficientFormalAdjoint A Z (fun y k ↦ (μ y : ℂ) * v k y) y j := by
    funext z j
    exact congrFun (he j) z
  change (μ x : ℂ) * coefficientOperator A Z
    (fun z j ↦ SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y) ^ 2 : ℂ))
      (imageBesselSchwartzCLM (imageBesselSchwartzCLM (q j) -
        SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) (imageBesselSchwartzCLM (q j)))) z) x i = _
  rw [he', coefficientOperator_integral_coefficientFormalAdjoint K A Z (fun y k ↦ (μ y : ℂ) * v k y) hK hKc hA hZ
    (fun k ↦ (Complex.ofRealCLM.contDiff.comp hμ).mul ((v k).smooth ⊤))
    (fun _ ↦ (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [coefficientSourceCommutatorTailKernel, Complex.ofReal_mul]
  change (μ x : ℂ) * ((imageNormalTwoFactorKernel K A Z i k (x, y) : ℂ) * ((μ y : ℂ) * v k y)) = _
  ring

end JanetCartan.ContinuumNormalReduction.ImageNormal
