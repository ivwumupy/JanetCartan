module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Schwartz
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors

/-!
# The two literal differential factors on Schwartz space

The factors `μ P` and `P* μ` of `app:ch_background:prop:bg-frame`, Step 1.
Only the masked coefficients multiply Schwartz functions, so no global growth
condition on the unmasked smooth arrays is needed. The divergence-form factor
keeps all derivatives of both the coefficient and the measurement cutoff.
The consumer is the literal commutator normal in `TestOperator`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory LineDeriv
open scoped SchwartzMap ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)

/-- The literal factor `μ P` as a continuous map of finite families of
Schwartz tests (`app:ch_background:prop:bg-frame`, Step 1). -/
def maskedCoefficientSchwartzCLM
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ) :
    (J → S) →L[ℂ] (I → S) :=
  ContinuousLinearMap.pi fun i ↦
    (∑ a, ∑ j, (SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((μ x * A x a i j : ℝ) : ℂ))).comp
      ((lineDerivOpCLM ℂ S (EuclideanSpace.single a (1 : ℝ))).comp (ContinuousLinearMap.proj j))) +
    ∑ j, (SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((μ x * Z x i j : ℝ) : ℂ))).comp
      (ContinuousLinearMap.proj j)

/-- The literal divergence factor `P* μ` on Schwartz tests. Derivatives
act after multiplication by `μ Aᵃ`, retaining all cutoff and coefficient
terms (`app:ch_background:prop:bg-frame`, Step 1). -/
def maskedCoefficientAdjointSchwartzCLM
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ) :
    (I → S) →L[ℂ] (J → S) :=
  ContinuousLinearMap.pi fun j ↦
    -(∑ a, ∑ i, (lineDerivOpCLM ℂ S (EuclideanSpace.single a (1 : ℝ))).comp
      ((SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((μ x * A x a i j : ℝ) : ℂ))).comp
        (ContinuousLinearMap.proj i))) +
    ∑ i, (SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((μ x * Z x i j : ℝ) : ℂ))).comp
      (ContinuousLinearMap.proj i)

private theorem maskedCoefficient_temperate (μ f : E → ℝ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (hf : ContDiff ℝ ∞ f) :
    (fun x ↦ ((μ x * f x : ℝ) : ℂ)).HasTemperateGrowth :=
  (hμc.mul_right.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).hasTemperateGrowth
    (Complex.ofRealCLM.contDiff.comp (hμ.mul hf))

omit [Fintype I] in
/-- Pointwise agreement with the actual coefficient operator, retaining its
zeroth term (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem maskedCoefficientSchwartzCLM_apply
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (u : J → S) (x : E) (i : I) :
    maskedCoefficientSchwartzCLM A Z μ u i x =
      (μ x : ℂ) * coefficientOperator A Z (fun y j ↦ u j y) x i := by
  simp only [maskedCoefficientSchwartzCLM, ContinuousLinearMap.pi_apply,
    add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,
    SchwartzMap.smulLeftCLM_apply_apply (maskedCoefficient_temperate μ _ hμ hμc (hA _ _ _)),
    SchwartzMap.smulLeftCLM_apply_apply (maskedCoefficient_temperate μ _ hμ hμc (hZ _ _)),
    LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  simp only [coefficientOperator, partialDeriv, Complex.ofReal_mul, mul_add,
    Finset.mul_sum, mul_assoc]

omit [Fintype J] in
/-- Pointwise agreement with `coefficientFormalAdjoint`, including the
coefficient and measurement-cutoff derivatives
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem maskedCoefficientAdjointSchwartzCLM_apply
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : I → S) (x : E) (j : J) :
    maskedCoefficientAdjointSchwartzCLM A Z μ v j x =
      coefficientFormalAdjoint A Z (fun y i ↦ (μ y : ℂ) * v i y) x j := by
  have he (a : Fin d) (i : I) :
      ⇑(SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((μ y * A y a i j : ℝ) : ℂ)) (v i)) =
      fun y ↦ (A y a i j : ℂ) * ((μ y : ℂ) * v i y) := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (maskedCoefficient_temperate μ _ hμ hμc (hA a i j))]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  simp only [maskedCoefficientAdjointSchwartzCLM, ContinuousLinearMap.pi_apply,
    add_apply, neg_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp only [he]
  simp only [SchwartzMap.smulLeftCLM_apply_apply
    (maskedCoefficient_temperate μ _ hμ hμc (hZ _ _)), smul_eq_mul]
  simp only [coefficientFormalAdjoint, partialDeriv, Complex.ofReal_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype J] in
/-- The masked divergence factor has compact support, even when the
original Schwartz datum is not compact (`app:ch_background:prop:bg-frame`,
Step 1). This is the compact test used by both literal Bessel multipliers. -/
theorem hasCompactSupport_maskedCoefficientAdjointSchwartzCLM
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (v : I → S) (j : J) :
    HasCompactSupport (maskedCoefficientAdjointSchwartzCLM A Z μ v j : E → ℂ) := by
  have he := funext fun x ↦ maskedCoefficientAdjointSchwartzCLM_apply A Z μ hA hZ hμ hμc v x j
  rw [he]
  exact hasCompactSupport_coefficientFormalAdjoint A Z _
    (fun _ ↦ (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right) j

/-- The two actual masked differential factors are formal Hermitian
adjoints with respect to Euclidean Lebesgue measure
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem maskedCoefficientSchwartzCLM_pairing
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (u : J → S) (v : I → S) :
    (∑ i, imageSchwartzPairing (maskedCoefficientSchwartzCLM A Z μ u i) (v i)) =
      ∑ j, imageSchwartzPairing (u j) (maskedCoefficientAdjointSchwartzCLM A Z μ v j) := by
  have hm i : ContDiff ℝ ∞ (fun y ↦ (μ y : ℂ) * v i y) :=
    (Complex.ofRealCLM.contDiff.comp hμ).mul ((v i).smooth ⊤)
  have hmc i : HasCompactSupport (fun y ↦ (μ y : ℂ) * v i y) :=
    (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right
  have h := integral_coefficientFormalAdjoint_hermitian A Z (fun y j ↦ u j y)
    (fun y i ↦ (μ y : ℂ) * v i y) hA hZ (fun j ↦ (u j).smooth ⊤) hm hmc
  have hi (f g : S) : Integrable (fun x ↦ star (f x) * g x) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (f.toLp 2 volume) (g.toLp 2 volume)).congr
    filter_upwards [f.coeFn_toLp 2, g.coeFn_toLp 2] with x hx hy
    simp only [hx, hy, RCLike.inner_apply']
    rfl
  simp only [imageSchwartzPairing_eq_integral]
  rw [← integral_finsetSum _ (fun i _ ↦ hi _ _),
    ← integral_finsetSum _ (fun j _ ↦ hi _ _)]
  simp_rw [maskedCoefficientSchwartzCLM_apply A Z μ hA hZ hμ hμc,
    maskedCoefficientAdjointSchwartzCLM_apply A Z μ hA hZ hμ hμc]
  rw [h]
  congr 1
  funext y
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

end JanetCartan.ContinuumNormalReduction.ImageNormal
