module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.IntegrationByParts

/-!
# Testing the literal matrix adjoint

Integration by parts for the actual coefficient arrays in
`app:ch_background:prop:bg-frame`, Step 1. The source test may include the
measurement mask. No adjoint identity is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Smooth coefficients send a smooth test to a smooth literal adjoint.
This supplies the test regularity for the image Bessel factors
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_coefficientFormalAdjoint
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ) (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i)) (j : J) :
    ContDiff ℝ ∞ (fun x ↦ coefficientFormalAdjoint A Z v x j) := by
  apply ContDiff.add (ContDiff.neg ?_) ?_
  · exact ContDiff.sum fun a _ ↦ ContDiff.sum fun i _ ↦
      ((((Complex.ofRealCLM.contDiff.comp (hA a i j)).mul (hv i)).fderiv_right
        (by simp)).clm_apply contDiff_const)
  · exact ContDiff.sum fun i _ ↦ (Complex.ofRealCLM.contDiff.comp (hZ i j)).mul (hv i)

/-- The divergence-form adjoint preserves compact support of the test,
so there are no boundary contributions in the fixed chart
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_coefficientFormalAdjoint
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ) (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (j : J) :
    HasCompactSupport (fun x ↦ coefficientFormalAdjoint A Z v x j) := by
  have hd (a : Fin d) (i : I) : HasCompactSupport
      (fun y ↦ partialDeriv (fun z ↦ (A z a i j : ℂ) * v z i) y a) :=
    (hc i).mul_left.fderiv_apply ℝ (EuclideanSpace.single a 1)
  have hz (i : I) : HasCompactSupport (fun y ↦ (Z y i j : ℂ) * v y i) :=
    (hc i).mul_left
  convert
    ((HasCompactSupport.finset_sum (s := Finset.univ) fun a _ ↦
      HasCompactSupport.finset_sum (s := Finset.univ) fun i _ ↦ hd a i).neg.add
        (HasCompactSupport.finset_sum (s := Finset.univ) fun i _ ↦ hz i)) using 1
  ext x
  simp [coefficientFormalAdjoint]

/-- Columnwise testing of the full divergence-form matrix adjoint. The
zeroth term is counted once, independently of the coordinate dimension
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_coefficientFormalAdjoint_column
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (f : E → ℂ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hf : ContDiff ℝ ∞ f) (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (j : J) :
    (∫ y, f y * coefficientFormalAdjoint A Z v y j) =
      ∫ y, ∑ i, ((∑ a, (A y a i j : ℂ) * partialDeriv f y a) +
        (Z y i j : ℂ) * f y) * v y i := by
  have hAv a i : ContDiff ℝ ∞ (fun y ↦ (A y a i j : ℂ) * v y i) :=
    (Complex.ofRealCLM.contDiff.comp (hA a i j)).mul (hv i)
  have hD a i : Integrable (fun y ↦ f y *
      partialDeriv (fun z ↦ (A z a i j : ℂ) * v z i) y a) :=
    (hf.continuous.mul (((hAv a i).continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
      (((hc i).mul_left.fderiv_apply ℝ (EuclideanSpace.single a 1)).mul_left)
  have hT a i : Integrable (fun y ↦ (A y a i j : ℂ) * partialDeriv f y a * v y i) :=
    (((Complex.ofRealCLM.continuous.comp (hA a i j).continuous).mul
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)).mul
      (hv i).continuous).integrable_of_hasCompactSupport (hc i).mul_left
  have hW i : Integrable (fun y ↦ (Z y i j : ℂ) * f y * v y i) :=
    (((Complex.ofRealCLM.continuous.comp (hZ i j).continuous).mul hf.continuous).mul
      (hv i).continuous).integrable_of_hasCompactSupport (hc i).mul_left
  have hparts a i : -(∫ y, f y *
      partialDeriv (fun z ↦ (A z a i j : ℂ) * v z i) y a) =
      ∫ y, (A y a i j : ℂ) * partialDeriv f y a * v y i := by
    rw [NormalComparison.CompactTransport.integral_mul_partialDeriv hf (hAv a i)
      (hc i).mul_left a, neg_neg]
    congr 1
    funext y
    ring
  simp only [coefficientFormalAdjoint, mul_add, mul_neg, Finset.mul_sum, add_mul,
    Finset.sum_mul]
  simp_rw [show ∀ y i, f y * ((Z y i j : ℂ) * v y i) =
    (Z y i j : ℂ) * f y * v y i by intros; ring]
  erw [integral_add ((integrable_finsetSum Finset.univ (fun a _ ↦
    integrable_finsetSum Finset.univ (fun i _ ↦ hD a i))).neg)
    (integrable_finsetSum Finset.univ (fun i _ ↦ hW i)), integral_neg]
  rw [integral_finsetSum Finset.univ (fun a _ ↦ integrable_finsetSum Finset.univ (fun i _ ↦ hD a i))]
  simp_rw [integral_finsetSum Finset.univ (fun i _ ↦ hD _ i)]
  simp only [← Finset.sum_neg_distrib]
  simp_rw [hparts]
  erw [integral_finsetSum Finset.univ (fun i _ ↦ hW i),
    integral_finsetSum Finset.univ (fun i _ ↦ (integrable_finsetSum Finset.univ (fun a _ ↦ hT a i)).add (hW i))]
  have hsum i : (∫ y, (∑ a, (A y a i j : ℂ) * partialDeriv f y a * v y i) +
      (Z y i j : ℂ) * f y * v y i) =
      (∫ y, ∑ a, (A y a i j : ℂ) * partialDeriv f y a * v y i) +
      ∫ y, (Z y i j : ℂ) * f y * v y i := by
    exact integral_add (integrable_finsetSum Finset.univ (fun a _ ↦ hT a i)) (hW i)
  simp only [Pi.add_apply]
  simp_rw [hsum, integral_finsetSum Finset.univ (fun a _ ↦ hT a _), Finset.sum_add_distrib]
  rw [Finset.sum_comm]

/-- The Fourier source phase converts the literal matrix adjoint into
`-i M(y,2πξ)ᵀ + Z(y)ᵀ`, including every variable coefficient
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_sourcePhase_coefficientFormalAdjoint
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (x ξ : E) (j : J) :
    (∫ y, (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) * coefficientFormalAdjoint A Z v y j) =
      ∫ y, (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
        ∑ i, (-Complex.I * differentialPencil A y ((2 * Real.pi) • ξ) i j +
          Z y i j) * v y i := by
  have hf : ContDiff ℝ ∞ (fun y ↦ (Real.fourierChar ⟪ξ, x - y⟫ : ℂ)) :=
    Pseudodifferential.contDiff_fourierChar.comp ((innerSL ℝ ξ).contDiff.comp
      (contDiff_const.sub contDiff_id))
  rw [integral_coefficientFormalAdjoint_column A Z _ v hA hZ hf hv hc j]
  congr 1
  funext y
  simp only [partialDeriv_sourceFourierPhase, differentialPencil, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, mul_add, add_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    ring
  · ring


variable [Fintype J]

/-- The full matrix integration-by-parts identity, with no compact-support
assumption on the field in the differentiated slot. The compact source slot
supplies all boundary cancellation (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_coefficientFormalAdjoint_pairing
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (u : E → J → ℂ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hu : ∀ j, ContDiff ℝ ∞ (fun x ↦ u x j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) :
    (∫ y, ∑ j, u y j * coefficientFormalAdjoint A Z v y j) =
      ∫ y, ∑ i, coefficientOperator A Z u y i * v y i := by
  have hL j : Integrable (fun y ↦ u y j * coefficientFormalAdjoint A Z v y j) :=
    ((hu j).continuous.mul (contDiff_coefficientFormalAdjoint A Z v hA hZ hv j).continuous).integrable_of_hasCompactSupport (hasCompactSupport_coefficientFormalAdjoint A Z v hc j).mul_left
  have hR j : Integrable (fun y ↦ ∑ i,
      ((∑ a, (A y a i j : ℂ) * partialDeriv (fun z ↦ u z j) y a) +
        (Z y i j : ℂ) * u y j) * v y i) := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply Continuous.integrable_of_hasCompactSupport _ (hc i).mul_left
    apply Continuous.mul _ (hv i).continuous
    apply Continuous.add
    · exact continuous_finsetSum _ fun a _ ↦
        (Complex.ofRealCLM.continuous.comp (hA a i j).continuous).mul
          (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const)
    · exact (Complex.ofRealCLM.continuous.comp (hZ i j).continuous).mul (hu j).continuous
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hL j)]
  simp_rw [integral_coefficientFormalAdjoint_column A Z _ v hA hZ (hu _) hv hc]
  rw [← integral_finsetSum Finset.univ (fun j _ ↦ hR j)]
  congr 1
  funext y
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coefficientOperator, add_mul, Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

omit [Fintype I] in
/-- Real coefficient arrays commute with complex conjugation. This turns
the bilinear integration-by-parts formula into the Hermitian adjoint formula
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientOperator_conj
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (u : E → J → ℂ) (x : E) (i : I) :
    coefficientOperator A Z (fun y j ↦ star (u y j)) x i =
      star (coefficientOperator A Z u x i) := by
  have hd j a : partialDeriv (fun y ↦ star (u y j)) x a =
      star (partialDeriv (fun y ↦ u y j) x a) := by
    change (fderiv ℝ (Complex.conjCLE ∘ (fun y ↦ u y j)) x) _ = _
    rw [Complex.conjCLE.comp_fderiv]
    rfl
  unfold coefficientOperator
  simp_rw [hd]
  simp [star_add, star_sum, star_mul, mul_comm]

/-- The literal divergence operator is the complex Hilbert-space formal
adjoint on compact smooth tests, proved from the coefficient arrays
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_coefficientFormalAdjoint_hermitian
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (u : E → J → ℂ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hu : ∀ j, ContDiff ℝ ∞ (fun x ↦ u x j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) :
    (∫ y, ∑ j, star (u y j) * coefficientFormalAdjoint A Z v y j) =
      ∫ y, ∑ i, star (coefficientOperator A Z u y i) * v y i := by
  have h := integral_coefficientFormalAdjoint_pairing A Z (fun y j ↦ star (u y j)) v
    hA hZ (fun j ↦ Complex.conjCLE.contDiff.comp (hu j)) hv hc
  simpa only [coefficientOperator_conj] using h

end JanetCartan.ContinuumNormalReduction.ImageNormal
