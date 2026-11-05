module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.Plateau

/-!
# Differentiating the one-factor remainder

The output differentiation in `app:ch_background:prop:bg-frame`, Step 1,
retains the zeroth-order coefficient and the original source mask. Compactness
comes from the kernel; the unmasked smooth input need not have compact support.
The consumer is the Schwartz action of the actual periodic image channel.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff SchwartzMap

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integrable_kernel_test (K : E × E → ℝ)
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (w : E → ℂ) (hw : Continuous w) (x : E) :
    Integrable (fun y ↦ (K (x, y) : ℂ) * w y) := by
  apply FourierIntegral.GraphDifferentiation.integrable_section
    (U := univ) (f := fun p : E × E ↦ (K p : ℂ) * w p.2)
    (hKc.image continuous_snd)
    ((Complex.continuous_ofReal.comp hK).mul (hw.comp continuous_snd)).continuousOn
    _ (mem_univ x)
  intro z _ y hy
  have hp : (z, y) ∉ tsupport K := fun hp ↦ hy ⟨(z, y), hp, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport hp]

/-- The actual first-order output factor differentiates the compact lattice
kernel under its integral. No compact-support premise is imposed on the input
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem maskedCoefficientOperator_oneFactorRemainder_integral
    {R : ℝ} (hR : R < 1 / 2) (ρ χ μ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ R)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ R)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (v : E → Fin d → ℂ) (hv : ∀ j, ContDiff ℝ ∞ (fun y ↦ v y j))
    (x : E) (i : Fin d) :
    (μ x : ℂ) * coefficientOperator A Z
      (fun z j ↦ ∫ y, (localizedImageBesselRemainder ρ χ z y : ℂ) * v y j) x i =
      ∑ j, ∫ y, (oneFactorRemainderKernel ρ χ μ A Z i j (x, y) : ℂ) * v y j := by
  let K := fun p : E × E ↦ localizedImageBesselRemainder ρ χ p.1 p.2
  have hK : ContDiff ℝ ∞ K :=
    contDiff_localizedImageBesselRemainder hR ρ χ hρ hχ hρs hχs
  have hKc : HasCompactSupport K :=
    hasCompactSupport_localizedImageBesselRemainder_of_cube_support ρ χ hρs hχs
  have hV (j : Fin d) : Integrable (fun y ↦ (K (x, y) : ℂ) * v y j) :=
    integrable_kernel_test K hK.continuous hKc _ (hv j).continuous x
  have hD (a j : Fin d) : Integrable (fun y ↦
      (fderiv ℝ K (x, y) (EuclideanSpace.single a 1, 0) : ℂ) * v y j) := by
    have hdK : ContDiff ℝ ∞ (fun p ↦
        fderiv ℝ K p (EuclideanSpace.single a 1, 0)) :=
      (hK.fderiv_right (by simp)).clm_apply contDiff_const
    apply integrable_kernel_test _ hdK.continuous _ _ (hv j).continuous x
    exact (hKc.fderiv ℝ).comp_left (g := fun L ↦ L (EuclideanSpace.single a 1, 0)) rfl
  have hT (a j : Fin d) : Integrable (fun y ↦ (A x a i j : ℂ) *
      (fderiv ℝ K (x, y) (EuclideanSpace.single a 1, 0) : ℂ) * v y j) := by
    simpa only [mul_assoc] using (hD a j).const_mul (A x a i j : ℂ)
  have hZ (j : Fin d) : Integrable (fun y ↦
      (Z x i j : ℂ) * (K (x, y) : ℂ) * v y j) := by
    simpa only [mul_assoc] using (hV j).const_mul (Z x i j : ℂ)
  have hentry (j : Fin d) :
      (∫ y, (oneFactorRemainderKernel ρ χ μ A Z i j (x, y) : ℂ) * v y j) =
      (μ x : ℂ) * ((∑ a, (A x a i j : ℂ) *
        ∫ y, (fderiv ℝ K (x, y) (EuclideanSpace.single a 1, 0) : ℂ) * v y j) +
        (Z x i j : ℂ) * ∫ y, (K (x, y) : ℂ) * v y j) := by
    simp only [oneFactorRemainderKernel, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_sum, add_mul, Finset.sum_mul, mul_assoc]
    rw [integral_const_mul, integral_add
      (integrable_finsetSum Finset.univ fun a _ ↦ by simpa only [mul_assoc] using hT a j)
      (by simpa only [mul_assoc] using hZ j),
      integral_finsetSum Finset.univ
        (fun a _ ↦ by simpa only [mul_assoc] using hT a j)]
    simp only [integral_const_mul, K]
  simp only [coefficientOperator]
  change (μ x : ℂ) * ((∑ a, ∑ j, (A x a i j : ℂ) *
    partialDeriv (fun z ↦ ∫ y, (K (z, y) : ℂ) * v y j) x a) +
    ∑ j, (Z x i j : ℂ) * ∫ y, (K (x, y) : ℂ) * v y j) = _
  simp_rw [partialDeriv_imageNormal_kernel_integral K hK hKc _ (hv _) x, hentry]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]


private theorem coefficientOperator_add_differentiable
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (u v : E → Fin d → ℂ) (x : E)
    (hu : ∀ j, DifferentiableAt ℝ (fun y ↦ u y j) x)
    (hv : ∀ j, DifferentiableAt ℝ (fun y ↦ v y j) x) (i : Fin d) :
    coefficientOperator A Z (fun y j ↦ u y j + v y j) x i =
      coefficientOperator A Z u x i + coefficientOperator A Z v x i := by
  simp only [coefficientOperator, partialDeriv, fderiv_fun_add (hu _) (hv _),
    add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- Once the localized Bessel comparison has been proved for a physical
representative, legitimate differentiation and the output plateau give the
one-factor channel formula. The remaining periodic construction must supply
this scalar Bessel comparison for its actual H¹ lift
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem maskedCoefficientOperator_eq_channelSchwartz_add_remainder
    {R : ℝ} (hR : R < 1 / 2) (ρ χ μ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ R)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ R)
    (hμc : HasCompactSupport μ)
    (hplateau : ∀ x ∈ tsupport μ, ρ =ᶠ[nhds x] (fun _ ↦ 1))
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (v : Fin d → 𝓢(E, ℂ)) (u : E → Fin d → ℂ)
    (hcomparison : ∀ x j, (ρ x : ℂ) * u x j =
      (ρ x : ℂ) * imageBesselSchwartzCLM
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) (v j)) x +
      ∫ y, (localizedImageBesselRemainder ρ χ x y : ℂ) * v j y)
    (x : E) (i : Fin d) :
    (μ x : ℂ) * coefficientOperator A Z u x i =
      channelSchwartz A Z χ μ v i x +
      ∑ j, ∫ y, (oneFactorRemainderKernel ρ χ μ A Z i j (x, y) : ℂ) * v j y := by
  let b (j : Fin d) := imageBesselSchwartzCLM
    (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) (v j))
  let K := fun p : E × E ↦ localizedImageBesselRemainder ρ χ p.1 p.2
  let e : E → Fin d → ℂ := fun z j ↦ ∫ y, (K (z, y) : ℂ) * v j y
  have hK : ContDiff ℝ ∞ K :=
    contDiff_localizedImageBesselRemainder hR ρ χ hρ hχ hρs hχs
  have hKc : HasCompactSupport K :=
    hasCompactSupport_localizedImageBesselRemainder_of_cube_support ρ χ hρs hχs
  have he : (fun y j ↦ (ρ y : ℂ) * u y j) =
      (fun y j ↦ (ρ y : ℂ) * b j y + e y j) := by
    funext y j
    exact hcomparison y j
  have hb (j : Fin d) : DifferentiableAt ℝ (fun y ↦ (ρ y : ℂ) * b j y) x :=
    ((Complex.ofRealCLM.contDiff.comp hρ).mul ((b j).smooth ⊤)).differentiable
      (by simp) x
  have hd (j : Fin d) : DifferentiableAt ℝ (fun y ↦ e y j) x :=
    differentiableAt_imageNormal_kernel_integral K hK hKc (v j) ((v j).smooth ⊤) x
  rw [← maskedCoefficientOperator_plateau ρ μ hplateau A Z u x i, he,
    coefficientOperator_add_differentiable A Z _ _ x hb hd i, mul_add,
    maskedCoefficientOperator_plateau ρ μ hplateau A Z (fun y j ↦ b j y) x i]
  have hc : channelSchwartz A Z χ μ v i x =
      (μ x : ℂ) * coefficientOperator A Z (fun y j ↦ b j y) x i :=
    maskedCoefficientSchwartzCLM_apply A Z μ hA hZ hμ hμc b x i
  rw [← hc]
  congr 1
  exact maskedCoefficientOperator_oneFactorRemainder_integral hR ρ χ μ hρ hχ hρs hχs
    A Z (fun y j ↦ v j y) (fun j ↦ (v j).smooth ⊤) x i

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
