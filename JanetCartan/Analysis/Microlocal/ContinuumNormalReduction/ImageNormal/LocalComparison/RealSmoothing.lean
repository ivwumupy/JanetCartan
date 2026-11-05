module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing
public import JanetCartan.Analysis.Operator.RealQuadratures
/-!
# Real smoothing error after the two image-normal factors

Real compression of the proved complex matrix-kernel realization gives the
actual real remainder in `app:ch_background:prop:bg-frame`, Step 1. Its real
kernel proves exact compatibility with complex inclusion, for both the operator
and its literal Hilbert adjoint. The complex L²-to-H¹ bounds therefore apply
without a new analytic premise or a norm-equivalence loss. Constants are for
these fixed cutoffs and smooth coefficient arrays.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "C²" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)
local notation "R²" => Lp (EuclideanSpace ℝ I) 2 (volume : Measure E)

private theorem realCompression_adjoint (T : C² →L[ℂ] C²) :
    (realOutputCompression T).adjoint = realOutputCompression (T).adjoint := by
  have hi : (l2ComplexInclusion (ι := I) (volume : Measure E)).adjoint = l2RealPart volume := by
    rw [← l2RealPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [realOutputCompression, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictScalars_complex, l2RealPart_adjoint, hi, ContinuousLinearMap.comp_assoc]

private theorem realMatrixIntegral_inclusion
    (K : I → I → E × E → ℝ) (f : R²) (x : E) (i : I) :
    (∑ k, ∫ y, (K i k (x, y) : ℂ) * l2ComplexInclusion volume f y k) =
      ((∑ k, ∫ y, K i k (x, y) * f y k : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL f] with y hy
  change l2ComplexInclusion volume f y = euclideanComplexInclusion (f y) at hy
  simp only [hy, euclideanComplexInclusion_apply, Complex.ofReal_mul]

private theorem realCompression_ae_integral
    (T : C² →L[ℂ] C²) (K : I → I → E × E → ℝ)
    (hT : ∀ f : C², T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, (K i k (x, y) : ℂ) * f y k)) (f : R²) :
    realOutputCompression T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, K i k (x, y) * f y k) := by
  filter_upwards [euclideanRealPart.coeFn_compLpL (T (l2ComplexInclusion volume f)),
    hT (l2ComplexInclusion volume f)] with x hx hT
  change realOutputCompression T f x = euclideanRealPart _ at hx
  rw [hx, hT]
  ext i
  change (∑ k, ∫ y, (K i k (x, y) : ℂ) * l2ComplexInclusion volume f y k).re = _
  rw [realMatrixIntegral_inclusion]
  rfl

private theorem inclusion_realCompression
    (T : C² →L[ℂ] C²) (K : I → I → E × E → ℝ)
    (hT : ∀ f : C², T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, (K i k (x, y) : ℂ) * f y k)) (f : R²) :
    l2ComplexInclusion volume (realOutputCompression T f) = T (l2ComplexInclusion volume f) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL (realOutputCompression T f),
    realCompression_ae_integral T K hT f, hT (l2ComplexInclusion volume f)] with x hx hy hz
  change l2ComplexInclusion volume (realOutputCompression T f) x = euclideanComplexInclusion _ at hx
  rw [hx, hy, hz]
  ext i
  exact (realMatrixIntegral_inclusion K f x i).symm

variable {r : ℝ} (hr : r < 1 / 2) (χ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : EuclideanSpace ℝ (Fin d) → Fin d → Matrix I J ℝ)
    (Z : EuclideanSpace ℝ (Fin d) → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
local notation "T" => localizedImageNormalRemainderOperator (I := I) (J := J) (d := d) hr χ ψ hχ hψ hχs hψs A Z hA hZ
local notation "K" => localizedImageNormalRemainderKernel χ ψ A Z

/-- The bounded real realization of `P R P*` for the localized Bessel kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
def realLocalizedImageNormalRemainderOperator : R² →L[ℝ] R² :=
  realOutputCompression
    (localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ)
local notation "R" => realLocalizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ

/-- The literal real Hilbert adjoint is compression of the complex adjoint
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realLocalizedImageNormalRemainderOperator_adjoint :
    (R).adjoint = realOutputCompression (T).adjoint := realCompression_adjoint T

/-- The real remainder integrates the actual two-factor matrix kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realLocalizedImageNormalRemainderOperator_ae_integral (f : R²) :
    R f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, K i k (x, y) * f y k) :=
  realCompression_ae_integral T K
    (localizedImageNormalRemainderOperator_ae_integral hr χ ψ hχ hψ hχs hψs A Z hA hZ) f

/-- The real Hilbert adjoint reverses spatial arguments and transposes matrix
indices, retaining every coefficient term (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realLocalizedImageNormalRemainderOperator_adjoint_ae_integral (f : R²) :
    (R).adjoint f =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (fun k ↦ ∑ i, ∫ x, K i k (x, y) * f x i) := by
  rw [realLocalizedImageNormalRemainderOperator_adjoint]
  exact realCompression_ae_integral (T).adjoint (fun k i p ↦ K i k p.swap)
    (localizedImageNormalRemainderOperator_adjoint_ae_integral hr χ ψ hχ hψ hχs hψs A Z hA hZ) f

/-- Complexification intertwines the real and complex remainders, proved from
the real kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem l2ComplexInclusion_realLocalizedImageNormalRemainderOperator (f : R²) :
    l2ComplexInclusion volume (R f) = T (l2ComplexInclusion volume f) :=
  inclusion_realCompression T K
    (localizedImageNormalRemainderOperator_ae_integral hr χ ψ hχ hψ hχs hψs A Z hA hZ) f

/-- Complexification also intertwines the literal Hilbert adjoints
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem l2ComplexInclusion_realLocalizedImageNormalRemainderOperator_adjoint (f : R²) :
    l2ComplexInclusion volume ((R).adjoint f) = (T).adjoint (l2ComplexInclusion volume f) := by
  rw [realLocalizedImageNormalRemainderOperator_adjoint]
  exact inclusion_realCompression (T).adjoint (fun k i p ↦ K i k p.swap)
    (localizedImageNormalRemainderOperator_adjoint_ae_integral hr χ ψ hχ hψ hχs hψs A Z hA hZ) f

/-- The real remainder and its Hilbert adjoint map L² to H¹ with a common
finite constant (`app:ch_background:prop:bg-frame`, Step 1). The Sobolev norms
are those of the literal complexified real outputs. No uniform tame dependence
on varying coefficients is claimed. -/
theorem realLocalizedImageNormalRemainderOperator_sobolev_one_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : R²,
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume (R f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (R f)) ≤ C * ‖f‖ ∧
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume ((R).adjoint f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume ((R).adjoint f)) ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hT⟩ := localizedImageNormalRemainderOperator_sobolev_one_bounds
    hr χ ψ hχ hψ hχs hψs A Z hA hZ
  refine ⟨C, hC, fun f ↦ ?_⟩
  rw [l2ComplexInclusion_realLocalizedImageNormalRemainderOperator,
    l2ComplexInclusion_realLocalizedImageNormalRemainderOperator_adjoint]
  have hb : ‖l2ComplexInclusion volume f‖ ≤ ‖f‖ := by
    simpa using (l2ComplexInclusion volume).le_of_opNorm_le
      (l2ComplexInclusion_norm_le volume) f
  exact ⟨(hT _).1, (hT _).2.1.trans (mul_le_mul_of_nonneg_left hb hC),
    (hT _).2.2.1, (hT _).2.2.2.trans (mul_le_mul_of_nonneg_left hb hC)⟩

/-- The real remainder is `P R P*` on compact real Schwartz tests, with the
literal divergence-form formal adjoint (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realLocalizedImageNormalRemainderOperator_schwartz_ae_coefficientOperator
    (v : 𝓢(E, EuclideanSpace ℝ I)) (hc : HasCompactSupport (v : E → EuclideanSpace ℝ I)) :
    l2ComplexInclusion volume (R (v.toLp 2 volume)) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (coefficientOperator A Z
        (fun z j ↦ ∫ y, (localizedImageBesselRemainder χ ψ z y : ℂ) *
          coefficientFormalAdjoint A Z (fun y i ↦ (v y i : ℂ)) y j) x) := by
  rw [l2ComplexInclusion_realLocalizedImageNormalRemainderOperator]
  apply localizedImageNormalRemainderOperator_ae_coefficientOperator
    hr χ ψ hχ hψ hχs hψs A Z hA hZ (fun y i ↦ (v y i : ℂ))
  · intro i
    exact Complex.ofRealCLM.contDiff.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : I ↦ ℝ) i).contDiff.comp (v.smooth ⊤))
  · intro i
    exact hc.comp_left (g := fun z : EuclideanSpace ℝ I ↦ (z i : ℂ)) (by simp)
  · filter_upwards [euclideanComplexInclusion.coeFn_compLpL (v.toLp 2 volume),
      v.coeFn_toLp 2 volume] with x hx hy
    change l2ComplexInclusion volume (v.toLp 2 volume) x =
      euclideanComplexInclusion ((v.toLp 2 volume) x) at hx
    rw [hx, hy]
    rfl

end JanetCartan.ContinuumNormalReduction.ImageNormal
