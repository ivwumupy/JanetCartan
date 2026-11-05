module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.Coefficients

/-!
# The differentiated local remainder kernel

The two first-order factors in `app:ch_background:prop:bg-frame`, Step 1,
lead to the source factor and matrix kernel below. The source factor retains
the zeroth coefficient, and the output derivative acts on the entire source
factor. These definitions supply the literal kernel for the integral-action
and Sobolev estimates; their identification with `P R P*` is a separate proof.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The source factor after integration by parts against the divergence-form
adjoint in `app:ch_background:prop:bg-frame`, Step 1. The coefficient index
order is that of `coefficientFormalAdjoint`. -/
def imageNormalSourceKernel (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (j : J) (k : I) (p : E × E) : ℝ :=
  (∑ b, A p.2 b k j * fderiv ℝ K p (0, EuclideanSpace.single b 1)) +
    Z p.2 k j * K p

/-- The explicit matrix kernel after both first-order factors in
`app:ch_background:prop:bg-frame`, Step 1. Both zeroth coefficients are
retained. The derivative is joint differentiation in the output direction. -/
def imageNormalTwoFactorKernel (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (i k : I) (p : E × E) : ℝ :=
  (∑ a, ∑ j, A p.1 a i j *
    fderiv ℝ (imageNormalSourceKernel K A Z j k) p (EuclideanSpace.single a 1, 0)) +
    ∑ j, Z p.1 i j * imageNormalSourceKernel K A Z j k p

omit [Fintype J] in
/-- Smoothness of the entire source factor, needed to differentiate its
integral in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem contDiff_imageNormalSourceKernel (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hK : ContDiff ℝ ∞ K)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (j : J) (k : I) :
    ContDiff ℝ ∞ (imageNormalSourceKernel K A Z j k) := by
  apply ContDiff.add
  · exact ContDiff.sum fun b _ ↦ ((hA b k j).comp contDiff_snd).mul
      ((hK.fderiv_right (by simp)).clm_apply contDiff_const)
  · exact ((hZ k j).comp contDiff_snd).mul hK

omit [Fintype J] in
/-- Compact support of the source factor follows from the actual kernel,
without any global coefficient bound (`app:ch_background:prop:bg-frame`). -/
theorem hasCompactSupport_imageNormalSourceKernel (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hK : HasCompactSupport K) (j : J) (k : I) :
    HasCompactSupport (imageNormalSourceKernel K A Z j k) := by
  have hd (b : Fin d) : HasCompactSupport (fun p : E × E ↦
      A p.2 b k j * fderiv ℝ K p (0, EuclideanSpace.single b 1)) :=
    (hK.fderiv_apply ℝ (0, EuclideanSpace.single b 1)).mul_left
  have hz : HasCompactSupport (fun p : E × E ↦ Z p.2 k j * K p) := hK.mul_left
  convert (HasCompactSupport.finset_sum (s := Finset.univ) fun b _ ↦ hd b).add hz using 1
  ext p
  simp [imageNormalSourceKernel]

/-- Smoothness after both differential factors, for the compact-kernel
realization in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem contDiff_imageNormalTwoFactorKernel (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hK : ContDiff ℝ ∞ K)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i k : I) :
    ContDiff ℝ ∞ (imageNormalTwoFactorKernel K A Z i k) := by
  have hS := contDiff_imageNormalSourceKernel K A Z hK hA hZ
  apply ContDiff.add
  · exact ContDiff.sum fun a _ ↦ ContDiff.sum fun j _ ↦
      ((hA a i j).comp contDiff_fst).mul
        (((hS j k).fderiv_right (by simp)).clm_apply contDiff_const)
  · exact ContDiff.sum fun j _ ↦ ((hZ i j).comp contDiff_fst).mul (hS j k)

/-- Both first-order factors preserve joint compact support. This is the
support input of the bounded realization (`app:ch_background:prop:bg-frame`). -/
theorem hasCompactSupport_imageNormalTwoFactorKernel (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hK : HasCompactSupport K) (i k : I) :
    HasCompactSupport (imageNormalTwoFactorKernel K A Z i k) := by
  have hS := hasCompactSupport_imageNormalSourceKernel K A Z hK
  have hd (a : Fin d) (j : J) : HasCompactSupport (fun p : E × E ↦ A p.1 a i j *
      fderiv ℝ (imageNormalSourceKernel K A Z j k) p (EuclideanSpace.single a 1, 0)) :=
    ((hS j k).fderiv_apply ℝ (EuclideanSpace.single a 1, 0)).mul_left
  have hz (j : J) : HasCompactSupport (fun p : E × E ↦
      Z p.1 i j * imageNormalSourceKernel K A Z j k p) := (hS j k).mul_left
  convert (HasCompactSupport.finset_sum (s := Finset.univ) fun a _ ↦
    HasCompactSupport.finset_sum (s := Finset.univ) fun j _ ↦ hd a j).add
      (HasCompactSupport.finset_sum (s := Finset.univ) fun j _ ↦ hz j) using 1
  ext p
  simp [imageNormalTwoFactorKernel]

/-- The concrete differentiated Bessel remainder, with the original two
cutoffs, in `app:ch_background:prop:bg-frame`, Step 1. -/
def localizedImageNormalRemainderKernel (χ ψ : E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (i k : I) (p : E × E) : ℝ :=
  imageNormalTwoFactorKernel (fun q ↦ localizedImageBesselRemainder χ ψ q.1 q.2) A Z i k p

/-- Unconditional kernel smoothness from smooth coefficients and the actual
cube-supported masks (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_localizedImageNormalRemainderKernel
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i k : I) :
    ContDiff ℝ ∞ (localizedImageNormalRemainderKernel χ ψ A Z i k) :=
  contDiff_imageNormalTwoFactorKernel _ A Z
    (contDiff_localizedImageBesselRemainder hr χ ψ hχ hψ hχs hψs) hA hZ i k

/-- Compact support for the concrete differentiated remainder, without a
support or boundedness premise on the coefficients (`app:ch_background:prop:bg-frame`). -/
theorem hasCompactSupport_localizedImageNormalRemainderKernel
    {r : ℝ} (χ ψ : E → ℝ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (i k : I) :
    HasCompactSupport (localizedImageNormalRemainderKernel χ ψ A Z i k) :=
  hasCompactSupport_imageNormalTwoFactorKernel _ A Z
    (hasCompactSupport_localizedImageBesselRemainder_of_cube_support χ ψ hχs hψs) i k

end JanetCartan.ContinuumNormalReduction.ImageNormal
