module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Basic
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Action.Integral

/-!
# The differentiated one-factor lattice kernel

The one-factor comparison in `app:ch_background:prop:bg-frame`, Step 1,
uses `μ P R(ρ,χ)`, where `ρ` is one on a neighborhood of the measurement
support. The source cutoff is differentiated neither here nor in the channel.
These concrete kernel facts supply the bounded real realization and its
literal adjoint. Identification with the periodic channel remains a separate
obligation, using the weak periodic coefficient operator.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual nonzero-lattice remainder after the output factor `μ P`.
The auxiliary output cutoff `ρ` stays inside the differentiated expression;
its derivative defects cancel only after proving its plateau property
(`app:ch_background:prop:bg-frame`, Step 1). -/
def oneFactorRemainderKernel (ρ χ μ : E → ℝ)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (p : E × E) : ℝ :=
  let K := fun q : E × E ↦ localizedImageBesselRemainder ρ χ q.1 q.2
  μ p.1 * ((∑ a, A p.1 a i j *
    fderiv ℝ K p (EuclideanSpace.single a 1, 0)) + Z p.1 i j * K p)

/-- Smoothness of every entry of the actual one-factor remainder, from
the proved lattice-series regularity and the fixed smooth coefficients
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_oneFactorRemainderKernel
    {r : ℝ} (hr : r < 1 / 2) (ρ χ μ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i j : Fin d) :
    ContDiff ℝ ∞ (oneFactorRemainderKernel ρ χ μ A Z i j) := by
  have hK := contDiff_localizedImageBesselRemainder hr ρ χ hρ hχ hρs hχs
  apply (hμ.comp contDiff_fst).mul
  apply ContDiff.add
  · exact ContDiff.sum fun a _ ↦ ((hA a i j).comp contDiff_fst).mul
      ((hK.fderiv_right (by simp)).clm_apply contDiff_const)
  · exact ((hZ i j).comp contDiff_fst).mul hK

/-- Output differentiation does not enlarge the original source support,
and multiplication by `μ` retains the actual measurement support. This is
the support input for `normalCrossTerms_periodic_endpoints`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem tsupport_oneFactorRemainderKernel_subset
    (ρ χ μ : E → ℝ)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    tsupport (oneFactorRemainderKernel ρ χ μ A Z i j) ⊆
      tsupport μ ×ˢ tsupport χ := by
  apply closure_minimal _ ((isClosed_tsupport μ).prod (isClosed_tsupport χ))
  intro p hp
  constructor
  · by_contra hn
    exact hp (by simp [oneFactorRemainderKernel, image_eq_zero_of_notMem_tsupport hn])
  · by_contra hn
    have hK : p ∉ tsupport (fun q : E × E ↦ localizedImageBesselRemainder ρ χ q.1 q.2) :=
      fun h ↦ hn ((tsupport_localizedImageBesselRemainder_subset ρ χ h).2)
    exact hp (by simp [oneFactorRemainderKernel, fderiv_of_notMem_tsupport ℝ hK,
      image_eq_zero_of_notMem_tsupport hK])

/-- Compactness of the concrete kernel uses only the original source and
measurement supports; no coefficient boundedness is assumed. This supplies
the actual L² realization in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem hasCompactSupport_oneFactorRemainderKernel
    {r : ℝ} (ρ χ μ : E → ℝ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hμs : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    HasCompactSupport (oneFactorRemainderKernel ρ χ μ A Z i j) :=
  ((hasCompactSupport_of_imageBessel_cube_support μ hμs).isCompact.prod
    (hasCompactSupport_of_imageBessel_cube_support χ hχs).isCompact).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_oneFactorRemainderKernel_subset ρ χ μ A Z i j)

/-- The literal reversed, transposed entry is smooth, as needed for the
real Hilbert adjoint's H¹ gain (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_oneFactorRemainderKernel_reverse
    {r : ℝ} (hr : r < 1 / 2) (ρ χ μ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i j : Fin d) :
    ContDiff ℝ ∞ (fun p : E × E ↦ oneFactorRemainderKernel ρ χ μ A Z i j p.swap) :=
  (contDiff_oneFactorRemainderKernel hr ρ χ μ hρ hχ hμ hρs hχs A Z hA hZ i j).comp
    (contDiff_snd.prodMk contDiff_fst)

/-- Reversing the arguments retains compact support, for the literal real
adjoint in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem hasCompactSupport_oneFactorRemainderKernel_reverse
    {r : ℝ} (ρ χ μ : E → ℝ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hμs : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    HasCompactSupport (fun p : E × E ↦ oneFactorRemainderKernel ρ χ μ A Z i j p.swap) :=
  (hasCompactSupport_oneFactorRemainderKernel ρ χ μ hχs hμs A Z i j).comp_homeomorph
    (Homeomorph.prodComm E E)

/-- The concrete complex matrix-kernel realization of the differentiated
one-factor remainder. Every scalar block is the existing bounded compact
kernel operator, rather than a subtraction of channel operators
(`app:ch_background:prop:bg-frame`, Step 1). -/
def complexOneFactorRemainderOperator
    {r : ℝ} (hr : r < 1 / 2) (ρ χ μ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hμs : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) :
    PeriodicLocalL2.EuclideanL2 d (EuclideanSpace ℂ (Fin d)) →L[ℂ]
      PeriodicLocalL2.EuclideanL2 d (EuclideanSpace ℂ (Fin d)) :=
  Pseudodifferential.vectorMatrixL2Operator fun i j ↦
    imageNormalRealKernelOperator (oneFactorRemainderKernel ρ χ μ A Z i j)
      (contDiff_oneFactorRemainderKernel hr ρ χ μ hρ hχ hμ hρs hχs A Z hA hZ i j).continuous
      (hasCompactSupport_oneFactorRemainderKernel ρ χ μ hχs hμs A Z i j)

/-- The actual real one-factor lattice remainder, constructed by real
compression of its explicit real matrix kernel. The integral action and the
paired H¹ estimates are further obligations of this construction
(`app:ch_background:prop:bg-frame`, Step 1). -/
def realOneFactorRemainderOperator
    {r : ℝ} (hr : r < 1 / 2) (ρ χ μ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hμs : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) :
    PeriodicLocalL2.EuclideanL2 d E →L[ℝ] PeriodicLocalL2.EuclideanL2 d E :=
  realOutputCompression
    (complexOneFactorRemainderOperator hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ)

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
