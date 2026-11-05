module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint

/-!
# Support and negative endpoint of the differentiated lattice remainder

The explicit operator `P R P*` for the local Bessel comparison retains the
two original cutoff supports after differentiation and integration by parts.
Its proved real adjoint endpoint therefore instantiates periodic H¹ transfer
and negative duality in `app:ch_background:prop:bg-frame`, Step 1. This treats
the single differentiated comparison remainder; the cross terms from two
Bessel factors are separate obligations of the image-normal assembly.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [Fintype I] [Fintype J] in
private theorem sourceKernel_tsupport (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (j : J) (k : I) :
    tsupport (imageNormalSourceKernel K A Z j k) ⊆ tsupport K := by
  apply closure_minimal _ (isClosed_tsupport K)
  intro p hp
  by_contra hn
  exact hp (by simp [imageNormalSourceKernel, fderiv_of_notMem_tsupport ℝ hn,
    image_eq_zero_of_notMem_tsupport hn])

omit [Fintype I] in
private theorem twoFactorKernel_tsupport (K : E × E → ℝ)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (i k : I) :
    tsupport (imageNormalTwoFactorKernel K A Z i k) ⊆ tsupport K := by
  apply closure_minimal _ (isClosed_tsupport K)
  intro p hp
  by_contra hn
  have hs (j : J) : p ∉ tsupport (imageNormalSourceKernel K A Z j k) :=
    fun h ↦ hn (sourceKernel_tsupport K A Z j k h)
  exact hp (by simp [imageNormalTwoFactorKernel, fderiv_of_notMem_tsupport ℝ (hs _),
    image_eq_zero_of_notMem_tsupport (hs _)])

omit [Fintype I] in
/-- The two normal factors do not enlarge either original cutoff support
of the explicit lattice remainder kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem tsupport_localizedImageNormalRemainderKernel_subset
    (χ ψ : E → ℝ) (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (i k : I) :
    tsupport (localizedImageNormalRemainderKernel χ ψ A Z i k) ⊆
      tsupport χ ×ˢ tsupport ψ :=
  (twoFactorKernel_tsupport _ A Z i k).trans
    (tsupport_localizedImageBesselRemainder_subset χ ψ)

/-- The real remainder and its literal adjoint retain respectively the
output and source cutoff supports on all data
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realLocalizedImageNormalRemainderOperator_support
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ x, ψ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (f : EuclideanL2 d (EuclideanSpace ℝ I)) :
    let R := realLocalizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ
    (∀ᵐ x ∂volume, x ∉ tsupport χ → R f x = 0) ∧
      (∀ᵐ y ∂volume, y ∉ tsupport ψ → (R).adjoint f y = 0) := by
  dsimp only
  constructor
  · filter_upwards [realLocalizedImageNormalRemainderOperator_ae_integral
      hr χ ψ hχ hψ hχs hψs A Z hA hZ f] with x hx
    intro hxs
    rw [hx]
    ext i
    have hz (k : I) (y : E) : localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h ↦ hxs ((tsupport_localizedImageNormalRemainderKernel_subset χ ψ A Z i k h).1)
    simp [hz]
  · filter_upwards [realLocalizedImageNormalRemainderOperator_adjoint_ae_integral
      hr χ ψ hχ hψ hχs hψs A Z hA hZ f] with y hy
    intro hys
    rw [hy]
    ext k
    have hz (i : I) (x : E) : localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h ↦ hys ((tsupport_localizedImageNormalRemainderKernel_subset χ ψ A Z i k h).2)
    simp [hz]

omit [Fintype I] in
/-- The differentiated lattice remainder has the actual periodic adjoint
H¹ lift and H⁻¹-to-L² bound. Its support and Euclidean endpoint are supplied
by the concrete kernel construction, with no smoothing estimate assumed
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realLocalizedImageNormalRemainderOperator_periodic_endpoints
    {m : ℕ} {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ x, ψ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : E → Fin d → Matrix (Fin m) J ℝ) (Z : E → Matrix (Fin m) J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) :
    let R := realLocalizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ
    ∃ C : ℝ, 0 ≤ C ∧
      (∃ B : PeriodicL2 d (EuclideanSpace ℝ (Fin m)) →L[ℝ]
          PeriodicSobolevSpace d (EuclideanSpace ℝ (Fin m)) 1,
        (PeriodicSobolevSpace.toL2 1).comp B = (transferOperator R).adjoint ∧ ‖B‖ ≤ C) ∧
      ∀ f : PeriodicL2 d (EuclideanSpace ℝ (Fin m)),
        ‖transferOperator R f‖ ≤ C * ‖PeriodicSobolevNegativeOne.ofL2 f‖ := by
  dsimp only
  let R := realLocalizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ
  obtain ⟨C, hC, hb⟩ := realLocalizedImageNormalRemainderOperator_sobolev_one_bounds
    hr χ ψ hχ hψ hχs hψs A Z hA hZ
  have hs (g : EuclideanL2 d (EuclideanSpace ℝ (Fin m))) :
      ∀ᵐ x ∂volume, x ∉ chartBox r → R.adjoint g x = 0 := by
    filter_upwards [(realLocalizedImageNormalRemainderOperator_support
      hr χ ψ hχ hψ hχs hψs A Z hA hZ g).2] with x hx
    intro hxr
    apply hx
    exact fun hxs ↦ hxr (imageBessel_cube_bounds_of_mem_tsupport ψ hψs hxs)
  have ht (g : EuclideanL2 d (EuclideanSpace ℝ (Fin m))) := (hb g).2.2
  refine ⟨((m : ℝ) * (1 + 2 * Real.pi * d)) * C, by positivity, ?_, ?_⟩
  · exact PeriodicEndpoint.exists_transferOperator_adjoint_h1 hr hC R hs ht
  · exact PeriodicEndpoint.transferOperator_negativeOne_bound hr hC R hs ht

end JanetCartan.ContinuumNormalReduction.ImageNormal
