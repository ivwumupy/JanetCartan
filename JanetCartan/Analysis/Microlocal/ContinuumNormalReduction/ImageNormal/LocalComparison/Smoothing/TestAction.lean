module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Action
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Realization

/-!
# Differential action of the localized Bessel remainder

The abstract integration-by-parts identity is instantiated with the actual
localized lattice remainder from `app:ch_background:prop:bg-frame`, Step 1.
The resulting matrix integral agrees with the bounded vector realization
on compact smooth representatives, in particular on compact Schwartz tests.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Both differential factors applied to the concrete localized Bessel
remainder give the displayed matrix kernel, including all zeroth-order
terms (`app:ch_background:prop:bg-frame`, Step 1). No kernel identity or
differentiation-under-the-integral premise is assumed. -/
theorem coefficientOperator_localizedImageBesselRemainder
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (v : E → I → ℂ) (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (x : E) (i : I) :
    coefficientOperator A Z
      (fun z j ↦ ∫ y, (localizedImageBesselRemainder χ ψ z y : ℂ) *
        coefficientFormalAdjoint A Z v y j) x i =
      ∑ k, ∫ y, (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * v y k :=
  coefficientOperator_integral_coefficientFormalAdjoint
    (fun p ↦ localizedImageBesselRemainder χ ψ p.1 p.2) A Z v
    (contDiff_localizedImageBesselRemainder hr χ ψ hχ hψ hχs hψs)
    (hasCompactSupport_localizedImageBesselRemainder_of_cube_support χ ψ hχs hψs)
    hA hZ hv hc x i

/-- The bounded complex vector realization agrees with `P R P*` on every
compact smooth representative (`app:ch_background:prop:bg-frame`, Step 1).
Here `R` acts by its proved integral formula, so differentiation acts on the
smooth integral rather than on an arbitrary L² representative. -/
theorem localizedImageNormalRemainderOperator_ae_coefficientOperator
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (v : E → I → ℂ) (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i))
    (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E))
    (hf : f =ᵐ[volume] fun x ↦ WithLp.toLp 2 (v x)) :
    localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (coefficientOperator A Z
        (fun z j ↦ ∫ y, (localizedImageBesselRemainder χ ψ z y : ℂ) *
          coefficientFormalAdjoint A Z v y j) x) := by
  filter_upwards [localizedImageNormalRemainderOperator_ae_integral
    hr χ ψ hχ hψ hχs hψs A Z hA hZ f] with x hx
  rw [hx]
  ext i
  change (∑ k, ∫ y, (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * f y k) =
    coefficientOperator A Z
      (fun z j ↦ ∫ y, (localizedImageBesselRemainder χ ψ z y : ℂ) *
        coefficientFormalAdjoint A Z v y j) x i
  rw [coefficientOperator_localizedImageBesselRemainder
    hr χ ψ hχ hψ hχs hψs A Z hA hZ v hv hc]
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [hf] with y hy
  rw [hy]

/-- Action on compact vector Schwartz tests of the bounded two-factor
remainder in `app:ch_background:prop:bg-frame`, Step 1. This is the concrete
test identity used in the local periodic--Euclidean comparison. -/
theorem localizedImageNormalRemainderOperator_schwartz_ae_coefficientOperator
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (v : 𝓢(E, EuclideanSpace ℂ I)) (hc : HasCompactSupport (v : E → EuclideanSpace ℂ I)) :
    localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ (v.toLp 2) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (coefficientOperator A Z
        (fun z j ↦ ∫ y, (localizedImageBesselRemainder χ ψ z y : ℂ) *
          coefficientFormalAdjoint A Z (fun y i ↦ v y i) y j) x) := by
  apply localizedImageNormalRemainderOperator_ae_coefficientOperator
    hr χ ψ hχ hψ hχs hψs A Z hA hZ (fun y i ↦ v y i)
  · intro i
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I ↦ ℂ) i).contDiff.comp (v.smooth ⊤)
  · intro i
    exact hc.comp_left (g := fun z : EuclideanSpace ℂ I ↦ z i) (by simp)
  · exact v.coeFn_toLp 2 volume

end JanetCartan.ContinuumNormalReduction.ImageNormal
