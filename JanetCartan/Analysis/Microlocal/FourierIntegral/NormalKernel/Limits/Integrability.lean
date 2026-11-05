module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Compact

/-!
# Absolute convergence of compact cross kernels paired with tensor tests

The finite-regularization Fubini step for
`app:ch_regular_base:eq:actual-normal-kernel` and its cross variant. All integrals
use Euclidean Lebesgue measure and physical covectors.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.NormalKernel

variable {n r : ℕ}

/-- The literal cross-kernel density paired with the tensor test
`conj (u x) * v y`, before frequency integration
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
def testedCrossDensity (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u v : Euclidean n → ℂ) (i j : Fin r) (x y η : Euclidean n) : ℂ :=
  Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
    (A x η * (B y η).conjTranspose) i j * star (u x) * v y

/-- The physical frequency integrand after testing in both output positions.
The normalization `(2π)⁻ⁿ` is kept outside this definition
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
def testedCrossFrequency (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u v : Euclidean n → ℂ) (i j : Fin r) (η : Euclidean n) : ℂ :=
  ∫ x, ∫ y, testedCrossDensity S A B u v i j x y η

variable {S : Euclidean n → Euclidean n → ℝ}
variable {A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
variable {u v : Euclidean n → ℂ}

/-- Compact amplitude support and compact tensor tests justify the full
three-variable absolute integral, used by `compactGraph_cross_tested`
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integrable_testedCrossDensity
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hu : Continuous u) (hv : Continuous v) (hsv : HasCompactSupport v)
    (i j : Fin r) :
    Integrable (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      testedCrossDensity S A B u v i j p.1.1 p.1.2 p.2)
      ((volume.prod volume).prod volume) := by
  let F (k : Fin r) (p : (Euclidean n × Euclidean n) × Euclidean n) :=
    Complex.exp (Complex.I * ((S p.1.1 p.2 - S p.1.2 p.2 : ℝ) : ℂ)) *
      (A p.1.1 p.2 i k * star (B p.1.2 p.2 j k)) * star (u p.1.1) * v p.1.2
  have hpx : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      (p.1.1, p.2)) := continuous_fst.fst.prodMk continuous_snd
  have hpy : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      (p.1.2, p.2)) := continuous_fst.snd.prodMk continuous_snd
  have hc (k : Fin r) : Continuous (F k) := by
    have ha := (hA i k).comp hpx
    have hb := (hB j k).comp hpy
    have hx := hS.comp hpx
    have hy := hS.comp hpy
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (hx.sub hy))).cexp.mul
      (ha.mul hb.star) |>.mul (hu.comp continuous_fst.fst).star |>.mul
        (hv.comp continuous_fst.snd)
  have hs (k : Fin r) : HasCompactSupport (F k) := by
    let K := tsupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k)
    apply HasCompactSupport.intro
      (((hsA i k).image continuous_fst).prod hsv |>.prod
        ((hsA i k).image continuous_snd))
    intro p hp
    by_cases ha : A p.1.1 p.2 i k = 0
    · simp [F, ha]
    by_cases hv : v p.1.2 = 0
    · simp [F, hv]
    have hmem : (p.1.1, p.2) ∈ K := subset_tsupport _ ha
    exact False.elim (hp ⟨⟨⟨(p.1.1, p.2), hmem, rfl⟩, subset_tsupport v hv⟩,
      ⟨(p.1.1, p.2), hmem, rfl⟩⟩)
  have hi := integrable_finsetSum Finset.univ
    (fun k _ ↦ (hc k).integrable_of_hasCompactSupport (hs k)
      (μ := (volume.prod volume).prod volume))
  convert hi using 1
  ext p
  simp [testedCrossDensity, F, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum, Finset.sum_mul]

/-- Integrating the compact tested density first in frequency or first in
both positions gives the same result. This is ordinary absolutely convergent
Fubini, used in `compactGraph_cross_tested`, not oscillatory Fubini
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integral_testedCrossDensity_swap
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hu : Continuous u) (hv : Continuous v) (hsv : HasCompactSupport v)
    (i j : Fin r) :
    (∫ x, ∫ y, ∫ η, testedCrossDensity S A B u v i j x y η) =
      ∫ η, testedCrossFrequency S A B u v i j η := by
  have hi := integrable_testedCrossDensity hS hA hsA hB hu hv hsv i j
  calc
    _ = ∫ p : Euclidean n × Euclidean n, ∫ η,
        testedCrossDensity S A B u v i j p.1 p.2 η ∂volume :=
      (integral_prod _ hi.integral_prod_left).symm
    _ = ∫ η, ∫ p : Euclidean n × Euclidean n,
        testedCrossDensity S A B u v i j p.1 p.2 η ∂volume :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_left_ae] with η hη
      exact integral_prod _ hη

/-- The tested frequency integrand is integrable for every compact
regularization. Thus its measurability need not be assumed in the later
limit theorem (`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integrable_testedCrossFrequency
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hu : Continuous u) (hv : Continuous v) (hsv : HasCompactSupport v)
    (i j : Fin r) : Integrable (testedCrossFrequency S A B u v i j) := by
  have hi := integrable_testedCrossDensity hS hA hsA hB hu hv hsv i j
  apply hi.integral_prod_right.congr
  filter_upwards [hi.prod_left_ae] with η hη
  exact integral_prod _ hη

end JanetCartan.FourierIntegral.NormalKernel
