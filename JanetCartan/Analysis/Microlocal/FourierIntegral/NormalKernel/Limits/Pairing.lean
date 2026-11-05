module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Limits.Integrability

/-!
# Compact cross-normal pairing with tensor tests

The finite-regularization identity used to pass
`app:ch_regular_base:eq:actual-normal-kernel` to tested limits. The test class is
continuous compactly supported scalar functions in specified matrix channels;
in particular it contains all smooth compactly supported tensor tests.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ComplexInnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n r : ℕ}

/-- Insert a continuous compactly supported test into one channel of the
actual Euclidean L² space, for testing
`app:ch_regular_base:eq:actual-normal-kernel`. -/
def compactChannelTest {u : Euclidean n → ℂ} (hu : Continuous u)
    (hsu : HasCompactSupport u) (i : Fin r) : NormalOutputL2 n r :=
  PiLp.single 2 i ((hu.memLp_of_hasCompactSupport hsu).toLp u)

/-- The finite compact cross-normal identity paired against a tensor test.
The identity follows from `compactGraph_cross_ae` and absolute Fubini, with no
assumed kernel pairing (`app:ch_regular_base:eq:actual-normal-kernel`, and the
cross-product sentence after `app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem compactGraph_cross_tested
    {S : Euclidean n → Euclidean n → ℝ}
    {A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    {u v : Euclidean n → ℂ}
    (hu : Continuous u) (hsu : HasCompactSupport u)
    (hv : Continuous v) (hsv : HasCompactSupport v) (i j : Fin r) :
    inner ℂ ((compactGraph hS hA hsA).adjoint (compactChannelTest hu hsu i))
      ((compactGraph hS hB hsB).adjoint (compactChannelTest hv hsv j)) =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η, testedCrossFrequency S A B u v i j η := by
  let K (x y : Euclidean n) : ℂ := ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
    Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
      (A x η * (B y η).conjTranspose) i j
  have hvrep : ∀ k : Fin r, (compactChannelTest hv hsv j) k =ᵐ[volume]
      fun y ↦ if k = j then v y else 0 := by
    intro k
    simp only [compactChannelTest, PiLp.single_apply]
    split_ifs
    · exact (hv.memLp_of_hasCompactSupport hsv (p := 2) (μ := volume)).coeFn_toLp
    · exact Lp.coeFn_zero ℂ 2 volume
  have hcross := compactGraph_cross_ae hS hA hsA hB hsB
    (compactChannelTest hv hsv j) i
  have hcross' :
      (compactGraph hS hA hsA ((compactGraph hS hB hsB).adjoint
        (compactChannelTest hv hsv j))) i =ᵐ[volume] fun x ↦ ∫ y, K x y * v y := by
    filter_upwards [hcross] with x hx
    rw [hx]
    calc
      _ = ∑ k : Fin r, ∫ y,
          (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
            Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
              (A x η * (B y η).conjTranspose) i k) *
                (if k = j then v y else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        apply integral_congr_ae
        filter_upwards [hvrep k] with y hy
        rw [hy]
      _ = _ := by
        rw [Finset.sum_eq_single j]
        · simp only [ite_true, K]
        · intro k _ hkj
          simp only [hkj, ite_false, mul_zero, integral_zero]
        · simp
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (PiLp.single 2 i ((hu.memLp_of_hasCompactSupport hsu).toLp u) :
    NormalOutputL2 n r) _ = _
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  swap
  · intro k _ hki
    simp only [PiLp.single_apply, hki, ite_false, inner_zero_left]
  swap
  · simp
  simp only [PiLp.single_apply, ite_true]
  rw [L2.inner_def]
  calc
    _ = ∫ x, (∫ y, K x y * v y) * star (u x) := by
      apply integral_congr_ae
      filter_upwards [hcross',
        (hu.memLp_of_hasCompactSupport hsu (p := 2) (μ := volume)).coeFn_toLp]
        with x hx hu'
      rw [hx, hu', RCLike.inner_apply, starRingEnd_apply]
    _ = ((2 * Real.pi) ^ n : ℂ)⁻¹ *
        ∫ x, ∫ y, ∫ η, testedCrossDensity S A B u v i j x y η := by
      simp only [K, testedCrossDensity, ← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        apply integral_congr_ae
        exact Eventually.of_forall fun y ↦ by
          apply integral_congr_ae
          exact Eventually.of_forall fun η ↦ by ring
    _ = _ := by rw [integral_testedCrossDensity_swap hS hA hsA hB hu hv hsv i j]

end JanetCartan.FourierIntegral.NormalKernel
