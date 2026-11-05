module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Blocks
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.ScalarCross
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Frequency

/-!
# The pure compact-frequency graph normal on Euclidean L²

For a supplied continuous real phase and continuous, jointly compactly supported
matrix amplitudes, the graph is constructed as a compact frequency kernel after
the Euclidean L² Fourier transform. Plancherel and absolutely convergent Fubini
compute its cross normal with the normalization of
`app:ch_regular_base:eq:actual-normal-kernel`.

No physical source cutoff is used. Actual phase/amplitude hypotheses remain the
responsibility of the phase geometry and Hamilton phase producers. Identification
with the literal iterated `graphOperator`, the weighted reverse formula, and the
unregularized distributional limit are separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n r : ℕ}
variable {S : Euclidean n → Euclidean n → ℝ}
variable {A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}

/-- One scalar channel of the compact-frequency graph, with the actual
Euclidean L² Fourier transform (`app:ch_regular_base:eq:actual-normal-kernel`). -/
def graphBlock (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (i k : Fin r) : Lp (α := Euclidean n) ℂ 2 →L[ℂ] Lp (α := Euclidean n) ℂ 2 :=
  (compactKernelOperator (μ := volume) (ν := volume)
    (continuous_frequencyEntry hS (a := fun x η ↦ A x η i k) (hA i k)) (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))).comp
      (fourierL2 n).toContinuousLinearEquiv.toContinuousLinearMap

/-- The matrix graph on the shared Lebesgue L² Hilbert space, constructed
without an assumed operator bound or a spatial source cutoff
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
def compactGraph (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k)) :
    NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r := blocks (graphBlock hS hA hsA)

/-- The constructed graph acts by its compact frequency integral on arbitrary
Euclidean L² inputs (`app:ch_regular_base:eq:actual-normal-kernel`). Agreement
with the iterated physical-source integral additionally uses the L¹ Fourier
representative theorem. -/
theorem compactGraph_ae_frequencyIntegral (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (f : NormalOutputL2 n r) (i : Fin r) :
    (compactGraph hS hA hsA f) i =ᵐ[volume] fun x ↦ ∑ k, ∫ ξ,
      frequencyEntry S (fun z η ↦ A z η i k) x ξ * (fourierL2 n (f k)) ξ := by
  have he (k : Fin r) := compactKernelOperator_ae_integral (ν := volume)
    (continuous_frequencyEntry hS (a := fun x η ↦ A x η i k) (hA i k))
    (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))
    (fourierL2 n (f k))
  change ∀ k, graphBlock hS hA hsA i k (f k) =ᵐ[volume] _ at he
  change (blocks (graphBlock hS hA hsA) f) i =ᵐ[volume] _
  rw [blocks_apply]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun k ↦ graphBlock hS hA hsA i k (f k)), ae_all_iff.mpr he] with x hx he
  exact hx.trans (Finset.sum_congr rfl fun k _ ↦ he k)

/-- The actual Hilbert adjoint is the inverse Fourier transform after the
compact frequency-kernel adjoint, with transposed matrix channels
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem compactGraph_adjoint (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k)) :
    (compactGraph hS hA hsA).adjoint = blocks (fun k i ↦
      (fourierL2 n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (compactKernelOperator (μ := volume) (ν := volume)
          (continuous_frequencyEntry hS (a := fun x η ↦ A x η i k) (hA i k))
          (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))).adjoint) := by
  unfold compactGraph
  rw [blocks_adjoint]
  simp only [graphBlock, ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]

/-- The cross normal, with finite channel sums displayed explicitly. Each
scalar Fubini step is justified by compact-kernel absolute convergence
(`app:ch_regular_base:eq:actual-normal-kernel`, cross-product sentence after
`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem compactGraph_cross_ae_entries (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (f : NormalOutputL2 n r) (i : Fin r) :
    (compactGraph hS hA hsA ((compactGraph hS hB hsB).adjoint f)) i =ᵐ[volume]
      fun x ↦ ∑ j, ∑ k, ∫ y,
        (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
          Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
            (A x η i k * star (B y η j k))) * f j y := by
  have he (j k : Fin r) :
      graphBlock hS hA hsA i k ((graphBlock hS hB hsB j k).adjoint (f j)) =ᵐ[volume]
        fun x ↦ ∫ y, (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
          Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
            (A x η i k * star (B y η j k))) * f j y := by
    have hc := congrArg (fun L : Lp (α := Euclidean n) ℂ 2 →L[ℂ]
      Lp (α := Euclidean n) ℂ 2 ↦ L (f j))
      (fourier_comp_cross
        (compactKernelOperator (μ := volume) (ν := volume)
          (continuous_frequencyEntry hS (a := fun x η ↦ A x η i k) (hA i k)) (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k)))
        (compactKernelOperator (μ := volume) (ν := volume)
          (continuous_frequencyEntry hS (a := fun x η ↦ B x η j k) (hB j k)) (hasCompactSupport_frequencyEntry S (a := fun x η ↦ B x η j k) (hsB j k))))
    change graphBlock hS hA hsA i k ((graphBlock hS hB hsB j k).adjoint (f j)) = _ at hc
    rw [hc]
    simpa only [ContinuousLinearMap.comp_apply, integral_frequencyEntry_mul_star] using
      compactKernel_cross_ae (continuous_frequencyEntry hS (a := fun x η ↦ A x η i k) (hA i k))
        (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))
        (continuous_frequencyEntry hS (a := fun x η ↦ B x η j k) (hB j k))
        (hasCompactSupport_frequencyEntry S (a := fun x η ↦ B x η j k) (hsB j k)) (f j)
  rw [compactGraph, compactGraph, blocks_cross_apply]
  have hi (j : Fin r) := Lp.coeFn_fun_finsetSum Finset.univ
    (fun k ↦ graphBlock hS hA hsA i k ((graphBlock hS hB hsB j k).adjoint (f j)))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j ↦ ∑ k, graphBlock hS hA hsA i k ((graphBlock hS hB hsB j k).adjoint (f j))),
    ae_all_iff.mpr hi, ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (he j))] with x hx hi he
  rw [hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [hi j]
  exact Finset.sum_congr rfl fun k _ ↦ he j k

/-- The finite channel contraction is the genuine matrix product `A B*`;
all exchanges with the frequency integral follow from compact support
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integral_matrix_cross (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (i j : Fin r) (x y : Euclidean n) :
    (∑ k, ∫ ξ, frequencyEntry S (fun z η ↦ A z η i k) x ξ *
      star (frequencyEntry S (fun z η ↦ B z η j k) y ξ)) =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
        Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
          (A x η * (B y η).conjTranspose) i j := by
  rw [← integral_finsetSum _ (fun k _ ↦ integrable_cross_section
    (continuous_frequencyEntry hS (a := fun x η ↦ A x η i k) (hA i k)) (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))
    (continuous_frequencyEntry hS (a := fun x η ↦ B x η j k) (hB j k)) (hasCompactSupport_frequencyEntry S (a := fun x η ↦ B x η j k) (hsB j k)) x y)]
  simp_rw [frequencyEntry, physicalEntry_mul_star]
  simp only [← Finset.mul_sum, ← Matrix.conjTranspose_apply, ← Matrix.mul_apply]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun η ↦ Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
      (A x η * (B y η).conjTranspose) i j) (2 * Real.pi) (hR := by positivity)]
  simp [finrank_euclideanSpace, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul]

/-- The literal pure cross-normal matrix kernel in physical covectors:
`(2π)⁻ⁿ ∫ exp(i(S(x,η)-S(y,η))) A(x,η) B(y,η)* dη`.
This is the compact-frequency L² formula of
`app:ch_regular_base:eq:actual-normal-kernel` and its stated cross variant. -/
theorem compactGraph_cross_ae (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j k))
    (f : NormalOutputL2 n r) (i : Fin r) :
    (compactGraph hS hA hsA ((compactGraph hS hB hsB).adjoint f)) i =ᵐ[volume]
      fun x ↦ ∑ j, ∫ y, (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η,
        Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
          (A x η * (B y η).conjTranspose) i j) * f j y := by
  refine (compactGraph_cross_ae_entries hS hA hsA hB hsB f i).trans
    (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ k, ∫ y, (∫ ξ, frequencyEntry S (fun z η ↦ A z η i k) x ξ *
        star (frequencyEntry S (fun z η ↦ B z η j k) y ξ)) * f j y := by
      apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦ congrArg (fun z ↦ z * f j y)
        (integral_frequencyEntry_mul_star S (fun z η ↦ A z η i k)
          (fun z η ↦ B z η j k) x y).symm
    _ = _ := by
      rw [← integral_finsetSum _ (fun k _ ↦ integrable_cross_action
        (continuous_frequencyEntry hS (a := fun x η ↦ A x η i k) (hA i k))
        (hasCompactSupport_frequencyEntry S (a := fun x η ↦ A x η i k) (hsA i k))
        (continuous_frequencyEntry hS (a := fun x η ↦ B x η j k) (hB j k))
        (hasCompactSupport_frequencyEntry S (a := fun x η ↦ B x η j k) (hsB j k)) (f j) x)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦
        (Finset.sum_mul Finset.univ (fun k ↦ ∫ ξ,
          frequencyEntry S (fun z η ↦ A z η i k) x ξ *
            star (frequencyEntry S (fun z η ↦ B z η j k) y ξ)) (f j y)).symm.trans
          (congrArg (fun z ↦ z * f j y) (integral_matrix_cross hS hA hsA hB hsB i j x y))

end JanetCartan.FourierIntegral.NormalKernel
