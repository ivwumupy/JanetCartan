module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.Intrinsic
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.Definitions
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cartesian norms of weak jets

The derivative norm in `app:not:fourier` and
`app:ch_regular_base:eq:ball-extension-sobolev` counts each multiindex once.
For Hilbert-valued jets its squared norm is the sum of the squared scalar
components in any fixed orthonormal basis. This is distinct from `jetL2Norm`,
which uses Fréchet operator norms and a sum over derivative orders.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical Cartesian evaluation of a weak jet (`app:not:fourier`). The
multiindex enumeration agrees with `BallExtension.cartesianDerivativeWithin`
and the periodic Fourier Sobolev API. -/
def cartesianJetDerivative
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
    (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : F :=
  J (sobolevDerivativeList α).length x
    (fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ ((sobolevDerivativeList α).get j))

/-- Each Cartesian evaluation is controlled by the operator norm of its own
derivative order (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem norm_cartesianJetDerivative_le
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
    (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖cartesianJetDerivative J α x‖ ≤ ‖J (∑ i, α i) x‖ := by
  have h := (J (sobolevDerivativeList α).length x).le_opNorm
    (fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ ((sobolevDerivativeList α).get j))
  simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one] at h
  exact h.trans_eq (congrArg (fun j ↦ ‖J j x‖) (sobolevDerivativeList_length α))

/-- Local L² integrability of an operator-valued jet implies L² integrability
of its Cartesian evaluations (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem memLp_cartesianJetDerivative {U : Set (EuclideanSpace ℝ (Fin n))}
    {J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    (α : Fin n → ℕ) (hJ : MemLp (J (∑ i, α i)) 2 (volume.restrict U)) :
    MemLp (cartesianJetDerivative J α) 2 (volume.restrict U) := by
  apply hJ.of_le
  · have hm : AEStronglyMeasurable (J (sobolevDerivativeList α).length)
        (volume.restrict U) := by
      rw [sobolevDerivativeList_length]
      exact hJ.aestronglyMeasurable
    exact (show Continuous (fun L : (EuclideanSpace ℝ (Fin n))
      [×(sobolevDerivativeList α).length]→L[ℝ] F ↦ L
        (fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ ((sobolevDerivativeList α).get j)))
      from by fun_prop).comp_aestronglyMeasurable hm
  · exact Filter.Eventually.of_forall (norm_cartesianJetDerivative_le J α)

/-- Sum of the Cartesian L² energies, counting each multiindex once, for
`app:ch_regular_base:eq:ball-extension-sobolev`. Integrability is a separate fact. -/
def cartesianJetEnergy (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) : ℝ :=
  ∑ α ∈ sobolevMultiindices n m,
    ∫ x in U, ‖cartesianJetDerivative J (fun i ↦ α (some i)) x‖ ^ 2

/-- Intrinsic Cartesian derivative norm of a weak jet (`app:not:fourier`). -/
def cartesianJetNorm (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) : ℝ :=
  Real.sqrt (cartesianJetEnergy U m J)

/-- Nonnegativity of the Cartesian weak-jet energy (`app:not:fourier`). -/
theorem cartesianJetEnergy_nonneg (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) : 0 ≤ cartesianJetEnergy U m J :=
  Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _

/-- Squaring recovers the Cartesian energy (`app:not:fourier`). -/
theorem cartesianJetNorm_sq (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) :
    cartesianJetNorm U m J ^ 2 = cartesianJetEnergy U m J :=
  Real.sq_sqrt (cartesianJetEnergy_nonneg U m J)

/-- For scalar classical within-jets this is exactly the existing manuscript
norm, without any comparison constant (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cartesianJetNorm_iteratedFDerivWithin
    (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    cartesianJetNorm U m (fun j ↦ iteratedFDerivWithin ℝ j f U) =
      BallExtension.cartesianSobolevNorm U m f := by
  simp only [cartesianJetNorm, cartesianJetEnergy, cartesianJetDerivative,
    BallExtension.cartesianSobolevNorm, BallExtension.cartesianSobolevEnergy,
    BallExtension.cartesianDerivativeWithin, Real.norm_eq_abs, sq_abs]

end JanetCartan.LocalSobolev

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Cartesian weak-jet energy is exactly the sum of the L² energies of all
scalar components in fixed orthonormal coordinates (`app:not:fourier`). This
uses the Hilbert norm of each Cartesian evaluation, not its Fréchet operator norm. -/
theorem cartesianJetEnergy_eq_sum_components {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ F) (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
    (hJ : ∀ j ≤ m, MemLp (J j) 2 (volume.restrict U)) :
    cartesianJetEnergy U m J =
      ∑ α ∈ sobolevMultiindices n m, ∑ i,
        ∫ x in U, (inner ℝ (b i)
          (cartesianJetDerivative J (fun k ↦ α (some k)) x)) ^ 2 := by
  unfold cartesianJetEnergy
  apply Finset.sum_congr rfl
  intro α hα
  have horder : ∑ i, α (some i) ≤ m := by
    have := mem_sobolevMultiindices.mp hα
    omega
  have hd := memLp_cartesianJetDerivative (fun k ↦ α (some k)) (hJ _ horder)
  calc
    _ = ∫ x in U, ∑ i, (inner ℝ (b i)
        (cartesianJetDerivative J (fun k ↦ α (some k)) x)) ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ (b.sum_sq_inner_right _).symm
    _ = _ := integral_finsetSum _ fun i _ ↦
      (memLp_two_iff_integrable_sq (hd.const_inner (b i)).aestronglyMeasurable).mp
        (hd.const_inner (b i))

end JanetCartan.LocalSobolev
