module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.FourierPairing
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.RestrictionPairing
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fourier norms of finite-dimensional real data

For `app:ch_regular_base:eq:negative-duality`, each real orthonormal component
is included in ℂ before taking the shared Euclidean L² Fourier transform.
The norm is the square root of the sum of squared component norms. These are
actual functions on Euclidean space with Lebesgue measure, not torus data.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ArbitraryAccuracy

open Pseudodifferential

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

/-- Include a real orthonormal coordinate in ℂ for the Fourier pairing in
`app:ch_regular_base:eq:negative-duality`. -/
def realFourierComponent (b : OrthonormalBasis ι ℝ F) (i : ι) : F →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ (b i))

/-- The actual L² class of a complexified real coordinate, with its original
measure (`app:ch_regular_base:eq:negative-duality`). -/
def realComponentL2 {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (b : OrthonormalBasis ι ℝ F) (i : ι) (u : Lp F 2 μ) : Lp ℂ 2 μ :=
  (realFourierComponent b i).compLp u

/-- Identification of the coordinate representative used by the whole-space
Fourier pairing (`app:ch_regular_base:eq:negative-duality`). -/
theorem realComponentL2_coeFn {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (b : OrthonormalBasis ι ℝ F) (i : ι) (u : Lp F 2 μ) :
    realComponentL2 b i u =ᵐ[μ] fun x ↦ (inner ℝ (b i) (u x) : ℂ) :=
  (realFourierComponent b i).coeFn_compLp u

/-- Componentwise Fourier Sobolev membership for the finite-dimensional real
source and test space in `app:ch_regular_base:eq:negative-duality`. -/
def MemComponentFourierSobolev (b : OrthonormalBasis ι ℝ F) (s : ℝ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) : Prop :=
  ∀ i, MemFourierSobolev s (realComponentL2 b i u)

/-- The Euclidean Fourier Sobolev norm of real data in orthonormal components
(`app:ch_regular_base:eq:negative-duality`). Use with the accompanying membership. -/
def componentFourierSobolevNorm (b : OrthonormalBasis ι ℝ F) (s : ℝ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) : ℝ :=
  Real.sqrt (∑ i, fourierSobolevNorm s (realComponentL2 b i u) ^ 2)

/-- Nonnegativity of the real Fourier norm
(`app:ch_regular_base:eq:negative-duality`). -/
theorem componentFourierSobolevNorm_nonneg (b : OrthonormalBasis ι ℝ F) (s : ℝ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) :
    0 ≤ componentFourierSobolevNorm b s u := Real.sqrt_nonneg _

/-- Every real L² datum has every nonpositive Fourier order, so the negative
source norm in `app:ch_regular:eq:inverse-remainder` is finite. -/
theorem memComponentFourierSobolev_of_nonpos (b : OrthonormalBasis ι ℝ F)
    {s : ℝ} (hs : s ≤ 0) (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) :
    MemComponentFourierSobolev b s u :=
  fun i ↦ memFourierSobolev_of_nonpos hs (realComponentL2 b i u)

/-- Real L² pairing is the sum of the real parts of its complexified coordinate
pairings (`app:ch_regular_base:eq:negative-duality`). -/
theorem inner_eq_sum_realComponentL2 {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (b : OrthonormalBasis ι ℝ F) (h v : Lp F 2 μ) :
    inner ℝ h v = ∑ i, (inner ℂ (realComponentL2 b i h) (realComponentL2 b i v)).re := by
  have hcoord (i : ι) :
      (inner ℂ (realComponentL2 b i h) (realComponentL2 b i v)).re =
        ∫ x, inner ℝ (b i) (h x) * inner ℝ (b i) (v x) ∂μ := by
    rw [L2.inner_def]
    have hi := (integral_re (L2.integrable_inner (𝕜 := ℂ)
      (realComponentL2 b i h) (realComponentL2 b i v))).symm
    refine hi.trans ?_
    apply integral_congr_ae
    filter_upwards [realComponentL2_coeFn b i h, realComponentL2_coeFn b i v]
      with x hx vx
    simp [hx, vx, mul_comm]
  simp_rw [hcoord]
  rw [L2.inner_def, ← integral_finsetSum]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [real_inner_comm (b _) (h x)] using (b.sum_inner_mul_inner (h x) (v x)).symm
  · intro i _
    exact ((Lp.memLp h).const_inner (b i)).integrable_mul ((Lp.memLp v).const_inner (b i))

/-- Weighted Cauchy–Schwarz for finite-dimensional real data, using genuine
complexified orthonormal components (`app:ch_regular_base:eq:negative-duality`). -/
theorem abs_inner_le_componentFourierSobolevNorm_mul (b : OrthonormalBasis ι ℝ F)
    {s : ℝ} {h v : Lp (α := EuclideanSpace ℝ (Fin n)) F 2}
    (hh : MemComponentFourierSobolev b (-s) h)
    (hv : MemComponentFourierSobolev b s v) :
    |inner ℝ h v| ≤ componentFourierSobolevNorm b (-s) h *
      componentFourierSobolevNorm b s v := by
  rw [inner_eq_sum_realComponentL2 b]
  calc
    _ ≤ ∑ i, |(inner ℂ (realComponentL2 b i h) (realComponentL2 b i v)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, fourierSobolevNorm (-s) (realComponentL2 b i h) *
        fourierSobolevNorm s (realComponentL2 b i v) := by
      apply Finset.sum_le_sum
      intro i _
      exact (RCLike.abs_re_le_norm _).trans
        (norm_inner_le_fourierSobolevNorm_mul (hh i) (hv i))
    _ ≤ _ := by
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

end JanetCartan.ArbitraryAccuracy
