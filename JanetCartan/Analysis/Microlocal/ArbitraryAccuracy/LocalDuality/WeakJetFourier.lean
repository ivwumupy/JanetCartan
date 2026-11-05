module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Scalar

/-!
# Genuine weak extensions and component Fourier norms

The component reduction for `app:ch_regular_base:eq:negative-duality` and
`app:ch_regular:eq:inverse-remainder` uses actual projected weak extensions.
The imported scalar comparison constructs distributional coordinate derivatives
from the genuine weak jets. Applying it to the projected extensions gives the
unconditional finite-dimensional real comparison below. Both positive constants
are uniform in the domain and extension, including dimension and order zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

namespace JanetCartan.ArbitraryAccuracy

open LocalSobolev Pseudodifferential

variable {n N : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

/-- An orthonormal coordinate has operator norm at most one, including an empty
basis, for the component reduction in `app:ch_regular_base:eq:negative-duality`. -/
theorem norm_realFourierComponent_le_one (b : OrthonormalBasis ι ℝ F) (i : ι) :
    ‖realFourierComponent b i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(inner ℝ (b i) x : ℂ)‖ ≤ 1 * ‖x‖
  simpa only [Complex.norm_real, b.orthonormal.norm_eq_one i] using
    norm_inner_le_norm (b i) x

/-- Each real coordinate of a genuine extension has a genuine scalar complex
weak extension (`app:ch_regular_base:eq:negative-duality`). Completeness follows
from the given finite basis and is not an additional hypothesis. -/
def realComponentExtension (b : OrthonormalBasis ι ℝ F) (i : ι)
    {W : Set (EuclideanSpace ℝ (Fin n))} {v : LocalL2 W F}
    (e : SobolevExtension W N v) : SobolevExtension W N (realComponentL2 b i v) := by
  let := b.toBasis.finiteDimensional_of_finite
  exact e.mapCLM (realFourierComponent b i)

/-- The constructed scalar extension represents the specified complexified
coordinate, for `app:ch_regular_base:eq:negative-duality`. -/
theorem realComponentExtension_toL2 (b : OrthonormalBasis ι ℝ F) (i : ι)
    {W : Set (EuclideanSpace ℝ (Fin n))} {v : LocalL2 W F}
    (e : SobolevExtension W N v) :
    (realComponentExtension b i e).toL2 = realComponentL2 b i e.toL2 := by
  let := b.toBasis.finiteDimensional_of_finite
  exact e.toL2_mapCLM (realFourierComponent b i)

/-- Projecting a genuine extension to an orthonormal coordinate decreases its
jet norm, for `app:ch_regular_base:eq:negative-duality`. -/
theorem realComponentExtension_jetNorm_le (b : OrthonormalBasis ι ℝ F) (i : ι)
    {W : Set (EuclideanSpace ℝ (Fin n))} {v : LocalL2 W F}
    (e : SobolevExtension W N v) :
    (realComponentExtension b i e).jetNorm ≤ e.jetNorm := by
  let := b.toBasis.finiteDimensional_of_finite
  exact (e.jetNorm_mapCLM_le (realFourierComponent b i)).trans
    (mul_le_of_le_one_left e.jetNorm_nonneg (norm_realFourierComponent_le_one b i))

/-- A uniform scalar extension comparison implies the real finite-component
comparison, with its positive constant chosen before the domain and extension.
This is only the component deduction for `app:ch_regular_base:eq:negative-duality`;
the scalar hypothesis must be supplied by the actual weak-derivative construction. -/
theorem componentFourierSobolev_extension_bounds_of_scalar
    (n N : ℕ) {C : ℝ} (hC : 0 < C)
    (hscalar : ∀ (W : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 W ℂ)
      (e : SobolevExtension W N v),
      MemFourierSobolev (N : ℝ) e.toL2 ∧
        fourierSobolevNorm (N : ℝ) e.toL2 ≤ C * e.jetNorm)
    (b : OrthonormalBasis ι ℝ F) :
    ∃ D : ℝ, 0 < D ∧ ∀ (W : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 W F)
      (e : SobolevExtension W N v),
      MemComponentFourierSobolev b (N : ℝ) e.toL2 ∧
        componentFourierSobolevNorm b (N : ℝ) e.toL2 ≤ D * e.jetNorm := by
  refine ⟨((Fintype.card ι : ℝ) + 1) * C, by positivity, ?_⟩
  intro W v e
  have hi (i : ι) := hscalar W (realComponentL2 b i v) (realComponentExtension b i e)
  simp_rw [realComponentExtension_toL2] at hi
  refine ⟨fun i ↦ (hi i).1, ?_⟩
  have hnorm (i : ι) : fourierSobolevNorm (N : ℝ) (realComponentL2 b i e.toL2) ≤
      C * e.jetNorm :=
    (hi i).2.trans (mul_le_mul_of_nonneg_left
      (realComponentExtension_jetNorm_le b i e) hC.le)
  calc
    _ ≤ ∑ i, fourierSobolevNorm (N : ℝ) (realComponentL2 b i e.toL2) := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨Finset.sum_nonneg (fun _ _ ↦ fourierSobolevNorm_nonneg _ _),
        Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ fourierSobolevNorm_nonneg _ _)⟩
    _ ≤ ∑ _i : ι, C * e.jetNorm := Finset.sum_le_sum (fun i _ ↦ hnorm i)
    _ ≤ (((Fintype.card ι : ℝ) + 1) * C) * e.jetNorm := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      nlinarith [mul_nonneg hC.le e.jetNorm_nonneg]

/-- Every genuine finite-dimensional real weak extension belongs to the component
Fourier Sobolev space, with a positive norm comparison constant chosen before the
domain, local datum, and extension. This supplies the extension bound used by the
local negative pairing in `app:ch_regular_base:eq:negative-duality` and the inverse
remainder in `app:ch_regular:eq:inverse-remainder`. The scalar input is proved from
the actual weak jets, and the projection preserves their weak identities and L²
representatives. Dimension zero, order zero, and an empty basis are included. -/
theorem componentFourierSobolev_extension_bounds (n N : ℕ)
    (b : OrthonormalBasis ι ℝ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 W F)
      (e : SobolevExtension W N v),
      MemComponentFourierSobolev b (N : ℝ) e.toL2 ∧
        componentFourierSobolevNorm b (N : ℝ) e.toL2 ≤ C * e.jetNorm := by
  obtain ⟨C, hC, hscalar⟩ := scalarFourierSobolev_extension_bounds n N
  exact componentFourierSobolev_extension_bounds_of_scalar n N hC hscalar b

end JanetCartan.ArbitraryAccuracy

namespace JanetCartan.LocalSobolev.SobolevExtension

open Pseudodifferential

variable {n : ℕ} {W : Set (EuclideanSpace ℝ (Fin n))} {v : LocalL2 W ℂ}

/-- The scalar comparison at order zero is exact, including dimension zero,
for `app:ch_regular_base:eq:negative-duality`. -/
theorem fourierSobolevNorm_zero_toL2 (e : SobolevExtension W 0 v) :
    fourierSobolevNorm 0 e.toL2 = e.jetNorm := by
  rw [fourierSobolevNorm_zero, jetNorm_zero]
  exact Lp.norm_toLp _ _

end JanetCartan.LocalSobolev.SobolevExtension
