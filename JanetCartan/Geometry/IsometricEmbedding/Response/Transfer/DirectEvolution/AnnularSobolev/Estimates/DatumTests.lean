module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.Counting
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Tests
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.DatumParameterCommutation.Algebra

/-!
# Fourier bounds for the original annular datum words

The source directions in `new:eq:carrier-ibp` need not be coordinate vectors.
We differentiate the original compact smooth datum, identify its literal
`originalDatumDerivative`, and bound each word by its own Fourier order.
The consumer is the weighted finite expansion in the annular Sobolev estimate.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open CompactTransfer FourierIntegral Pseudodifferential
open IsometricEmbedding.Response.NearCarrier
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- A literal source directional derivative of the compact test, consumed by
`new:eq:carrier-ibp`. It differentiates no auxiliary datum or projection. -/
def annularTestDirectionalDeriv (v : E) (u : graphTestSpace n r) : graphTestSpace n r :=
  ⟨fun x => fderiv ℝ u.val x v,
    (u.property.1.fderiv_right (by simp)).clm_apply contDiff_const,
    u.property.2.fderiv_apply ℝ v⟩

/-- The actual original-datum word on a parameter-independent compact test.
Its source directions remain exactly those in the published branch list
(`new:eq:carrier-ibp`). -/
def annularTestDatumWord (ds : List (E × P)) (u : graphTestSpace n r) : graphTestSpace n r :=
  orderedTransferAction (fun e => annularTestDirectionalDeriv e.1) ds u

/-- Identification with the original datum derivatives, including zero
parameter directions. Consumer: the annular weak expansion
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem annularTestDatumWord_eq_original (ds : List (E × P))
    (u : graphTestSpace n r) (x : E) (c : P) :
    (annularTestDatumWord ds u).val x =
      originalDatumDerivative ds (fun q => u.val q.1) (x, c) := by
  induction ds generalizing x c with
  | nil => rfl
  | cons e ds ih =>
    have he : originalDatumDerivative ds (fun q : E × P => u.val q.1) =
        fun q => (annularTestDatumWord ds u).val q.1 := by
      funext q
      exact (ih q.1 q.2).symm
    change fderiv ℝ (annularTestDatumWord ds u).val x e.1 =
      fderiv ℝ (originalDatumDerivative ds (fun q : E × P => u.val q.1)) (x, c) e
    rw [he]
    have h := ((annularTestDatumWord ds u).property.1.differentiable (by simp) x).hasFDerivAt.comp
      (x, c) (ContinuousLinearMap.fst ℝ E P).hasFDerivAt
    exact (congrArg (fun D : (E × P) →L[ℝ] V => D e) h.fderiv).symm

private theorem directional_eq_sum (v : E) (u : graphTestSpace n r) :
    annularTestDirectionalDeriv v u =
      ∑ i : Fin n, (v i : ℂ) • graphTestPartialDeriv i u := by
  apply Subtype.ext
  funext x
  change fderiv ℝ u.val x v = _
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply]
  change (∑ i, v i • fderiv ℝ u.val x (EuclideanSpace.single i 1)) = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, graphTestPartialDeriv, partialDeriv]
  congr 1

private theorem coordinate_directional_eq_sum (v : E) (u : graphTestSpace n r) (a : Fin r) :
    finiteL2CoordinateIsometry volume (graphTestToLp (annularTestDirectionalDeriv v u)) a =
      ∑ i : Fin n, v i •
        finiteL2CoordinateIsometry volume (graphTestToLp (graphTestPartialDeriv i u)) a := by
  rw [directional_eq_sum, map_sum, map_sum]
  simp only [map_smul]
  change (∑ i, (v i : ℂ) • finiteL2CoordinateIsometry volume
    (graphTestToLp (graphTestPartialDeriv i u))) a = _
  rw [show (∑ i, (v i : ℂ) • finiteL2CoordinateIsometry volume
    (graphTestToLp (graphTestPartialDeriv i u))) a =
      ∑ i, (v i : ℂ) • finiteL2CoordinateIsometry volume
        (graphTestToLp (graphTestPartialDeriv i u)) a by
    simpa only [PiLp.proj_apply, PiLp.smul_apply] using
      map_sum (PiLp.proj (𝕜 := ℂ) 2 _ a)
        (fun i => (v i : ℂ) • finiteL2CoordinateIsometry volume
          (graphTestToLp (graphTestPartialDeriv i u))) Finset.univ]
  simp only [Complex.coe_smul]
  rfl

/-- Each unit-bounded source direction costs at most `n * 2π` and one
Fourier derivative. Consumer: `annularTestDatumWord_coordinate_bound`,
for the actual original datum in `new:eq:carrier-ibp`. -/
theorem annularTestDirectionalDeriv_coordinate_bound (v : E) (hv : ‖v‖ ≤ 1)
    (u : graphTestSpace n r) (a : Fin r) (t : ℝ) (ht : 0 ≤ t) :
    fourierSobolevNorm t (finiteL2CoordinateIsometry volume
      (graphTestToLp (annularTestDirectionalDeriv v u)) a) ≤
      ((n : ℝ) * (2 * Real.pi)) * fourierSobolevNorm (t + 1)
        (finiteL2CoordinateIsometry volume (graphTestToLp u) a) := by
  rw [coordinate_directional_eq_sum]
  have hmem (i : Fin n) := datum_memFourierSobolev_smul
    (graphTest_memVectorFourierSobolev t (graphTestPartialDeriv i u) a) (v i)
  apply (fourierSobolev_finsetSum Finset.univ _ (fun i _ => hmem i)).2.trans
  calc
    _ ≤ ∑ _i : Fin n, (2 * Real.pi) * fourierSobolevNorm (t + 1)
        (finiteL2CoordinateIsometry volume (graphTestToLp u) a) := by
      apply Finset.sum_le_sum
      intro i _
      rw [datum_fourierSobolevNorm_smul]
      have hvi : ‖v i‖ ≤ 1 := (PiLp.norm_apply_le v i).trans hv
      exact (mul_le_mul_of_nonneg_right hvi (fourierSobolevNorm_nonneg _ _)).trans
        (by simpa [orderedTransferAction] using graphTest_coordinate_word_bound u [i] a t ht)
    _ = _ := by simp [mul_assoc]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The Fourier cost of every actual source word, with its own length.
This retains the original datum and the `2π` normalization in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem annularTestDatumWord_coordinate_bound (ds : List (E × P))
    (hds : ∀ e ∈ ds, ‖e.1‖ ≤ 1) (u : graphTestSpace n r)
    (a : Fin r) (t : ℝ) (ht : 0 ≤ t) :
    fourierSobolevNorm t (finiteL2CoordinateIsometry volume
      (graphTestToLp (annularTestDatumWord ds u)) a) ≤
      ((n : ℝ) * (2 * Real.pi)) ^ ds.length * fourierSobolevNorm (t + ds.length)
        (finiteL2CoordinateIsometry volume (graphTestToLp u) a) := by
  induction ds generalizing t with
  | nil => simp [annularTestDatumWord, orderedTransferAction]
  | cons e ds ih =>
    apply (annularTestDirectionalDeriv_coordinate_bound e.1
      (hds e List.mem_cons_self) (annularTestDatumWord ds u) a t ht).trans
    calc
      _ ≤ ((n : ℝ) * (2 * Real.pi)) *
          (((n : ℝ) * (2 * Real.pi)) ^ ds.length * fourierSobolevNorm (t + 1 + ds.length)
            (finiteL2CoordinateIsometry volume (graphTestToLp u) a)) :=
        mul_le_mul_of_nonneg_left (ih (fun v hv => hds v (List.mem_cons_of_mem e hv))
          (t + 1) (by linarith)) (by positivity)
      _ = _ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, pow_succ]
        rw [show t + 1 + (ds.length : ℝ) = t + (ds.length + 1) by ring]
        ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- L² norm of the literal original-datum derivative, bounded by the Fourier
norm at precisely its datum order. Consumer: annular finite-sum assembly
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem annularTestDatumWord_norm_le (ds : List (E × P))
    (hds : ∀ e ∈ ds, ‖e.1‖ ≤ 1) (u : graphTestSpace n r) :
    ‖graphTestToLp (annularTestDatumWord ds u)‖ ≤
      ((r : ℝ) * ((n : ℝ) * (2 * Real.pi)) ^ ds.length) *
        vectorFourierSobolevNorm (ds.length : ℝ) (graphTestToLp u) := by
  calc
    _ ≤ ∑ a, fourierSobolevNorm 0 (finiteL2CoordinateIsometry volume
        (graphTestToLp (annularTestDatumWord ds u)) a) := by
      simpa using matrixFourierSobolevNorm_le_sum 0
        (finiteL2CoordinateIsometry volume (graphTestToLp (annularTestDatumWord ds u)))
    _ ≤ ∑ _a : Fin r, ((n : ℝ) * (2 * Real.pi)) ^ ds.length *
        vectorFourierSobolevNorm (ds.length : ℝ) (graphTestToLp u) := by
      apply Finset.sum_le_sum
      intro a _
      have h := annularTestDatumWord_coordinate_bound ds hds u a 0 le_rfl
      simp only [zero_add] at h
      exact h.trans
        (mul_le_mul_of_nonneg_left (fourierSobolevNorm_coordinate_le _ _ a) (by positivity))
    _ = _ := by simp [mul_assoc]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
