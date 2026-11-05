module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.Bessel.Scalar
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces

/-! # Real Euclidean Bessel synthesis
Coordinate synthesis using a finite orthonormal basis constructs the actual output
of `⟨D⟩⁻¹` in `app:ch_background:defn:bg-row`. No geometry assumptions enter.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumRow

variable {n : ℕ}

private theorem coeff_compLp {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : F →L[ℝ] G) (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    periodicFourierCoeff (A.compLp u) k =
      (A (periodicFourierCoeff u k).1, A (periodicFourierCoeff u k).2) := by
  rw [periodicFourierCoeff_congr_ae (A.coeFn_compLp u)]
  have hr := ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
    ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous
      ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)
  have hi := ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
    ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous
      ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)
  apply Prod.ext
  · simpa [periodicFourierCoeff] using A.integral_comp_comm hr
  · simpa [periodicFourierCoeff] using A.integral_comp_comm hi

/-- Actual real Euclidean synthesis of the Bessel inverse Fourier coefficients
(`app:ch_background:defn:bg-row`, `app:not:fourier`). -/
theorem exists_periodicBessel_output (u : OutputL2 n) :
    ∃ v : OutputL2 n, ∀ k,
      periodicL2FourierCoeff k v = periodicBesselSymbol k • periodicL2FourierCoeff k u := by
  classical
  let b := stdOrthonormalBasis ℝ (Euclidean n)
  let c := fun i ↦ (innerSL ℝ (b i)).compLp u
  choose v hv using fun i ↦ exists_periodicBessel_scalar (c i)
  let A := fun i ↦ ContinuousLinearMap.toSpanSingleton ℝ (b i)
  refine ⟨∑ i, (A i).compLp (v i), fun k ↦ ?_⟩
  rw [map_sum]
  have hc (i) : periodicFourierCoeff (v i) k =
      (periodicBesselSymbol k * ⟪b i, (periodicFourierCoeff u k).1⟫,
       periodicBesselSymbol k * ⟪b i, (periodicFourierCoeff u k).2⟫) := by
    rw [hv i k, coeff_compLp]
    rfl
  simp only [periodicL2FourierCoeff_apply, coeff_compLp, hc]
  simp only [← WithLp.toLp_sum, ← WithLp.toLp_smul]
  apply (WithLp.equiv 2 _).injective
  change (∑ i, ((periodicBesselSymbol k * ⟪b i, (periodicFourierCoeff u k).1⟫) • b i,
    (periodicBesselSymbol k * ⟪b i, (periodicFourierCoeff u k).2⟫) • b i)) =
      periodicBesselSymbol k • periodicFourierCoeff u k
  apply Prod.ext <;>
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      ← smul_smul, ← Finset.smul_sum, b.sum_repr']

/-- Fourier uniqueness in real L², used to turn the constructed output into a
linear operator (`app:not:fourier`). -/
theorem periodicBessel_coeff_ext {u v : OutputL2 n}
    (h : ∀ k, periodicL2FourierCoeff k u = periodicL2FourierCoeff k v) : u = v := by
  apply (PeriodicSobolevSpace.zeroEquivL2 (n := n) (F := Euclidean n)).symm.injective
  apply (PeriodicSobolevSpace.analysisIsometry 0).injective
  apply lp.ext
  funext k
  change periodicSobolevWeight 0 k • periodicL2FourierCoeff k u =
    periodicSobolevWeight 0 k • periodicL2FourierCoeff k v
  rw [h k]

end JanetCartan.ContinuumRow
