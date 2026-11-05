module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Translation.Algebra

/-!
# The actual constant Fourier factors commute with translation

For the image contribution to `app:ch_background:eq:bg-commutator`, use the
constructed real Fourier coefficients, including the physical `2π` factors.
No abstract Fourier multiplier or commutation hypothesis is introduced.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannelTranslation

open ContinuumRow MeasureTheory

variable {n : ℕ}

private theorem pairMul_smul (z : ℂ) (r : ℝ) (v : FourierPair (Euclidean n)) :
    fourierPairMul z (r • v) = r • fourierPairMul z v := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [fourierPairMul, smul_add, smul_sub, smul_smul] <;> module

private theorem pairMul_comm (z w : ℂ) (v : FourierPair (Euclidean n)) :
    fourierPairMul z (fourierPairMul w v) =
      fourierPairMul w (fourierPairMul z v) := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [fourierPairMul, smul_add, smul_sub, smul_smul] <;> module

/-- The actual Bessel inverse commutes with every torus translation
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem besselInverse_translation (a : Torus n) (u : OutputL2 n) :
    periodicBesselInverse (periodicL2Translation a u) =
      periodicL2Translation a (periodicBesselInverse u) := by
  apply periodicBessel_coeff_ext
  intro k
  simp only [periodicL2FourierCoeff_besselInverse, periodicL2FourierCoeff_translation,
    pairMul_smul]

/-- The L² realization of the actual H¹ lift intertwines translation
(`app:ch_background:prop:bg-inverse`). -/
theorem besselLift_translation (a : Torus n) (u : OutputL2 n) :
    PeriodicSobolevSpace.toL2 1 (periodicBesselLift (periodicL2Translation a u)) =
      periodicL2Translation a (PeriodicSobolevSpace.toL2 1 (periodicBesselLift u)) := by
  simpa only [toL2_periodicBesselLift] using besselInverse_translation a u

/-- The bounded constant factor `Dⱼ J` in the finite image expansion
(`app:ch_background:defn:bg-row`). -/
def besselDerivative (j : Fin n) : OutputL2 n →L[ℝ] OutputL2 n :=
  reducedCoordinateDerivative j ∘L periodicBesselLift

/-- The physical Fourier symbol of `Dⱼ J`, in the shared real-pair convention
(`app:not:fourier`; `app:ch_background:eq:bg-commutator`). -/
theorem besselDerivative_fourier (j : Fin n) (u : OutputL2 n) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (besselDerivative j u) =
      fourierPairMul ⟨0, 2 * Real.pi * (k j : ℝ)⟩
        (periodicBesselSymbol k • periodicL2FourierCoeff k u) := by
  rw [← periodicL2FourierCoeff_besselInverse, ← toL2_periodicBesselLift]
  change WithLp.toLp 2
    (periodicFourierCoeff (PeriodicSobolevSpace.toL2 0
      (PeriodicSobolevSpace.coordinateDerivative 0 j (periodicBesselLift u))) k) = _
  rw [PeriodicSobolevSpace.periodicFourierCoeff_coordinateDerivative]
  apply WithLp.ofLp_injective
  simp [fourierPairMul, periodicL2FourierCoeff_apply]

/-- `Dⱼ J` is an L² contraction (`app:ch_background:prop:bg-frame`). -/
theorem norm_besselDerivative_le (j : Fin n) : ‖besselDerivative j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [besselDerivative, ContinuousLinearMap.comp_apply,
    norm_periodicBesselLift, one_mul] using
      reducedCoordinateDerivative_norm_le j (periodicBesselLift u)

/-- The actual derivative/Bessel factor commutes with translation, deduced from
its real Fourier coefficients (`app:ch_background:eq:bg-commutator`). -/
theorem besselDerivative_translation (j : Fin n) (a : Torus n) (u : OutputL2 n) :
    besselDerivative j (periodicL2Translation a u) =
      periodicL2Translation a (besselDerivative j u) := by
  apply periodicBessel_coeff_ext
  intro k
  simp only [besselDerivative_fourier, periodicL2FourierCoeff_translation,
    pairMul_smul]
  rw [pairMul_comm]

/-- Conjugation fixes the actual Bessel inverse
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_besselInverse (a : Torus n) :
    conjugate a periodicBesselInverse = periodicBesselInverse := by
  ext1 u
  change periodicL2Translation a (periodicBesselInverse (periodicL2Translation (-a) u)) = _
  rw [besselInverse_translation, ← periodicL2Translation_add, add_neg_cancel,
    periodicL2Translation_zero]

/-- Conjugation fixes each actual `Dⱼ J` factor
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_besselDerivative (a : Torus n) (j : Fin n) :
    conjugate a (besselDerivative j) = besselDerivative j := by
  ext1 u
  change periodicL2Translation a (besselDerivative j (periodicL2Translation (-a) u)) = _
  rw [besselDerivative_translation, ← periodicL2Translation_add, add_neg_cancel,
    periodicL2Translation_zero]

/-- The Bessel inverse contributes no divided translation difference
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugationDifference_besselInverse (i : Fin n) (h : ℝ) :
    periodicConjugationDifference periodicBesselInverse i h = 0 := by
  change h⁻¹ • (conjugate _ periodicBesselInverse - periodicBesselInverse) = 0
  rw [conjugate_besselInverse, sub_self, smul_zero]

/-- The derivative/Bessel factors contribute no divided translation difference
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugationDifference_besselDerivative (j i : Fin n) (h : ℝ) :
    periodicConjugationDifference (besselDerivative j) i h = 0 := by
  change h⁻¹ • (conjugate _ (besselDerivative j) - besselDerivative j) = 0
  rw [conjugate_besselDerivative, sub_self, smul_zero]

end JanetCartan.ContinuumCommutator.ImageChannelTranslation
