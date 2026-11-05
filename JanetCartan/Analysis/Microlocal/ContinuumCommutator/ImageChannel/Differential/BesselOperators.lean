module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Iterated

/-!
# Constant Fourier factors of the literal image channel

The image contribution to `app:ch_background:eq:bg-commutator` is assembled
from coefficient multipliers and the actual operators `J` and `Dᵢ J`.
This file constructs their actions on every integer Sobolev space, proves
compatibility with the existing L² operators and proves derivative commutation.
The consumer is the finite-factor image-normal commutator, and ultimately
`HigherRegularity.mem_succ_of_commutators`.
-/

public noncomputable section

open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open ContinuumRow PeriodicSobolevSpace

variable {n : ℕ}

private def besselSobolevLinear (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →ₗ[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s where
  toFun u := ofL2 s (periodicBesselInverse (toL2 s u))
    (antitone_periodicSobolevLevel (Nat.le_succ s) (periodicBesselInverse_mem_succ s u))
  map_add' u v := by
    apply toL2_injective s
    simp only [map_add, toL2_ofL2]
  map_smul' c u := by
    apply toL2_injective s
    simp only [map_smul, toL2_ofL2, RingHom.id_apply]

private theorem toL2_besselSobolevLinear (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (besselSobolevLinear s u) = periodicBesselInverse (toL2 s u) :=
  toL2_ofL2 _ _ _

private theorem norm_besselSobolevLinear_le (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖besselSobolevLinear s u‖ ≤ ‖u‖ := by
  rw [← (analysisIsometry s).norm_map, ← (analysisIsometry s).norm_map u]
  apply lp.norm_mono (by norm_num)
  intro k
  change ‖analysis s (besselSobolevLinear s u) k‖ ≤ ‖analysis s u k‖
  rw [analysis_apply, toL2_besselSobolevLinear,
    periodicL2FourierCoeff_besselInverse, smul_comm]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (periodicBesselSymbol_pos k)]
  exact mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k)

/-- The existing Bessel inverse acting without a change of Sobolev level
(`app:ch_background:eq:bg-commutator`). -/
def besselSobolev (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s :=
  (besselSobolevLinear s).mkContinuous 1 (fun u ↦ by
    simpa only [one_mul] using norm_besselSobolevLinear_le s u)

/-- The bounded constant factor `Dᵢ J` of the principal image terms, using the
published H¹ Bessel lift (`app:ch_background:eq:bg-commutator`). -/
@[expose] def derivativeBessel (i : Fin n) : OutputL2 n →L[ℝ] OutputL2 n :=
  reducedCoordinateDerivative i ∘L periodicBesselLift

/-- The actual Sobolev action of `Dᵢ J`, constructed from the one-order gain
and the completed weak derivative (`app:ch_background:eq:bg-commutator`). -/
@[expose] def derivativeBesselSobolev (s : ℕ) (i : Fin n) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s :=
  coordinateDerivative s i ∘L periodicBesselGain s

/-- Every Bessel restriction has the original L² action
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem toL2_besselSobolev (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (besselSobolev s u) = periodicBesselInverse (toL2 s u) :=
  toL2_besselSobolevLinear s u

/-- Real-pair Fourier formula for the existing Bessel inverse
(`app:not:fourier`; `app:ch_background:eq:bg-commutator`). -/
theorem fourierCoeff_besselInverse (u : OutputL2 n) (k : Fin n → ℤ) :
    periodicFourierCoeff (periodicBesselInverse u) k =
      periodicBesselSymbol k • periodicFourierCoeff u k :=
  congrArg (WithLp.ofLp : FourierPair (Euclidean n) → Euclidean n × Euclidean n)
    (periodicL2FourierCoeff_besselInverse u k)

/-- `Dᵢ J` retains the physical unit-torus factor `2π kᵢ`
(`app:not:fourier`; `app:ch_background:eq:bg-commutator`). -/
theorem fourierCoeff_derivativeBessel (i : Fin n) (u : OutputL2 n) (k : Fin n → ℤ) :
    periodicFourierCoeff (derivativeBessel i u) k =
      (-(2 * Real.pi * (k i : ℝ)) •
          (periodicBesselSymbol k • (periodicFourierCoeff u k).2),
        (2 * Real.pi * (k i : ℝ)) •
          (periodicBesselSymbol k • (periodicFourierCoeff u k).1)) := by
  change periodicFourierCoeff (toL2 0 (coordinateDerivative 0 i
    (periodicBesselLift u))) k = _
  rw [periodicFourierCoeff_coordinateDerivative, toL2_periodicBesselLift,
    fourierCoeff_besselInverse]
  rfl

/-- Every constructed `Dᵢ J` restriction agrees with its literal L² factor
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem toL2_derivativeBesselSobolev (s : ℕ) (i : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (derivativeBesselSobolev s i u) = derivativeBessel i (toL2 s u) := by
  apply periodicBessel_coeff_ext
  intro k
  simp only [periodicL2FourierCoeff_apply]
  congr 1
  change periodicFourierCoeff (toL2 s (coordinateDerivative s i
    (periodicBesselGain s u))) k = _
  rw [periodicFourierCoeff_coordinateDerivative, toL2_periodicBesselGain,
    fourierCoeff_besselInverse, fourierCoeff_derivativeBessel]
  rfl

/-- The constant Bessel factor is a contraction at every order
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_besselSobolev_apply_le (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) : ‖besselSobolev s u‖ ≤ ‖u‖ := by
  exact norm_besselSobolevLinear_le s u

/-- The derivative Bessel factor is a contraction at every order
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_derivativeBesselSobolev_apply_le (s : ℕ) (i : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖derivativeBesselSobolev s i u‖ ≤ ‖u‖ := by
  change ‖coordinateDerivative s i (periodicBesselGain s u)‖ ≤ ‖u‖
  calc
    _ ≤ ‖periodicBesselGain s u‖ := norm_coordinateDerivative_le s i _
    _ = ‖u‖ := norm_periodicBesselGain s u

/-- The actual L² derivative Bessel factor is a contraction
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_derivativeBessel_apply_le (i : Fin n) (u : OutputL2 n) :
    ‖derivativeBessel i u‖ ≤ ‖u‖ := by
  change ‖reducedCoordinateDerivative i (periodicBesselLift u)‖ ≤ ‖u‖
  calc
    _ ≤ ‖periodicBesselLift u‖ := reducedCoordinateDerivative_norm_le i _
    _ = ‖u‖ := norm_periodicBesselLift u

/-- Bessel convolution commutes with any represented weak derivative. No
regularity of the input beyond that weak identity is assumed
(`app:ch_background:eq:bg-commutator`). -/
theorem hasWeakDerivative_besselInverse {i : Fin n} {u v : OutputL2 n}
    (h : HasPeriodicWeakDerivative i u v) :
    HasPeriodicWeakDerivative i (periodicBesselInverse u) (periodicBesselInverse v) := by
  have hd := hasPeriodicWeakDerivative_coordinateDerivative 0 i (periodicBesselLift u)
  rw [toL2_periodicBesselLift] at hd
  have he : toL2 0 (coordinateDerivative 0 i (periodicBesselLift u)) =
      periodicBesselInverse v := by
    apply periodicBessel_coeff_ext
    intro k
    simp only [periodicL2FourierCoeff_apply]
    congr 1
    rw [hd.periodicFourierCoeff_eq, fourierCoeff_besselInverse,
      fourierCoeff_besselInverse, h.periodicFourierCoeff_eq]
    exact Prod.ext (smul_comm _ _ _) (smul_comm _ _ _)
  rwa [he] at hd

/-- The constructed Sobolev Bessel action commutes with coordinate
differentiation (`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivative_besselSobolev (s : ℕ) (i : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) (s + 1)) :
    coordinateDerivative s i (besselSobolev (s + 1) u) =
      besselSobolev s (coordinateDerivative s i u) := by
  apply toL2_injective s
  rw [toL2_besselSobolev]
  have h := hasPeriodicWeakDerivative_coordinateDerivative s i (besselSobolev (s + 1) u)
  rw [toL2_besselSobolev] at h
  exact h.unique (hasWeakDerivative_besselInverse
    (hasPeriodicWeakDerivative_coordinateDerivative s i u))

/-- The constructed `Dⱼ J` Sobolev action commutes with every coordinate
derivative. The proof uses its literal `2π` Fourier formula
(`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivative_derivativeBesselSobolev (s : ℕ) (i j : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) (s + 1)) :
    coordinateDerivative s i (derivativeBesselSobolev (s + 1) j u) =
      derivativeBesselSobolev s j (coordinateDerivative s i u) := by
  apply toL2_injective s
  apply periodicBessel_coeff_ext
  intro k
  simp only [periodicL2FourierCoeff_apply]
  congr 1
  rw [periodicFourierCoeff_coordinateDerivative, toL2_derivativeBesselSobolev,
    toL2_derivativeBesselSobolev, fourierCoeff_derivativeBessel,
    fourierCoeff_derivativeBessel, periodicFourierCoeff_coordinateDerivative]
  apply Prod.ext <;> simp only [smul_smul] <;> congr 1 <;> ring

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
