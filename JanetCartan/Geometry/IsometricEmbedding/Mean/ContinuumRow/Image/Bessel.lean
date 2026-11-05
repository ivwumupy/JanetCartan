module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.Bessel.Operator

/-!
# Bessel inverse and one-order Sobolev gain

The actual real periodic operator `⟨D⟩⁻¹` in `app:ch_background:defn:bg-row`
uses the unit-torus frequencies `2π|k|` of `app:not:fourier`. Its restrictions
are isometries from Hˢ into Hˢ⁺¹, all compatible with the same L² operator.
The L²-to-H¹ lift is the input to `reducedWeakOperator` in the image channel.
All dimensions, including zero, are covered.
-/

public noncomputable section

namespace JanetCartan.ContinuumRow

open PeriodicSobolevSpace

variable {n : ℕ}

private theorem weighted_bessel (s : ℕ) (u : OutputL2 n) (k : Fin n → ℤ) :
    weightedPeriodicL2FourierCoeff (s + 1) (periodicBesselInverse u) k =
      weightedPeriodicL2FourierCoeff s u k := by
  simp only [weightedPeriodicL2FourierCoeff_apply, periodicL2FourierCoeff_besselInverse,
    smul_smul, periodicSobolevWeight_succ_mul_bessel]

/-- The actual Bessel inverse gains one Sobolev order
(`app:ch_background:defn:bg-row`), including `s = 0`. -/
theorem periodicBesselInverse_mem_succ (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    periodicBesselInverse (toL2 s u) ∈ periodicSobolevLevel n (Euclidean n) (s + 1) := by
  change Memℓp (weightedPeriodicL2FourierCoeff (s + 1) _) 2
  have h : weightedPeriodicL2FourierCoeff (s + 1) (periodicBesselInverse (toL2 s u)) =
      analysis s u := by
    funext k
    exact weighted_bessel s (toL2 s u) k
  rw [h]
  exact lp.memℓp _

private def besselGainLinear (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →ₗ[ℝ]
      PeriodicSobolevSpace n (Euclidean n) (s + 1) where
  toFun u := ofL2 (s + 1) (periodicBesselInverse (toL2 s u))
    (periodicBesselInverse_mem_succ s u)
  map_add' u v := by
    apply toL2_injective (s + 1)
    simp only [map_add, toL2_ofL2]
  map_smul' c u := by
    apply toL2_injective (s + 1)
    simp only [map_smul, toL2_ofL2, RingHom.id_apply]

private theorem analysis_besselGainLinear (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    analysis (s + 1) (besselGainLinear s u) = analysis s u := by
  apply lp.ext
  funext k
  exact weighted_bessel s (toL2 s u) k

private theorem norm_besselGainLinear (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) : ‖besselGainLinear s u‖ = ‖u‖ := by
  rw [← (analysisIsometry (s + 1)).norm_map, ← (analysisIsometry s).norm_map]
  exact congrArg norm (analysis_besselGainLinear s u)

/-- The Bessel inverse as a bounded one-order Sobolev gain map
(`app:ch_background:defn:bg-row`). -/
def periodicBesselGain (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) (s + 1) :=
  (besselGainLinear s).mkContinuous 1 (fun u ↦ by
    rw [norm_besselGainLinear, one_mul])

/-- All Sobolev gains have the same underlying L² action
(`app:ch_background:defn:bg-row`). -/
@[simp] theorem toL2_periodicBesselGain (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 (s + 1) (periodicBesselGain s u) = periodicBesselInverse (toL2 s u) := by
  exact toL2_ofL2 _ _ _

/-- Compatibility as an equality of bounded maps (`app:ch_background:defn:bg-row`). -/
theorem toL2_comp_periodicBesselGain (s : ℕ) :
    toL2 (s + 1) ∘L periodicBesselGain (n := n) s = periodicBesselInverse ∘L toL2 s := by
  ext u
  rfl

/-- Literal Fourier identity at each Sobolev level (`app:not:fourier`). -/
theorem periodicL2FourierCoeff_besselGain (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (toL2 (s + 1) (periodicBesselGain s u)) =
      (Real.sqrt (1 + frequencyNorm k ^ 2))⁻¹ • periodicL2FourierCoeff k (toL2 s u) :=
  periodicL2FourierCoeff_besselInverse (toL2 s u) k

/-- The gain map preserves the weighted norm exactly (`app:not:fourier`). -/
@[simp] theorem norm_periodicBesselGain (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) : ‖periodicBesselGain s u‖ = ‖u‖ :=
  norm_besselGainLinear s u

/-- Operator norm bound for every Sobolev gain (`app:ch_background:defn:bg-row`). -/
theorem norm_periodicBesselGain_le (s : ℕ) : ‖periodicBesselGain (n := n) s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u ↦ by
    rw [norm_periodicBesselGain, one_mul])

/-- The L²-to-H¹ lift used before the weak reduced operator in
`app:ch_background:defn:bg-row`. The zero-order identification is isometric. -/
def periodicBesselLift : OutputL2 n →L[ℝ] PeriodicSobolevSpace n (Euclidean n) 1 :=
  periodicBesselGain 0 ∘L zeroEquivL2.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The lift is literally the same L² Bessel inverse
(`app:ch_background:defn:bg-row`). -/
@[simp] theorem toL2_periodicBesselLift (u : OutputL2 n) :
    toL2 1 (periodicBesselLift u) = periodicBesselInverse u := by
  exact toL2_periodicBesselGain 0 _

/-- Compatibility required by the image-channel consumer
(`app:ch_background:defn:bg-row`). -/
theorem toL2_comp_periodicBesselLift :
    toL2 1 ∘L periodicBesselLift (n := n) = periodicBesselInverse := by
  ext u
  rfl

/-- Literal Fourier identity for the lift (`app:not:fourier`). -/
theorem periodicL2FourierCoeff_besselLift (u : OutputL2 n) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (toL2 1 (periodicBesselLift u)) =
      (Real.sqrt (1 + frequencyNorm k ^ 2))⁻¹ • periodicL2FourierCoeff k u :=
  periodicL2FourierCoeff_besselInverse u k

/-- The lift is an isometry for the H¹ norm (`app:not:fourier`). -/
@[simp] theorem norm_periodicBesselLift (u : OutputL2 n) : ‖periodicBesselLift u‖ = ‖u‖ := by
  change ‖periodicBesselGain 0 (zeroEquivL2.symm u)‖ = ‖u‖
  rw [norm_periodicBesselGain, LinearIsometryEquiv.norm_map]

/-- The lift has norm at most one (`app:ch_background:defn:bg-row`). -/
theorem norm_periodicBesselLift_le : ‖periodicBesselLift (n := n)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u ↦ by
    rw [norm_periodicBesselLift, one_mul])

/-- The zeroth gain and the L² lift agree under the canonical isometry
(`app:ch_background:defn:bg-row`). -/
theorem periodicBesselGain_zero :
    periodicBesselGain (n := n) 0 = periodicBesselLift ∘L
      zeroEquivL2.toContinuousLinearEquiv.toContinuousLinearMap := by
  ext u
  rfl

/-- The Fourier multiplier in the manuscript's exponent convention
(`app:not:fourier`). -/
theorem periodicL2FourierCoeff_besselInverse_rpow (u : OutputL2 n) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (periodicBesselInverse u) =
      (1 + frequencyNorm k ^ 2) ^ (-(1 / 2 : ℝ)) • periodicL2FourierCoeff k u := by
  rw [periodicL2FourierCoeff_besselInverse, periodicBesselSymbol_eq_rpow]

end JanetCartan.ContinuumRow
