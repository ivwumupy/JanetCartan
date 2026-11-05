module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Substitution
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CarrierMean
import Mathlib.Algebra.Order.Star.Real

/-!
# Positivity of the transport diagonal

The detector integral and reflected-matrix comparison of
`app:ch_background:eq:bg-real-symbol`. These results concern the literal diagonal
amplitude. Identification as a principal symbol requires the separate full
amplitude reduction and bounded-frequency smoothing arguments.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n N : ℕ}

/-- Each diagonal detector is a nonnegative weight times `q qᵀ`, including
arbitrary real regularization and angular masks
(`app:ch_background:eq:bg-symbol`). -/
theorem normalDensityEntry_diagonal_posSemidef (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (x : Torus n) (u : CarrierVariable n) :
    Matrix.PosSemidef (fun i j ↦ normalDensityEntry d m x x u i j) := by
  let q := reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) u.1)
  let w := d.measurementCutoff x ^ 2 * m u ^ 2 *
    d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) ^ 2 * d.highCutoff ‖u.2‖ ^ 2 *
      ‖u.2‖ * ‖d.normalField (d.chartPoint x) u.1‖ ^ 4
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hq := (Matrix.posSemidef_vecMulVec_self_star (fun i ↦ q i)).smul hw
  have he : (fun i j ↦ normalDensityEntry d m x x u i j) =
      w • Matrix.vecMulVec (fun i ↦ q i) (star (fun i ↦ q i)) := by
    ext i j
    simp only [normalDensityEntry, Matrix.smul_apply, Matrix.vecMulVec_apply,
      star_trivial, smul_eq_mul]
    dsimp [w, q]
    ring
  rw [he]
  exact hq

/-- Absolute inverse-Jacobian multiplication and zero extension preserve the
positive detector matrix (`app:ch_background:eq:bg-symbol`). -/
theorem inverseDensityEntry_diagonal_posSemidef (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (x : Torus n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean 2) (k : Euclidean n) :
    Matrix.PosSemidef (fun i j ↦ inverseDensityEntry d m x x e D Ψ U J v k i j) := by
  by_cases hk : k ∈ Ψ v '' D v
  · simp only [inverseDensityEntry, Set.indicator_of_mem hk]
    exact (normalDensityEntry_diagonal_posSemidef d m x
      (chartCarrierVariable e v (U v k))).smul (show (0 : ℝ) ≤ |(J v (U v k)).det|⁻¹ by positivity)
  · simp only [inverseDensityEntry, Set.indicator_of_notMem hk]
    exact Matrix.PosSemidef.zero

/-- Positivity of the actual spectator integral, with entrywise integrability
justifying finite matrix contractions (`app:ch_background:eq:bg-symbol`). -/
theorem fullAmplitudeEntry_diagonal_posSemidef (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (x : Torus n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (k : Euclidean n)
    (hint : ∀ i j, Integrable (fun v ↦ inverseDensityEntry d m x x e D Ψ U J v k i j)) :
    Matrix.PosSemidef (fun i j ↦ fullAmplitudeEntry d m x x e D Ψ U J k i j) :=
  NormalizedBackground.posSemidef_integral_entries hint
    (fun v ↦ inverseDensityEntry_diagonal_posSemidef d m x e D Ψ U J v k)

/-- The homogeneous diagonal prescribed by `app:ch_background:eq:bg-symbol`:
set the high cutoff and regularization to one in the full amplitude. No
homogeneity of arbitrary input geometry is asserted by this definition. -/
def homogeneousDiagonalMatrix (d : CarrierData n N) (x : Torus n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ fullAmplitudeEntry { d with highCutoff := fun _ ↦ 1 }
    (fun _ ↦ 1) x x e D Ψ U J k i j

/-- The reflected diagonal matrix in `app:ch_background:eq:bg-real-symbol`.
The angular mask is not assumed even. -/
def reflectedDiagonalMatrix (a : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  (2 * (2 * Real.pi) ^ n) • (a k + a (-k))

/-- The positive-semidefinite comparison in `app:ch_background:eq:bg-real-symbol`.
Only the reflected detector needs to be positive for this comparison. -/
theorem reflectedDiagonalMatrix_sub_posSemidef
    (a : Euclidean n → Matrix (Fin n) (Fin n) ℝ) (k : Euclidean n)
    (ha : (a (-k)).PosSemidef) :
    (reflectedDiagonalMatrix a k - (2 * (2 * Real.pi) ^ n) • a k).PosSemidef := by
  have he : reflectedDiagonalMatrix a k - (2 * (2 * Real.pi) ^ n) • a k =
      (2 * (2 * Real.pi) ^ n) • a (-k) := by
    simp [reflectedDiagonalMatrix, smul_add]
  rw [he]
  exact ha.smul (by positivity)

/-- The actual homogeneous spectator integral satisfies the reflected comparison
without any evenness hypothesis (`app:ch_background:eq:bg-real-symbol`). -/
theorem homogeneousDiagonalMatrix_reflected_comparison (d : CarrierData n N)
    (x : Torus n) (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (k : Euclidean n)
    (hint : ∀ i j, Integrable (fun v ↦ inverseDensityEntry
      { d with highCutoff := fun _ ↦ 1 } (fun _ ↦ 1) x x e D Ψ U J v (-k) i j)) :
    (reflectedDiagonalMatrix (homogeneousDiagonalMatrix d x e D Ψ U J) k -
      (2 * (2 * Real.pi) ^ n) • homogeneousDiagonalMatrix d x e D Ψ U J k).PosSemidef :=
  reflectedDiagonalMatrix_sub_posSemidef _ _
    (fullAmplitudeEntry_diagonal_posSemidef _ _ _ _ _ _ _ _ _ hint)

end JanetCartan.ContinuumRow.TransportKernel
