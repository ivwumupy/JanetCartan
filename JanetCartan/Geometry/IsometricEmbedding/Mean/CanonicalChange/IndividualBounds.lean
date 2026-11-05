module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.ComponentOperator
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Sobolev
public import JanetCartan.Analysis.Fourier.Periodic.Interpolation

/-!
# Individual bounds for the same canonical changes

The individual estimates of `main:prop:canonical` use the original raw
half-derivative bound and the uncut base, before any sample weight is applied.
This derives the component norm and the extra half power in the individual
`C^s` estimate. The finite accumulation keeps the original residual norm sum.
The consumers are the final sampled derivative amplitude in
`app:ch_pairs:lem:pairs-ledger` and the individual bound of
`main:lem:mean-recurrence`. Actual primitive raw and prepared-base profiles
still belong to their producers.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalChange
open ContinuumRow CurrentMean CurrentMean.SmoothPeriodicFamily

variable {n : ℕ} {ι m : Type*} [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ι → ℝ)
    (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)

omit [∀ i, CompleteSpace (Raw i)] in
/-- The individual component bound of `main:prop:canonical` follows from
the actual raw `H^0` estimate. The continuity witness `CG` is unchanged and
need not equal the sharper quantitative bound; only the literal action of
the SAME operator is used. -/
theorem norm_smoothRawCrossOperator_le_of_sobolev_zero
    {coefBound baseBound rawBound K : ℝ}
    (hcoefBound : 0 ≤ coefBound) (hbaseBound : 0 ≤ baseBound)
    (hrawBound : 0 ≤ rawBound) (hK : 0 ≤ K)
    (hcoef : cNorm (fundamentalCell n) 0 (periodicLift C) ≤ coefBound)
    (i : ι) (hbase : componentCSeminorm 0 i base ≤ baseBound)
    (hraw : ∀ v, periodicSobolevNorm 0 (fun x ↦ (G i v).val x ()) ≤
      rawBound * K ^ (1/2 : ℝ) * ‖v‖) :
    ‖smoothRawCrossOperator base C hC G CG hG i‖ ≤
      (2 * coefBound * baseBound * rawBound) * K ^ (1/2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [smoothRawCrossOperator_apply]
  apply (norm_smoothRawCrossResponse_toL2_le base C hC G i v).trans
  have hL2 : periodicL2Norm (fun x ↦ (G i v).val x ()) ≤
      rawBound * K ^ (1/2 : ℝ) * ‖v‖ := by
    let := matrixFrobeniusInnerProductSpace (m := m) (n := Fin n) (E := ℂ)
    simpa only [periodicSobolevNorm_zero_eq_periodicL2Norm (memLp (G i v) ())] using hraw v
  have hb : cNorm (fundamentalCell n) 0 (periodicLift (fun x ↦ base.val x i)) ≤ baseBound := hbase
  have hbnonneg := cNorm_nonneg (fundamentalCell n) 0 (periodicLift (fun x ↦ base.val x i))
  have hL2nonneg : 0 ≤ periodicL2Norm (fun x ↦ (G i v).val x ()) := Real.sqrt_nonneg _
  calc
    _ ≤ (2 * coefBound * baseBound) * (rawBound * K ^ (1/2 : ℝ) * ‖v‖) := by
      gcongr
    _ = _ := by ring

/-- The individual `K^(s+(n+1)/2)` estimate in
`app:ch_mean_pairs:eq:mean-canonical-bounds`, on the SAME constructed
component adjoint and inverse. No canonical-input bound is assumed. -/
theorem componentCSeminorm_smoothCanonicalDerivative_le
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (s : ℕ)
    {coefBound baseBound rawBound rawC K : ℝ}
    (hcoefBound : 0 ≤ coefBound) (hbaseBound : 0 ≤ baseBound)
    (hrawBound : 0 ≤ rawBound) (hrawC : 0 ≤ rawC) (hK : 0 < K)
    (hcoef : cNorm (fundamentalCell n) 0 (periodicLift C) ≤ coefBound)
    (i : ι) (hbase : componentCSeminorm 0 i base ≤ baseBound)
    (hrawH : ∀ v, periodicSobolevNorm 0 (fun x ↦ (G i v).val x ()) ≤
      rawBound * K ^ (1/2 : ℝ) * ‖v‖)
    (hraw : ∀ v, componentCSeminorm s () (G i v) ≤
      rawC * K ^ ((s : ℝ) + (n : ℝ) / 2) * ‖v‖) (e : OutputL2 n) :
    componentCSeminorm s i
        (smoothCanonicalDerivative (smoothRawCrossOperator base C hC G CG hG) G Q₀ e) ≤
      (rawC * (2 * coefBound * baseBound * rawBound) * ‖Q₀‖) *
        K ^ ((s : ℝ) + ((n : ℝ) + 1) / 2) * ‖e‖ := by
  have hA := norm_smoothRawCrossOperator_le_of_sobolev_zero base C hC G CG hG
    hcoefBound hbaseBound hrawBound hK.le hcoef i hbase hrawH
  have h := size_adjoint_inverse_le (smoothRawCrossOperator base C hC G CG hG i) Q₀
    (fun v ↦ componentCSeminorm s () (G i v)) (by positivity) hA hraw e
  change componentCSeminorm s i
    (smoothCanonicalDerivative (smoothRawCrossOperator base C hC G CG hG) G Q₀ e) ≤ _ at h
  apply h.trans_eq
  rw [show (s : ℝ) + ((n : ℝ) + 1) / 2 = ((s : ℝ) + (n : ℝ) / 2) + 1/2 by ring]
  simp only [Real.rpow_add hK]
  ring

omit G CG hG in
/-- The individual accumulated estimate of `main:lem:mean-recurrence`,
derived from the original component bounds. It has no sample-count or
update-count factor and remains valid for components with zero weight. -/
theorem componentCSeminorm_sum_smoothCanonicalDerivative_le
    (G : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ℕ → ι → ℝ)
    (hG : ∀ l i v, periodicL2Norm (fun x ↦ (G l i v).val x ()) ≤ CG l i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ) (s I : ℕ)
    {coefBound baseBound rawBound rawC Kmax inverseBound : ℝ}
    (hcoefBound : 0 ≤ coefBound) (hbaseBound : 0 ≤ baseBound)
    (hrawBound : 0 ≤ rawBound) (hrawC : 0 ≤ rawC) (hQ : ‖Q₀‖ ≤ inverseBound)
    (hcoef : cNorm (fundamentalCell n) 0 (periodicLift C) ≤ coefBound)
    (i : ι) (hbase : componentCSeminorm 0 i base ≤ baseBound)
    (hK : ∀ l < I, 0 < K l) (hKmax : ∀ l < I, K l ≤ Kmax)
    (hrawH : ∀ l < I, ∀ v, periodicSobolevNorm 0 (fun x ↦ (G l i v).val x ()) ≤
      rawBound * K l ^ (1/2 : ℝ) * ‖v‖)
    (hraw : ∀ l < I, ∀ v, componentCSeminorm s () (G l i v) ≤
      rawC * K l ^ ((s : ℝ) + (n : ℝ) / 2) * ‖v‖) (e : ℕ → OutputL2 n) :
    componentCSeminorm s i
      (∑ l ∈ Finset.range I, smoothCanonicalDerivative
        (smoothRawCrossOperator base C hC (G l) (CG l) (hG l)) (G l) Q₀ (e l)) ≤
      (rawC * (2 * coefBound * baseBound * rawBound) * inverseBound) *
        Kmax ^ ((s : ℝ) + ((n : ℝ) + 1) / 2) * ∑ l ∈ Finset.range I, ‖e l‖ := by
  have hQnonneg : 0 ≤ inverseBound := (norm_nonneg _).trans hQ
  apply MeanRecurrence.seminorm_sum_le
  intro l hl
  apply (componentCSeminorm_smoothCanonicalDerivative_le base C hC (G l) (CG l) (hG l)
    Q₀ s hcoefBound hbaseBound hrawBound hrawC (hK l hl) hcoef i hbase
    (hrawH l hl) (hraw l hl) (e l)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul
    (mul_le_mul_of_nonneg_left hQ (by positivity))
    (Real.rpow_le_rpow (hK l hl).le (hKmax l hl) (by positivity))
    (Real.rpow_nonneg (hK l hl).le _) (by positivity)

omit G CG hG in
/-- Adding the original prepared zero atom to its own canonical updates
gives the individual profile used by `app:ch_pairs:lem:pairs-ledger`.
The residual-sum and scalar smallness inputs are supplied by the checked
canonical run and the original forcing exponent. This deduction does not
assume a final amplitude estimate. -/
theorem componentCSeminorm_base_add_sum_smoothCanonicalDerivative_le
    (G : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ℕ → ι → ℝ)
    (hG : ∀ l i v, periodicL2Norm (fun x ↦ (G l i v).val x ()) ≤ CG l i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ) (s I : ℕ)
    {coefBound baseBound baseC rawBound rawC Kmax inverseBound ε : ℝ}
    (hcoefBound : 0 ≤ coefBound) (hbaseBound : 0 ≤ baseBound)
    (hrawBound : 0 ≤ rawBound) (hrawC : 0 ≤ rawC) (hQ : ‖Q₀‖ ≤ inverseBound)
    (hcoef : cNorm (fundamentalCell n) 0 (periodicLift C) ≤ coefBound)
    (i : ι) (hbase : componentCSeminorm 0 i base ≤ baseBound)
    (hbaseC : componentCSeminorm s i base ≤ baseC * Kmax ^ s)
    (hKmaxPos : 0 < Kmax)
    (hK : ∀ l < I, 0 < K l) (hKmax : ∀ l < I, K l ≤ Kmax)
    (hrawH : ∀ l < I, ∀ v, periodicSobolevNorm 0 (fun x ↦ (G l i v).val x ()) ≤
      rawBound * K l ^ (1/2 : ℝ) * ‖v‖)
    (hraw : ∀ l < I, ∀ v, componentCSeminorm s () (G l i v) ≤
      rawC * K l ^ ((s : ℝ) + (n : ℝ) / 2) * ‖v‖)
    (e : ℕ → OutputL2 n) (hsum : ∑ l ∈ Finset.range I, ‖e l‖ ≤ 2 * ε)
    (hsmall : ε * Kmax ^ (((n : ℝ) + 1) / 2) ≤ 1) :
    componentCSeminorm s i
      (base + ∑ l ∈ Finset.range I, smoothCanonicalDerivative
        (smoothRawCrossOperator base C hC (G l) (CG l) (hG l)) (G l) Q₀ (e l)) ≤
      (baseC + 2 * rawC * (2 * coefBound * baseBound * rawBound) * inverseBound) * Kmax ^ s := by
  let B := rawC * (2 * coefBound * baseBound * rawBound) * inverseBound
  have hQnonneg : 0 ≤ inverseBound := (norm_nonneg _).trans hQ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hacc := componentCSeminorm_sum_smoothCanonicalDerivative_le base C hC G CG hG Q₀ K s I
    hcoefBound hbaseBound hrawBound hrawC hQ hcoef i hbase hK hKmax hrawH hraw e
  have hbound : B * Kmax ^ ((s : ℝ) + ((n : ℝ) + 1) / 2) *
      ∑ l ∈ Finset.range I, ‖e l‖ ≤ 2 * B * Kmax ^ s := by
    calc
      _ ≤ B * Kmax ^ ((s : ℝ) + ((n : ℝ) + 1) / 2) * (2 * ε) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hB (Real.rpow_nonneg hKmaxPos.le _))
      _ = (2 * B * Kmax ^ s) * (ε * Kmax ^ (((n : ℝ) + 1) / 2)) := by
        rw [Real.rpow_add hKmaxPos, Real.rpow_natCast]
        ring
      _ ≤ (2 * B * Kmax ^ s) * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ componentCSeminorm s i base + componentCSeminorm s i
        (∑ l ∈ Finset.range I, smoothCanonicalDerivative
          (smoothRawCrossOperator base C hC (G l) (CG l) (hG l)) (G l) Q₀ (e l)) :=
      map_add_le_add _ _ _
    _ ≤ baseC * Kmax ^ s + 2 * B * Kmax ^ s := add_le_add hbaseC (hacc.trans hbound)
    _ = _ := by dsimp only [B]; ring

end JanetCartan.CanonicalChange
