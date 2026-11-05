module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.IndividualBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.PrefixData

/-!
# Canonical Fourier bounds from the original raw derivative profile

For `main:eq:old-canonical`, apply the original wide-band prefix before the
same full smooth raw map. Its cross operator is exactly the existing grouped
prefix row in refined coordinates. The primitive raw `H^0` bound therefore
gives the canonical initial-data estimates without a separate kernel-band
estimate or an assumed canonical-input bound. The original raw measure,
detector, zero atom and fixed inverse are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.CurrentMean
open CanonicalChange CanonicalTailRealization CanonicalDataBounds
open RawInputPartition RawInputRealization RawPrimary ContinuumRow SmoothPeriodicFamily

variable {n J : ℕ} {m ι : Type*} [Fintype m]

/-- The actual raw derivative map at a retained prefix, using the original
wide-band projection and its real Hilbert coordinate change
(`main:eq:old-canonical`, `app:ch_mean_pairs:defn:mean-canonical`). -/
def canonicalWidePrefixRawMap
    (G : WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ)) (L : ℕ) :
    RefinedInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ) :=
  G.comp ((((widePrefix n J L).restrictScalars ℝ).toLinearMap).comp
    (realWideRefinement n J).symm.toLinearEquiv.toLinearMap)

/-- The original raw projection supplies the prefix continuity witness
from the SAME full raw map (`main:eq:old-canonical`). Its Hilbert norm is
contractive; the coordinate change preserves both real quadratures. This
qualitative continuity constant is separate from the sharp raw profile
used for the uniform canonical estimates. -/
theorem periodicL2Norm_canonicalWidePrefixRawMap_le
    (G : WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ℝ)
    (hG : ∀ v, periodicL2Norm (fun x ↦ (G v).val x ()) ≤ CG * ‖v‖)
    (L : ℕ) (v : RefinedInput n J) :
    periodicL2Norm (fun x ↦ (canonicalWidePrefixRawMap G L v).val x ()) ≤ max CG 0 * ‖v‖ := by
  have hprefix (w : WideInput n J) : ‖widePrefix n J L w‖ ≤ ‖w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    rw [widePrefix_apply]
    split_ifs
    · exact le_rfl
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  change periodicL2Norm (fun x ↦ (G (widePrefix n J L ((realWideRefinement n J).symm v))).val x ()) ≤ _
  apply (hG _).trans
  apply (mul_le_mul_of_nonneg_right (le_max_left CG 0) (norm_nonneg _)).trans
  apply mul_le_mul_of_nonneg_left _ (le_max_right CG 0)
  exact (hprefix _).trans_eq ((realWideRefinement n J).symm.norm_map v)

variable (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (G : ι → WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ι → ℝ)
    (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)

/-- Taking the cross response after the original raw prefix produces the
SAME full component composed with the grouped projection
(`main:eq:canonical-identity`). Continuity witnesses do not select a new
operator, and no kernel or response-integral equality is assumed. -/
theorem smoothRawCrossOperator_widePrefix_eq_groupedPrefixRow (K : ℝ)
    (CGcut : ι → ℝ)
    (hGcut : ∀ i v, periodicL2Norm (fun x ↦
      (canonicalWidePrefixRawMap (G i) (cutoffCount K) v).val x ()) ≤ CGcut i * ‖v‖)
    (i : ι) :
    smoothRawCrossOperator base C hC
      (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) CGcut hGcut i =
      groupedPrefixRow (refinedRow (smoothRawCrossOperator base C hC G CG hG i)) K := by
  apply ContinuousLinearMap.ext
  intro v
  have hp : widePrefix n J (cutoffCount K) ((realWideRefinement n J).symm v) =
      (realWideRefinement n J).symm (refinedPrefix n J (cutoffCount K) v) := by
    apply (realWideRefinement n J).injective
    change wideRefinement n J (widePrefix n J (cutoffCount K) ((wideRefinement n J).symm v)) = _
    rw [wideRefinement_prefix]
    simp only [LinearIsometryEquiv.apply_symm_apply]
  change smoothResidualToL2 n (smoothRawCrossResponse base C hC
    (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) i v) =
      smoothResidualToL2 n (smoothRawCrossResponse base C hC G i
        ((realWideRefinement n J).symm (refinedPrefix n J (cutoffCount K) v)))
  congr 1
  apply Subtype.ext
  funext x u
  cases u
  simp only [smoothRawCrossResponse_apply, canonicalWidePrefixRawMap, LinearMap.comp_apply]
  change C x ((2 : ℝ) • mixedHermitianTensor (base.val x i)
    (((G i) (widePrefix n J (cutoffCount K) ((realWideRefinement n J).symm v))).val x ())) = _
  rw [hp]

/-- The canonical derivative is the SAME full raw map evaluated on the
original wide-prefix adjoint datum (`main:eq:old-canonical`,
`main:eq:canonical-identity`). The second raw projection is idempotent, so
the derivative and the initial Fourier measure use exactly the same input,
with no replacement wave or independently chosen datum. -/
theorem smoothCanonicalDerivative_widePrefix_eq (K : ℝ)
    (CGcut : ι → ℝ)
    (hGcut : ∀ i v, periodicL2Norm (fun x ↦
      (canonicalWidePrefixRawMap (G i) (cutoffCount K) v).val x ()) ≤ CGcut i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (r : OutputL2 n) (x : Torus n) (i : ι) :
    (smoothCanonicalDerivative
      (smoothRawCrossOperator base C hC
        (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) CGcut hGcut)
      (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) Q₀ r).val x i =
      (G i (widePrefix n J (cutoffCount K)
        ((smoothRawCrossOperator base C hC G CG hG i).adjoint (Q₀ r)))).val x () := by
  change (canonicalWidePrefixRawMap (G i) (cutoffCount K)
    ((smoothRawCrossOperator base C hC
      (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) CGcut hGcut i).adjoint (Q₀ r))).val x () = _
  rw [smoothRawCrossOperator_widePrefix_eq_groupedPrefixRow base C hC G CG hG K CGcut hGcut i]
  change (G i (widePrefix n J (cutoffCount K) ((realWideRefinement n J).symm
    (adjointInput (groupedPrefixRow (refinedRow (smoothRawCrossOperator base C hC G CG hG i)) K) Q₀ r)))).val x () = _
  rw [adjointInput_groupedPrefixRow, adjoint_refinedRow]
  change (G i (widePrefix n J (cutoffCount K) ((wideRefinement n J).symm
    (refinedPrefix n J (cutoffCount K) ((wideRefinement n J)
      ((smoothRawCrossOperator base C hC G CG hG i).adjoint (Q₀ r))))))).val x () = _
  rw [← wideRefinement_prefix, LinearIsometryEquiv.symm_apply_apply]
  have hp (w : WideInput n J) : widePrefix n J (cutoffCount K)
      (widePrefix n J (cutoffCount K) w) = widePrefix n J (cutoffCount K) w := by
    apply PiLp.ext
    intro j
    simp only [widePrefix_apply]
    split_ifs <;> rfl
  rw [hp]


include hG in
/-- The actual canonical Fourier `L¹` and initial `C^s` estimates follow
from the SAME raw `H^0` profile (`main:prop:canonical`). The component norm
is derived; no kernel-band or canonical-input bound is assumed. All constants
are explicit in the primitive measurement, prepared-base, raw and inverse
bounds, independently of the full input ceiling and update count. -/
theorem canonicalWidePrefix_initialData_bounds (hn : 1 ≤ n)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    {coefBound baseBound rawBound inverseBound K : ℝ}
    (hcoefBound : 0 ≤ coefBound) (hbaseBound : 0 ≤ baseBound) (hrawBound : 0 ≤ rawBound)
    (hcoef : cNorm (fundamentalCell n) 0 (periodicLift C) ≤ coefBound)
    (hQ : ‖Q₀‖ ≤ inverseBound) (hK : 1 ≤ K) (hKJ : cutoffCount K ≤ J)
    (CGcut : ι → ℝ)
    (hGcut : ∀ i v, periodicL2Norm (fun x ↦
      (canonicalWidePrefixRawMap (G i) (cutoffCount K) v).val x ()) ≤ CGcut i * ‖v‖)
    (i : ι) (hbase : componentCSeminorm 0 i base ≤ baseBound)
    (hraw : ∀ v, periodicSobolevNorm 0 (fun x ↦
      (canonicalWidePrefixRawMap (G i) (cutoffCount K) v).val x ()) ≤
        rawBound * K ^ (1/2 : ℝ) * ‖v‖) (r : OutputL2 n) :
    let A := smoothRawCrossOperator base C hC
      (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) CGcut hGcut i
    let β := fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val
    (∫ η, ‖fourierDensity β A Q₀ r η‖) ≤
      (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) *
        (2 * coefBound * baseBound * rawBound) * inverseBound) * K ^ (((n : ℝ) + 1) / 2) * ‖r‖ ∧
    ∀ (s : ℕ) (S : Set (Euclidean (n - 1))), cNorm S s (initialDatum β A Q₀ r) ≤
      (((s + 1 : ℕ) : ℝ) * refinedFourierConstant n M * 4 ^ ((s : ℝ) + (n : ℝ) / 2) *
        (2 * coefBound * baseBound * rawBound) * inverseBound) *
          K ^ ((s : ℝ) + ((n : ℝ) + 1) / 2) * ‖r‖ := by
  have hA := norm_smoothRawCrossOperator_le_of_sobolev_zero base C hC
    (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) CGcut hGcut
    hcoefBound hbaseBound hrawBound (zero_le_one.trans hK) hcoef i hbase hraw
  rw [← Real.sqrt_eq_rpow] at hA
  dsimp only
  rw [smoothRawCrossOperator_widePrefix_eq_groupedPrefixRow base C hC G CG hG K CGcut hGcut i] at hA ⊢
  constructor
  · exact integral_norm_fourierDensity_groupedPrefixRow_le hn
      (fun j ↦ measurable_weightedRadialBand hd j.1.val) hM
      (fun j ↦ norm_weightedRadialBand_le hb j.1.val) (by positivity) hK hKJ _ Q₀ hA hQ r
  · intro s S
    exact cNorm_initialDatum_groupedPrefixRow_le hn
      (fun j ↦ measurable_weightedRadialBand hd j.1.val) hM
      (fun j ↦ norm_weightedRadialBand_le hb j.1.val) (by positivity) hK hKJ _ Q₀ hA hQ r s S

end JanetCartan.CurrentMean
