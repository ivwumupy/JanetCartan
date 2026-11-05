module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.PeriodicAlgebra
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Cutoff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Translation of the fixed exterior multiplier

For `app:ch_background:prop:bg-inverse`, conjugation on the actual real,
Euclidean-vector L² space translates the cutoff with the positive-shift convention.
The mean-value inequality on a coordinate line bounds the divided coefficient
from a primitive first derivative of its Euclidean periodic lift. The exterior
normal has coefficient `χ²`, with derivative budget `2 M K`.

These estimates supply the exterior summand to
`norm_periodic_operator_differenceQuotient_le`; the parent translation construction
assembles it with the compact-chart PDO summands.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator

variable {n : ℕ}

/-- Positive translation of a continuous cutoff
(`app:ch_background:prop:bg-inverse`). -/
def translatedExteriorCutoff (χ : C(Torus n, ℝ)) (a : Torus n) : C(Torus n, ℝ) :=
  ⟨fun x ↦ χ (x + a), χ.continuous.comp (continuous_id.add continuous_const)⟩

/-- The literal divided coefficient in the exterior translation commutator
(`app:ch_background:prop:bg-inverse`). -/
def exteriorCutoffDifferenceQuotient (χ : C(Torus n, ℝ)) (i : Fin n) (h : ℝ) :
    C(Torus n, ℝ) :=
  h⁻¹ • (translatedExteriorCutoff χ (periodicCoordinateShift i h) - χ)

/-- Conjugation of the actual cutoff multiplier translates its coefficient
(`app:ch_background:prop:bg-inverse`). -/
theorem cutoffMultiplier_conjugation (χ : C(Torus n, ℝ)) (a : Torus n) :
    (periodicL2Translation a).toContinuousLinearMap.comp
      ((cutoffMultiplier χ).comp (periodicL2Translation (-a)).toContinuousLinearMap) =
        cutoffMultiplier (translatedExteriorCutoff χ a) := by
  ext1 v
  apply Lp.ext
  filter_upwards [periodicL2Translation_coe a
      (cutoffMultiplier χ (periodicL2Translation (-a) v)),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      (cutoffMultiplier_coeFn χ (periodicL2Translation (-a) v)),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      (periodicL2Translation_coe (-a) v),
    cutoffMultiplier_coeFn (translatedExteriorCutoff χ a) v] with x ht hm hi hr
  change periodicL2Translation a (cutoffMultiplier χ (periodicL2Translation (-a) v)) x = _
  rw [ht, hm, hi, hr]
  simp [translatedExteriorCutoff]

/-- The divided conjugation difference is multiplication by
`(χ(x + h eᵢ) - χ(x))/h` (`app:ch_background:prop:bg-inverse`). -/
theorem periodicConjugationDifference_cutoffMultiplier (χ : C(Torus n, ℝ))
    (i : Fin n) (h : ℝ) :
    periodicConjugationDifference (cutoffMultiplier χ) i h =
      cutoffMultiplier (exteriorCutoffDifferenceQuotient χ i h) := by
  rw [periodicConjugationDifference, cutoffMultiplier_conjugation]
  ext1 v
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul h⁻¹
      (cutoffMultiplier (translatedExteriorCutoff χ (periodicCoordinateShift i h)) v -
        cutoffMultiplier χ v),
    Lp.coeFn_sub (cutoffMultiplier (translatedExteriorCutoff χ (periodicCoordinateShift i h)) v)
      (cutoffMultiplier χ v),
    cutoffMultiplier_coeFn (translatedExteriorCutoff χ (periodicCoordinateShift i h)) v,
    cutoffMultiplier_coeFn χ v,
    cutoffMultiplier_coeFn (exteriorCutoffDifferenceQuotient χ i h) v]
    with x hs hd ht hc hr
  change (h⁻¹ • (cutoffMultiplier (translatedExteriorCutoff χ (periodicCoordinateShift i h)) v -
    cutoffMultiplier χ v) : OutputL2 n) x = _
  rw [hs, hr]
  simp only [Pi.smul_apply, hd, Pi.sub_apply, ht, hc]
  change h⁻¹ • (χ (x + periodicCoordinateShift i h) • v x - χ x • v x) =
    (h⁻¹ * (χ (x + periodicCoordinateShift i h) - χ x)) • v x
  rw [mul_smul, sub_smul]

private theorem exterior_quotient_coordinateLine (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (t : ℝ) :
    torusQuotient (x + t • EuclideanSpace.single i 1) =
      torusQuotient x + periodicCoordinateShift i t := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp [torusQuotient, periodicCoordinateShift]
  · simp [torusQuotient, periodicCoordinateShift, hj]

/-- Mean-value estimate from a primitive coordinate derivative of the periodic
lift, with no Lipschitz or commutator assumption
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_exteriorCutoff_sub_le (χ : C(Torus n, ℝ))
    (hχ : Differentiable ℝ (periodicLift χ)) (i : Fin n) {K : ℝ}
    (hK : ∀ x, ‖fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1)‖ ≤ K)
    (x : Torus n) (h : ℝ) :
    ‖χ (x + periodicCoordinateShift i h) - χ x‖ ≤ K * |h| := by
  have hsurj : Function.Surjective (@torusQuotient n) :=
    ((IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap).surjective
  obtain ⟨y, rfl⟩ := hsurj x
  have hd (t : ℝ) : HasDerivAt
      (fun s : ℝ ↦ periodicLift χ (y + s • EuclideanSpace.single i 1))
      (fderiv ℝ (periodicLift χ) (y + t • EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) t := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hχ (y + t • EuclideanSpace.single i 1)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ)) |>.const_add y)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) ↦ (hd t).hasDerivWithinAt)
    (fun t _ ↦ hK (y + t • EuclideanSpace.single i 1)) convex_univ
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ h)
  simpa only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs, periodicLift,
    Function.comp_apply, exterior_quotient_coordinateLine] using hb

/-- The divided coefficient is uniformly bounded, including the totalized zero
step (`app:ch_background:prop:bg-inverse`). -/
theorem norm_exteriorCutoffDifferenceQuotient_le (χ : C(Torus n, ℝ))
    (hχ : Differentiable ℝ (periodicLift χ)) (i : Fin n) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1)‖ ≤ K)
    (h : ℝ) : ‖exteriorCutoffDifferenceQuotient χ i h‖ ≤ K := by
  apply (ContinuousMap.norm_le _ hK0).mpr
  intro x
  change ‖h⁻¹ * (χ (x + periodicCoordinateShift i h) - χ x)‖ ≤ K
  by_cases hh : h = 0
  · simp [hh, hK0]
  rw [norm_mul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |h|⁻¹ * (K * |h|) := mul_le_mul_of_nonneg_left
      (norm_exteriorCutoff_sub_le χ hχ i hK x h) (inv_nonneg.mpr (abs_nonneg h))
    _ = K := by field_simp [hh]

/-- Uniform L² operator estimate for the fixed exterior multiplier, directly
usable in `norm_periodic_operator_differenceQuotient_le`
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_periodicConjugationDifference_cutoffMultiplier_le (χ : C(Torus n, ℝ))
    (hχ : Differentiable ℝ (periodicLift χ)) (i : Fin n) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1)‖ ≤ K)
    (h : ℝ) : ‖periodicConjugationDifference (cutoffMultiplier χ) i h‖ ≤ K := by
  rw [periodicConjugationDifference_cutoffMultiplier]
  exact (cutoffMultiplier_norm_le _).trans
    (norm_exteriorCutoffDifferenceQuotient_le χ hχ i hK0 hK h)

/-- Pointwise meaning of the exterior commutator on actual L² classes
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicConjugationDifference_cutoffMultiplier_coe (χ : C(Torus n, ℝ))
    (i : Fin n) (h : ℝ) (v : OutputL2 n) :
    periodicConjugationDifference (cutoffMultiplier χ) i h v =ᵐ[volume]
      fun x ↦ ((χ (x + periodicCoordinateShift i h) - χ x) / h) • v x := by
  rw [periodicConjugationDifference_cutoffMultiplier]
  simpa only [exteriorCutoffDifferenceQuotient, ContinuousMap.coe_smul,
    ContinuousMap.coe_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    translatedExteriorCutoff, ContinuousMap.coe_mk, div_eq_mul_inv, mul_comm] using
    cutoffMultiplier_coeFn (exteriorCutoffDifferenceQuotient χ i h) v

/-- The exterior normal `Mχ Mχ*` is literally multiplication by `χ²`
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-inverse`). -/
theorem cutoffMultiplier_sq_eq_comp_adjoint (χ : C(Torus n, ℝ)) :
    cutoffMultiplier (χ ^ 2) = (cutoffMultiplier χ).comp (cutoffMultiplier χ).adjoint := by
  rw [cutoffMultiplier_adjoint]
  ext1 v
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn (χ ^ 2) v,
    cutoffMultiplier_coeFn χ (cutoffMultiplier χ v), cutoffMultiplier_coeFn χ v]
    with x hs ho hi
  change cutoffMultiplier (χ ^ 2) v x = cutoffMultiplier χ (cutoffMultiplier χ v) x
  rw [hs, ho, hi]
  simp [pow_two, mul_smul]

/-- The shared exterior channel has normal coefficient `(1 - ψ)²`
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-inverse`). -/
theorem exteriorChannel_normal_eq_cutoff_sq (ψ : C(Torus n, ℝ)) :
    (exteriorChannel ψ).comp (exteriorChannel ψ).adjoint =
      cutoffMultiplier ((1 - ψ) ^ 2) :=
  (cutoffMultiplier_sq_eq_comp_adjoint (1 - ψ)).symm

/-- The product rule gives the primitive coordinate derivative of the exterior
normal coefficient (`app:ch_background:prop:bg-inverse`). -/
theorem fderiv_periodicLift_cutoff_sq (χ : C(Torus n, ℝ))
    (hχ : Differentiable ℝ (periodicLift χ)) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    fderiv ℝ (periodicLift (χ ^ 2 : C(Torus n, ℝ))) x (EuclideanSpace.single i 1) =
      2 * periodicLift χ x * fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1) := by
  have hd := ((hχ x).hasFDerivAt.pow 2).fderiv
  change fderiv ℝ (fun y ↦ periodicLift χ y ^ 2) x (EuclideanSpace.single i 1) = _
  rw [hd]
  simp [two_smul, add_mul]
  ring

/-- A bound `M` on the cutoff and `K` on its coordinate derivative yields
`2 M K` for the derivative of `χ²` (`app:ch_background:prop:bg-inverse`). -/
theorem norm_fderiv_periodicLift_cutoff_sq_le (χ : C(Torus n, ℝ))
    (hχ : Differentiable ℝ (periodicLift χ)) (i : Fin n) {M K : ℝ}
    (hM : ∀ x, ‖χ x‖ ≤ M)
    (hK : ∀ x, ‖fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1)‖ ≤ K)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (periodicLift (χ ^ 2 : C(Torus n, ℝ))) x (EuclideanSpace.single i 1)‖ ≤ 2 * M * K := by
  rw [fderiv_periodicLift_cutoff_sq χ hχ x i, norm_mul, norm_mul]
  norm_num only [Real.norm_ofNat]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hM (torusQuotient x)) (by norm_num))
    (hK x) (norm_nonneg _) (mul_nonneg (by norm_num)
      ((norm_nonneg (χ (torusQuotient x))).trans (hM _)))

/-- The fixed exterior normal has a uniform divided conjugation bound derived
only from primitive coefficient and first-derivative budgets
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_periodicConjugationDifference_cutoff_sq_le (χ : C(Torus n, ℝ))
    (hχ : Differentiable ℝ (periodicLift χ)) (i : Fin n) {M K : ℝ}
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K) (hM : ∀ x, ‖χ x‖ ≤ M)
    (hK : ∀ x, ‖fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1)‖ ≤ K)
    (h : ℝ) :
    ‖periodicConjugationDifference (cutoffMultiplier (χ ^ 2)) i h‖ ≤ 2 * M * K := by
  exact norm_periodicConjugationDifference_cutoffMultiplier_le (χ ^ 2) (hχ.pow 2) i
    (mul_nonneg (mul_nonneg (by norm_num) hM0) hK0)
    (norm_fderiv_periodicLift_cutoff_sq_le χ hχ i hM hK) h

/-- The exterior normal estimate in the exact form consumed by the H¹
inverse argument (`app:ch_background:prop:bg-inverse`). -/
theorem norm_cutoff_sq_differenceQuotient_le (χ : C(Torus n, ℝ))
    (hχ : Differentiable ℝ (periodicLift χ)) (i : Fin n) {M K : ℝ}
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K) (hM : ∀ x, ‖χ x‖ ≤ M)
    (hK : ∀ x, ‖fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1)‖ ≤ K)
    (h : ℝ) (v : OutputL2 n) :
    ‖cutoffMultiplier (χ ^ 2) (periodicL2DifferenceQuotient i h v)‖ ≤
      ‖periodicL2DifferenceQuotient i h (cutoffMultiplier (χ ^ 2) v)‖ +
        (2 * M * K) * ‖v‖ := by
  exact (norm_periodic_operator_differenceQuotient_le _ i h v).trans
    (add_le_add_right (mul_le_mul_of_nonneg_right
      (norm_periodicConjugationDifference_cutoff_sq_le χ hχ i hM0 hK0 hM hK h)
      (norm_nonneg v)) _)

end JanetCartan.ContinuumCommutator
