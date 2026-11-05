module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.PeriodicAlgebra
public import JanetCartan.Analysis.Operator.CoerciveInverse
public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# First-order regularity of the coercive periodic inverse

For `app:ch_background:prop:bg-inverse`, coercivity and a uniform bound for the
actual divided translation conjugation imply that `E v ∈ H¹` forces `v ∈ H¹`.
The proof estimates bounded difference quotients of the L² class `v` before
asserting any derivative or Sobolev regularity of `v`.

The translation bound is required only for `0 < |h| ≤ h₀`, with any `h₀ > 0`.
Larger steps are bounded using the translation isometry and `2 / h₀`, so the
existing converse for `|h| ≤ 1` applies without enlarging the producer's
neighborhood. Absolute values on `B` avoid an unnecessary sign assumption.

`periodicCoerciveInverseH1` is the bounded H¹ restriction of the same `E.inverse`
constructed by `CoerciveInverse`, with an additive estimate in the H¹ and L²
norms of the datum. The consumer `jc-continuum-elliptic-bootstrap` must supply
the gap from `jc-continuum-normal` and the conjugation estimate from
`ContinuumCommutator/Translation/Assembly` and `Translation/Exterior` for its
actual normal. No Sobolev regularity implication is an input here.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator

open scoped InnerProductSpace

variable {n : ℕ}

/-- The finite remainder estimate for steps outside the producer's translation
neighborhood (`app:ch_background:prop:bg-inverse`). -/
private theorem norm_differenceQuotient_le_remainder
    (v : PeriodicL2 n (Euclidean n)) (i : Fin n) (h : ℝ)
    {h₀ : ℝ} (hh₀ : 0 < h₀) (hh : h₀ ≤ |h|) :
    ‖periodicL2DifferenceQuotient i h v‖ ≤ 2 * h₀⁻¹ * ‖v‖ := by
  change ‖h⁻¹ • (periodicL2Translation (periodicCoordinateShift i h) v - v)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |h|⁻¹ * (‖periodicL2Translation (periodicCoordinateShift i h) v‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (abs_nonneg h))
    _ = |h|⁻¹ * (2 * ‖v‖) := by rw [norm_periodicL2Translation]; ring
    _ ≤ h₀⁻¹ * (2 * ‖v‖) :=
      mul_le_mul_of_nonneg_right (inv_anti₀ hh₀ hh) (by positivity)
    _ = _ := by ring

variable (E : PeriodicL2 n (Euclidean n) →L[ℝ] PeriodicL2 n (Euclidean n))
  {c B h₀ : ℝ} (hc : 0 < c)
  (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫_ℝ)
  (hh₀ : 0 < h₀)
  (htranslation : ∀ (i : Fin n) (h : ℝ), 0 < |h| → |h| ≤ h₀ →
    ‖periodicConjugationDifference E i h‖ ≤ B)

include hc hgap hh₀ htranslation

/-- Coercivity and the actual conjugation estimate give bounded difference
quotients of `v` from H¹ regularity of `E v`
(`app:ch_background:prop:bg-inverse`). No derivative of `v` is assumed. -/
theorem hasBoundedPeriodicDifferenceQuotients_of_coercive
    (v : PeriodicL2 n (Euclidean n)) (hEv : E v ∈ periodicSobolevLevel n (Euclidean n) 1) :
    HasBoundedPeriodicDifferenceQuotients v
      (c⁻¹ * (‖PeriodicSobolevSpace.ofL2 1 (E v) hEv‖ + |B| * ‖v‖) +
        2 * h₀⁻¹ * ‖v‖) := by
  intro i h hh _
  by_cases hsmall : |h| ≤ h₀
  · have hforward : ‖periodicL2DifferenceQuotient i h (E v)‖ ≤
        ‖PeriodicSobolevSpace.ofL2 1 (E v) hEv‖ :=
      norm_periodicL2DifferenceQuotient_le_sobolev
        (PeriodicSobolevSpace.ofL2 1 (E v) hEv) i h (abs_pos.mp hh)
    have hbound := (CoerciveInverse.mul_norm_le_norm_apply E hgap
      (periodicL2DifferenceQuotient i h v)).trans
      ((norm_periodic_operator_differenceQuotient_le E i h v).trans
        (add_le_add hforward (mul_le_mul_of_nonneg_right
          ((htranslation i h hh hsmall).trans (le_abs_self B)) (norm_nonneg v))))
    exact ((le_inv_mul_iff₀ hc).mpr hbound).trans (le_add_of_nonneg_right (by positivity))
  · exact (norm_differenceQuotient_le_remainder v i h hh₀ (le_of_not_ge hsmall)).trans
      (le_add_of_nonneg_left (by positivity))

/-- First-order regularity for the actual periodic L² class
(`app:ch_background:prop:bg-inverse`). This is the order-one input to the
consumer's elliptic bootstrap. -/
theorem mem_periodicSobolevLevel_one_of_coercive
    (v : PeriodicL2 n (Euclidean n)) (hEv : E v ∈ periodicSobolevLevel n (Euclidean n) 1) :
    v ∈ periodicSobolevLevel n (Euclidean n) 1 := by
  exact mem_periodicSobolevLevel_one_of_boundedDifferenceQuotients v _ (by positivity)
    (hasBoundedPeriodicDifferenceQuotients_of_coercive E hc hgap hh₀ htranslation v hEv)

/-- The quantitative first-order estimate, with the original Sobolev norm and
an explicit dependence on the translation radius
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_periodicSobolevSpace_one_le_of_coercive
    (v : PeriodicL2 n (Euclidean n)) (hEv : E v ∈ periodicSobolevLevel n (Euclidean n) 1) :
    ‖PeriodicSobolevSpace.ofL2 1 v
      (mem_periodicSobolevLevel_one_of_coercive E hc hgap hh₀ htranslation v hEv)‖ ≤
      ‖v‖ + Real.sqrt n *
        (c⁻¹ * (‖PeriodicSobolevSpace.ofL2 1 (E v) hEv‖ + |B| * ‖v‖) +
          2 * h₀⁻¹ * ‖v‖) := by
  let C := c⁻¹ * (‖PeriodicSobolevSpace.ofL2 1 (E v) hEv‖ + |B| * ‖v‖) +
    2 * h₀⁻¹ * ‖v‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hδ := hasBoundedPeriodicDifferenceQuotients_of_coercive E hc hgap hh₀ htranslation v hEv
  have hb := norm_periodicSobolevSpace_one_le_of_boundedDifferenceQuotients v C hC hδ
  apply hb.trans
  change Real.sqrt (‖v‖ ^ 2 + (n : ℝ) * C ^ 2) ≤ ‖v‖ + Real.sqrt n * C
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    nlinarith [mul_nonneg (norm_nonneg v) (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hC)]

/-- The same coercive L² inverse preserves H¹
(`app:ch_background:prop:bg-inverse`). -/
theorem inverse_mem_periodicSobolevLevel_one_of_coercive
    (e : PeriodicL2 n (Euclidean n)) (he : e ∈ periodicSobolevLevel n (Euclidean n) 1) :
    E.inverse e ∈ periodicSobolevLevel n (Euclidean n) 1 := by
  apply mem_periodicSobolevLevel_one_of_coercive E hc hgap hh₀ htranslation
  rwa [CoerciveInverse.apply_inverse E hc hgap]

/-- The additive H¹ estimate for the same inverse in
`app:ch_background:eq:bg-r-inverse` at order one. The conjugation bound `B`
occurs only in the coefficient of the datum's L² norm. -/
theorem norm_inverse_periodicSobolevSpace_one_le_of_coercive
    (e : PeriodicL2 n (Euclidean n)) (he : e ∈ periodicSobolevLevel n (Euclidean n) 1) :
    ‖PeriodicSobolevSpace.ofL2 1 (E.inverse e)
      (inverse_mem_periodicSobolevLevel_one_of_coercive E hc hgap hh₀ htranslation e he)‖ ≤
      Real.sqrt n * c⁻¹ * ‖PeriodicSobolevSpace.ofL2 1 e he‖ +
        (1 + Real.sqrt n * (c⁻¹ * |B| + 2 * h₀⁻¹)) * c⁻¹ * ‖e‖ := by
  have hEe : E (E.inverse e) ∈ periodicSobolevLevel n (Euclidean n) 1 := by
    rwa [CoerciveInverse.apply_inverse E hc hgap]
  have hb : ‖PeriodicSobolevSpace.ofL2 1 (E.inverse e)
      (inverse_mem_periodicSobolevLevel_one_of_coercive E hc hgap hh₀ htranslation e he)‖ ≤
      ‖E.inverse e‖ + Real.sqrt n *
        (c⁻¹ * (‖PeriodicSobolevSpace.ofL2 1 e he‖ + |B| * ‖E.inverse e‖) +
          2 * h₀⁻¹ * ‖E.inverse e‖) := by
    simpa only [PeriodicSobolevSpace.norm_eq, PeriodicSobolevSpace.toL2_ofL2,
      CoerciveInverse.apply_inverse E hc hgap] using
      norm_periodicSobolevSpace_one_le_of_coercive E hc hgap hh₀ htranslation
        (E.inverse e) hEe
  calc
    _ ≤ _ := hb
    _ ≤ c⁻¹ * ‖e‖ + Real.sqrt n *
        (c⁻¹ * (‖PeriodicSobolevSpace.ofL2 1 e he‖ + |B| * (c⁻¹ * ‖e‖)) +
          2 * h₀⁻¹ * (c⁻¹ * ‖e‖)) := by
      have hbase := CoerciveInverse.norm_inverse_apply_le E hc hgap e
      gcongr
    _ = _ := by ring

/-- The bounded H¹ restriction of `E.inverse`
(`app:ch_background:prop:bg-inverse`). -/
def periodicCoerciveInverseH1 :
    PeriodicSobolevSpace n (Euclidean n) 1 →L[ℝ] PeriodicSobolevSpace n (Euclidean n) 1 :=
  ({ toFun := fun e ↦ PeriodicSobolevSpace.ofL2 1
        (E.inverse (PeriodicSobolevSpace.toL2 1 e))
        (inverse_mem_periodicSobolevLevel_one_of_coercive E hc hgap hh₀ htranslation
          _ (PeriodicSobolevSpace.toL2_mem 1 e))
     map_add' := by
       intro e f
       apply PeriodicSobolevSpace.toL2_injective 1
       simp
     map_smul' := by
       intro r e
       apply PeriodicSobolevSpace.toL2_injective 1
       simp } :
      PeriodicSobolevSpace n (Euclidean n) 1 →ₗ[ℝ] PeriodicSobolevSpace n (Euclidean n) 1
    ).mkContinuous
    (Real.sqrt n * c⁻¹ + (1 + Real.sqrt n * (c⁻¹ * |B| + 2 * h₀⁻¹)) * c⁻¹)
    (by
      intro e
      have hb := norm_inverse_periodicSobolevSpace_one_le_of_coercive
        E hc hgap hh₀ htranslation (PeriodicSobolevSpace.toL2 1 e)
          (PeriodicSobolevSpace.toL2_mem 1 e)
      change ‖PeriodicSobolevSpace.ofL2 1 (E.inverse (PeriodicSobolevSpace.toL2 1 e)) _‖ ≤ _
      simp only [PeriodicSobolevSpace.ofL2_toL2] at hb
      calc
        _ ≤ _ := hb
        _ ≤ Real.sqrt n * c⁻¹ * ‖e‖ +
            (1 + Real.sqrt n * (c⁻¹ * |B| + 2 * h₀⁻¹)) * c⁻¹ * ‖e‖ := by
          gcongr
          exact PeriodicSobolevSpace.norm_toL2_le 1 e
        _ = _ := by ring)

/-- Forgetting H¹ regularity recovers exactly the original L² inverse
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem toL2_periodicCoerciveInverseH1 (e : PeriodicSobolevSpace n (Euclidean n) 1) :
    PeriodicSobolevSpace.toL2 1 (periodicCoerciveInverseH1 E hc hgap hh₀ htranslation e) =
      E.inverse (PeriodicSobolevSpace.toL2 1 e) := rfl

/-- Explicit H¹ operator norm bound for the same inverse
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_periodicCoerciveInverseH1_le :
    ‖periodicCoerciveInverseH1 E hc hgap hh₀ htranslation‖ ≤
      Real.sqrt n * c⁻¹ + (1 + Real.sqrt n * (c⁻¹ * |B| + 2 * h₀⁻¹)) * c⁻¹ := by
  apply LinearMap.mkContinuous_norm_le
  positivity

end JanetCartan.ContinuumCommutator
