module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Realization

/-!
# The continuum carrier extension from regularized full normals

The conditional deduction of `app:ch_background:prop:bg-frame`, Step 1, on the
literal initial measure and full complex torus output of `app:ch_background:eq:bg-T`.
The producer supplies cutoff operators realizing the literal masked integrals,
exact full-output identities `T_R T_R* = N_R`, and uniform bounds for `N_R` from
the complete normal amplitudes. Compact smooth density is proved, cutoff removal
is eventual equality on compact supports, and Fatou gives the uncut test bound.
No uncut L² bound or L² convergence is assumed.

The actual inputs remain obligations of `jc-deduce-continuum-carrier-regularization`,
`jc-continuum-transport-normal-kernel`, `jc-continuum-transport-symbol`, and
`jc-normal-compact-frequency-realization`. Consumers `jc-continuum-row`,
`jc-continuum-initial-adjoint`, and `jc-continuum-l2-inverse` must instantiate
these hypotheses. This deduction does not assert the geometric construction.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.ContinuumRow

variable {n N : ℕ}

/-- Hilbert `TT*` gives the square-root bound from the complete normal on
full output (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_carrierRegularization_le
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (A : ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n)
    {C : ℝ} (hC : 0 ≤ C) (hA : T.comp T.adjoint = A) (hb : ‖A‖ ≤ C) :
    ‖T‖ ≤ Real.sqrt C := by
  apply (Real.le_sqrt (norm_nonneg _) hC).mpr
  have he := ContinuousLinearMap.norm_adjoint_comp_self T.adjoint
  simp only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] at he
  rw [sq, ← he, hA]
  exact hb

/-- A mask equal to one on each compact set eventually leaves every compact
initial test integral unchanged (`app:ch_background:eq:bg-T`). This is literal
function equality, and does not presume any uncut integrability estimate. -/
theorem regularizedCarrierIntegral_eventually_eq (d : CarrierData n N)
    (m : ℕ → CarrierVariable n → ℝ)
    (hm : ∀ K : Set (CarrierVariable n), IsCompact K →
      ∀ᶠ k in atTop, ∀ z ∈ K, m k z = 1)
    (f : CarrierVariable n → ℂ) (hf : HasCompactSupport f) :
    ∀ᶠ k in atTop, regularizedCarrierIntegral d (m k) f = carrierTestIntegral d f := by
  filter_upwards [hm (tsupport f) hf] with k hk
  have he : (fun z ↦ (m k z : ℂ) * f z) = f := by
    funext z
    by_cases hz : z ∈ tsupport f
    · simp [hk z hz]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  funext x
  change carrierTestIntegral d (fun z ↦ (m k z : ℂ) * f z) x = _
  rw [he]

/-- Compact-test convergence follows from cutoff removal itself, rather than
an assumed L² limit (`app:ch_background:eq:bg-T`). -/
theorem regularizedCarrierIntegral_tendsto (d : CarrierData n N)
    (m : ℕ → CarrierVariable n → ℝ)
    (hm : ∀ K : Set (CarrierVariable n), IsCompact K →
      ∀ᶠ k in atTop, ∀ z ∈ K, m k z = 1)
    (u : carrierInitialTestSpace n) (x : Torus n) :
    Tendsto (fun k ↦ regularizedCarrierIntegral d (m k) u.val x) atTop
      (𝓝 (carrierTestIntegral d u.val x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [regularizedCarrierIntegral_eventually_eq d m hm u.val u.property.2]
    with k hk
  exact (congrFun hk x).symm

/-- Bounded extension of the literal continuum carrier from exact regularized
full normals (`app:ch_background:prop:bg-frame`, Step 1). The hypotheses concern
only masked operators, their full normals, and exhaustion by masks. The result
includes Fatou's test membership and estimate, equal operator/adjoint bounds,
AE realization, support for all inputs, and uniqueness. -/
theorem exists_carrierL2Extension (d : CarrierData n N)
    (m : ℕ → CarrierVariable n → ℝ)
    (hm : ∀ K : Set (CarrierVariable n), IsCompact K →
      ∀ᶠ k in atTop, ∀ z ∈ K, m k z = 1)
    (T : ℕ → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hrealizes : ∀ k (u : carrierInitialTestSpace n),
      T k (carrierInitialTestToLp u) =ᵐ[volume] regularizedCarrierIntegral d (m k) u.val)
    (A : ℕ → ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n)
    (hnormal : ∀ k, (T k).comp (T k).adjoint = A k)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ k, ‖A k‖ ≤ C) :
    (∀ u : carrierInitialTestSpace n,
      MemLp (carrierTestIntegral d u.val) 2 volume ∧
      (eLpNorm (carrierTestIntegral d u.val) 2 volume).toReal ≤
        Real.sqrt C * ‖carrierInitialTestToLp u‖) ∧
    ∃ U : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      ‖U‖ ≤ Real.sqrt C ∧ ‖U.adjoint‖ ≤ Real.sqrt C ∧
      (∀ u : carrierInitialTestSpace n,
        U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ d.outputChart → U f x = 0) ∧
      ∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ u : carrierInitialTestSpace n,
          W (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val) → W = U := by
  have hb (k) := norm_carrierRegularization_le (T k) (A k) hC (hnormal k) (hbound k)
  have hl (u : carrierInitialTestSpace n) : ∀ᵐ x ∂volume,
      Tendsto (fun k ↦ T k (carrierInitialTestToLp u) x) atTop
        (𝓝 (carrierTestIntegral d u.val x)) := by
    filter_upwards [ae_all_iff.mpr (fun k ↦ hrealizes k u)] with x hx
    exact (regularizedCarrierIntegral_tendsto d m hm u x).congr (fun k ↦ (hx k).symm)
  refine ⟨?_, ?_⟩
  · intro u
    exact carrierLimit_memLp_bound (fun k ↦ T k (carrierInitialTestToLp u))
      (carrierTestIntegral d u.val) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (fun k ↦ ((T k).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))) (hl u)
  · obtain ⟨U, hU, hUa, hUr, huniq⟩ := exists_carrierLimit_extension T
      (fun u ↦ carrierTestIntegral d u.val) (Real.sqrt_nonneg C) hb hl
    exact ⟨U, hU, hUa, hUr, carrierRealization_eq_zero_outside d U hUr, huniq⟩

end JanetCartan.ContinuumRow
