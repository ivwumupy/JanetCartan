module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Density.Realization

/-!
# Compact smooth density in the physical carrier Sobolev Hilbert spaces

Actual compactly supported smooth functions of all physical `(z,y)` variables
are dense in every `PhysicalSobolevSpace n s`. The convergence uses the full
physical derivative weight, including `2π`, through orthonormal coordinates
and the checked Euclidean compact smooth approximation theorem. This supplies
the density of the carrier inputs `X^s` in `app:ch_background:prop:bg-adjoint`
and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace JanetCartan.CarrierSobolev
open ContinuumRow Pseudodifferential

namespace PhysicalSobolevSpace

variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- Every actual physical Sobolev element is the limit, in its full Sobolev
Hilbert norm, of realizations of compactly supported smooth physical functions.
This establishes the density obligation for `app:ch_background:prop:bg-adjoint`
and `app:ch_background:prop:bg-inverse` at every natural order. -/
theorem exists_compactSmooth_tendsto (s : ℕ) (f : PhysicalSobolevSpace n s) :
    ∃ (φ : ℕ → CarrierVariable n → ℂ) (hφ : ∀ k, ContDiff ℝ ∞ (φ k))
      (hc : ∀ k, HasCompactSupport (φ k)),
      Tendsto (fun k ↦ compactSmooth s (φ k) (hφ k) (hc k)) atTop (𝓝 f) := by
  let v := densityL2Equiv n (toL2 s f)
  have hv : MemFourierSobolev (s : ℝ) v :=
    (toL2_mem s f).memFourierSobolev_densityL2Equiv
  obtain ⟨g, hg, hc, hu, hlim, _⟩ :=
    exists_compactSmooth_fourierSobolev_nat_tendsto s v hv
  let u : ℕ → Lp ℂ 2 (volume : Measure (DensityEuclidean n)) := fun k ↦
    ((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k)
  let φ : ℕ → CarrierVariable n → ℂ := fun k ↦ g k ∘ densityCoordinates n
  have hφ (k : ℕ) : ContDiff ℝ ∞ (φ k) :=
    (hg k).comp (densityCoordinates n).contDiff
  have hφc (k : ℕ) : HasCompactSupport (φ k) :=
    (hc k).comp_homeomorph (densityCoordinates n).toHomeomorph
  have he (k : ℕ) : densityL2Equiv n (compactSmoothL2 (φ k) (hφ k) (hφc k)) = u k := by
    rw [densityL2Equiv_compactSmoothL2]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
      (((hφ k).comp (densityCoordinates n).symm.contDiff).continuous.memLp_of_hasCompactSupport
        ((hφc k).comp_homeomorph (densityCoordinates n).symm.toHomeomorph)),
      MemLp.coeFn_toLp ((hg k).continuous.memLp_of_hasCompactSupport (hc k))] with x hx hy
    simp only [φ, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at hx
    exact hx.trans hy.symm
  refine ⟨φ, hφ, hφc, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hupper (k : ℕ) :
      ‖compactSmooth s (φ k) (hφ k) (hφc k) - f‖ ≤
        densityWeightConstant s * fourierSobolevNorm (s : ℝ) (u k - v) := by
    have he' : densityL2Equiv n
        (toL2 s (compactSmooth s (φ k) (hφ k) (hφc k) - f)) = u k - v := by
      rw [map_sub, map_sub, toL2_compactSmooth, he]
    rw [norm_eq]
    have hm : MemFourierSobolev (s : ℝ)
        (densityL2Equiv n (toL2 s (compactSmooth s (φ k) (hφ k) (hφc k) - f))) := by
      rw [he']
      exact (hu k).sub hv
    simpa only [he'] using physicalSobolevNorm_le_fourierSobolevNorm hm
  apply squeeze_zero (fun _ ↦ norm_nonneg _) hupper
  simpa only [mul_zero] using hlim.const_mul (densityWeightConstant s)

/-- The realizations of actual compact smooth functions have dense range in the
physical Sobolev topology, for `app:ch_background:prop:bg-adjoint`. The source
subtype records only smoothness and compact support, not Sobolev membership. -/
theorem denseRange_compactSmooth (s : ℕ) :
    DenseRange (fun φ : carrierInitialTestSpace n ↦
        compactSmooth s φ.val φ.property.1 φ.property.2) := by
  intro f
  obtain ⟨φ, hφ, hc, hlim⟩ := exists_compactSmooth_tendsto s f
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦
    ⟨⟨φ k, hφ k, hc k⟩, rfl⟩)

end PhysicalSobolevSpace
end JanetCartan.CarrierSobolev
