module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Density.Weights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Tests

/-!
# Compact smooth functions in the actual physical Sobolev levels

The realization below requires only smoothness and compact support on the
physical carrier domain, as needed for `app:ch_background:prop:bg-adjoint`
and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.CarrierSobolev
open ContinuumRow Pseudodifferential

variable {n : ℕ}

/-- The literal physical L² class of a compact smooth function
(`app:ch_background:prop:bg-adjoint`). -/
def compactSmoothL2 (φ : CarrierVariable n → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : CarrierL2 n :=
  carrierInitialTestToLp ⟨φ, hφ, hc⟩

/-- Finite-coordinate transport of a compact smooth physical function is its
actual composition with the inverse coordinates (`app:ch_background:prop:bg-adjoint`). -/
theorem densityL2Equiv_compactSmoothL2 (φ : CarrierVariable n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    densityL2Equiv n (compactSmoothL2 φ hφ hc) =
      (((hφ.comp (densityCoordinates n).symm.contDiff).continuous).memLp_of_hasCompactSupport
        (hc.comp_homeomorph (densityCoordinates n).symm.toHomeomorph)).toLp
          (φ ∘ (densityCoordinates n).symm) := by
  apply Lp.ext
  refine (densityL2Equiv_coeFn n _).trans ?_
  exact ((densityCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (MemLp.coeFn_toLp (hφ.continuous.memLp_of_hasCompactSupport hc))).trans
      (MemLp.coeFn_toLp _).symm

/-- Every genuinely compactly supported smooth physical function has finite
full physical Sobolev energy at every natural order
(`app:ch_background:prop:bg-adjoint`). -/
theorem memPhysicalSobolev_compactSmooth (s : ℕ) (φ : CarrierVariable n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemPhysicalSobolev s (compactSmoothL2 φ hφ hc) := by
  apply memPhysicalSobolev_of_memFourierSobolev_densityL2Equiv
  rw [densityL2Equiv_compactSmoothL2]
  exact memFourierSobolev_nat_toLp s (φ ∘ (densityCoordinates n).symm)
    (hφ.comp (densityCoordinates n).symm.contDiff)
    (hc.comp_homeomorph (densityCoordinates n).symm.toHomeomorph)

namespace PhysicalSobolevSpace

/-- Realize an actual compact smooth function in the complete physical Sobolev
space. Membership is proved, not assumed (`app:ch_background:prop:bg-adjoint`). -/
def compactSmooth (s : ℕ) (φ : CarrierVariable n → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : PhysicalSobolevSpace n s :=
  ofL2 s (compactSmoothL2 φ hφ hc) (memPhysicalSobolev_compactSmooth s φ hφ hc)

/-- The realization retains the given physical L² class
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem toL2_compactSmooth (s : ℕ) (φ : CarrierVariable n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    toL2 s (compactSmooth s φ hφ hc) = compactSmoothL2 φ hφ hc := rfl

/-- The realization represents the original physical function almost everywhere
(`app:ch_background:prop:bg-adjoint`). -/
theorem compactSmooth_coeFn (s : ℕ) (φ : CarrierVariable n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    toL2 s (compactSmooth s φ hφ hc) =ᵐ[carrierMeasure n] φ := by
  exact (carrierInitialTest_memLp ⟨φ, hφ, hc⟩).coeFn_toLp

end PhysicalSobolevSpace
end JanetCartan.CarrierSobolev
