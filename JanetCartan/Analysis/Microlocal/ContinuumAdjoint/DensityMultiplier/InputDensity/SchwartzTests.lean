module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputTests
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.CompactSchwartz.Cutoff

/-!
# Schwartz functions and compact tests on the raw carrier domain

The density proof for `app:ch_background:eq:bg-density-adjoint` uses Schwartz
functions in the shared finite Euclidean coordinates. These are only coordinates
for the literal product measure, not a new Sobolev scale. Expanding cutoffs give
actual compact smooth `(z,η)` tests and converge in Schwartz topology.

The consuming raw density assembly still needs continuity of the Schwartz
realization in the full raw Sobolev norm and Schwartz representatives of the
inverse partial transform of compact physical tests.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap Topology ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- Schwartz functions in the already published full carrier coordinates,
realized in literal raw L², for `app:ch_background:prop:bg-adjoint`. This is
the common representative map for the two raw density prerequisites. -/
def rawSchwartzToL2 (n : ℕ) : 𝓢(DensityEuclidean n, ℂ) →L[ℂ] CarrierL2 n :=
  (densityL2Equiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume)

/-- The Schwartz realization is precisely the pullback by the existing
measure-preserving coordinates (`app:ch_background:prop:bg-adjoint`). -/
theorem rawSchwartzToL2_coeFn (f : 𝓢(DensityEuclidean n, ℂ)) :
    rawSchwartzToL2 n f =ᵐ[carrierMeasure n] f ∘ densityCoordinates n := by
  refine (densityL2Equiv_symm_coeFn n (f.toLp 2 volume)).trans ?_
  exact (densityCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (f.coeFn_toLp 2 volume)

/-- Smoothness and compact support alone turn a Schwartz function into an
actual raw test for `app:ch_background:eq:bg-density-adjoint`. -/
def rawSchwartzTest (f : 𝓢(DensityEuclidean n, ℂ))
    (hf : HasCompactSupport (f : DensityEuclidean n → ℂ)) : carrierInitialTestSpace n :=
  ⟨f ∘ densityCoordinates n, (f.smooth ⊤).comp (densityCoordinates n).contDiff,
    hf.comp_homeomorph (densityCoordinates n).toHomeomorph⟩

/-- A compact Schwartz function has the same literal raw L² realization
through either test interface (`app:ch_background:eq:bg-density-adjoint`). -/
@[simp] theorem carrierInitialTestToLp_rawSchwartzTest
    (f : 𝓢(DensityEuclidean n, ℂ))
    (hf : HasCompactSupport (f : DensityEuclidean n → ℂ)) :
    carrierInitialTestToLp (rawSchwartzTest f hf) = rawSchwartzToL2 n f := by
  apply Lp.ext
  exact (carrierInitialTest_memLp (rawSchwartzTest f hf)).coeFn_toLp.trans
    (rawSchwartzToL2_coeFn f).symm

/-- Expanding cutoffs supply compact smooth frequency-side tests for the
Schwartz approximation step of `app:ch_background:eq:bg-density-adjoint`. -/
def rawSchwartzCutoffTest (f : 𝓢(DensityEuclidean n, ℂ)) (j : ℕ) :
    carrierInitialTestSpace n :=
  rawSchwartzTest (Pseudodifferential.CompactSchwartz.truncate f j)
    (Pseudodifferential.CompactSchwartz.truncate_hasCompactSupport f j)

/-- The raw cutoff test is the literal cutoff Schwartz L² class. The full
raw Sobolev convergence proof consumes this equality
(`app:ch_background:eq:bg-density-adjoint`). -/
@[simp] theorem carrierInitialTestToLp_rawSchwartzCutoffTest
    (f : 𝓢(DensityEuclidean n, ℂ)) (j : ℕ) :
    carrierInitialTestToLp (rawSchwartzCutoffTest f j) =
      rawSchwartzToL2 n (Pseudodifferential.CompactSchwartz.truncate f j) :=
  carrierInitialTestToLp_rawSchwartzTest _ _

/-- Actual frequency-side compact truncations converge in literal raw L².
Higher-order density must additionally establish convergence in the full raw
Sobolev norm (`app:ch_background:eq:bg-density-adjoint`). -/
theorem tendsto_carrierInitialTestToLp_rawSchwartzCutoffTest
    (f : 𝓢(DensityEuclidean n, ℂ)) :
    Tendsto (fun j ↦ carrierInitialTestToLp (rawSchwartzCutoffTest f j))
      atTop (𝓝 (rawSchwartzToL2 n f)) := by
  simpa only [carrierInitialTestToLp_rawSchwartzCutoffTest, Function.comp_def] using
    ((rawSchwartzToL2 n).continuous.tendsto f).comp
      (Pseudodifferential.CompactSchwartz.tendsto_truncate f)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
