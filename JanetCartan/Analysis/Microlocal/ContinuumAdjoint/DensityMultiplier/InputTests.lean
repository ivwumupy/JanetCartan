module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.RawSpace

/-!
# Compact frequency-side tests in the shared raw Sobolev space

The forward partial-Plancherel estimate puts every compact smooth `(z,η)`
test in the existing raw Sobolev space. The linear realization below provides
one checked interface for the two independent input obligations of
`app:ch_background:eq:bg-density-adjoint`: density in the full raw norm and
the reverse mixed-jet norm comparison. It introduces no new Sobolev scale.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- Compact smooth frequency-side tests have full raw Sobolev regularity,
by the proved partial-Plancherel estimate
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierInitialTest_memRawSobolev (s : ℕ) (f : carrierInitialTestSpace n) :
    MemRawSobolev s (carrierInitialTestToLp f) := by
  obtain ⟨_, _, h⟩ := exists_partialUnitaryInverse_test_sobolev_bound (n := n) s
  exact (h f).1

/-- Realization of actual compact smooth raw tests in the shared complete
Hilbert level. The density and reverse-comparison tasks for
`app:ch_background:eq:bg-density-adjoint` both use this same map. -/
def rawTestSobolev (s : ℕ) : carrierInitialTestSpace n →ₗ[ℂ] RawSobolevSpace n s where
  toFun f := RawSobolevSpace.ofRawL2 s (carrierInitialTestToLp f)
    (carrierInitialTest_memRawSobolev s f)
  map_add' f g := by
    apply RawSobolevSpace.toRawL2_injective s
    simp only [RawSobolevSpace.toRawL2_ofRawL2, map_add]
  map_smul' c f := by
    apply RawSobolevSpace.toRawL2_injective s
    simp only [RawSobolevSpace.toRawL2_ofRawL2, map_smul, RingHom.id_apply]

/-- The shared Hilbert realization retains exactly the original raw test
class (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem toRawL2_rawTestSobolev (s : ℕ) (f : carrierInitialTestSpace n) :
    RawSobolevSpace.toRawL2 s (rawTestSobolev s f) = carrierInitialTestToLp f :=
  RawSobolevSpace.toRawL2_ofRawL2 s _ _

/-- The norm of the test realization is the existing full raw norm, with
the shared partial unitary normalization
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_rawTestSobolev (s : ℕ) (f : carrierInitialTestSpace n) :
    ‖rawTestSobolev s f‖ = rawSobolevNorm s (carrierInitialTestToLp f) := by
  rw [RawSobolevSpace.norm_eq, toRawL2_rawTestSobolev]

end JanetCartan.ContinuumAdjoint.DensityMultiplier
