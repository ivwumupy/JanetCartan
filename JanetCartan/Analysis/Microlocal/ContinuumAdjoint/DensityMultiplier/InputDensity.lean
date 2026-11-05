module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzTests
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.Zero
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzRealization
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages

/-!
# Assembly of compact frequency-side density in the full raw Sobolev norm

For `app:ch_background:eq:bg-density-adjoint`, compact frequency-side tests
must be dense for the full norm after partial unitary synthesis. The proof
below separates two analytic prerequisites: a continuous Schwartz realization
in that norm, and actual Schwartz preimages of compact physical tests under
partial synthesis. It then combines Schwartz cutoff convergence with the
existing full physical Sobolev density theorem.

The two analytic prerequisites are constructed in the companion modules and
instantiated below. Thus density is unconditional at every order. No reverse
mixed-jet comparison is used in this proof.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap Topology

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- A continuous Schwartz realization in the full raw Sobolev norm sends
the explicit compact frequency cutoffs to their Schwartz limit. This is the
cutoff step in `app:ch_background:eq:bg-density-adjoint`; its continuity
hypothesis must be proved for the actual raw norm. -/
theorem tendsto_rawTestSobolev_rawSchwartzCutoffTest (s : ℕ)
    (R : 𝓢(DensityEuclidean n, ℂ) →L[ℂ] RawSobolevSpace n s)
    (hR : ∀ f, RawSobolevSpace.toRawL2 s (R f) = rawSchwartzToL2 n f)
    (f : 𝓢(DensityEuclidean n, ℂ)) :
    Tendsto (fun j ↦ rawTestSobolev s (rawSchwartzCutoffTest f j))
      atTop (𝓝 (R f)) := by
  have he (j : ℕ) : rawTestSobolev s (rawSchwartzCutoffTest f j) =
      R (Pseudodifferential.CompactSchwartz.truncate f j) := by
    apply RawSobolevSpace.toRawL2_injective s
    rw [toRawL2_rawTestSobolev, carrierInitialTestToLp_rawSchwartzCutoffTest, hR]
  simp_rw [he]
  simpa only [Function.comp_def] using
    (R.continuous.tendsto f).comp (Pseudodifferential.CompactSchwartz.tendsto_truncate f)

/-- Compact frequency-side test density follows from continuity of the
actual Schwartz realization and Schwartz preimages of compact physical tests
under partial unitary synthesis (`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`). The first input supplies full
raw-norm convergence of cutoffs; the second connects their closure to the
already dense physical tests. Neither premise assumes density or a reverse
mixed-jet comparison. The final construction must supply both inputs before
using this theorem in `exists_mixedCarrierJet_approximation_of_denseRange`. -/
theorem denseRange_rawTestSobolev_of_schwartz (s : ℕ)
    (R : 𝓢(DensityEuclidean n, ℂ) →L[ℂ] RawSobolevSpace n s)
    (hR : ∀ f, RawSobolevSpace.toRawL2 s (R f) = rawSchwartzToL2 n f)
    (hpreimage : ∀ φ : carrierInitialTestSpace n,
      ∃ f : 𝓢(DensityEuclidean n, ℂ),
        partialUnitaryInverse n (rawSchwartzToL2 n f) = carrierInitialTestToLp φ) :
    DenseRange (rawTestSobolev (n := n) s) := by
  have hclosure (f : 𝓢(DensityEuclidean n, ℂ)) :
      R f ∈ closure (Set.range (rawTestSobolev (n := n) s)) :=
    mem_closure_of_tendsto (tendsto_rawTestSobolev_rawSchwartzCutoffTest s R hR f)
      (Eventually.of_forall fun j ↦ ⟨rawSchwartzCutoffTest f j, rfl⟩)
  have hphysical (φ : carrierInitialTestSpace n) :
      PhysicalSobolevSpace.compactSmooth s φ.val φ.property.1 φ.property.2 ∈
        closure (Set.range (rawTestSobolev (n := n) s)) := by
    obtain ⟨f, hf⟩ := hpreimage φ
    have he : R f =
        PhysicalSobolevSpace.compactSmooth s φ.val φ.property.1 φ.property.2 := by
      apply PhysicalSobolevSpace.toL2_injective s
      rw [← RawSobolevSpace.partialUnitaryInverse_toRawL2, hR, hf,
        PhysicalSobolevSpace.toL2_compactSmooth]
      rfl
    exact he ▸ hclosure f
  intro u
  refine (closure_minimal ?_ isClosed_closure)
    (RawSobolevSpace.denseRange_compactSmooth s u)
  rintro _ ⟨φ, rfl⟩
  exact hphysical φ

/-- Compact smooth frequency-side tests are dense in every existing full raw
Sobolev level. The continuous Schwartz realization and the actual Schwartz
preimages of compact physical tests discharge the two analytic inputs to the
assembly above (`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`). -/
theorem denseRange_rawTestSobolev (s : ℕ) :
    DenseRange (rawTestSobolev (n := n) s) := by
  exact denseRange_rawTestSobolev_of_schwartz s (rawSchwartzSobolev s)
    (toRawL2_rawSchwartzSobolev s)
    (fun φ ↦ exists_rawSchwartz_preimage_compactSmooth n φ)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
