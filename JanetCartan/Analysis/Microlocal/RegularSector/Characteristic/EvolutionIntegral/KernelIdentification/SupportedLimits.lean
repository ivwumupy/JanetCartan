module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedElapsed

/-!
# Uncut elapsed graphs from the primitive regularizations

This specializes the datum-wise dominated-convergence argument to the original
supported phase and masks. The parent construction must produce the finite
realizations, uniform LOW bound and forward/adjoint strong limits by applying
`exists_fullGraphFamily_of_wholeImage_phase`; no conclusion is inserted as an
assumed uncut test action.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Supported primitive regularity and the exact regularizations exported by
`exists_fullGraphFamily_of_wholeImage_phase` give forward/adjoint measurability
and convergence after time integration. The producer's inputs `hreal`,
`hrealAdj`, `hbound`, `hlim`, `hlimAdj` remain explicit obligations of the parent.
Consumer: uncut assembly of `app:ch_regular_base:eq:fixed-time-representation`.
This conditional theorem does not assert that the primitive constructor has
been instantiated. -/
theorem supported_elapsedGraph_measurability_and_integral_limits
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    {C : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u))) :
    (∀ u, AEStronglyMeasurable (fun r ↦ elapsedGraph Ψ b χout χsource β r u)
      (volume.restrict (Icc 0 Δ))) ∧
    (∀ u, AEStronglyMeasurable (fun r ↦ (elapsedGraph Ψ b χout χsource β r).adjoint u)
      (volume.restrict (Icc 0 Δ))) ∧
    (∀ u, Tendsto (fun j ↦ ∫ r in Icc 0 Δ, Treg j r u) atTop
      (𝓝 (elapsedGraphIntegral Δ Ψ b χout χsource β u))) ∧
    (∀ u, Tendsto (fun j ↦ ∫ r in Icc 0 Δ, (Treg j r).adjoint u) atTop
      (𝓝 (∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u))) := by
  have hm := aestronglyMeasurable_supported_elapsed_regularizations Ψ b χout χsource β
    Δ hΔ hΨ hb ho hs hβ hocs hscs χ hχ hχcs Treg hreal hrealAdj
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun j r ↦ Treg j r u)
      (fun j ↦ (hm j u).1)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hlim r hr u
  · intro u
    apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun j r ↦ (Treg j r).adjoint u)
      (fun j ↦ (hm j u).2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hlimAdj r hr u
  · exact fun u ↦ tendsto_integral_apply_of_uniform_bound Treg
      (fun j v ↦ (hm j v).1) hbound hlim u
  · intro u
    apply tendsto_integral_apply_of_uniform_bound (C := C) (fun j r ↦ (Treg j r).adjoint)
      (fun j v ↦ (hm j v).2) _ hlimAdj u
    intro j r hr
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound j r hr

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
