module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedFixedTime

/-!
# The fixed elapsed graph is the strong limit of physical spatial slices

The literal compact identities identify the strong approximants supplied by
`exists_fullGraphFamily_of_wholeImage_phase`. No uncut test-kernel identity is
assumed. Source: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
/-- At each fixed elapsed time, `Basic.elapsedGraph` is the L² limit of the
spatial evolution applied to the actual compact-frequency multiplier slices.
The full order is `Mχout U_b B_(χⱼβ) Mχsource`. The exact inputs `hreal` and
`hlim` come from `exists_fullGraphFamily_of_wholeImage_phase`; the parent must
instantiate that producer. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_strongLimit_spatialGraphs
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (r : ℝ) (hr : r ∈ Icc 0 Δ) (u : graphTestSpace (d + 1) q) :
    ∃ R : ℕ → SpacetimeL2 d q,
      (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (χout x • graphOperator (Ψ (x 0) (x 0 - r))
          (fun y _ η ↦ b (x 0) (x 0 - r) y η)
          (cutPhysicalMultiplierSlice β (χ j)
            (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
            hβ (hχ j) (hχcs j) (x 0 - r)) (spatialPart x))) ∧
      Tendsto R atTop (𝓝 (elapsedGraph Ψ b χout χsource β r (graphTestToLp u))) := by
  refine ⟨fun j ↦ Treg j r (graphTestToLp u), ?_, hlim r hr _⟩
  intro j
  apply (hreal j r hr u).trans
  apply Eventually.of_forall
  intro x
  apply congrArg (WithLp.toLp 2)
  apply cut_elapsedGraph_eq_spatialGraph_of_support Ψ b χout χsource β (χ j) hs r u x
    _ _ hβ (hχ j) (hχcs j)
  · intro hx ξ hξ
    exact (hΨ r hr x hx ξ hξ).comp (f := fun ξ : E ↦
      ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
  · intro hx ξ hξ
    exact (hb r hr x hx ξ hξ).comp (f := fun ξ : E ↦
      ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
