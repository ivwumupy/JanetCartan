module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Realization

/-!
# Strong graph limits give the required distributional realizations

This connects the actual regularizations constructed in `FullLowBounds` to the
weak identities of `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology SchwartzMap
namespace JanetCartan.FourierIntegral.FullLowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- A strong limit of the same literal regularizations realizes the weak
frequency-cutoff limit. This applies to both original and reverse kernels;
`FullLowBounds` supplies the operator limits and the literal identifications.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphDistributionalRealization_of_strong_limit
    (K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ)
    (χ : ℕ → E → ℂ) (A : FullAmplitude n r)
    (T : H →L[ℂ] H) (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace n r), Treg j (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2
        (K (frequencyCutFullAmplitude (χ j) A) (fun y ↦ (u.val y).ofLp) x))
    (hlim : ∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (T u))) :
    GraphDistributionalRealization K χ A T := by
  intro u φ
  have ht := (Lp.toTemperedDistributionCLM V (volume : Measure E) 2).continuous.tendsto
    (T (graphTestToLp u)) |>.comp (hlim (graphTestToLp u))
  have hp := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp ht φ
  apply hp.congr
  intro j
  change (Lp.toTemperedDistribution (Treg j (graphTestToLp u))) φ = _
  rw [Lp.toTemperedDistribution_apply]
  exact integral_congr_ae ((hreal j u).mono fun x hx ↦ congrArg (φ x • ·) hx)

end JanetCartan.FourierIntegral.FullLowBounds
