module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.MultiplierSlices
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.RetardedFourier
/-!
# The compact physical retarded operator

The proved multiplier-slice inversion turns the finite spectral triangle into
`Mχout E_b B_(θβ) Mχsource` with the physical Fourier normalization.
Source: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The actual compact-frequency retarded spatial evolution, with the source
mask applied before the spacetime multiplier and the output mask applied last.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def cutRetardedPhysical (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β θ : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (a : ℝ) (u : graphTestSpace (d + 1) q) (x : E) : V :=
  χout x • ∫ s in a..x 0, graphOperator (Ψ (x 0) s)
    (fun y _ η ↦ b (x 0) s y η)
    (cutPhysicalMultiplierSlice β θ (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
      hβ hθ hθcs s) (spatialPart x)

/-- The finite elapsed integral is the physical retarded expression at every
output point. The mask confines the output time and the amplitude's lower
buffer kills the excess elapsed interval, including endpoints. Consumer: the
L² regularization identity in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_cut_elapsedGraph_eq_retardedPhysical
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hscs : HasCompactSupport χsource) (hθcs : HasCompactSupport θ)
    (a Δ : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : graphTestSpace (d + 1) q) (x : E) :
    (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x) =
      cutRetardedPhysical Ψ b χout χsource β θ hs hβ hθ hθcs a u x := by
  by_cases hx : χout x = 0
  · simp [graphOperator, frequencyCutFullAmplitude, elapsedAmplitude, hx, cutRetardedPhysical]
  · rw [integral_cut_elapsedGraph_eq_retardedFourier Ψ b χout χsource β θ hΨ hb ho hs
      hβ.continuous hθ.continuous hscs hθcs a Δ hzero u x (hout x hx).1
      (by linarith [(hout x hx).2])]
    simp_rw [cutFixedTimeFourier_eq_graphOperator Ψ b β θ _ hβ hθ hθcs]
    exact intervalIntegral.integral_smul _ _
end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
