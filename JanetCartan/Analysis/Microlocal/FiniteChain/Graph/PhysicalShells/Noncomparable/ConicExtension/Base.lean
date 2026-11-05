module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Estimates

/-!
# Support-local Base

Support-local variants for `app:ch_regular:eq:chain-tail`: higher phase grades
are needed only on the full amplitude's support. This permits an actual conic
phase, with no quantitative extension hypothesis outside its original domain.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Pointwise Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
open FourierIntegral KernelEstimates KernelEstimates.Noncomparable
  KernelEstimates.NoncomparableGeometry Retarded.HalfSpace Retarded.KernelDecay
  JanetCartan.Localization
variable {n r : ℕ}
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 256

/-- Physical-base integration gives `L/R` per integration, independently of
all ratios between the three frequencies. The amplitude hypotheses are only
primitive full-symbol derivatives, including both positions. The gap and
higher phase grades are the precise inputs of the larger-gap producer;
`S` may be any fixed real symbol power (`app:ch_regular:eq:chain-tail`). -/
theorem norm_baseIntegral_le_on_support {ι : Type*} [Fintype ι]
    (backward : Bool) (ρ : ℝ) {R L S δ G : ℝ}
    (hR : 0 < R) (hL : 0 ≤ L) (hS : 0 ≤ S) (hδ : 0 < δ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (x y : Euclidean n) (w : Euclidean n × Euclidean n × Euclidean n)
    {U K : Set (Euclidean n × Euclidean n)} (hU : IsOpen U) (hK : IsCompact K)
    (e : ι → Euclidean n × Euclidean n) (P B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (b q : ℕ)
    (hφ : ContDiffOn ℝ ∞ (normalizedBasePhase backward ρ R φ x y w) U)
    (hA : ContDiffOn ℝ ∞ (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) U)
    (hsU : tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ U)
    (hsK : tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ K)
    (hgap : ∀ z ∈ U, δ ≤ phaseGradientSquare e (normalizedBasePhase backward ρ R φ x y w) z)
    (hupper : ∀ z ∈ U, ‖fderiv ℝ (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ G)
    (hp : ∀ z ∈ tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)), ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ P j * L ^ j)
    (ha : ∀ z ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) z‖ ≤
        S * B j * L ^ (j + b)) :
    ‖baseIntegral backward ρ φ A x y w‖ ≤
      (decayConstant e δ G P B q * (baseMeasure n).real K) * S * L ^ b * (L / R) ^ q := by
  have h := norm_scaled_vector_integral_le (μ := baseMeasure n) hU hK e
    (normalizedBasePhase backward ρ R φ x y w)
    (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1))
    hφ hA hsU hsK hδ hS hL hR hgap hupper hB b q
    hp (fun z hz j => ha z (hsK hz) j)
  simpa only [scaled_normalizedBasePhase backward ρ hR.ne', baseIntegral] using h

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
