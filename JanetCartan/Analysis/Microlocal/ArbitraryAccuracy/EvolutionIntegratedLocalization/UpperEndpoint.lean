module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.FourierSplitting
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic

/-!
# Removal of the artificial upper elapsed-time endpoint

The output slab and the original lower source-time buffer in
`app:ch_regular_base:eq:fixed-time-representation` make the actual masked
amplitude vanish at large elapsed times. A strict slab buffer gives a whole
vanishing collar, so half-space integration by parts for
`app:ch_regular:eq:chain-tail` has only the genuine boundary at zero.
Both physical masks and the original adjoint multiplier order are retained.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral
open RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph

variable {d q : ℕ}

/-- The actual output cutoff and lower buffer kill all elapsed times beyond
the fixed physical slab. No support condition on the source mask or frequency
multiplier is needed (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedAmplitude_eq_zero_above_slab
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {a T r : ℝ} (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (hout : ∀ x, T < x 0 → χout x = 0) (hr : T - a ≤ r)
    (x z ξ : Euclidean (d + 1)) :
    elapsedAmplitude b χout χsource β r x z ξ = 0 := by
  by_cases hx : x 0 ≤ T
  · exact elapsedAmplitude_eq_zero_of_lower_buffer b χout χsource β a r hb x z ξ
      (by linarith)
  · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r x z ξ
      (Or.inl (hout x (lt_of_not_ge hx)))

/-- A strict upper slab buffer produces an entire vanishing collar before
the artificial endpoint, as required by the half-space kernel estimate in
`app:ch_regular:lem:finite-chain`. This includes the endpoint itself. -/
theorem elapsedAmplitude_eq_zero_upper_collar
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {a T Δ ε r : ℝ} (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (hout : ∀ x, T < x 0 → χout x = 0) (hbuffer : T - a + ε ≤ Δ)
    (hr : Δ - ε ≤ r) (x z ξ : Euclidean (d + 1)) :
    elapsedAmplitude b χout χsource β r x z ξ = 0 :=
  elapsedAmplitude_eq_zero_above_slab b χout χsource β hb hout (by linarith) x z ξ

/-- The lower-time buffer lies strictly inside the fixed slab, so its positive
upper-end collar width is constructed from the actual time endpoints. It is
independent of all frequency and accuracy parameters
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem exists_elapsedAmplitude_upper_collar
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {a T Δ : ℝ} (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (hout : ∀ x, T < x 0 → χout x = 0) (hslab : T - a < Δ) :
    ∃ ε > 0, ∀ r, Δ - ε ≤ r → ∀ x z ξ,
      elapsedAmplitude b χout χsource β r x z ξ = 0 := by
  refine ⟨(Δ - (T - a)) / 2, by linarith, ?_⟩
  intro r hr x z ξ
  exact elapsedAmplitude_eq_zero_upper_collar b χout χsource β hb hout
    (show T - a + (Δ - (T - a)) / 2 ≤ Δ by linarith) hr x z ξ

/-- The literal compact-frequency forward test action vanishes in the same
upper collar, including every physical mask and every frequency cutoff
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem cut_elapsedGraph_eq_zero_upper_collar
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β θ : Euclidean (d + 1) → ℂ)
    {a T Δ ε r : ℝ} (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (hout : ∀ x, T < x 0 → χout x = 0) (hbuffer : T - a + ε ≤ Δ)
    (hr : Δ - ε ≤ r) (f : Euclidean (d + 1) → Fin q → ℂ) :
    graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r)) f = 0 := by
  funext x
  simp [graphOperator, frequencyCutFullAmplitude,
    elapsedAmplitude_eq_zero_upper_collar b χout χsource β hb hout hbuffer hr]

/-- The adjoint test action vanishes with exactly the same buffer. Its
amplitude is the conjugate transpose in the original `(x,z,ξ)` positions,
and its multiplier is conjugated, preserving `Mχsource* Bβ* E_b* Mχout*`
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem cut_reverse_elapsedGraph_eq_zero_upper_collar
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β θ : Euclidean (d + 1) → ℂ)
    {a T Δ ε r : ℝ} (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (hout : ∀ x, T < x 0 → χout x = 0) (hbuffer : T - a + ε ≤ Δ)
    (hr : Δ - ε ≤ r) (f : Euclidean (d + 1) → Fin q → ℂ) :
    reverseGraphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) f = 0 := by
  funext z
  simp [reverseGraphOperator, frequencyCutFullAmplitude,
    elapsedAmplitude_eq_zero_upper_collar b χout χsource β hb hout hbuffer hr]

/-- The localized joint amplitude also vanishes in the upper collar.
The statement includes the identity contribution `1-mo`, source shoulders,
and all three covectors; it applies before any frequency integration
(`app:ch_regular:eq:chain-tail`). -/
theorem jointAmplitude_elapsed_eq_zero_upper_collar
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (ρ : ℝ) (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    {a T Δ ε r : ℝ} (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (hout : ∀ x, T < x 0 → χout x = 0) (hbuffer : T - a + ε ≤ Δ)
    (hr : Δ - ε ≤ r) :
    jointAmplitude ρ (elapsedAmplitude b χout χsource β r) mi mo χA χo x y p = 0 := by
  simp only [jointAmplitude,
    elapsedAmplitude_eq_zero_upper_collar b χout χsource β hb hout hbuffer hr, smul_zero]

/-- The adjoint localized amplitude has the identical vanishing collar,
without exchanging the original amplitude positions. Both localizer
covectors and the identity contribution remain explicit
(`app:ch_regular:eq:chain-tail`). -/
theorem jointAmplitude_reverse_elapsed_eq_zero_upper_collar
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (ρ : ℝ) (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    {a T Δ ε r : ℝ} (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (hout : ∀ x, T < x 0 → χout x = 0) (hbuffer : T - a + ε ≤ Δ)
    (hr : Δ - ε ≤ r) :
    jointAmplitude ρ (fun u z ξ ↦ (elapsedAmplitude b χout χsource β r u z ξ).conjTranspose)
      mi mo χA χo x y p = 0 := by
  simp only [jointAmplitude,
    elapsedAmplitude_eq_zero_upper_collar b χout χsource β hb hout hbuffer hr,
    Matrix.conjTranspose_zero, smul_zero]

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
