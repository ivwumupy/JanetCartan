module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.ProducerCutoffs
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Basic

/-!
# Primitive finite realizations supply the elapsed graph prefixes

These adapters use exactly the cutoff equality and finite test identities of
`exists_elapsedGraphFamily_of_primitive_phase`. They introduce no new analytic
premise. The reverse operator uses the conjugate-transposed forward amplitude
and conjugate cutoffs, preserving both physical amplitude positions.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open FourierIntegral FiniteChain.Graph.PhysicalShells
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- Exact finite primitive test actions give the eventual shell-prefix
realizations consumed by `eq_localized_of_finite_graph_realizations`. The
contracting low ball vanishes on the producer's closed carrier; every low
shell remains in the prefix (`app:ch_regular:eq:chain-tail`). -/
theorem eventually_oriented_graphPrefix_realization
    (backward : Bool) (S : E → E → ℝ) (A : FullAmplitude (d + 1) q)
    {F : Set E} (hF : IsClosed F) (hzero : (0 : E) ∉ F)
    (hs : ∀ x y ξ, ξ ∉ F → A x y ξ = 0)
    (χ : ℕ → E → ℂ)
    (hχeq : ∀ (B : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F → B x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) B =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) B)
    (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace (d + 1) q), Treg j (graphTestToLp u) =ᵐ[volume]
      fun x => WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
        S (frequencyCutFullAmplitude (χ j) A) (fun y => (u.val y).ofLp)) x)) :
    ∀ᶠ N in atTop, ∀ u : graphTestSpace (d + 1) q,
      Treg (2 ^ N - 1) (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
        (((if backward then reverseGraphOperator else graphOperator) S
          (fun x y ξ => ((∑ j ∈ Finset.range N, graphCutoff j ξ : ℝ) : ℂ) • A x y ξ)
          (fun y => (u.val y).ofLp)) x) := by
  filter_upwards [eventually_graphShell_prefix_eq_producer hF hzero χ hχeq] with N hN
  intro u
  have he := hN A hs
  have hv := hreal (2 ^ N - 1) u
  rw [← he] at hv
  exact hv

/-- The primitive cutoff equality also holds for the conjugate cutoff family.
Thus the finite literal-adjoint realization is an input to the same prefix
adapter, with no real-cutoff assumption. Consumer: the reverse case of the
actual elapsed graph estimate (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem conjugate_producer_cutoffs_eq_physical
    {F : Set E} (χ : ℕ → E → ℂ)
    (hχeq : ∀ (B : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F → B x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) B =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) B) :
    ∀ (B : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F → B x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (fun ξ => star (χ j ξ)) B =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) B := by
  intro B hs j
  have he := hχeq (fun x y ξ => (B x y ξ).conjTranspose)
    (fun x y ξ hξ => by simp only [hs x y ξ hξ, Matrix.conjTranspose_zero]) j
  funext x y ξ
  have hp := congrArg Matrix.conjTranspose (congrFun (congrFun (congrFun he x) y) ξ)
  simpa only [frequencyCutFullAmplitude, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, complexPhysicalCutoff,
    Complex.star_def, Complex.conj_ofReal] using hp

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
