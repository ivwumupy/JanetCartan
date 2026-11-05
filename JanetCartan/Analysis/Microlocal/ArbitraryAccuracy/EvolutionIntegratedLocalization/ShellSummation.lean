module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellSummation.Interchange
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellSummation.Majorants
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellSummation.Splitting
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension

/-!
# Summation of the noncomparable literal elapsed shells

This supplies the separated-shell part of `app:ch_regular:eq:chain-tail`
for the parent's same-operator integrated localization. It uses the published
`elapsedPhysicalShellKernel`, including both physical localizer rescalings,
the original masks and source shoulders, and the identity term in `1-mo`.
Both orientations and both graph branches are included. The output index
zero is never removed.

The explicit per-time input below is exactly the conclusion of
`PhysicalShells.Noncomparable.exists_conicPhysicalPair_bound_of_primitive_grades`.
That producer uses `ConicExtension.Summation` and `PhysicalTransfer`.
Its phase and amplitude profiles for the elapsed family are supplied by
`EvolutionLocalization.PrimitiveGrades.elapsedPhase_physicalBase_grade` and
`EvolutionLocalization.PrimitiveGrades.exists_elapsedAmplitudeProfiles`.
The producer's fixed loss is `bi + (m + bo) + bA + threshold + 2`, chosen
before accuracy. The parent must instantiate those same primitive data.

The compact regularity input is the one used by `OutputDifferentiation`;
`contDiff_jointElapsedAmplitude` constructs its amplitude smoothness from
the normalized symbol and masks, and
`hasCompactSupport_cut_jointElapsedAmplitude` supplies its compact carrier.
For a supported phase the parent uses `exists_supported_twoTimePhase_extension`
and the supported kernel identity before `contDiff_jointElapsedPhase`;
smoothness of the original conic phase outside its chart is not asserted.
`Interchange` proves elapsed integration
and all output-derivative interchanges. `Splitting` proves the exact
high/low identity for reassembly. No integrated estimate is assumed here.
Comparable stationary-phase estimates, actual uniform primitive data and
the final operator identification remain obligations of the parent.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph PhysicalShells PhysicalShells.Noncomparable
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256

/-- Nonnegative summable majorants for the actual separated elapsed shell
jets, in either orientation. The sum has the form of
`app:ch_regular:eq:chain-tail`, with `C_A = d+1` and fixed `bLoss`, while
only `D N` varies with accuracy. The indicated series of literal output
jets is absolutely summable and its sum obeys the same bound.

`hper` is a **per-time** estimate, produced by
`exists_conicPhysicalPair_bound_of_primitive_grades` from the original
phase/amplitude grades named above. Its instantiation, along with the
compact primitive regularity, belongs to the parent. No integrated shell
estimate, differentiation identity, or summability assumption is an input. -/
theorem exists_elapsedSeparatedShell_majorants
    (backward : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (θ : ℝ → ℂ) (y : Euclidean (d + 1)) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (hΨ : ∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r)))
    (hb : ∀ r ∈ Icc 0 Δ, Continuous
      (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × Euclidean (d + 1) ↦
        orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (hi : Continuous mi) (ho : ContDiff ℝ ∞ mo)
    (carriers : ∀ low j k r, r ∈ Icc 0 Δ →
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphBranchCutoff low j) (outputCutoff k))
    (hF : ContDiff ℝ ∞
      (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) 0 y))
    (ha : ∀ low j k, ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p))
    (K : Bool → ℕ → ℕ → Set (ℝ × JointVariables (Euclidean (d + 1))))
    (hK : ∀ low j k, IsCompact (K low j k))
    (hs : ∀ low j k, tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K low j k)
    (c C a b₀ : ℝ) (m bLoss : ℕ) (D : ℕ → ℝ) (hD : ∀ N, 0 ≤ D N)
    (hper : ∀ N low j k,
      SeparatedRanges c C (a * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
      ∀ r ∈ Icc 0 Δ, ∀ (x : Euclidean (d + 1)) (v : Fin m → Euclidean (d + 1)),
      (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t ↦ KernelLimits.regularizedJointKernel backward
        (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D N * ρ ^ (d + 1) * L ^ bLoss * (L / ρ) ^ N * pairWeight low (d + 1) j k) :
    ∃ M : ℕ → Bool → (ℕ × ℕ) → ℝ, ∀ N low,
      (∀ p, 0 ≤ M N low p) ∧ Summable (M N low) ∧
      (∑' p, M N low p) ≤ (4 * volume.real (Icc 0 Δ) * D N) *
        ρ ^ (m + (d + 1)) * L ^ bLoss * (L / ρ) ^ N ∧
      ∀ (x : Euclidean (d + 1)) (v : Fin m → Euclidean (d + 1)), (∀ i, ‖v i‖ ≤ 1) →
        let J := {p : ℕ × ℕ | ¬ IsComparablePair c C a b₀ ρ low p.1 p.2}.indicator
          (fun p ↦ iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
            χout χsource β mi mo (graphBranchCutoff low p.1) (outputCutoff p.2) t y) x v)
        (∀ p, ‖J p‖ ≤ M N low p) ∧ Summable J ∧ Summable (fun p ↦ ‖J p‖) ∧
          ‖∑' p, J p‖ ≤ (4 * volume.real (Icc 0 Δ) * D N) *
            ρ ^ (m + (d + 1)) * L ^ bLoss * (L / ρ) ^ N := by
  classical
  let B := fun N ↦ D N * ρ ^ (d + 1) * L ^ bLoss * (L / ρ) ^ N
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hB (N : ℕ) : 0 ≤ B N := by
    have hDN := hD N
    dsimp [B]
    positivity
  refine ⟨fun N ↦ elapsedSeparatedPairMajorant d c C a b₀ ρ Δ (B N), ?_⟩
  intro N low
  have hm := elapsedSeparatedPairMajorant_properties d c C a b₀ ρ Δ (hB N) low
  have hmass := elapsedSeparatedPairMajorant_accuracy_bound d m bLoss N c C a b₀ Δ
    hρ hL0 (hD N) low
  refine ⟨hm.1, hm.2.1, hmass, ?_⟩
  intro x v hv
  dsimp only
  let J := {p : ℕ × ℕ | ¬ IsComparablePair c C a b₀ ρ low p.1 p.2}.indicator
    (fun p ↦ iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo (graphBranchCutoff low p.1) (outputCutoff p.2) t y) x v)
  have hjet (p : ℕ × ℕ) : ‖J p‖ ≤ elapsedSeparatedPairMajorant d c C a b₀ ρ Δ (B N) low p := by
    by_cases hp : IsComparablePair c C a b₀ ρ low p.1 p.2
    · simp [J, elapsedSeparatedPairMajorant, hp]
    have hsep : SeparatedRanges c C (a * ρ) (b₀ * ρ)
        (graphLower low p.1) (graphUpper low p.1) (outputLower p.2) (outputUpper p.2) :=
      Classical.not_not.mp hp
    have h := norm_iteratedFDeriv_elapsedPhysicalShellKernel_le backward hρ0 Δ Ψ b
      χout χsource β mi mo (graphBranchCutoff low p.1) (outputCutoff p.2) θ y
      hθ hΨ hb hi ho (contDiff_graphBranchCutoff low p.1).continuous
      (contDiff_outputCutoff p.2).continuous (carriers low p.1 p.2) hF
      (ha low p.1 p.2) (hK low p.1 p.2) (hs low p.1 p.2) m x v
      (fun r hr ↦ hper N low p.1 p.2 hsep r hr x v hv)
    simp only [J, mem_ofPred_eq, hp, not_false_eq_true, indicator_of_mem,
      elapsedSeparatedPairMajorant, ↓reduceIte]
    exact h.trans_eq (by dsimp [B]; ring)
  exact ⟨hjet, hm.2.1.of_norm_bounded hjet,
    hm.2.1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hjet,
    (tsum_of_norm_bounded hm.2.1.hasSum hjet).trans hmass⟩

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
