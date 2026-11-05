module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Summation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.PhysicalTransfer

/-!
# Noncomparable physical pair estimates

The input/output masks, both positions of the full amplitude, and the three
Fourier normalizations are those of `app:ch_regular:eq:joint-kernel-phase`.
The primitive cutoff/carrier hypotheses are the obligations of
`jc-graph-physical-cutoff-geometry`; the parent supplies its actual phase and
symbol profiles. No kernel bound, convergence, or decomposition is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Pointwise Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
open FourierIntegral KernelEstimates KernelEstimates.Noncomparable
  KernelEstimates.NoncomparableGeometry
variable {n r : ℕ}
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256

/-- Summable bounds for the actual physical cutoff pairs, including both
orientations, negative-order full symbols, full input shoulders, bounded
output frequencies and arbitrarily small graph frequencies. The constant and
fixed loss precede every varying phase, scale, symbol and pair index. The
phase extension is justified by support agreement. The weights are summable
in positive dimension by `summable_pairWeight`; `q = m = 0` supplies the
globally uniform zeroth majorant required for cutoff removal. The parent
instantiates primitive hypotheses and assembles the comparable regime
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_physicalPair_summable_majorant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    (backward : Bool) {c C G Ci ε : ℝ} (hc : 0 < c) (hCi : 0 ≤ Ci) (hε : 0 < ε)
    {Kb : Set (Euclidean n × Euclidean n)} {Bwave Bξ Bη Bζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hBwave : IsCompact Bwave)
    (hBξ : IsCompact Bξ) (hBη : IsCompact Bη) (hBζ : IsCompact Bζ)
    (P B O : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hO : ∀ j, 0 ≤ O j)
    (sA si so : ℝ) (bi bo bA m : ℕ) :
    ∃ (threshold : ℕ) (D : ℕ → ℝ), (∀ q, 0 ≤ D q) ∧
    ∀ (ρ R L σA σi σo : ℝ), 0 < ρ → 1 ≤ R → 1 ≤ L →
      1 ≤ σA → 1 ≤ σi → 1 ≤ σo → σA ≤ R → σi ≤ R → σo ≤ R → ρ ≤ R →
    ∀ (S Φ φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
      (mi mo : LocalizerSymbol n) (low : Bool) (j k : ℕ) (x y : Euclidean n)
      (Kξ Kη Kζ : Set (Euclidean n))
      (U : (Euclidean n × Euclidean n × Euclidean n) → Set (Euclidean n × Euclidean n))
      (g : (Euclidean n × Euclidean n × Euclidean n) →
        (Euclidean n × Euclidean n) → Euclidean n)
      (a b lξ uξ lζ uζ : ℝ),
    IsCompact Kξ → IsCompact Kη → IsCompact Kζ →
    branchRadius low j ≤ R → (2 : ℝ) ^ k ≤ R →
    Kξ ⊆ (branchRadius low j / ρ) • Bξ → Kη ⊆ Bη →
    Kζ ⊆ (((2 : ℝ) ^ k) / ρ) • Bζ →
    (∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0) →
    tsupport (fun ξ => graphBranchCutoff low j (ρ • ξ)) ⊆ Kξ →
    tsupport (fun η => mi (y, η)) ⊆ Kη →
    tsupport (fun ζ => outputCutoff k (ρ • ζ)) ⊆ Kζ →
    (∀ ξ ∈ Kξ, lξ ≤ ‖ρ • ξ‖ ∧ ‖ρ • ξ‖ ≤ uξ) →
    (∀ η ∈ Kη, a ≤ ‖ρ • η‖ ∧ ‖ρ • η‖ ≤ b) →
    (∀ ζ ∈ Kζ, lζ ≤ ‖ρ • ζ‖ ∧ ‖ρ • ζ‖ ≤ uζ) →
    SeparatedRanges c C a b lξ uξ lζ uζ → ε * R ≤ max lξ (max a lζ) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, IsOpen (U w)) →
    (∀ u ξ, Φ u (ρ • ξ) = ρ * φ u ξ) →
    ContDiff ℝ ∞ mo →
    ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) => A p.1.1 p.1.2 (ρ • p.2.1)) →
    ContDiff ℝ ∞ (fun η => mi (y, η)) →
    ContDiff ℝ ∞ (jointPhase backward φ 0 y) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      ContDiffOn ℝ ∞ (normalizedBasePhase backward ρ R φ x y w) (U w)) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ContDiffOn ℝ ∞
      (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) (U w)) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) ⊆ U w) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      DifferentiableAt ℝ (fun u => Φ u (ρ • w.1)) z.1) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      fderiv ℝ (fun u => Φ u (ρ • w.1)) z.1 = innerSL ℝ (g w z)) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      c * ‖ρ • w.1‖ ≤ ‖g w z‖ ∧ ‖g w z‖ ≤ C * ‖ρ • w.1‖) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      ‖fderiv ℝ (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ G) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ d, 1 ≤ d →
      ‖iteratedFDeriv ℝ (d + 1) (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ P d * L ^ d) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ d,
      ‖iteratedFDeriv ℝ d (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) z‖ ≤
        σA ^ sA * B d * L ^ (d + bA)) →
    (∀ η ∈ Kη, ‖mi (y, η)‖ ≤ (σi ^ si * Ci) * L ^ bi) →
    (∀ ζ ∈ Kζ, (ρ / R) • ζ ∈ Bwave) →
    (∀ ζ ∈ Kζ, ∀ d,
      ‖iteratedFDeriv ℝ d (fun t => mo (t, ζ)) x‖ ≤ σo ^ so * O d * L ^ (d + bo)) →
    (∀ u z ξ, A u z ξ ≠ 0 → graphBranchCutoff low j ξ ≠ 0 → S u ξ = Φ u ξ) →
    Continuous (Function.uncurry Φ) →
    Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n => A p.1.1 p.1.2 p.2) →
    Continuous mi →
    ∀ (_carriers : KernelLimits.RegularizedCarriers A mi (graphBranchCutoff low j) (outputCutoff k)),
    ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun z => mi (z.1, ρ⁻¹ • z.2)) (fun z => mo (z.1, ρ⁻¹ • z.2))
            (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D q * ρ ^ n * L ^ (bi + (m + bo) + bA + threshold + 2) *
          (L / ρ) ^ q * pairWeight low n j k := by
  obtain ⟨threshold, D, hD, hbound⟩ := exists_normalizedPair_summable_majorant (r := r)
    eu ez backward hc hCi hε hKb hBwave hBξ hBη hBζ P B O hB hO sA si so bi bo bA m
  refine ⟨threshold, D, hD, ?_⟩
  intro ρ R L σA σi σo hρ hR hL hσA hσi hσo hσAR hσiR hσoR hρR
    S Φ φ A mi mo low j k x y Kξ Kη Kζ U g a b lξ uξ lζ uζ hKξ hKη hKζ
    hj hk hvξ hvη hvζ hAzero hχA hmi hχo hξ hη hζ hsep hlarge hU hhom
    ho hAsmooth hismooth hφsmooth hφ hA hsU hΦ hg hcomp hupper hp ha hi hw hb
    hphase hΦcont hAcont hicont carriers q v hv
  rw [iteratedFDeriv_physicalPair_eq_normalized_extension backward S Φ φ A mi mo low j k
    x y hρ hphase hhom hΦcont hAcont hicont ho.continuous carriers m v]
  exact hbound ρ R L σA σi σo hρ hR hL hσA hσi hσo hσAR hσiR hσoR hρR
    Φ φ A mi mo low j k x y Kξ Kη Kζ U g a b lξ uξ lζ uζ hKξ hKη hKζ
    hj hk hvξ hvη hvζ hAzero hχA hmi hχo hξ hη hζ hsep hlarge hU hhom
    ho hAsmooth hismooth hφsmooth hφ hA hsU hΦ hg hcomp hupper hp ha hi hw hb q v hv

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
