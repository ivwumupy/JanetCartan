module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension.PairEstimate

/-!
# Support-local Summation

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

/-- The actual normalized kernel jets of each noncomparable physical pair
have one common summable majorant. The constant and fixed threshold precede
all phases, symbols, scales, carriers and pair indices. `q = 0` gives a
majorant uniform in both external positions, without claiming rapid decay
there. Negative symbol orders use scales at least one, while the low graph
carrier keeps its shrinking volume. The output index zero remains present.
The parent transfers this bound with
`iteratedFDeriv_physicalPair_eq_normalized_extension` and sums the weights
using `summable_pairWeight`; every primitive support/profile premise must be
instantiated on the actual data (`app:ch_regular:eq:chain-tail`). -/
theorem exists_normalizedPair_summable_majorant_on_support {ι κ : Type*} [Fintype ι] [Fintype κ]
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
    ∀ (Φ φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
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
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      ∀ z ∈ tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)),
      ∀ d, 1 ≤ d →
      ‖iteratedFDeriv ℝ (d + 1) (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ P d * L ^ d) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ d,
      ‖iteratedFDeriv ℝ d (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) z‖ ≤
        σA ^ sA * B d * L ^ (d + bA)) →
    (∀ η ∈ Kη, ‖mi (y, η)‖ ≤ (σi ^ si * Ci) * L ^ bi) →
    (∀ ζ ∈ Kζ, (ρ / R) • ζ ∈ Bwave) →
    (∀ ζ ∈ Kζ, ∀ d,
      ‖iteratedFDeriv ℝ d (fun t => mo (t, ζ)) x‖ ≤ σo ^ so * O d * L ^ (d + bo)) →
    ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t => KernelEstimates.regularizedJointKernel backward
          ρ φ A mi mo (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D q * ρ ^ n * L ^ (bi + (m + bo) + bA + threshold + 2) *
          (L / ρ) ^ q * pairWeight low n j k := by
  obtain ⟨D, hD, hbound⟩ := exists_normalizedPair_derivative_bound_on_support (r := r)
    eu ez backward hc hCi hε hKb hBwave P B O hB hO sA si so bi bo bA m
  let p : ℝ := (m : ℝ) + max 0 sA + max 0 si + max 0 so
  let threshold := Nat.ceil ((2 * n : ℕ) + p : ℝ)
  let V : ℝ := volume.real Bξ * volume.real Bη * volume.real Bζ
  let D' := fun q => D (q + threshold + 2) * V
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hthreshold : (2 * n : ℕ) + p ≤ (threshold : ℝ) := Nat.le_ceil _
  refine ⟨threshold, D', fun q => mul_nonneg (hD _) hV, ?_⟩
  intro ρ R L σA σi σo hρ hR hL hσA hσi hσo hσAR hσiR hσoR hρR
    Φ φ A mi mo low j k x y Kξ Kη Kζ U g a b lξ uξ lζ uζ hKξ hKη hKζ
    hj hk hvξ hvη hvζ hAzero hχA hmi hχo hξ hη hζ hsep hlarge hU hhom
    ho hAsmooth hismooth hφsmooth hφ hA hsU hΦ hg hcomp hupper hp ha hi hw hb q v hv
  have hR0 := zero_lt_one.trans_le hR
  have hL0 := zero_le_one.trans hL
  have hrad := branchRadius_pos low j
  have hvη' : Kη ⊆ (ρ / ρ) • Bη := by simpa [hρ.ne'] using hvη
  have hvol := independent_frequency_volume_le hρ (branchRadius_pos low j).le hρ.le
    (by positivity : (0 : ℝ) ≤ 2 ^ k) hBξ hBη hBζ hvξ hvη' hvζ
  have hord := three_symbol_orders_le hσA hσi hσo hσAR hσiR hσoR sA si (max 0 so)
  simp only [← max_assoc, max_self] at hord
  have hsize : (volume.real Kξ * volume.real Kη * volume.real Kζ) *
        (ρ ^ (3 * n) * R ^ m * (σA ^ sA * σi ^ si * σo ^ max 0 so)) ≤
      V * (branchRadius low j ^ n * ρ ^ n * ((2 : ℝ) ^ k) ^ n) * R ^ p := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hvol (pow_nonneg hR0.le m))
      hord (by positivity) (by positivity)
    apply le_trans (le_of_eq (by ring)) hh |>.trans_eq
    dsimp [p, V]
    simp only [Real.rpow_add hR0, Real.rpow_natCast]
    ring
  have hscalar : (branchRadius low j ^ n * ρ ^ n * ((2 : ℝ) ^ k) ^ n) *
        R ^ p * (L / R) ^ (q + threshold + 2) ≤
      ρ ^ n * L ^ (threshold + 2) * (L / ρ) ^ q * pairWeight low n j k := by
    cases low
    · simpa only [branchRadius, pairWeight, Bool.false_eq_true, ↓reduceIte,
        mul_assoc, mul_comm, mul_left_comm] using
        expanding_pair_size_le hρ hR hL0 hρR n j k threshold q hj hk hthreshold
    · have ht : (n : ℝ) + p ≤ (threshold : ℝ) := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at hthreshold
        linarith
      simpa only [branchRadius, pairWeight, ↓reduceIte, mul_assoc, mul_comm, mul_left_comm] using
        contracting_pair_size_le hρ hR hL0 hρR n j k threshold q hk ht
  have hraw := hbound ρ R L σA σi σo hρ hR hL hσA hσi hσo Φ φ A mi mo low j k x y
    Kξ Kη Kζ U g a b lξ uξ lζ uζ hKξ hKη hKζ hAzero hχA hmi hχo hξ hη hζ hsep
    hlarge hU hhom ho hAsmooth hismooth hφsmooth hφ hA hsU hΦ hg hcomp hupper hp ha hi hw hb
    (q + threshold + 2) v hv
  apply hraw.trans
  calc
    _ = (D (q + threshold + 2) * L ^ (bi + (m + bo) + bA)) *
        ((volume.real Kξ * volume.real Kη * volume.real Kζ) *
          (ρ ^ (3 * n) * R ^ m * (σA ^ sA * σi ^ si * σo ^ max 0 so))) *
            (L / R) ^ (q + threshold + 2) := by ring
    _ ≤ (D (q + threshold + 2) * L ^ (bi + (m + bo) + bA)) *
        (V * (branchRadius low j ^ n * ρ ^ n * ((2 : ℝ) ^ k) ^ n) * R ^ p) *
          (L / R) ^ (q + threshold + 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsize (mul_nonneg (hD _) (pow_nonneg hL0 _)))
        (pow_nonneg (div_nonneg hL0 hR0.le) _)
    _ = (D (q + threshold + 2) * V * L ^ (bi + (m + bo) + bA)) *
        ((branchRadius low j ^ n * ρ ^ n * ((2 : ℝ) ^ k) ^ n) * R ^ p *
          (L / R) ^ (q + threshold + 2)) := by ring
    _ ≤ (D (q + threshold + 2) * V * L ^ (bi + (m + bo) + bA)) *
        (ρ ^ n * L ^ (threshold + 2) * (L / ρ) ^ q * pairWeight low n j k) :=
      mul_le_mul_of_nonneg_left hscalar
        (mul_nonneg (mul_nonneg (hD _) hV) (pow_nonneg hL0 _))
    _ = _ := by dsimp [D']; simp only [pow_add]; ring

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
