module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhysicalDecay
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellSummation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Summation

/-!
# Complete elapsed-shell majorants from joint primitive grades

The comparable shells use joint half-space integration by parts, while the
separated shells use the identified per-time estimates. The exact high/low
splitting and existing uniformly summable physical pair weights combine both
regimes. No integrated estimate is an input. Consumers: the same-operator
identification and Sobolev transfer in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates PhysicalShells
open PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables (Euclidean (d + 1))

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 1600000

private theorem elapsedShellScale_mono {ρ L C D e eTop : ℝ} {b B N : ℕ}
    (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (hC : 0 ≤ C) (hCD : C ≤ D)
    (he : e ≤ eTop) (hb : b ≤ B) :
    C * ρ ^ e * L ^ b * (L / ρ) ^ N ≤ D * ρ ^ eTop * L ^ B * (L / ρ) ^ N := by
  have hρ0 := zero_lt_one.trans_le hρ
  have hL0 := zero_le_one.trans hL
  have hD := hC.trans hCD
  gcongr

/-- The complete literal elapsed shell family has a nonnegative summable
majorant for every evaluated output jet. The constants precede the frequency,
derivative scale, phase, symbol and shell indices. The fixed losses are
`max 0 s + 3*(d+1)` and `max (m+bo+ba) bLoss`, independently of accuracy.

The comparable inputs are joint primitive phase/amplitude/collar grades;
`UniformCollar` constructs their common geometric constants from compact
stationary exclusions. `hper` is precisely the identified *per-time* separated
estimate exported by `PhysicalShells.Noncomparable` and `EvolutionLocalization`.
The arbitrary-energy fixed-time graph is never identified with the integrated
stationary relation. The original graph cutoff is recovered by exact high/low
splitting, including all contracting shells and output index zero.
Source: `app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`. -/
theorem exists_elapsedPhysicalShellKernel_majorants_of_joint_grades
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : ι → JointVariables E) (eI : κ → V)
    (backward : Bool) (s Δ : ℝ) (m bo ba bLoss : ℕ)
    (c C b₀ : ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    {K : Set V} (hK : IsCompact K)
    (δT δI GT GI : ℝ) (hδT : 0 < δT) (hδI : 0 < δI)
    (P H W O A D : ℕ → ℝ)
    (hH : ∀ j, 0 ≤ H j) (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j) (hA : ∀ j, 0 ≤ A j) (hD : ∀ j, 0 ≤ D j) :
    ∃ Cq : ℕ → ℝ, (∀ N, 0 ≤ Cq N) ∧
    ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
    ∀ (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
      (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d + 1))
      (θ : ℝ → ℂ) (X Y : Set E),
    (∀ y ∉ Y, ∀ η, mi (y, η) = 0) →
    (∀ r ∈ Icc 0 Δ, θ r = 1) →
    (∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r))) →
    (∀ r ∈ Icc 0 Δ, Continuous (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2)) →
    Continuous mi → ContDiff ℝ ∞ mo →
    (∀ j k r, r ∈ Icc 0 Δ →
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphCutoff j) (outputCutoff k)) →
    (∀ y ∈ Y, ∀ x, ContDiff ℝ ∞
      (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y)) →
    (∀ y ∈ Y, ∀ low j k, ContDiff ℝ ∞ (fun p : V ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p)) →
    (∀ y ∈ Y, ∀ low j k, HasCompactSupport (fun p : V ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p)) →
    (∀ y ∈ Y, ∀ low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      tsupport (fun p : V ↦ θ p.1 •
        jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
          (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K) →
    ∀ (a T : ℝ), (∀ t t' u η, t' ≤ a → b t t' u η = 0) →
    (∀ u, T < u 0 → χout u = 0) → T - a ≤ Δ →
    ∀ (χ : E → E → V → ℂ) (UT UI : E → E → Set V) (ε : ℝ), 0 < ε →
    (∀ x ∈ X, ∀ y ∈ Y, ContDiff ℝ ∞ (χ x y)) →
    (∀ x ∈ X, ∀ y ∈ Y, IsOpen (UT x y)) →
    (∀ x ∈ X, ∀ y ∈ Y, IsOpen (UI x y)) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p, |p.1| < ε → χ x y p = 1) →
    (∀ x ∈ X, ∀ y ∈ Y,
      elapsedOutputJetCarrier K mi mo x y ∩ tsupport (χ x y) ⊆ UT x y) →
    (∀ x ∈ X, ∀ y ∈ Y,
      (elapsedOutputJetCarrier K mi mo x y ∩ tsupport (1 - χ x y)) ∩
        {p | 0 < p.1} ⊆ UI x y) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT x y →
      δT ≤ phaseGradientSquare eT (fun w ↦
        jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y (r, w)) p) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT x y →
      ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) (r, p)‖ ≤ GT) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ UI x y ∩ {p | 0 < p.1},
      δI ≤ phaseGradientSquare eI
        (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ UI x y ∩ {p | 0 < p.1},
      ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p‖ ≤ GI) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y)) p‖ ≤ P j * L ^ j) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (χ x y) p‖ ≤ H j) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2.2)‖ ≤ W j) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j mo (x, p.2.2.2.2)‖ ≤ O j * L ^ (j + bo)) →
    (∀ low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ l,
      ‖iteratedFDeriv ℝ l (fun w : V ↦ θ w.1 •
        jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
          (graphBranchCutoff low j) (outputCutoff k) 0 y w) p‖ ≤
        ρ ^ s * A l * L ^ (l + ba)) →
    (∀ N low j k, SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
      ∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ y ∈ Y, ∀ v : Fin m → E,
      (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t ↦ KernelLimits.regularizedJointKernel backward
        (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D N * ρ ^ (d + 1) * L ^ bLoss * (L / ρ) ^ N * pairWeight low (d + 1) j k) →
    ∃ M : ℕ → (ℕ × ℕ) → ℝ, ∀ N,
      (∀ p, 0 ≤ M N p) ∧ Summable (M N) ∧
      (∑' p, M N p) ≤ Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
        L ^ (max ((m + bo) + ba) bLoss) * (L / ρ) ^ N ∧
      ∀ x ∈ X, ∀ y, ∀ v : Fin m → E, (∀ i, ‖v i‖ ≤ 1) →
        (∀ j k, ‖iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
          χout χsource β mi mo (graphCutoff j) (outputCutoff k) t y) x v‖ ≤ M N (j, k)) ∧
        Summable (fun p : ℕ × ℕ ↦ iteratedFDeriv ℝ m
          (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
            (graphCutoff p.1) (outputCutoff p.2) t y) x v) := by
  classical
  let B := fun N ↦ jointNormalization (d + 1) *
    collarDecayConstant (jointMeasure (d + 1)) K eT eI δT δI GT GI P H
      (elapsedOutputJetProfile W O A m) N
  have hB (N : ℕ) : 0 ≤ B N := mul_nonneg (jointNormalization_nonneg _)
    (collarDecayConstant_nonneg _ _ _ _ _ _ _ _ _ hH
      (elapsedOutputJetProfile_nonneg hW hO hA m) N)
  let D' := fun N ↦ B N + volume.real (Icc 0 Δ) * D N
  have hD' N : 0 ≤ D' N := add_nonneg (hB N) (mul_nonneg measureReal_nonneg (hD N))
  obtain ⟨mass, hmass, hweights⟩ := exists_graphPairWeight_mass (n := d + 1)
    (by omega) c C b₀ ha₀
  refine ⟨fun N ↦ D' N * mass, fun N ↦ mul_nonneg (hD' N) hmass, ?_⟩
  intro ρ L hρ hL Ψ b χout χsource β mi mo θ X Y hiy hθ hΨ hbcont hi ho carriers
    hF ha hcompact hs a T hb hout hslab χ UT UI ε hε hχ hUT hUI hχ_one hχT hχI
    hgapT hupperT hgapI hupperI hp hχ_bound hw hmo hab hper
  let scale := fun N ↦ ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
    L ^ (max ((m + bo) + ba) bLoss) * (L / ρ) ^ N
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hscale N : 0 ≤ scale N := by dsimp [scale]; positivity
  let cb (low : Bool) (j k : ℕ) (r : ℝ) (hr : r ∈ Icc 0 Δ) :
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphBranchCutoff low j) (outputCutoff k) :=
    { carriers j k r hr with compact_graphCutoff := hasCompactSupport_graphBranchCutoff low j }
  let Kreg := fun y low j k ↦ tsupport (fun p : V ↦ θ p.1 •
    jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
      (graphBranchCutoff low j) (outputCutoff k) 0 y p)
  have hbranch (N : ℕ) (low : Bool) (j k : ℕ) (x : E) (hx : x ∈ X)
      (y : E) (hy : y ∈ Y) (v : Fin m → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
      ‖iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
        χout χsource β mi mo (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        (D' N * scale N) * regimePairWeight (d + 1) c C a₀ b₀ ρ low (j, k) := by
    by_cases hc : IsComparablePair c C a₀ b₀ ρ low j k
    · simp only [regimePairWeight, hc, ↓reduceIte, mul_one]
      have h := norm_iteratedFDeriv_elapsedPhysicalShellKernel_le_joint_grades
        backward hρ hL s Δ Ψ b χout χsource β mi mo _ _ θ hθ hb hout hslab
        hΨ hbcont hi (contDiff_graphBranchCutoff low j).continuous
        (contDiff_outputCutoff k).continuous (cb low j k) x y ho (hF y hy)
        (ha y hy low j k) hK (hs y hy low j k hc) (hUT x hx y hy) (hUI x hx y hy)
        eT eI (χ x y) (hχ x hx y hy) (hχT x hx y hy) (hχI x hx y hy) hε
        (hχ_one x hx y hy) hδT hδI (hgapT x hx y hy) (hupperT x hx y hy)
        (hgapI x hx y hy) (hupperI x hx y hy) hH hW hO hA bo ba m N v hv
        (hp x hx y hy) (hχ_bound x hx y hy) (hw x hx y hy) (hmo x hx y hy)
        (hab low j k hc x hx y hy)
      apply h.trans
      change B N * _ * _ * _ ≤ D' N * scale N
      have hBD : B N ≤ D' N := le_add_of_nonneg_right (mul_nonneg measureReal_nonneg (hD N))
      simpa only [scale, mul_assoc] using elapsedShellScale_mono hρ hL (hB N) hBD
        (show (m : ℝ) + (s + (3 * (d + 1) : ℕ)) ≤
          (m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ)) from
            add_le_add le_rfl (add_le_add (le_max_right 0 s) le_rfl))
        (le_max_left ((m + bo) + ba) bLoss)
    · have hsep : SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
          (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) :=
        Classical.not_not.mp hc
      simp only [regimePairWeight, hc, ↓reduceIte]
      have h := norm_iteratedFDeriv_elapsedPhysicalShellKernel_le backward hρ0 Δ Ψ b
        χout χsource β mi mo _ _ θ y hθ hΨ hbcont hi ho
        (contDiff_graphBranchCutoff low j).continuous (contDiff_outputCutoff k).continuous
        (cb low j k) (hF y hy 0) (ha y hy low j k) (hcompact y hy low j k)
        (Subset.rfl) m x v (fun r hr ↦ hper N low j k hsep r hr x hx y hy v hv)
      apply h.trans
      have he : ((d + 1 : ℕ) : ℝ) ≤ (m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ)) := by
        have := le_max_left (0 : ℝ) s
        push_cast
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith
      have hDD : volume.real (Icc 0 Δ) * D N ≤ D' N := le_add_of_nonneg_left (hB N)
      have hmono : (volume.real (Icc 0 Δ) * D N) * ρ ^ (d + 1) * L ^ bLoss *
          (L / ρ) ^ N ≤ D' N * scale N := by
        rw [← Real.rpow_natCast]
        simpa only [scale, mul_assoc] using elapsedShellScale_mono hρ hL
          (mul_nonneg measureReal_nonneg (hD N)) hDD he (le_max_right _ _)
      convert mul_le_mul_of_nonneg_right hmono (pairWeight_nonneg low (d + 1) j k) using 1; ring
  have hwts := hweights ρ hρ
  let M := fun N p ↦ (D' N * scale N) * graphPairWeight (d + 1) c C a₀ b₀ ρ p
  have hMn N p : 0 ≤ M N p := mul_nonneg (mul_nonneg (hD' N) (hscale N))
    (graphPairWeight_nonneg _ _ _ _ _ _ p)
  have hMs N : Summable (M N) := hwts.1.mul_left _
  refine ⟨M, ?_⟩
  intro N
  refine ⟨hMn N, hMs N, ?_, ?_⟩
  · calc
      (∑' p, M N p) = (D' N * scale N) * ∑' p, graphPairWeight (d + 1) c C a₀ b₀ ρ p :=
        tsum_mul_left
      _ ≤ (D' N * scale N) * mass :=
        mul_le_mul_of_nonneg_left hwts.2 (mul_nonneg (hD' N) (hscale N))
      _ = _ := by dsimp [scale]; ring
  · intro x hx y v hv
    have hjet (j k : ℕ) :
        ‖iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
          χout χsource β mi mo (graphCutoff j) (outputCutoff k) t y) x v‖ ≤ M N (j, k) := by
      by_cases hy : y ∈ Y
      · rw [iteratedFDeriv_elapsedPhysicalShellKernel_graphCutoff_split backward hρ0 Δ Ψ b
          χout χsource β mi mo j k θ y hθ hΨ hbcont hi ho (carriers j k) (hF y hy 0)
          (ha y hy · j k) (fun low ↦ Kreg y low j k) (hcompact y hy · j k)
          (fun _ ↦ Subset.rfl) m x v]
        exact (norm_add_le _ _).trans ((add_le_add (hbranch N false j k x hx y hy v hv)
          (hbranch N true j k x hx y hy v hv)).trans_eq (by dsimp [M, graphPairWeight]; ring))
      · have hz : (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
            χout χsource β mi mo (graphCutoff j) (outputCutoff k) t y) = 0 := by
          funext t
          simp [elapsedPhysicalShellKernel, KernelLimits.regularizedJointKernel,
            KernelLimits.regularizedJointIntegrand, KernelLimits.regularizedJointAmplitude, hiy y hy]
        simpa only [hz, iteratedFDeriv_zero, Pi.zero_apply, zero_apply, norm_zero]
          using hMn N (j, k)
    exact ⟨hjet, (hMs N).of_norm_bounded (fun p ↦ hjet p.1 p.2)⟩

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
