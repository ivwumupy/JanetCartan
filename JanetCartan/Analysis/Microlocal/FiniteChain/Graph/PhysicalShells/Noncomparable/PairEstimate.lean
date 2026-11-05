module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Geometry

/-!
# Actual independent cutoff-pair derivatives

The consumer is the physical pair assembly in `app:ch_regular:eq:chain-tail`.
The cutoff support intervals, carrier inclusions and phase/symbol profiles are
primitive inputs. Their producers are `jc-graph-physical-cutoff-geometry` and
the parent's fixed phase and full-symbol data. A gradient gap or a kernel bound
is never assumed. Constants precede the phases, symbols, shell indices, and
scales. All three Fourier volumes remain separate, for subsequent use of
`independent_frequency_volume_le`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
open FourierIntegral KernelEstimates KernelEstimates.Noncomparable
  KernelEstimates.NoncomparableGeometry Retarded.HalfSpace Retarded.KernelDecay
variable {n r : ℕ}

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256

/-- Select one of the two actual graph annuli, preserving its independent
index from the output cutoff (`app:ch_regular:eq:joint-kernel-phase`). -/
def graphBranchCutoff (low : Bool) (j : ℕ) : Euclidean n → ℝ :=
  if low then lowGraphCutoff j else highGraphCutoff j

/-- The actual graph annuli are smooth (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_graphBranchCutoff (low : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (graphBranchCutoff (n := n) low j) := by
  cases low
  · exact contDiff_highGraphCutoff j
  · exact contDiff_lowGraphCutoff j

/-- The actual graph annuli have compact support
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem hasCompactSupport_graphBranchCutoff (low : Bool) (j : ℕ) :
    HasCompactSupport (graphBranchCutoff (n := n) low j) := by
  cases low
  · exact hasCompactSupport_highGraphCutoff j
  · exact hasCompactSupport_lowGraphCutoff j

private theorem norm_sub_bump_le_one (v w : Euclidean n) :
    ‖frequencyBump n v - frequencyBump n w‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(frequencyBump n).nonneg (x := v),
    (frequencyBump n).le_one (x := v), (frequencyBump n).nonneg (x := w),
    (frequencyBump n).le_one (x := w)]

/-- Physical-base integration uses only the zeroth cutoff norm, uniformly
even for the contracting annuli (`app:ch_regular:eq:chain-tail`). -/
theorem norm_graphBranchCutoff_le_one (low : Bool) (j : ℕ) (ξ : Euclidean n) :
    ‖graphBranchCutoff low j ξ‖ ≤ 1 := by
  cases low <;> exact norm_sub_bump_le_one _ _

/-- The independent output index includes the bounded ball with the same
uniform bound (`app:ch_regular:eq:chain-tail`). -/
theorem norm_outputCutoff_le_one (k : ℕ) (ζ : Euclidean n) :
    ‖outputCutoff k ζ‖ ≤ 1 := by
  cases k with
  | zero =>
      change ‖frequencyBump n _‖ ≤ 1
      rw [Real.norm_of_nonneg (frequencyBump n).nonneg]
      exact (frequencyBump n).le_one
  | succ k => exact norm_sub_bump_le_one _ _

/-- Uniform actual output-derivative estimates for independent physical
graph/output cutoffs, from annular input support and primitive physical
covector comparison. No derivative of a frequency cutoff is estimated.
The symbol scales are at least one, but their frequency carriers may shrink
to zero. Negative symbol orders and the weighted two-position inverse
amplitude are retained. The constant is chosen before every varying phase,
symbol, physical scale, carrier and pair index. Source:
`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`. -/
theorem exists_normalizedPair_derivative_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    (backward : Bool) {c C G Ci ε : ℝ} (hc : 0 < c) (hCi : 0 ≤ Ci) (hε : 0 < ε)
    {Kb : Set (Euclidean n × Euclidean n)} {Bwave : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hBwave : IsCompact Bwave)
    (P B O : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hO : ∀ j, 0 ≤ O j)
    (sA si so : ℝ) (bi bo bA m : ℕ) :
    ∃ D : ℕ → ℝ, (∀ q, 0 ≤ D q) ∧
    ∀ (ρ R L σA σi σo : ℝ), 0 < ρ → 1 ≤ R → 1 ≤ L →
      1 ≤ σA → 1 ≤ σi → 1 ≤ σo →
    ∀ (Φ φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
      (mi mo : LocalizerSymbol n) (low : Bool) (j k : ℕ) (x y : Euclidean n)
      (Kξ Kη Kζ : Set (Euclidean n))
      (U : (Euclidean n × Euclidean n × Euclidean n) → Set (Euclidean n × Euclidean n))
      (g : (Euclidean n × Euclidean n × Euclidean n) →
        (Euclidean n × Euclidean n) → Euclidean n)
      (a b lξ uξ lζ uζ : ℝ),
    IsCompact Kξ → IsCompact Kη → IsCompact Kζ →
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
    ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t => KernelEstimates.regularizedJointKernel backward
          ρ φ A mi mo (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D q * (volume.real Kξ * volume.real Kη * volume.real Kζ) *
          (ρ ^ (3 * n) * R ^ m * (σA ^ sA * σi ^ si * σo ^ max 0 so)) *
            L ^ (bi + (m + bo) + bA) * (L / R) ^ q := by
  obtain ⟨W, hW, hWave⟩ := exists_baseWave_profile hBwave
  let D := fun q => jointNormalization n *
    decayConstant (baseDirections eu ez) (gapCoefficient c C * ε ^ 2) G P B q *
      (baseMeasure n).real Kb * Ci * derivativeConvolution W (fun d => 1 + O d) m
  refine ⟨D, ?_, ?_⟩
  · intro q
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (jointNormalization_nonneg n)
      (decayConstant_nonneg _ _ _ _ _ hB q)) measureReal_nonneg) hCi)
      (derivativeConvolution_nonneg hW (fun d => by linarith [hO d]) m)
  intro ρ R L σA σi σo hρ hR hL hσA hσi hσo Φ φ A mi mo low j k x y Kξ Kη Kζ U g
    a b lξ uξ lζ uζ hKξ hKη hKζ hAzero hχA hmi hχo hξ hη hζ hsep hlarge hU hhom
    ho hAsmooth hismooth hφsmooth hφ hA hsU hΦ hg hcomp hupper hp ha hi hw hb q v hv
  have hsK (w : Euclidean n × Euclidean n × Euclidean n) :
      tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) ⊆ Kb := by
    apply closure_minimal _ hKb.isClosed
    intro z hz
    by_contra hn
    exact hz (hAzero z.1 z.2 (ρ • w.1) hn)
  have hgap (w : Euclidean n × Euclidean n × Euclidean n) (hw' : w ∈ Kξ ×ˢ Kη ×ˢ Kζ)
      (z : Euclidean n × Euclidean n) (hz : z ∈ U w) :
      gapCoefficient c C * ε ^ 2 ≤ Localization.phaseGradientSquare (baseDirections eu ez)
        (normalizedBasePhase backward ρ R φ x y w) z :=
    normalizedBasePhase_fractional_gap_of_separatedRanges eu ez backward ρ (zero_lt_one.trans_le hR)
      hc hε.le Φ φ x y w z (g w z) (fun u => hhom u w.1) (hΦ w hw' z hz) (hg w hw' z hz)
      (hcomp w hw' z hz).1 (hcomp w hw' z hz).2
      (hξ w.1 hw'.1) (hη w.2.1 hw'.2.1) (hζ w.2.2 hw'.2.2) hsep hlarge
  have hb' (ζ : Euclidean n) (hζ' : ζ ∈ Kζ) (d : ℕ) :
      ‖iteratedFDeriv ℝ d (fun t => mo (t, ζ)) x‖ ≤
        σo ^ max 0 so * O d * L ^ (d + bo) :=
    (hb ζ hζ' d).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hσo (le_max_right 0 so)) (hO d))
      (pow_nonneg (zero_le_one.trans hL) _))
  rw [iteratedFDeriv_normalizedJointKernel_eq_restricted backward ρ φ A mi mo
    (graphBranchCutoff low j) (outputCutoff k) x y hKb hKξ hKη hKζ hAzero hχA hmi hχo m v]
  apply (norm_iteratedFDeriv_regularizedShellKernel_le backward hρ.le hR hL
    (Real.rpow_nonneg (zero_le_one.trans hσA) sA)
    (Real.one_le_rpow hσo (le_max_left 0 so))
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hσi) si) hCi)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) (mul_pos (gapCoefficient_pos c C) (sq_pos_of_pos hε))
    φ A mi mo (graphBranchCutoff low j) (outputCutoff k) x y hKb hKξ hKη hKζ U hU
    (baseDirections eu ez) P B W O hB hW hO 0 0 bi bo bA m q v hv ho hAsmooth hismooth
    (contDiff_graphBranchCutoff low j) (contDiff_outputCutoff k) hφsmooth hφ hA hsU
    (fun w _ => hsK w) hgap hupper hp ha hi
    (fun ξ _ => by simpa using norm_graphBranchCutoff_le_one low j (ρ • ξ))
    (fun ζ _ => by simpa using norm_outputCutoff_le_one k (ρ • ζ))
    (fun ζ hζ' d => hWave d _ (hw ζ hζ')) hb').trans_eq
  dsimp [D]
  simp only [zero_add, one_mul]
  ring

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
