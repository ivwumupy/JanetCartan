module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.Differentiation

/-!
# Graph shell decay by physical-base integration

The checked single-shell estimate for `app:ch_regular:eq:chain-tail` retains the
literal joint phase, both amplitude positions, all three Fourier measures and
the original input normalization. Only physical-base derivatives enter repeated
integration by parts. Phase gaps remain the input of the separate geometry
producer. The uniform dyadic family is assembled in `Summation`.
Operator identities and removal of regularizers are separate obligations.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace Retarded.KernelDecay
variable {n r : ℕ}

/-- Actual output derivatives of the regularized shell kernel from primitive
full-symbol, cutoff and mask grades, with `L/R` per integration. The fixed grade
loss is independent of the integration order, and the full symbol scale `S`
can be any positive or negative real order at its own radius. Source shoulders
and bounded smaller frequencies require no frequency derivatives of the input
mask. This is the single-shell input of the parent's graph-factor assembly
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_regularizedShellKernel_le {ι : Type*} [Fintype ι]
    (backward : Bool) {ρ R L S So I Ca Co δ G : ℝ}
    (hρ : 0 ≤ ρ) (hR : 1 ≤ R) (hL : 1 ≤ L) (hS : 0 ≤ S) (hSo : 1 ≤ So)
    (hI : 0 ≤ I) (hCa : 0 ≤ Ca) (hCo : 0 ≤ Co) (hδ : 0 < δ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {Kb : Set (Euclidean n × Euclidean n)} {Kξ Kη Kζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hKξ : IsCompact Kξ) (hKη : IsCompact Kη) (hKζ : IsCompact Kζ)
    (U : (Euclidean n × Euclidean n × Euclidean n) → Set (Euclidean n × Euclidean n))
    (hU : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, IsOpen (U w))
    (e : ι → Euclidean n × Euclidean n) (P B W O : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (ba bc bi bo bA m q : ℕ) (v : Fin m → Euclidean n) (hv : ∀ i, ‖v i‖ ≤ 1)
    (ho : ContDiff ℝ ∞ mo)
    (hAsmooth : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) => A p.1.1 p.1.2 (ρ • p.2.1)))
    (hismooth : ContDiff ℝ ∞ (fun ξ => mi (y, ξ)))
    (hcasmooth : ContDiff ℝ ∞ χA) (hcosmooth : ContDiff ℝ ∞ χo)
    (hφsmooth : ContDiff ℝ ∞ (jointPhase backward φ 0 y))
    (hφ : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      ContDiffOn ℝ ∞ (normalizedBasePhase backward ρ R φ x y w) (U w))
    (hA : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ContDiffOn ℝ ∞
      (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) (U w))
    (hsU : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ U w)
    (hsK : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ Kb)
    (hgap : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      δ ≤ phaseGradientSquare e (normalizedBasePhase backward ρ R φ x y w) z)
    (hupper : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      ‖fderiv ℝ (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ G)
    (hp : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (normalizedBasePhase backward ρ R φ x y w) z‖ ≤ P j * L ^ j)
    (ha : ∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ j,
      ‖iteratedFDeriv ℝ j (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) z‖ ≤
        S * B j * L ^ (j + bA))
    (hi : ∀ η ∈ Kη, ‖mi (y, η)‖ ≤ I * L ^ bi)
    (hca : ∀ ξ ∈ Kξ, ‖χA (ρ • ξ)‖ ≤ Ca * L ^ ba)
    (hco : ∀ ζ ∈ Kζ, ‖χo (ρ • ζ)‖ ≤ Co * L ^ bc)
    (hw : ∀ ζ ∈ Kζ, ∀ j, ‖iteratedFDeriv ℝ j
      (fun t => outputJointWave (t, (ρ / R) • ζ)) 0‖ ≤ W j)
    (hb : ∀ ζ ∈ Kζ, ∀ j,
      ‖iteratedFDeriv ℝ j (fun t => mo (t, ζ)) x‖ ≤ So * O j * L ^ (j + bo)) :
    ‖iteratedFDeriv ℝ m
      (fun t => regularizedShellKernel backward ρ φ A mi mo χA χo Kb Kξ Kη Kζ t y) x v‖ ≤
      (jointNormalization n * decayConstant e δ G P B q * (baseMeasure n).real Kb *
        volume.real Kξ * volume.real Kη * volume.real Kζ *
          (Ca * Co * I * derivativeConvolution W (fun j => 1 + O j) m)) *
      (ρ ^ (3 * n) * R ^ m * S * So) * L ^ (ba + bc + bi + (m + bo) + bA) * (L / R) ^ q := by
  rw [iteratedFDeriv_regularizedShellKernel_eq backward ρ φ A mi mo χA χo x y
    hKb hKξ hKη hKζ hAsmooth hismooth ho hcasmooth hcosmooth hφsmooth hsK]
  exact norm_shellOutputIntegral_le backward hρ hR hL hS hSo hI hCa hCo hδ
    φ A mi mo χA χo x y hKb hKξ hKη hKζ U hU e P B W O hB hW hO
    ba bc bi bo bA m q v hv ho hφ hA hsU hsK hgap hupper hp ha hi hca hco hw hb

end JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
