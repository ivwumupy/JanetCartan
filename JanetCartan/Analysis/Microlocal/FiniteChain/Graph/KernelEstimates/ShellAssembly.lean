module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.PhysicalPhase

/-!
# Noncomparable graph estimates from physical phase grades

This assembles the two independent prerequisites for `app:ch_regular:eq:chain-tail`.
All shell gaps are discharged from homogeneity and physical covector comparison.
The remaining hypotheses are primitive symbol, cutoff and physical phase grades.
The actual phase charts and full amplitudes are supplied by the parent graph
localization construction. Regularization identities belong to `Graph.KernelLimits`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Pointwise Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace Retarded.KernelDecay
open Retarded.KernelSobolev Noncomparable NoncomparableGeometry
variable {n r : ℕ}

/-- The larger-frequency geometry and actual output-derivative shell estimates
combine to give summable bounds with constants preceding all scales. There is
no gradient-gap, kernel-bound or transferred-amplitude premise. Negative symbol
orders and bounded smaller frequencies are included. The fixed power is
`m + 3*n + max 0 sA + max 0 si + max 0 so`; the grade offset is independent
of accuracy (`app:ch_regular:eq:chain-tail`). -/
theorem exists_shell_bounds_of_physical_grades {ι κ : Type*} [Fintype ι] [Fintype κ]
    (backward : Bool)
    {Kb : Set (Euclidean n × Euclidean n)} {Bξ Bη Bζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hBξ : IsCompact Bξ) (hBη : IsCompact Bη) (hBζ : IsCompact Bζ)
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    {c C₀ G Ca Co Ci : ℝ} (hc : 0 < c) (hCa : 0 ≤ Ca) (hCo : 0 ≤ Co) (hCi : 0 ≤ Ci)
    (P B O : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hO : ∀ j, 0 ≤ O j)
    (sA si so : ℝ) (ba bc bi bo bA m : ℕ) :
    ∃ (a : ℕ) (C : ℕ → ℝ), (∀ q, 0 ≤ C q) ∧
    ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
    ∀ (Φ φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
      (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
      (x y : Euclidean n) (σA σi σo : ℕ → ℝ)
      (Kξ Kη Kζ : ℕ → Set (Euclidean n))
      (g : ℕ → (Euclidean n × Euclidean n × Euclidean n) →
        (Euclidean n × Euclidean n) → Euclidean n)
      (U : ℕ → (Euclidean n × Euclidean n × Euclidean n) → Set (Euclidean n × Euclidean n)),
    (∀ k, 1 ≤ σA k) → (∀ k, 1 ≤ σi k) → (∀ k, 1 ≤ σo k) →
    (∀ k, σA k ≤ (2 : ℝ) ^ k * ρ) →
    (∀ k, σi k ≤ (2 : ℝ) ^ k * ρ) →
    (∀ k, σo k ≤ (2 : ℝ) ^ k * ρ) →
    (∀ k, IsCompact (Kξ k)) → (∀ k, IsCompact (Kη k)) → (∀ k, IsCompact (Kζ k)) →
    (∀ k, Kξ k ⊆ (((2 : ℝ) ^ k * ρ) / ρ) • Bξ) →
    (∀ k, Kη k ⊆ (((2 : ℝ) ^ k * ρ) / ρ) • Bη) →
    (∀ k, Kζ k ⊆ (((2 : ℝ) ^ k * ρ) / ρ) • Bζ) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → IsOpen (U k w)) →
    ContDiff ℝ ∞ mo →
    ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) => A p.1.1 p.1.2 (ρ • p.2.1)) →
    ContDiff ℝ ∞ (fun ξ => mi (y, ξ)) →
    (∀ k, ContDiff ℝ ∞ (χA k)) → (∀ k, ContDiff ℝ ∞ (χo k)) →
    ContDiff ℝ ∞ (jointPhase backward φ 0 y) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ u, Φ u (ρ • w.1) = ρ * φ u w.1) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ContDiff ℝ ∞
      (basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2))) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ContDiffOn ℝ ∞
      (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) (U k w)) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k →
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ U k w) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k →
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ Kb) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ U k w,
      DifferentiableAt ℝ (fun u => Φ u (ρ • w.1)) z.1) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ U k w,
      fderiv ℝ (fun u => Φ u (ρ • w.1)) z.1 = innerSL ℝ (g k w z)) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ U k w,
      c * ‖ρ • w.1‖ ≤ ‖g k w z‖) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ U k w,
      ‖g k w z‖ ≤ C₀ * ‖ρ • w.1‖) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k →
      OutsideInputAnnuli c C₀ (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k →
      (2 : ℝ) ^ k * ρ ≤ largestFrequency (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ U k w,
      ‖fderiv ℝ (basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) z‖ ≤
        ((2 : ℝ) ^ k * ρ) * G) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ Kb, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1)
        (basePhase backward Φ x y (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) z‖ ≤
          ((2 : ℝ) ^ k * ρ) * (P j * L ^ j)) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ Kb, ∀ j,
      ‖iteratedFDeriv ℝ j (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) z‖ ≤
        (σA k) ^ sA * B j * L ^ (j + bA)) →
    (∀ k η, η ∈ Kη k → ‖mi (y, η)‖ ≤ ((σi k) ^ si * Ci) * L ^ bi) →
    (∀ k ξ, ξ ∈ Kξ k → ‖χA k (ρ • ξ)‖ ≤ Ca * L ^ ba) →
    (∀ k ζ, ζ ∈ Kζ k → ‖χo k (ρ • ζ)‖ ≤ Co * L ^ bc) →
    (∀ k ζ, ζ ∈ Kζ k → ∀ j,
      ‖iteratedFDeriv ℝ j (fun t => mo (t, ζ)) x‖ ≤ (σo k) ^ so * O j * L ^ (j + bo)) →
    ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      let J := fun k => iteratedFDeriv ℝ m
        (fun t => regularizedShellKernel backward ρ φ A mi mo (χA k) (χo k)
          Kb (Kξ k) (Kη k) (Kζ k) t y) x v
      let F := C q * ρ ^ ((3 * n + m : ℕ) + max 0 sA + max 0 si + max 0 so : ℝ) *
        L ^ (ba + bc + bi + (m + bo) + bA)
      (∀ k, ‖J k‖ ≤ F * dyadicShellWeight a q (L / ρ) k) ∧
      Summable (fun k => ‖J k‖) ∧ HasSum J (∑' k, J k) ∧
      ‖∑' k, J k‖ ≤ 2 * F * (L / ρ) ^ q := by
  obtain ⟨a, C, hC, hbound⟩ := exists_regularizedShellKernel_dyadic_bounds
    (r := r) backward hKb hBξ hBη hBζ (baseDirections eu ez)
    (gapCoefficient_pos c C₀) hCa hCo hCi P B O hB hO sA si so ba bc bi bo bA m
  refine ⟨a, C, hC, ?_⟩
  intro ρ L hL hLρ Φ φ A mi mo χA χo x y σA σi σo Kξ Kη Kζ g U
    hσA hσi hσo hσAR hσiR hσoR hKξ hKη hKζ hsξ hsη hsζ hU
    ho hAsmooth hismooth hcasmooth hcosmooth hφsmooth hhom hphysical hA hsU hsK
    hslice hg hlow hhigh hsep hlarge hupper hp hamp hi hca hco hb q v hv
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hR (k : ℕ) : 0 < (2 : ℝ) ^ k * ρ := mul_pos (by positivity) hρ
  apply hbound ρ L hL hLρ φ A mi mo χA χo x y σA σi σo Kξ Kη Kζ U
    hσA hσi hσo hσAR hσiR hσoR hKξ hKη hKζ hsξ hsη hsζ hU
    ho hAsmooth hismooth hcasmooth hcosmooth hφsmooth
    (fun k w hw => ?_) hA hsU hsK
    (fun k w hw z hz => ?_) (fun k w hw z hz => ?_)
    (fun k w hw z hz j hj => ?_) hamp hi hca hco hb q v hv
  · rw [normalizedBasePhase_eq_physical backward ρ _ Φ φ x y w (hhom k w hw)]
    exact ((hphysical k w hw).const_smul (((2 : ℝ) ^ k * ρ)⁻¹)).contDiffOn
  · exact normalizedBasePhase_gap_of_comparison eu ez backward ρ (hR k) hc Φ φ x y w z
      (g k w z) (hhom k w hw) (hslice k w hw z hz) (hg k w hw z hz)
      (hlow k w hw z hz) (hhigh k w hw z hz) (hsep k w hw) (hlarge k w hw)
  · exact norm_fderiv_normalizedBasePhase_le backward ρ (hR k) Φ φ x y w z
      (hhom k w hw) ((hphysical k w hw).differentiable (by simp)).differentiableAt
      (hupper k w hw z hz)
  · exact norm_iteratedFDeriv_normalizedBasePhase_le backward ρ (hR k) Φ φ x y w z
      (j + 1) (hhom k w hw) ((hphysical k w hw).contDiffAt.of_le (by simp))
      (hp k w hw z hz j hj)

end JanetCartan.FiniteChain.Graph.KernelEstimates
