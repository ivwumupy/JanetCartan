module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.UniformDecay
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellKernels

/-!
# Joint half-space decay for the literal physical elapsed kernel

This connects the common-carrier estimate to the actual independently regularized
physical kernel in `app:ch_regular:eq:chain-tail`. The normalized two-time phase
is the original phase under physical dilation, not a fixed-time zero-energy
replacement. Both elapsed boundary branches and the literal masks are retained.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

/-- Joint phase/amplitude/collar grades imply decay of every actual physical
elapsed-shell output jet. The constant uses a common carrier, and its fixed
losses are independent of accuracy. Physical normalization, differentiation,
and elapsed integration are identified by the existing kernel APIs. Consumer:
`exists_elapsedPhysicalShellKernel_majorants_of_joint_grades`
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_elapsedPhysicalShellKernel_le_joint_grades
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (backward : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (s Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (θ : ℝ → ℂ) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    {a T : ℝ} (hb : ∀ t t' u η, t' ≤ a → b t t' u η = 0)
    (hout : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r)))
    (hbcont : ∀ r ∈ Icc 0 Δ, Continuous
      (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × Euclidean (d + 1) ↦
        orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (hi : Continuous mi) (hg : Continuous χA) (hc : Continuous χo)
    (carriers : ∀ r ∈ Icc 0 Δ,
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi χA χo)
    (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (hF : ∀ t, ContDiff ℝ ∞ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) t y))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p))
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p) ⊆ K)
    {UT UI : Set (ℝ × JointVariables (Euclidean (d + 1)))}
    (hUT : IsOpen UT) (hUI : IsOpen UI)
    (eT : ι → JointVariables (Euclidean (d + 1)))
    (eI : κ → ℝ × JointVariables (Euclidean (d + 1)))
    (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχT : elapsedOutputJetCarrier K mi mo x y ∩ tsupport χ ⊆ UT)
    (hχI : (elapsedOutputJetCarrier K mi mo x y ∩ tsupport (1 - χ)) ∩ {p | 0 < p.1} ⊆ UI)
    {ε : ℝ} (hε : 0 < ε) (hχ_one : ∀ p, |p.1| < ε → χ p = 1)
    {δT δI GT GI : ℝ} (hδT : 0 < δT) (hδI : 0 < δI)
    (hgapT : ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT →
      δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y (r, w)) p)
    (hupperT : ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT →
      ‖fderiv ℝ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) (r, p)‖ ≤ GT)
    (hgapI : ∀ p ∈ UI ∩ {p | 0 < p.1},
      δI ≤ phaseGradientSquare eI (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p)
    (hupperI : ∀ p ∈ UI ∩ {p | 0 < p.1},
      ‖fderiv ℝ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p‖ ≤ GI)
    {P H W O A : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j) (hA : ∀ j, 0 ≤ A j) (bo ba m N : ℕ)
    (v : Fin m → Euclidean (d + 1)) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hp : ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y)) p‖ ≤ P j * L ^ j)
    (hχ_bound : ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j χ p‖ ≤ H j)
    (hw : ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ k,
      ‖iteratedFDeriv ℝ k outputJointWave (0, p.2.2.2.2)‖ ≤ W k)
    (hmo : ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ k,
      ‖iteratedFDeriv ℝ k mo (x, p.2.2.2.2)‖ ≤ O k * L ^ (k + bo))
    (hab : ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ k,
      ‖iteratedFDeriv ℝ k (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
        θ w.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
          χA χo 0 y w) p‖ ≤ ρ ^ s * A k * L ^ (k + ba)) :
    ‖iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo χA χo t y) x v‖ ≤
      (jointNormalization (d + 1) * collarDecayConstant (jointMeasure (d + 1))
        K eT eI δT δI GT GI P H
          (elapsedOutputJetProfile W O A m) N) *
        ρ ^ ((m : ℝ) + (s + (3 * (d + 1) : ℕ))) * L ^ ((m + bo) + ba) * (L / ρ) ^ N := by
  unfold elapsedPhysicalShellKernel
  rw [iteratedFDeriv_integral_physicalElapsedKernel_eq_normalized backward
    (zero_lt_one.trans_le hρ) Δ Ψ b χout χsource β mi mo χA χo x y
    hΨ hbcont hi ho.continuous hg hc carriers m v]
  exact norm_iteratedFDeriv_integral_regularizedElapsedKernel_apply_le_commonCarrier
    backward hρ hL s Δ (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) b
    χout χsource β mi mo χA χo θ hθ hb hout hslab x y ho hF ha hK hs
    hUT hUI eT eI χ hχ hχT hχI hε hχ_one hδT hδI hgapT hupperT hgapI hupperI
    hH hW hO hA bo ba m N v hv hp hχ_bound hw hmo hab

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
