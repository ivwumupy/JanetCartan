module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputDifferentiation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CollarGeometry

/-!
# Differentiated compact-frequency elapsed kernel decay

This is the comparable compact-frequency output-jet estimate in
`app:ch_regular:eq:chain-tail`. The literal bounded elapsed integral is
differentiated, identified with a half-space integral and estimated using its
two gradient branches. Primitive joint amplitude and output-symbol grades
produce the differentiated amplitude bound. The geometric hypotheses are
the exact output of `exists_jointElapsedPhase_collar_data` on the common
buffered carrier. This is not yet the unregularized L²-to-Hᵐ estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

/-- The fixed derivative profile after extracting `ρ^m` from output
derivatives. It includes every derivative of the complementary output
symbol and the complete elapsed masked amplitude
(`app:ch_regular:eq:chain-tail`). -/
def elapsedOutputJetProfile (W O A : ℕ → ℝ) (m : ℕ) : ℕ → ℝ :=
  derivativeConvolution (fun k ↦ derivativeConvolution W (fun i ↦ 1 + O i) (m + k)) A

/-- Nonnegative primitive profiles give nonnegative output-jet constants
(`app:ch_regular:eq:chain-tail`). -/
theorem elapsedOutputJetProfile_nonneg {W O A : ℕ → ℝ}
    (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j) (hA : ∀ j, 0 ≤ A j) (m j : ℕ) :
    0 ≤ elapsedOutputJetProfile W O A m j :=
  derivativeConvolution_nonneg
    (fun _ ↦ derivativeConvolution_nonneg hW (fun i ↦ by linarith [hO i]) _) hA j

/-- Arbitrary pointwise decay of every output derivative of the actual
bounded compact-frequency elapsed integral, in both literal orientations.
The frequency loss is `s+3*(d+1)` and the amplitude offset `m+bo+ba` is
fixed independently of accuracy `N`. The amplitude bounds come from
`AmplitudeGrades`; the collar data come from `CollarGeometry`. No estimate
of the differentiated or integrated kernel is assumed
(`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:fixed-time-representation`). -/
theorem norm_iteratedFDeriv_integral_regularizedElapsedKernel_apply_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (backward : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (s Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (θ : ℝ → ℂ) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    {a T : ℝ} (hb : ∀ t t' u η, t' ≤ a → b t t' u η = 0)
    (hout : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (hF : ∀ t, ContDiff ℝ ∞ (jointElapsedPhase backward Ψ t y))
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
      δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p)
    (hupperT : ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT →
      ‖fderiv ℝ (jointElapsedPhase backward Ψ x y) (r, p)‖ ≤ GT)
    (hgapI : ∀ p ∈ UI ∩ {p | 0 < p.1},
      δI ≤ phaseGradientSquare eI (jointElapsedPhase backward Ψ x y) p)
    (hupperI : ∀ p ∈ UI ∩ {p | 0 < p.1},
      ‖fderiv ℝ (jointElapsedPhase backward Ψ x y) p‖ ≤ GI)
    {P H W O A : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j) (hA : ∀ j, 0 ≤ A j) (bo ba m N : ℕ)
    (v : Fin m → Euclidean (d + 1)) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hp : ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward Ψ x y)) p‖ ≤ P j * L ^ j)
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
    ‖iteratedFDeriv ℝ m (fun t ↦ ∫ r in Icc 0 Δ,
      KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y) x v‖ ≤
      (jointNormalization (d + 1) * collarDecayConstant (jointMeasure (d + 1))
        (elapsedOutputJetCarrier K mi mo x y) eT eI δT δI GT GI P H
          (elapsedOutputJetProfile W O A m) N) *
        ρ ^ ((m : ℝ) + (s + (3 * (d + 1) : ℕ))) * L ^ ((m + bo) + ba) * (L / ρ) ^ N := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  rw [iteratedFDeriv_integral_regularizedElapsedKernel_apply_eq_halfSpace
    backward ρ Δ Ψ b χout χsource β mi mo χA χo θ hθ hb hout hslab x y ho hF ha hK hs m v,
    norm_smul, Real.norm_of_nonneg (mul_nonneg (jointNormalization_nonneg _)
      (pow_nonneg hρ0.le _))]
  have hj := contDiff_cutElapsedOutputJetAmplitude backward hρ0.ne' Ψ b χout χsource β
    mi mo χA χo θ x y ho ha m v
  have hjs := tsupport_cutElapsedOutputJetAmplitude_subset_bufferedCarrier backward hρ0.ne'
    Ψ b χout χsource β mi mo χA χo θ x y ho hs m v
  have h := norm_halfSpace_vector_integral_le (μ := jointMeasure (d + 1)) hUT hUI
    (isCompact_elapsedOutputJetCarrier hK mi mo x y) eT eI
    (jointElapsedPhase backward Ψ x y)
    (cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v)
    χ (hF x) hj hχ hjs hχT hχI hε hχ_one hδT hδI hL hρ
    (mul_pos (pow_pos hρ0 m) (Real.rpow_pos_of_pos hρ0 s))
    hgapT hupperT hgapI hupperI hH (elapsedOutputJetProfile_nonneg hW hO hA m)
    ((m + bo) + ba) N hp hχ_bound (fun p hp' j ↦
      norm_iteratedFDeriv_cutElapsedOutputJetAmplitude_le backward hρ hL Ψ b χout χsource β
        mi mo χA χo θ x y ho ha hW hO bo ba m v hv p (hw p hp') (hmo p hp') (hab p hp') j)
  apply (mul_le_mul_of_nonneg_left h
    (mul_nonneg (jointNormalization_nonneg _) (pow_nonneg hρ0.le _))).trans_eq
  rw [Real.rpow_add hρ0, Real.rpow_add hρ0, Real.rpow_natCast, Real.rpow_natCast]
  ring

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
