module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputDecay
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.UniformCollar

/-!
# Uniform compact-frequency elapsed kernel constants

For `app:ch_regular:eq:chain-tail`, the constant for an individual output
jet initially contains the volume of its buffered carrier. Bounding that
volume by the common compact carrier removes its dependence on the external
bases without enlarging the domain on which a gradient gap is required.
Together with `UniformCollar`, this supplies one quantitative estimate for
the finite family. The shell sum and unregularized identification remain
separate obligations; no operator estimate is an input here.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

/-- Enlarge only the volume carrier in the actual elapsed half-space
constant. This does not assert a gap off the buffered support. Consumer:
`norm_iteratedFDeriv_integral_regularizedElapsedKernel_apply_le_commonCarrier`
(`app:ch_regular:eq:chain-tail`). -/
theorem elapsedCollarDecayConstant_le_of_subset
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K C : Set (ℝ × JointVariables (Euclidean (d + 1)))}
    (hC : IsCompact C) (hKC : K ⊆ C)
    (eT : ι → JointVariables (Euclidean (d + 1)))
    (eI : κ → ℝ × JointVariables (Euclidean (d + 1)))
    (δT δI GT GI : ℝ) (P : ℕ → ℝ) {H A : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (hA : ∀ j, 0 ≤ A j) (N : ℕ) :
    collarDecayConstant (jointMeasure (d + 1)) K eT eI δT δI GT GI P H A N ≤
      collarDecayConstant (jointMeasure (d + 1)) C eT eI δT δI GT GI P H A N := by
  have hprof := collarAmplitudeProfile_nonneg hH hA
  have ht := decayConstant_nonneg eT δT GT P _ hprof N
  have hi := decayConstant_nonneg eI δI GI P _ hprof N
  have hfst := measureReal_mono (μ := volume) (image_mono hKC)
    (hC.image continuous_fst).measure_lt_top.ne
  have hsnd := measureReal_mono (μ := jointMeasure (d + 1)) (image_mono hKC)
    (hC.image continuous_snd).measure_lt_top.ne
  have hvol := measureReal_mono (μ := volume.prod (jointMeasure (d + 1))) hKC
    hC.measure_lt_top.ne
  unfold collarDecayConstant
  exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hfst ht) hsnd
    measureReal_nonneg (mul_nonneg ht measureReal_nonneg))
    (mul_le_mul_of_nonneg_left hvol hi)

/-- The differentiated bounded elapsed kernel has a common explicit constant
independent of its external bases. `UniformCollar` supplies shared geometric
data, while the primitive two-time grades supply the shared profiles. Only
the true buffered support needs a gradient gap; the larger compact carrier
is used solely to bound the volumes. The frequency and coefficient exponents
are unchanged and independent of accuracy. Both literal orientations and
every output-symbol jet, including the identity, remain present
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_integral_regularizedElapsedKernel_apply_le_commonCarrier
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
        K eT eI δT δI GT GI P H
          (elapsedOutputJetProfile W O A m) N) *
        ρ ^ ((m : ℝ) + (s + (3 * (d + 1) : ℕ))) * L ^ ((m + bo) + ba) * (L / ρ) ^ N := by
  have h := norm_iteratedFDeriv_integral_regularizedElapsedKernel_apply_le
    backward hρ hL s Δ Ψ b χout χsource β mi mo χA χo θ hθ hb hout hslab x y ho hF ha
    hK hs hUT hUI eT eI χ hχ hχT hχI hε hχ_one hδT hδI hgapT hupperT hgapI hupperI
    hH hW hO hA bo ba m N v hv hp hχ_bound hw hmo hab
  have hmono := elapsedCollarDecayConstant_le_of_subset hK
    (show elapsedOutputJetCarrier K mi mo x y ⊆ K from inter_subset_left)
    eT eI δT δI GT GI P hH (elapsedOutputJetProfile_nonneg hW hO hA m) N
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmono (jointNormalization_nonneg _))
        (Real.rpow_nonneg (zero_le_one.trans hρ) _))
      (pow_nonneg (zero_le_one.trans hL) _))
    (pow_nonneg (div_nonneg (zero_le_one.trans hL) (zero_le_one.trans hρ)) _)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
