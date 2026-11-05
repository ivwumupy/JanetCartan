module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.FrequencyGaps
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.BufferedGeometry.Profiles
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.BufferedGeometry.Reversal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.PhysicalMasks
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Tangential geometry of noncomparable retarded shells

The base directions alone detect the larger-frequency gap in
`app:ch_regular:lem:finite-chain`. These quantitative estimates supply the
noncomparable part of `app:ch_regular:eq:chain-tail` for both literal phases.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- Common-base time and transverse directions, with zero covector components.
Only these tangential directions are used on noncomparable shells
(`app:ch_regular:lem:finite-chain`). -/
def baseFrequencyDirections (e : OrthonormalBasis ι ℝ E) : Unit ⊕ ι → TangentialVariables E
  | .inl _ => ((1, 0), 0, 0)
  | .inr i => ((0, e i), 0, 0)

/-- The tangential squared gradient in common-base directions is exactly the
squared Euclidean frequency difference, for both literal orientations
(`app:ch_regular:lem:finite-chain`). -/
theorem literalPhase_base_gradientSquare (e : OrthonormalBasis ι ℝ E)
    (upper : Bool) (xi xo : ℝ × E) (d : ℝ) (z : TangentialVariables E) :
    Localization.phaseGradientSquare (baseFrequencyDirections e)
      (fun w => literalPhase upper xi xo (d, w)) z =
      (z.2.2.1 - z.2.1.1) ^ 2 + ‖z.2.2.2 - z.2.1.2‖ ^ 2 := by
  have hs (a : E) : ∑ i, (inner ℝ a (e i)) ^ 2 = ‖a‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using e.sum_sq_norm_inner_left a
  cases upper
  · simp [literalPhase, Localization.phaseGradientSquare, baseFrequencyDirections,
      fderiv_packedPhase_tangential_apply, Fintype.sum_sum_type, hs]
  · rw [show literalPhase true xi xo = LocalizedKernel.packedUpperPhase xi xo from rfl,
      upper_tangential_gradientSquare_eq]
    have he : (fun i => swapTangentialCovectors (baseFrequencyDirections e i)) =
        baseFrequencyDirections e := by
      funext i
      cases i <;> rfl
    rw [he]
    simp [Localization.phaseGradientSquare, baseFrequencyDirections,
      fderiv_packedPhase_tangential_apply, Fintype.sum_sum_type, hs,
      swapTangentialCovectors, norm_sub_rev]
    ring

/-- A larger normalized radius at least `c` gives the explicit squared gap
`c²/4`, including a zero or bounded smaller frequency. This is the gap consumed
by noncomparable tangential integration by parts
(`app:ch_regular:lem:finite-chain`). -/
theorem noncomparable_literalPhase_gradient_gap (e : OrthonormalBasis ι ℝ E)
    (upper : Bool) (xi xo : ℝ × E) (d : ℝ) (z : TangentialVariables E)
    {c : ℝ} (hc : 0 ≤ c)
    (hlarge : c ≤ max (frequencySize z.2.2.1 z.2.2.2) (frequencySize z.2.1.1 z.2.1.2))
    (hsep : 2 * frequencySize z.2.2.1 z.2.2.2 ≤ frequencySize z.2.1.1 z.2.1.2 ∨
      2 * frequencySize z.2.1.1 z.2.1.2 ≤ frequencySize z.2.2.1 z.2.2.2) :
    c ^ 2 / 4 ≤ Localization.phaseGradientSquare (baseFrequencyDirections e)
      (fun w => literalPhase upper xi xo (d, w)) z := by
  have hg := noncomparable_frequency_gap z.2.2.1 z.2.1.1 z.2.2.2 z.2.1.2 hsep
  have hsq : (frequencySize (z.2.2.1 - z.2.1.1) (z.2.2.2 - z.2.1.2)) ^ 2 =
      (z.2.2.1 - z.2.1.1) ^ 2 + ‖z.2.2.2 - z.2.1.2‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hn : 0 ≤ frequencySize (z.2.2.1 - z.2.1.1) (z.2.2.2 - z.2.1.2) :=
    Real.sqrt_nonneg _
  rw [literalPhase_base_gradientSquare]
  nlinarith

/-- Physical noncomparability and a lower bound at scale `ρ` imply the uniform
normalized squared gap. The smaller shell has no positive lower bound
(`app:ch_regular:lem:finite-chain`). -/
theorem normalized_noncomparable_literalPhase_gradient_gap (e : OrthonormalBasis ι ℝ E)
    (upper : Bool) (xi xo : ℝ × E) (d : ℝ) (z : TangentialVariables E)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hlarge : ρ * c ≤ max (frequencySize (ρ • z.2.2).1 (ρ • z.2.2).2)
      (frequencySize (ρ • z.2.1).1 (ρ • z.2.1).2))
    (hsep : 2 * frequencySize (ρ • z.2.2).1 (ρ • z.2.2).2 ≤
        frequencySize (ρ • z.2.1).1 (ρ • z.2.1).2 ∨
      2 * frequencySize (ρ • z.2.1).1 (ρ • z.2.1).2 ≤
        frequencySize (ρ • z.2.2).1 (ρ • z.2.2).2) :
    c ^ 2 / 4 ≤ Localization.phaseGradientSquare (baseFrequencyDirections e)
      (fun w => literalPhase upper xi xo (d, w)) z := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, frequencySize_smul, abs_of_pos hρ, ← mul_max_of_nonneg _ _ hρ.le] at hlarge
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, frequencySize_smul, abs_of_pos hρ] at hsep
  apply noncomparable_literalPhase_gradient_gap e upper xi xo d z hc
    ((mul_le_mul_iff_right₀ hρ).mp hlarge)
  rcases hsep with h | h
  · left
    nlinarith
  · right
    nlinarith

/-- Continuity of the squared gap, used to construct an open integration region
rather than assuming one (`app:ch_regular:lem:finite-chain`). -/
theorem continuous_literalPhase_base_gradientSquare (e : OrthonormalBasis ι ℝ E)
    (upper : Bool) (xi xo : ℝ × E) :
    Continuous (fun x : ℝ × TangentialVariables E =>
      Localization.phaseGradientSquare (baseFrequencyDirections e)
        (fun w => literalPhase upper xi xo (x.1, w)) x.2) := by
  simp only [literalPhase_base_gradientSquare]
  fun_prop

/-- Compact joint carriers and primitive annular separation produce all the
open-gap and phase-profile data for the tangential half-space estimate. The
profile and upper derivative bound are chosen before the shell scale, the
integration order and any external parameter in the compact family. This is
the geometric input to the noncomparable part of `app:ch_regular:eq:chain-tail`.
-/
theorem exists_noncomparable_tangential_geometry {X : Type*} [TopologicalSpace X]
    {S : Set (X × (ℝ × TangentialVariables E))} (hS : IsCompact S)
    (e : OrthonormalBasis ι ℝ E) (upper : Bool)
    (xi xo : X → ℝ × E) (hi : Continuous xi) (ho : Continuous xo)
    {c : ℝ} (hc : 0 < c)
    (hlarge : ∀ p ∈ S, c ≤ max (frequencySize p.2.2.2.2.1 p.2.2.2.2.2)
      (frequencySize p.2.2.2.1.1 p.2.2.2.1.2))
    (hsep : ∀ p ∈ S,
      2 * frequencySize p.2.2.2.2.1 p.2.2.2.2.2 ≤ frequencySize p.2.2.2.1.1 p.2.2.2.1.2 ∨
      2 * frequencySize p.2.2.2.1.1 p.2.2.2.1.2 ≤ frequencySize p.2.2.2.2.1 p.2.2.2.2.2) :
    ∃ G : ℝ, ∃ P : ℕ → ℝ, (∀ j, 0 ≤ P j) ∧ ∀ p : X,
      ∃ U : Set (ℝ × TangentialVariables E), IsOpen U ∧ {x | (p, x) ∈ S} ⊆ U ∧
      (∀ d, 0 ≤ d → ∀ z, (d, z) ∈ U →
        c ^ 2 / 8 ≤ Localization.phaseGradientSquare (baseFrequencyDirections e)
          (fun w => literalPhase upper (xi p) (xo p) (d, w)) z) ∧
      (∀ d, 0 ≤ d → ∀ z, (d, z) ∈ U →
        ‖fderiv ℝ (literalPhase upper (xi p) (xo p)) (d, z)‖ ≤ G) ∧
      (∀ x, (p, x) ∈ S → ∀ j, ∀ L : ℝ, 1 ≤ L →
        ‖iteratedFDeriv ℝ j (fderiv ℝ (literalPhase upper (xi p) (xo p))) x‖ ≤
          P j * L ^ j) := by
  obtain ⟨P, hP, hp⟩ := exists_uniform_literalPhase_profile hS upper
    (xi ∘ Prod.fst) (xo ∘ Prod.fst) Prod.snd
    (hi.comp continuous_fst) (ho.comp continuous_fst) continuous_snd
  refine ⟨P 0 + 1, P, hP, fun p => ?_⟩
  let T := fun x : ℝ × TangentialVariables E =>
    Localization.phaseGradientSquare (baseFrequencyDirections e)
      (fun w => literalPhase upper (xi p) (xo p) (x.1, w)) x.2
  let B := fun x => ‖fderiv ℝ (literalPhase upper (xi p) (xo p)) x‖
  have hT : Continuous T := continuous_literalPhase_base_gradientSquare e upper (xi p) (xo p)
  have hB : Continuous B :=
    ((contDiff_literalPhase upper (xi p) (xo p)).fderiv_right (m := ∞) (by simp)).continuous.norm
  refine ⟨{x | c ^ 2 / 8 < T x} ∩ {x | B x < P 0 + 1},
    (isOpen_lt continuous_const hT).inter (isOpen_lt hB continuous_const), ?_,
    fun _ _ _ hx => hx.1.le, fun _ _ _ hx => hx.2.le,
    fun x hx j L hL => hp (p, x) hx j L hL⟩
  intro x hx
  have hg := noncomparable_literalPhase_gradient_gap e upper (xi p) (xo p) x.1 x.2
    hc.le (hlarge (p, x) hx) (hsep (p, x) hx)
  have hb := hp (p, x) hx 0 1 le_rfl
  simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one, Function.comp_apply] at hb
  exact ⟨(by dsimp [T]; nlinarith [sq_pos_of_pos hc]), hb.trans_lt (lt_add_one _)⟩

end JanetCartan.FiniteChain.Retarded.KernelDecay
