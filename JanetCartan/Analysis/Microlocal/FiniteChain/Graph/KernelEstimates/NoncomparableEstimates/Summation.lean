module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.SingleShell
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.Powers

/-!
# Summable regularized graph shells

The actual output jets in `app:ch_regular:eq:chain-tail` are summed from
primitive full-symbol, cutoff and mask grades. Constants precede all scales,
regularizers and external positions. The separate larger-gap producer must
supply the normalized phase hypotheses; no kernel estimate is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Pointwise Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace Retarded.KernelDecay
open Retarded.KernelSobolev
variable {n r : ℕ}

set_option maxHeartbeats 800000 in
/-- Absolute summation of the actual output derivatives of explicitly
regularized graph shells (`app:ch_regular:eq:chain-tail`). The three Fourier
measures cost `3*n`, output differentiation costs `m`, and arbitrary fixed
real symbol orders cost their positive parts. The fixed integer `a` is chosen above
this total; `q+a+1` physical-base integrations then give the existing
`dyadicShellWeight`. Both the power of `ρ` and the grade loss are independent
of `q`. Smaller radii may equal one, including source shoulders.

The constants are chosen before `ρ`, `L`, the symbols, regularizers, carriers,
and external positions. The wave profile is derived from the fixed compact
output carrier. The only quantitative phase inputs are the precise gap,
first derivative bound and higher grades for `normalizedBasePhase`. The parent
`jc-graph-factor-kernel-estimates` must instantiate the gap from
`jc-graph-factor-kernel-larger-gap` and the upper derivative bounds from its
primitive phase grades. This theorem asserts no operator identity or removal
of regularizers. -/
theorem exists_regularizedShellKernel_dyadic_bounds {ι : Type*} [Fintype ι]
    (backward : Bool)
    {Kb : Set (Euclidean n × Euclidean n)} {Bξ Bη Bζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hBξ : IsCompact Bξ) (hBη : IsCompact Bη) (hBζ : IsCompact Bζ)
    (e : ι → Euclidean n × Euclidean n) {δ G Ca Co Ci : ℝ}
    (hδ : 0 < δ) (hCa : 0 ≤ Ca) (hCo : 0 ≤ Co) (hCi : 0 ≤ Ci)
    (P B O : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hO : ∀ j, 0 ≤ O j)
    (sA si so : ℝ) (ba bc bi bo bA m : ℕ) :
    ∃ (a : ℕ) (C : ℕ → ℝ), (∀ q, 0 ≤ C q) ∧
    ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
    ∀ (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
      (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
      (x y : Euclidean n) (σA σi σo : ℕ → ℝ)
      (Kξ Kη Kζ : ℕ → Set (Euclidean n))
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
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ContDiffOn ℝ ∞
      (normalizedBasePhase backward ρ ((2 : ℝ) ^ k * ρ) φ x y w) (U k w)) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ContDiffOn ℝ ∞
      (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) (U k w)) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k →
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ U k w) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k →
      tsupport (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • w.1)) ⊆ Kb) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ U k w,
      δ ≤ phaseGradientSquare e
        (normalizedBasePhase backward ρ ((2 : ℝ) ^ k * ρ) φ x y w) z) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ U k w,
      ‖fderiv ℝ (normalizedBasePhase backward ρ ((2 : ℝ) ^ k * ρ) φ x y w) z‖ ≤ G) →
    (∀ k w, w ∈ Kξ k ×ˢ Kη k ×ˢ Kζ k → ∀ z ∈ Kb, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1)
        (normalizedBasePhase backward ρ ((2 : ℝ) ^ k * ρ) φ x y w) z‖ ≤ P j * L ^ j) →
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
  let a := Nat.ceil ((3 * n + m : ℕ) + max 0 sA + max 0 si + max 0 so : ℝ)
  have hthreshold : (3 * n + m : ℕ) + max 0 sA + max 0 si + max 0 so ≤ (a : ℝ) :=
    Nat.le_ceil _
  obtain ⟨W, hW, hWave⟩ := exists_baseWave_profile hBζ
  let D := Ca * Co * Ci * derivativeConvolution W (fun j => 1 + O j) m
  let V := volume.real Bξ * volume.real Bη * volume.real Bζ
  let C := fun q => jointNormalization n * decayConstant e δ G P B (q + a + 1) *
    (baseMeasure n).real Kb * D * V
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (mul_nonneg hCa hCo) hCi)
    (derivativeConvolution_nonneg hW (fun j => by linarith [hO j]) m)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hC q : 0 ≤ C q := mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (jointNormalization_nonneg n)
      (decayConstant_nonneg e δ G P B hB (q + a + 1))) measureReal_nonneg) hD) hV
  refine ⟨a, C, hC, ?_⟩
  intro ρ L hL hLρ φ A mi mo χA χo x y σA σi σo Kξ Kη Kζ U
    hσA hσi hσo hσAR hσiR hσoR hKξ hKη hKζ hsξ hsη hsζ hU
    ho hAsmooth hismooth hcasmooth hcosmooth hφsmooth hφ hA hsU hsK
    hgap hupper hp hamp hi hca hco hb q v hv
  let R := fun k : ℕ => (2 : ℝ) ^ k * ρ
  let p : ℝ := (3 * n + m : ℕ) + max 0 sA + max 0 si + max 0 so
  let b := ba + bc + bi + (m + bo) + bA
  let J := fun k => iteratedFDeriv ℝ m
    (fun t => regularizedShellKernel backward ρ φ A mi mo (χA k) (χo k)
      Kb (Kξ k) (Kη k) (Kζ k) t y) x v
  let F := C q * ρ ^ p * L ^ b
  change (∀ k, ‖J k‖ ≤ F * dyadicShellWeight a q (L / ρ) k) ∧
    Summable (fun k => ‖J k‖) ∧ HasSum J (∑' k, J k) ∧
    ‖∑' k, J k‖ ≤ 2 * F * (L / ρ) ^ q
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR k : 1 ≤ R k := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (hL.trans hLρ)
  have hR0 k : 0 < R k := zero_lt_one.trans_le (hR k)
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg (hC q) (Real.rpow_nonneg hρ.le p))
    (pow_nonneg hL0 b)
  have hbound (k : ℕ) : ‖J k‖ ≤ F * dyadicShellWeight a q (L / ρ) k := by
    have hw (ζ) (hζ : ζ ∈ Kζ k) (j) : ‖iteratedFDeriv ℝ j
        (fun t => outputJointWave (t, (ρ / R k) • ζ)) 0‖ ≤ W j := by
      apply hWave j
      obtain ⟨z, hz, rfl⟩ := hsζ k hζ
      have he : (ρ / R k) * ((2 : ℝ) ^ k * ρ / ρ) = 1 := by
        change (ρ / R k) * (R k / ρ) = 1
        field_simp [hρ.ne', (hR0 k).ne']
      simpa only [smul_smul, he, one_smul] using hz
    have hb' (ζ) (hζ : ζ ∈ Kζ k) (j) :
        ‖iteratedFDeriv ℝ j (fun t => mo (t, ζ)) x‖ ≤
          (σo k) ^ (max 0 so) * O j * L ^ (j + bo) :=
      (hb k ζ hζ j).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (hσo k) (le_max_right 0 so)) (hO j))
        (pow_nonneg hL0 _))
    have hjet := norm_iteratedFDeriv_regularizedShellKernel_le backward hρ.le (hR k) hL
      (Real.rpow_nonneg (zero_le_one.trans (hσA k)) sA)
      (Real.one_le_rpow (hσo k) (le_max_left 0 so))
      (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hσi k)) si) hCi)
      hCa hCo hδ φ A mi mo (χA k) (χo k) x y hKb (hKξ k) (hKη k) (hKζ k)
      (U k) (hU k) e P B W O hB hW hO ba bc bi bo bA m (q + a + 1) v hv
      ho hAsmooth hismooth (hcasmooth k) (hcosmooth k) hφsmooth
      (hφ k) (hA k) (hsU k) (hsK k) (hgap k) (hupper k) (hp k) (hamp k)
      (hi k) (hca k) (hco k) hw hb'
    let T := jointNormalization n * decayConstant e δ G P B (q + a + 1) *
      (baseMeasure n).real Kb * D
    have hT : 0 ≤ T := mul_nonneg (mul_nonneg
      (mul_nonneg (jointNormalization_nonneg n)
        (decayConstant_nonneg e δ G P B hB (q + a + 1))) measureReal_nonneg) hD
    have hsize := three_frequency_size_le hρ (hR k) (hσA k) (hσi k) (hσo k)
      (hσAR k) (hσiR k) (hσoR k) hBξ hBη hBζ (hsξ k) (hsη k) (hsζ k) sA si so m
    calc
      ‖J k‖ ≤ T * L ^ b *
          ((ρ ^ (3 * n) * (volume.real (Kξ k) * volume.real (Kη k) * volume.real (Kζ k))) *
            (R k) ^ m * ((σA k) ^ sA * (σi k) ^ si * (σo k) ^ (max 0 so))) *
          (L / R k) ^ (q + a + 1) := by
        convert hjet using 1
        dsimp [T, D, b]
        ring
      _ ≤ T * L ^ b * (V * (R k) ^ p) * (L / R k) ^ (q + a + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize
          (mul_nonneg hT (pow_nonneg hL0 _))) (pow_nonneg (div_nonneg hL0 (hR0 k).le) _)
      _ = (C q * L ^ b) * ((R k) ^ p * (L / R k) ^ (q + a + 1)) := by
        dsimp [C, T]; ring
      _ ≤ (C q * L ^ b) * (ρ ^ p * dyadicShellWeight a q (L / ρ) k) :=
        mul_le_mul_of_nonneg_left (real_shell_power_le_dyadicWeight hρ hL0 a q k hthreshold)
          (mul_nonneg (hC q) (pow_nonneg hL0 _))
      _ = F * dyadicShellWeight a q (L / ρ) k := by dsimp [F]; ring
  have hθ := div_nonneg hL0 hρ.le
  have hθ' := (div_le_one hρ).mpr hLρ
  have hs := (summable_dyadicShellWeight a q hθ hθ').mul_left F
  have hn : Summable (fun k => ‖J k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound hs
  refine ⟨hbound, hn, hn.of_norm.hasSum, ?_⟩
  calc
    ‖∑' k, J k‖ ≤ ∑' k, ‖J k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, F * dyadicShellWeight a q (L / ρ) k := hn.tsum_le_tsum hbound hs
    _ = F * ∑' k, dyadicShellWeight a q (L / ρ) k := tsum_mul_left
    _ ≤ F * (2 * (L / ρ) ^ q) :=
      mul_le_mul_of_nonneg_left (tsum_dyadicShellWeight_le a q hθ hθ') hF
    _ = 2 * F * (L / ρ) ^ q := by ring

end JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
