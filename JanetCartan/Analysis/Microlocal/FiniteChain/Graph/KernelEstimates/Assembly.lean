module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.ShellAssembly
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Decay

/-!
# Joint and shell estimates for the graph kernel

The final pointwise input to the parent `Retarded.KernelSobolev` assembly for
`app:ch_regular:eq:chain-tail`: actual comparable output derivatives plus the
absolutely convergent series of actual noncomparable output derivatives.
The exact comparable joint gap is supplied by buffered localizers; all shell
gaps are derived here from physical covector comparison. Identification with
the operator and differentiating regularization limits remain separate work
in `Graph.KernelLimits`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Pointwise Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace Retarded.KernelDecay
open Noncomparable NoncomparableGeometry
variable {n r : ℕ}

private theorem graded_monomial_mono {ρ L A p p' : ℝ} {b b' q : ℕ}
    (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (hA : 0 ≤ A) (hp : p ≤ p') (hb : b ≤ b') :
    A * ρ ^ p * L ^ b * (L / ρ) ^ q ≤ A * ρ ^ p' * L ^ b' * (L / ρ) ^ q := by
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ hp) hA)
      (pow_le_pow_right₀ hL hb) (pow_nonneg hL0 _) (mul_nonneg hA (Real.rpow_nonneg hρ0 _)))
    (pow_nonneg (div_nonneg hL0 hρ0) _)

/-- The comparable jet plus the noncomparable shell series obeys `ρ^(m+C_A) L^b (L/ρ)^q`,
with both losses independent of accuracy. The conclusion concerns the literal
joint integral and actual shell derivatives, and assumes no kernel or operator
bound. Forward graphs, reverse graphs with `weightedInverseAmplitude`, and
negative symbol orders use the same theorem. The inverse amplitude represents
the existing operator by `reverseGraphOperator_weightedInverseAmplitude`
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_regularizedGraphKernel_graded_bounds {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (backward : Bool)
    {Kb : Set (Euclidean n × Euclidean n)} {Bξ Bη Bζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hBξ : IsCompact Bξ) (hBη : IsCompact Bη) (hBζ : IsCompact Bζ)
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    {c C₀ G Ca Co Ci : ℝ} (hc : 0 < c) (hCa : 0 ≤ Ca) (hCo : 0 ≤ Co) (hCi : 0 ≤ Ci)
    (P B O : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hO : ∀ j, 0 ≤ O j)
    (sA si so : ℝ) (ba bc bi bo bA m : ℕ)
    (D : AmplitudeProfiles) {Kc : Set (JointVariables (Euclidean n))} (hKc : IsCompact Kc)
    (ec : ν → JointVariables (Euclidean n)) {δc Gc : ℝ} (hδc : 0 < δc)
    (Pc Wc Oc : ℕ → ℝ) (hWc : ∀ j, 0 ≤ Wc j) (hOc : ∀ j, 0 ≤ Oc j)
    (sc : ℝ) (boc : ℕ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
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
    ∀ (χAc χoc : Euclidean n → ℝ) (Uc : Set (JointVariables (Euclidean n))),
    HasAmplitudeGrades D ρ (ρ ^ sc) L A mi (fun _ => 0) χAc χoc 0 y Kc →
    IsOpen Uc →
    tsupport (jointAmplitude ρ A mi (fun _ => 0) χAc χoc 0 y) ⊆ Kc →
    (∀ p ∈ Uc, δc ≤ phaseGradientSquare ec (jointPhase backward φ x y) p) →
    (∀ p ∈ Uc, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ Gc) →
    (∀ p ∈ Kc, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (jointPhase backward φ x y) p‖ ≤ Pc j * L ^ j) →
    (∀ p ∈ Kc, ∀ j, ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2)‖ ≤ Wc j) →
    (∀ p ∈ Kc, ∀ j, ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) (0, p.2.2.2)‖ ≤ Oc j * L ^ (j + boc)) →
    ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
    tsupport (outputJetAmplitude backward ρ φ A mi mo χAc χoc x y m v) ⊆ Uc →
      let J := fun k => iteratedFDeriv ℝ m
        (fun t => regularizedShellKernel backward ρ φ A mi mo (χA k) (χo k)
          Kb (Kξ k) (Kη k) (Kζ k) t y) x v
      Summable (fun k => ‖J k‖) ∧
      ‖iteratedFDeriv ℝ m
          (fun t => regularizedJointKernel backward ρ φ A mi mo χAc χoc t y) x v +
        ∑' k, J k‖ ≤
          C q * ρ ^ ((m : ℝ) + max (sc + (3 * n : ℕ))
            ((3 * n : ℕ) + max 0 sA + max 0 si + max 0 so)) *
          L ^ (max ((m + boc) + D.offset) (ba + bc + bi + (m + bo) + bA)) * (L / ρ) ^ q := by
  obtain ⟨a, Cs, hCs, hshell⟩ := exists_shell_bounds_of_physical_grades
    (r := r) backward hKb hBξ hBη hBζ eu ez hc hCa hCo hCi
    P B O hB hO sA si so ba bc bi bo bA m
  let Cc := fun q => jointNormalization n *
    decayConstant ec δc Gc Pc (D.outputJetProfile Wc Oc m) q * (jointMeasure n).real Kc
  have hCc (q) : 0 ≤ Cc q := mul_nonneg (mul_nonneg (jointNormalization_nonneg n)
    (decayConstant_nonneg ec δc Gc Pc (D.outputJetProfile Wc Oc m)
      (D.outputJetProfile_nonneg hWc hOc m) q)) measureReal_nonneg
  refine ⟨fun q => Cc q + 2 * Cs q, fun q => add_nonneg (hCc q) (mul_nonneg (by norm_num) (hCs q)), ?_⟩
  intro ρ L hL hLρ Φ φ A mi mo χA χo x y σA σi σo Kξ Kη Kζ g U
    hσA hσi hσo hσAR hσiR hσoR hKξ hKη hKζ hsξ hsη hsζ hU
    ho hAsmooth hismooth hcasmooth hcosmooth hφsmooth hhom hphysical hA hsU hsK
    hslice hg hlow hhigh hsep hlarge hupper hp hamp hi hca hco hb
    χAc χoc Uc hac hUc hsc hgapc hupperc hpc hwc hbc q v hv hsUc
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  obtain ⟨_, hsum, _, hsb⟩ := hshell ρ L hL hLρ Φ φ A mi mo χA χo x y
    σA σi σo Kξ Kη Kζ g U hσA hσi hσo hσAR hσiR hσoR hKξ hKη hKζ
    hsξ hsη hsζ hU ho hAsmooth hismooth hcasmooth hcosmooth hφsmooth hhom hphysical
    hA hsU hsK hslice hg hlow hhigh hsep hlarge hupper hp hamp hi hca hco hb q v hv
  have hcb := norm_iteratedFDeriv_regularizedJointKernel_apply_le backward hρ hL sc φ x y
    hac ho hφsmooth hUc hKc hsc ec hδc hgapc hupperc Pc hpc hWc hOc boc m q v hv hwc hbc hsUc
  refine ⟨hsum, (norm_add_le _ _).trans ((add_le_add hcb hsb).trans ?_)⟩
  let p : ℝ := (m : ℝ) + max (sc + (3 * n : ℕ))
    ((3 * n : ℕ) + max 0 sA + max 0 si + max 0 so)
  let b := max ((m + boc) + D.offset) (ba + bc + bi + (m + bo) + bA)
  have hcmono := graded_monomial_mono (q := q) (hL.trans hLρ) hL (hCc q)
    (show (m : ℝ) + (sc + (3 * n : ℕ)) ≤ p by
      dsimp [p]
      exact add_le_add (le_refl _) (le_max_left _ _))
    (le_max_left ((m + boc) + D.offset) (ba + bc + bi + (m + bo) + bA))
  have hsmono := graded_monomial_mono (q := q) (hL.trans hLρ) hL
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hCs q))
    (show ((3 * n + m : ℕ) + max 0 sA + max 0 si + max 0 so : ℝ) ≤ p by
      have ht := add_le_add (le_refl (m : ℝ))
        (le_max_right (sc + (3 * n : ℕ))
          ((3 * n : ℕ) + max 0 sA + max 0 si + max 0 so))
      simpa only [p, Nat.cast_add, add_assoc, add_comm, add_left_comm] using ht)
    (le_max_right ((m + boc) + D.offset) (ba + bc + bi + (m + bo) + bA))
  change _ ≤ (Cc q + 2 * Cs q) * ρ ^ p * L ^ b * (L / ρ) ^ q
  calc
    _ = Cc q * ρ ^ ((m : ℝ) + (sc + (3 * n : ℕ))) * L ^ ((m + boc) + D.offset) *
          (L / ρ) ^ q +
        (2 * Cs q) * ρ ^ ((3 * n + m : ℕ) + max 0 sA + max 0 si + max 0 so : ℝ) *
          L ^ (ba + bc + bi + (m + bo) + bA) * (L / ρ) ^ q := by dsimp [Cc]; ring
    _ ≤ Cc q * ρ ^ p * L ^ b * (L / ρ) ^ q +
        (2 * Cs q) * ρ ^ p * L ^ b * (L / ρ) ^ q := add_le_add hcmono hsmono
    _ = _ := by ring

end JanetCartan.FiniteChain.Graph.KernelEstimates
