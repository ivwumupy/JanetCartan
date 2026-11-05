module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Reflection
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol

/-!
# Reflection of the same normalized determinant symbol

The sign is determined by the dimension of the original determinant. Covector
reflection preserves zero energy and transforms a signed Hamilton curve into
a signed Hamilton curve with the same absolute speed. These identities are
the analytic input for propagating the reflected proof relation in
`app:ch_regular:lem:finite-chain`; no symmetry of a finite chart selection is
assumed and no coefficient field is replaced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ActualCarriers HamiltonPhase

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => E × E

/-- The literal normalized determinant has its dimension-dependent parity,
including at the zero covector (`app:ch_regular:lem:finite-chain`). -/
theorem normalizedSymbol_covector_reflection
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (p : P) :
    normalizedSymbol Q (physicalCovectorReflection p) =
      (-1 : ℝ) ^ (d + 1) * normalizedSymbol Q p := by
  have hd := determinant_smul (Q p.1) p.2 (-1)
  simp only [neg_one_smul] at hd
  simp only [physicalCovectorReflection_apply, normalizedSymbol,
    determinantNormalization, norm_neg, hd, mul_assoc]

/-- Covector reflection preserves the characteristic set of the SAME
normalized pencil (`app:ch_regular:lem:finite-chain`). -/
theorem normalizedSymbol_reflection_eq_zero_iff
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (p : P) :
    normalizedSymbol Q (physicalCovectorReflection p) = 0 ↔ normalizedSymbol Q p = 0 := by
  rw [normalizedSymbol_covector_reflection, mul_eq_zero]
  simp only [pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0), false_or]

/-- Differentiate the actual determinant parity. The physical derivative
has the symbol's parity, and its covector derivative has the opposite parity.
Consumer: reflected whole-segment graph-error transport
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem normalizedHamilton_gradients_covector_reflection
    {Q : E → Fin (d + 1) → MetricTensor (d + 1)} (hQ : ContDiff ℝ ∞ Q)
    {p : P} (hp : p.2 ≠ 0) :
    let H := normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn
    H.hx (physicalCovectorReflection p) = (-1 : ℝ) ^ (d + 1) • H.hx p ∧
      H.hp (physicalCovectorReflection p) = -((-1 : ℝ) ^ (d + 1)) • H.hp p := by
  intro H
  have hdom : p ∈ H.domain := ⟨mem_univ _, hp⟩
  have hdomr : physicalCovectorReflection p ∈ H.domain :=
    ⟨mem_univ _, neg_ne_zero.mpr hp⟩
  have hleft := (H.hasFDerivAt_h _ hdomr).comp p
    physicalCovectorReflection.toContinuousLinearEquiv.hasFDerivAt
  have hright := (H.hasFDerivAt_h p hdom).const_mul ((-1 : ℝ) ^ (d + 1))
  have heq : H.h ∘ physicalCovectorReflection =
      fun q ↦ (-1 : ℝ) ^ (d + 1) * H.h q := by
    funext q
    exact normalizedSymbol_covector_reflection Q q
  rw [heq] at hleft
  have hdiff := hleft.unique hright
  constructor
  · apply ext_inner_right ℝ
    intro v
    have hv := congrArg (fun L : P →L[ℝ] ℝ ↦ L (v, 0)) hdiff
    simpa [hamiltonDifferential_apply, real_inner_smul_left] using hv
  · apply ext_inner_right ℝ
    intro v
    have hv := congrArg (fun L : P →L[ℝ] ℝ ↦ L (0, v)) hdiff
    have hv' : -inner ℝ (H.hp (physicalCovectorReflection p)) v =
        (-1 : ℝ) ^ (d + 1) * inner ℝ (H.hp p) v := by
      simpa [hamiltonDifferential_apply] using hv
    rw [real_inner_smul_left]
    linarith

/-- Reflecting a signed Hamilton curve changes its signed speed by a unit
sign. Both physical points and the entire elapsed interval are retained.
This is used for the reflected relation, not to alter the actual solver
(`app:ch_regular:lem:finite-chain`). -/
theorem normalizedHamilton_reflected_curve
    {Q : E → Fin (d + 1) → MetricTensor (d + 1)} (hQ : ContDiff ℝ ∞ Q)
    {x ξ : ℝ → E} {c : ℝ → ℝ} {t : ℝ} (hξ : ξ t ≠ 0)
    (hx : HasDerivAt x
      (c t • (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn).hp (x t, ξ t)) t)
    (hp : HasDerivAt ξ
      (c t • -(normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn).hx (x t, ξ t)) t) :
    let H := normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn
    let cr := c t * -((-1 : ℝ) ^ (d + 1))
    HasDerivAt x (cr • H.hp (x t, -ξ t)) t ∧
      HasDerivAt (fun s ↦ -ξ s) (cr • -H.hx (x t, -ξ t)) t ∧ |cr| = |c t| := by
  intro H cr
  obtain ⟨hhx, hhp⟩ := normalizedHamilton_gradients_covector_reflection hQ (p := (x t, ξ t)) hξ
  change H.hx (x t, -ξ t) = _ at hhx
  change H.hp (x t, -ξ t) = _ at hhp
  have hs : ((-1 : ℝ) ^ (d + 1)) * ((-1 : ℝ) ^ (d + 1)) = 1 := by
    rw [← mul_pow]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hhp, smul_smul]
    convert hx using 1
    dsimp [cr]
    congr 1
    rw [mul_assoc, neg_mul_neg, hs, mul_one]
  · rw [hhx, ← smul_neg, smul_smul]
    convert hp.neg using 1
    rw [← neg_smul]
    dsimp [cr]
    congr 1
    rw [mul_assoc, neg_mul, hs, mul_neg_one]
  · dsimp [cr]
    rw [abs_mul, abs_neg, abs_pow]
    norm_num

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
