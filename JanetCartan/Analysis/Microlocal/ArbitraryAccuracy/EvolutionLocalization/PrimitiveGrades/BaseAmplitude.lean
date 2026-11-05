module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.FrequencyOrders

/-!
# Full physical-base amplitude grades

The frequency is frozen before differentiating the two physical positions.
The original spatial symbol weight is compared to the actual graph branch
weight using the multiplier cone, for every real order. The bounded branches
therefore require no false uniform normalized-frequency derivative budget on
a ball. Consumer: the `hAbase` input of
`exists_graph_factor_sobolev_bound_of_primitive_grades`.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelDecay
variable {d q : ℕ}

/-- Fixed constants for physical base differentiation, retaining both masks
and the original multiplier (`app:ch_regular:eq:high-amplitude`). -/
def elapsedBaseSymbolProfile (Kb : Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (χout χsource : Euclidean (d + 1) → ℂ) (B : ℕ → ℝ) (Bβ C s : ℝ) (k : ℕ) : ℝ :=
  Bβ * elapsedOrderConstant C s * derivativeConvolution
    (fun i => cNorm Kb i (fun z => χout z.1 * χsource z.2)) B k

/-- Nonnegativity of the physical full-symbol profile
(`app:ch_regular:eq:high-amplitude`). -/
theorem elapsedBaseSymbolProfile_nonneg
    (Kb : Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (χout χsource : Euclidean (d + 1) → ℂ)
    {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k) {Bβ : ℝ} (hBβ : 0 ≤ Bβ) (C s : ℝ) (k : ℕ) :
    0 ≤ elapsedBaseSymbolProfile Kb χout χsource B Bβ C s k :=
  mul_nonneg (mul_nonneg hBβ (elapsedOrderConstant_nonneg C s))
    (derivativeConvolution_nonneg (fun _ => cNorm_nonneg ..) hB k)

/-- Construct the precise physical base amplitude profile, uniformly in the
elapsed interval and all graph branches. The primitive inputs are the original
two-time joint symbol grades, the original multiplier cone and its order-zero
size bound. `U` is a primitive symbol carrier; its inclusion is supplied by
the two-time chart/support geometry. Neither an elapsed grade nor a kernel
bound is a premise. The original fixed offset is preserved, and the profile
is chosen before `L,ρ,r,b` (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_physicalElapsedAmplitude_grades
    {Kb : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hKb : IsCompact Kb)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    {Bβ C : ℝ} (hBβ : 0 ≤ Bβ) (hC : 0 ≤ C)
    (hβ : ∀ ξ, ‖β ξ‖ ≤ Bβ)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ C * ‖spatialPart ξ‖)
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (offset : ℕ) (s Δ : ℝ) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
      ∀ (L ρ : ℝ), 1 ≤ L → 1 ≤ ρ →
      ∀ (b : TwoTimeAmplitude d q), ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) →
      ∀ U : Set (TwoTimePoint d),
      (∀ p ∈ U, ∀ k, ‖iteratedFDeriv ℝ k (SymbolBudgets.jointAmplitude b) p‖ ≤
          (1 + ‖p.2‖) ^ s * B k * L ^ (k + offset)) →
      ∀ r ∈ Icc 0 Δ,
      (∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j, ∀ z ∈ Kb,
        β (ρ • ξ) ≠ 0 → elapsedPoint r (z, ρ • ξ) ∈ U) →
      ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j, ∀ z ∈ Kb, ∀ k,
      ‖iteratedFDeriv ℝ k (fun v : Euclidean (d + 1) × Euclidean (d + 1) =>
        elapsedAmplitude b χout χsource β r v.1 v.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low j)) ^ s * D k * L ^ (k + offset) := by
  refine ⟨elapsedBaseSymbolProfile Kb χout χsource B Bβ C s,
    elapsedBaseSymbolProfile_nonneg Kb χout χsource hB hBβ C s, ?_⟩
  intro L ρ hL hρ b hb U hbudget r _ hmap low j ξ hξ z hz k
  let freq := ρ • ξ
  let M := fun v : Euclidean (d + 1) × Euclidean (d + 1) => χout v.1 * χsource v.2
  let F := fun v : ℝ × ℝ × Euclidean d => b v.1 v.2.1 v.2.2 (spatialPart freq)
  let A := fun v : Euclidean (d + 1) × Euclidean (d + 1) =>
    F (elapsedBaseLinear v + (0, -r, 0))
  have hM : ContDiff ℝ ∞ M := (hχout.comp contDiff_fst).mul (hχsource.comp contDiff_snd)
  have hF : ContDiff ℝ ∞ F := hb.comp (contDiff_id.prodMk contDiff_const)
  have hA : ContDiff ℝ ∞ A := hF.comp (elapsedBaseLinear.contDiff.add contDiff_const)
  have he : (fun v : Euclidean (d + 1) × Euclidean (d + 1) =>
      elapsedAmplitude b χout χsource β r v.1 v.2 freq) =
      fun v => β freq • (M v • A v) := by
    funext v
    simp only [elapsedAmplitude, M, A, F, elapsedBaseLinear]
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      Prod.mk_add_mk, add_zero, sub_eq_add_neg]
    rw [smul_smul]
    congr 1
    ring
  change ‖iteratedFDeriv ℝ k (fun v : Euclidean (d + 1) × Euclidean (d + 1) =>
    elapsedAmplitude b χout χsource β r v.1 v.2 freq) z‖ ≤ _
  rw [he]
  by_cases hzero : β freq = 0
  · simp only [hzero, zero_smul]
    change ‖iteratedFDeriv ℝ k (0 : (Euclidean (d + 1) × Euclidean (d + 1)) →
      Matrix (Fin q) (Fin q) ℂ) z‖ ≤ _
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) s)
      (elapsedBaseSymbolProfile_nonneg Kb χout χsource hB hBβ C s k))
        (pow_nonneg (zero_le_one.trans hL) _)
  have hm i : ‖iteratedFDeriv ℝ i M z‖ ≤ cNorm Kb i M * L ^ (i + 0) :=
    (norm_iteratedFDeriv_le_cNorm hKb (hM.of_le (by simp)) hz le_rfl).trans
      (le_mul_of_one_le_right (cNorm_nonneg ..) (one_le_pow₀ hL))
  have ha i : ‖iteratedFDeriv ℝ i A z‖ ≤
      (1 + ‖spatialPart freq‖) ^ s * B i * L ^ (i + offset) := by
    have hh := norm_iteratedFDeriv_affine_contraction_le elapsedBaseLinear
      norm_elapsedBaseLinear_le (0, -r, 0) isOpen_univ hF.contDiffOn
      (p := z) (mem_univ _) i
    apply hh.trans
    let inc := ContinuousLinearMap.inl ℝ (ℝ × ℝ × Euclidean d) (Euclidean d)
    have hinc : ‖inc‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      simp [inc, Prod.norm_def]
    have hslice := norm_iteratedFDeriv_affine_contraction_le inc hinc
      (0, spatialPart freq) isOpen_univ hb.contDiffOn
      (p := elapsedBaseLinear z + (0, -r, 0)) (mem_univ _) i
    have hslice' : ‖iteratedFDeriv ℝ i F (elapsedBaseLinear z + (0, -r, 0))‖ ≤
        ‖iteratedFDeriv ℝ i (SymbolBudgets.jointAmplitude b) (elapsedPoint r (z, freq))‖ := by
      simpa [F, inc, SymbolBudgets.jointAmplitude, elapsedBaseLinear,
        elapsedPoint_eq, sub_eq_add_neg] using hslice
    apply hslice'.trans
    simpa only [elapsedPoint_eq] using
      hbudget (elapsedPoint r (z, freq)) (hmap low j ξ hξ z hz hzero) i
  have hprod := norm_iteratedFDeriv_smul_le_amplitude_grades hM hA
    (fun i => cNorm_nonneg Kb i M) (zero_le_one.trans hL) 0 offset z hm ha k
  have hweight := spatialBracket_rpow_le_branchRadius hC s low j freq
    (hcone freq (subset_tsupport β hzero))
    ((mem_normalizedGraphCarrier_iff (zero_lt_one.trans_le hρ).ne' low j ξ).mp hξ)
  rw [iteratedFDeriv_const_smul_apply' (f := fun v => M v • A v)
    ((hM.smul hA).contDiffAt.of_le (by simp)), norm_smul]
  calc
    _ ≤ Bβ * ((1 + ‖spatialPart freq‖) ^ s *
        derivativeConvolution (fun i => cNorm Kb i M) B k * L ^ (k + offset)) :=
      mul_le_mul (hβ freq) (by simpa only [zero_add] using hprod) (norm_nonneg _) hBβ
    _ ≤ Bβ * (((max 1 (branchRadius low j)) ^ s * elapsedOrderConstant C s) *
        derivativeConvolution (fun i => cNorm Kb i M) B k * L ^ (k + offset)) := by
      apply mul_le_mul_of_nonneg_left _ hBβ
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hweight
          (derivativeConvolution_nonneg (fun _ => cNorm_nonneg ..) hB k))
        (pow_nonneg (zero_le_one.trans hL) _)
    _ = _ := by unfold elapsedBaseSymbolProfile; dsimp [M]; ring

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
