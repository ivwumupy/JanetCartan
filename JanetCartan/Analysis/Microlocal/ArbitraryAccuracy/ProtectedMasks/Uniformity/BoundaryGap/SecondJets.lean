module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.RootFlow
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.ConicBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhaseGrades

/-!
# The boundary collar's second jet from the original C³ budget

`exists_uniform_fieldRoot_twoTimeHamiltonPhase` supplies exactly the summed
budget consumed below, at `n = 2`. Its domains and constants precede `Q`.
The local phase is estimated on the constructor's closed `2β` target buffer;
conic normalization uses the same buffer and the fixed normalization map.
Consumer: elapsed variation in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open ConicPhase

variable {d : ℕ}

/-- Extract the common local C² phase budget from the literal order-two
output of `UniformGeometry.exists_uniform_fieldRoot_twoTimeHamiltonPhase`.
Only the original C³ coefficient bound enters; all four other nonnegative
terms are retained in the producer premise (`app:ch_regular:eq:chain-tail`). -/
theorem twoTimePhase_secondJet_budget_of_rootFlow
    (z : RootState (Euclidean d)) (ρ T σ β : ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (x : Euclidean (d + 1)) (R : ℝ)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    {B M : ℝ} (hB : 0 ≤ B) (hQM : cNorm (closedBall x R) 3 Q ≤ M)
    (hbudget : cNorm (closedBall z ((3 * ρ) / 4) ×ˢ Icc (-T / 4) (T / 4)) 2 Φ +
      (cNorm (closedBall (z.1, z) σ) 2 (twoTimeState Φ) +
        cNorm (closedBall (z.1, z) σ) 2 (twoTimeProjection Φ)) +
      (cNorm (closedBall (z.1, z) (2 * β)) 2 C.symm +
        cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C)) ≤
          B * (1 + cNorm (closedBall x R) 3 Q)) :
    cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C) ≤ B * (1 + M) := by
  have h₁ := cNorm_nonneg (closedBall z ((3 * ρ) / 4) ×ˢ Icc (-T / 4) (T / 4)) 2 Φ
  have h₂ := cNorm_nonneg (closedBall (z.1, z) σ) 2 (twoTimeState Φ)
  have h₃ := cNorm_nonneg (closedBall (z.1, z) σ) 2 (twoTimeProjection Φ)
  have h₄ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) 2 C.symm
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_left hQM 1) hB
  linarith

/-- Restrict the actual constructor's phase budget to the smaller common
radius used in `exists_uniform_fieldRoot_conicGeometry`. This closes the
`γ ≤ β` domain restriction without a new low-jet assumption
(`app:ch_regular:lem:finite-chain`). -/
theorem twoTimePhase_secondJet_budget_restrict
    (z : RootState (Euclidean d)) {γ β N : ℝ} (hγβ : γ ≤ β)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hbuffer : closedBall (z.1, z) (2 * β) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hN : cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C) ≤ N) :
    cNorm (closedBall (z.1, z) (2 * γ)) 2 (twoTimePhase C) ≤ N :=
  (cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall (by linarith))
    (isCompact_closedBall _ _)
    (fun q hq ↦ (hs.contDiffAt (C.open_target.mem_nhds (hbuffer hq))).of_le (by simp))).trans hN

/-- The constructor's center in the joint budget coordinates. This is a
fixed reassociation, independent of the coefficient field
(`app:ch_regular_base:eq:fixed-time-representation`). -/
def boundaryBudgetCenter (z : RootState (Euclidean d)) : SymbolBudgets.TwoTimePoint d :=
  ((z.1, (z.1, z.2.1)), z.2.2)

/-- Reassociation preserves the entire closed target buffer, including its
boundary (`app:ch_regular:eq:chain-tail`). -/
theorem budgetCoordinates_mem_boundary_buffer
    (z : RootState (Euclidean d)) (a : ℝ) {q : SymbolBudgets.TwoTimePoint d} :
    budgetCoordinates q ∈ closedBall (z.1, z) a ↔
      q ∈ closedBall (boundaryBudgetCenter z) a := by
  simp only [mem_closedBall, budgetCoordinates, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, boundaryBudgetCenter, Prod.dist_eq, max_assoc]

/-- The actual local phase's joint second jet on the fixed closed `2β`
buffer. The low budget is produced by `twoTimePhase_secondJet_budget_of_rootFlow`;
smoothness and target containment are returned by the same constructor
(`app:ch_regular:lem:finite-chain`). -/
theorem chartPhase_secondJet_on_buffer
    (z : RootState (Euclidean d)) (β : ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hbuffer : closedBall (z.1, z) (2 * β) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {N : ℝ} (hN : cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C) ≤ N) :
    (∀ q ∈ closedBall (boundaryBudgetCenter z) (2 * β),
      ContDiffAt ℝ 2 (SymbolBudgets.jointPhase (chartPhase C)) q) ∧
    ∀ q ∈ closedBall (boundaryBudgetCenter z) (2 * β),
      ‖iteratedFDeriv ℝ 2 (SymbolBudgets.jointPhase (chartPhase C)) q‖ ≤ N := by
  have hmap : MapsTo budgetCoordinates (closedBall (boundaryBudgetCenter z) (2 * β))
      (closedBall (z.1, z) (2 * β)) :=
    fun _ hq ↦ (budgetCoordinates_mem_boundary_buffer z _).mpr hq
  have hsm q (hq : q ∈ closedBall (boundaryBudgetCenter z) (2 * β)) :
      ContDiffAt ℝ 2 (SymbolBudgets.jointPhase (chartPhase C)) q :=
    ((hs.contDiffAt (C.open_target.mem_nhds (hbuffer (hmap hq)))).comp q
      (budgetCoordinates (d := d)).contDiff.contDiffAt).of_le (by simp)
  refine ⟨hsm, fun q hq ↦ ?_⟩
  apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _) hsm hq le_rfl).trans
  apply LE.le.trans ?_ hN
  rw [show SymbolBudgets.jointPhase (chartPhase C) =
    (fun q ↦ twoTimePhase C (budgetCoordinates q)) from rfl]
  simpa only [add_zero] using
    (SymbolBudgets.cNorm_preAffine_contraction_le budgetCoordinates norm_budgetCoordinates_le 0
      (isCompact_closedBall (z.1, z) (2 * β)) C.open_target hbuffer hs
      (by simpa only [add_zero] using hmap) 2)

/-- The same producer budget controls normalized conic second jets on any
fixed compact joint carrier whose normalized image stays in the constructor's
closed `2β` buffer. Positivity and image containment are explicit fixed-domain
restrictions; radial scale and `Q` do not enter the normalization constant
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem normalizedConicPhase_secondJet_on_fixed_carrier
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d)) (β : ℝ)
    {K : Set (SymbolBudgets.TwoTimePoint d)} (hK : IsCompact K)
    (hpos : ∀ q ∈ K, 0 < ℓ q.2)
    (hmap : MapsTo (normalize ℓ ∘ budgetCoordinates) K (closedBall (z.1, z) (2 * β)))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hbuffer : closedBall (z.1, z) (2 * β) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {N : ℝ} (hN : cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C) ≤ N)
    {R : ℝ} (hR : 0 < R) :
    (∀ q ∈ K, ContDiffAt ℝ 2 (SymbolBudgets.jointPhase
      (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C))) q) ∧
    ∀ q ∈ K, ‖iteratedFDeriv ℝ 2 (SymbolBudgets.jointPhase
      (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C))) q‖ ≤
        jetBoundConstant ℓ (budgetCoordinates '' K) 2 * N := by
  have hsm q (hq : q ∈ K) : ContDiffAt ℝ 2 (SymbolBudgets.jointPhase
      (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C))) q := by
    rw [show curriedPhase ℓ C = curriedExtend ℓ (twoTimePhase C) from rfl,
      normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C) hR]
    exact ((contDiffOn_jointPhase_curriedExtend ℓ C.open_target hs).contDiffAt
      (((isOpen_domain ℓ C.open_target).preimage budgetCoordinates.continuous).mem_nhds
        ⟨hpos q hq, hbuffer (hmap hq)⟩)).of_le (by simp)
  refine ⟨hsm, fun q hq ↦ ?_⟩
  apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hsm hq le_rfl).trans
  exact (cNorm_normalizedTwoTimePhase_phase_le ℓ C hs hK (isCompact_closedBall _ _)
    hbuffer hpos hmap hR 2).trans
      (mul_le_mul_of_nonneg_left hN (jetBoundConstant_pos _ _ _).le)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
