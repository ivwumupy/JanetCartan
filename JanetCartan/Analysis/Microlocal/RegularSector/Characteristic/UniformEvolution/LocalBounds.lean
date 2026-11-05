module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.Assembly
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.RestrictionBounds

/-!
# Local consumers of the constructed signed retarded operators

These apply the existing restriction and pairing theorems to the operators
constructed in `Assembly`. Their test actions establish the actual local
zero-extension identities; no additional output-support identity or graph
bound is assumed. The high coefficient profile and fixed shifts are unchanged.
Source: `app:ch_regular_base:eq:negative-duality` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open FourierIntegral EvolutionIntegral RetardedLocalization
open LocalSobolev Pseudodifferential ArbitraryAccuracy
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "Mat" => MetricTensor (d+1)

/-- The same constructed operator and literal adjoint have the local negative
pairing on their actual mask domains. `hOp` is the conclusion of
`exists_retained_local_solver_and_residual`, including its original test
action; `RetardedLocalization` derives both zero extensions from that action
(`negative-duality`). -/
theorem retained_signed_bounds_local_negative_pairing
    (KQ : Set E) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (Δ a : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (o : ℕ) (A₀ : ℝ) (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s)
    (Op : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hOp : RetainedSignedRetardedBounds KQ Q B Δ a Ψ W χout χsource β hs o A₀ A Op)
    {U Vout : Set E} (hU : IsOpen U) (hVout : IsOpen Vout)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hos : tsupport χout ⊆ Vout) (hss : tsupport χsource ⊆ U) (k : ℕ) :
    let C := (((q : ℝ) * scalarLocalDualityConstant (d+1) k) *
      (((q : ℝ)*q*A (k+o)) *
        (1 + retardedCoefficientProfile KQ Q B (k+o+(FullLowBounds.fullLowReserve (d+1)+2)))))
    (∀ (f : LocalL2 U V) (v : LocalL2 Vout V), MemRestrictionSobolev Vout k v →
      ‖inner ℂ (localRetardedOperator hU.measurableSet Vout Op f) v‖ ≤ C *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ))
          (SmallSupport.zeroExtend hU.measurableSet f) * restrictionSobolevNorm Vout k v) ∧
    (∀ (g : LocalL2 Vout V) (v : LocalL2 U V), MemRestrictionSobolev U k v →
      ‖inner ℂ ((localRetardedOperator hU.measurableSet Vout Op).adjoint g) v‖ ≤ C *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ))
          (SmallSupport.zeroExtend hVout.measurableSet g) * restrictionSobolevNorm U k v) := by
  simpa only [one_mul] using localRetardedOperator_negative_pairing Ψ W χout χsource β hs a Op
    (fun u ↦ (hOp.2.2.2.2.2 u).1) hU hVout hoc hsc hos hss o
    (FullLowBounds.fullLowReserve (d+1)+2) (Δ := 1) zero_le_one A
    (retardedCoefficientProfile KQ Q B) hA
    (fun m ↦ add_nonneg (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _))
    (by simpa only [one_mul] using hOp.2.2.2.1) k

/-- A dimension-only constant converts the SAME constructed residual's
gain-one bound to restriction `H¹` in both orientations. No new norm of
the residual or its coefficients is assumed (`energy-complete-residual`). -/
theorem exists_retained_local_residual_H1_constant (d q : ℕ) :
    ∃ D > (0 : ℝ),
    ∀ (KQ : Set (Euclidean (d+1)))
      (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
      (B : Euclidean (d+1) → MetricTensor (d+1))
      (Δ a : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
      (χout χsource β : Euclidean (d+1) → ℂ) (hs : ContDiff ℝ ∞ χsource)
      (A₀ : ℝ) (A : ℕ → ℝ) (Op : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q),
      RetainedSignedRetardedBounds KQ Q B Δ a Ψ W χout χsource β hs 1 A₀ A Op →
    ∀ (U Vout : Set (Euclidean (d+1))) (hU : MeasurableSet U) (_hVout : MeasurableSet Vout),
      (∀ f : LocalL2 U (EuclideanSpace ℂ (Fin q)),
        MemRestrictionSobolev Vout 1 (localRetardedOperator hU Vout Op f) ∧
        restrictionSobolevNorm Vout 1 (localRetardedOperator hU Vout Op f) ≤
          (D * A 1 * (1 + retardedCoefficientProfile KQ Q B
            (1+(FullLowBounds.fullLowReserve (d+1)+2)))) * ‖f‖) ∧
      (∀ g : LocalL2 Vout (EuclideanSpace ℂ (Fin q)),
        MemRestrictionSobolev U 1 ((localRetardedOperator hU Vout Op).adjoint g) ∧
        restrictionSobolevNorm U 1 ((localRetardedOperator hU Vout Op).adjoint g) ≤
          (D * A 1 * (1 + retardedCoefficientProfile KQ Q B
            (1+(FullLowBounds.fullLowReserve (d+1)+2)))) * ‖g‖) := by
  obtain ⟨D, hD, hlocal⟩ := exists_localRetarded_restrictionH1_constant d q
  refine ⟨D, hD, ?_⟩
  intro KQ Q B Δ a Ψ W χout χsource β hs A₀ A Op hOp U Vout hU hVout
  simpa only [one_mul] using hlocal Op (FullLowBounds.fullLowReserve (d+1)+2) 1 A
    (retardedCoefficientProfile KQ Q B) (by simpa only [one_mul] using hOp.2.2.2.1)
    U Vout hU hVout

end JanetCartan.RegularSector.Characteristic.UniformEvolution
