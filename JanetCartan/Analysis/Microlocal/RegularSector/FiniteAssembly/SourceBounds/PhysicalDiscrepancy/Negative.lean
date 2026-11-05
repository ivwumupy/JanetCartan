module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.PhysicalDiscrepancy

/-!
# Signed measured bounds for the same physical angular discrepancy

The actual order-zero restriction estimates supply dual bounds on the original
supported/restriction pairs. The identity is subtracted once after pairing.
Neither orientation is assigned the analytic residual's gain-one endpoint.
Consumers: the retained complete physical error in `FixedDomainInverse` and
`app:ch_regular:eq:chain-tail`; source: `measured-adjoint`, `negative-duality`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds Pseudodifferential
open LocalSobolev Realization ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

/-- The literal complex adjoint transfers an order-zero restriction bound
into the corresponding supported pairing (`negative-duality`). -/
private theorem source_complex_order_zero_pairing
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H) (s : ℕ) (C : ℝ)
    (hT : ∀ v : LocalL2 V F, MemRestrictionSobolev V s v →
      MemRestrictionSobolev U s ((localRetardedOperator hU V T).adjoint v) ∧
      restrictionSobolevNorm U s ((localRetardedOperator hU V T).adjoint v) ≤
        C*restrictionSobolevNorm V s v)
    (u : LocalL2 U F) (v : LocalL2 V F) (hv : MemRestrictionSobolev V s v) :
    ‖inner ℂ (localRetardedOperator hU V T u) v‖ ≤
      (((d+1 : ℝ)*scalarLocalDualityConstant (d+1) s)*C)*
        vectorFourierSobolevNorm (-(s : ℝ)) (SmallSupport.zeroExtend hU u)*
          restrictionSobolevNorm V s v := by
  obtain ⟨hm, hn⟩ := hT v hv
  rw [complex_inner_localRetardedOperator_adjoint hU hV]
  have hp := norm_inner_le_vectorNegativeNorm_mul_restrictionSobolevNorm hU s u _ hm
  simp only [Nat.cast_add, Nat.cast_one] at hp
  apply hp.trans
  have hc : 0 ≤ ((d+1 : ℝ)*scalarLocalDualityConstant (d+1) s)*
      vectorFourierSobolevNorm (-(s : ℝ)) (SmallSupport.zeroExtend hU u) :=
    mul_nonneg (mul_nonneg (by positivity) (scalarLocalDualityConstant_pos _ _).le)
      (norm_nonneg _)
  convert mul_le_mul_of_nonneg_left hn hc using 1
  ring

/-- The same real Hilbert adjoint and component Fourier norm supply the
order-zero supported/restriction pairing (`negative-duality`). -/
private theorem source_real_order_zero_pairing
    {U V : Set E} (hU : MeasurableSet U)
    (R : LocalL2 U RF →L[ℝ] LocalL2 V RF) (s : ℕ) (C : ℝ)
    (hR : ∀ v : LocalL2 V RF, MemRestrictionSobolev V s v →
      MemRestrictionSobolev U s (R.adjoint v) ∧
      restrictionSobolevNorm U s (R.adjoint v) ≤ C*restrictionSobolevNorm V s v)
    (u : LocalL2 U RF) (v : LocalL2 V RF) (hv : MemRestrictionSobolev V s v) :
    |inner ℝ (R u) v| ≤
      (localDualityConstant (d+1) s (EuclideanSpace.basisFun (Fin (d+1)) ℝ)*C)*
        componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
          (-(s : ℝ)) (SmallSupport.zeroExtend hU u)*restrictionSobolevNorm V s v := by
  obtain ⟨hm, hn⟩ := hR v hv
  rw [← ContinuousLinearMap.adjoint_inner_right]
  apply (abs_inner_le_negativeNorm_mul_restrictionSobolevNorm
    (EuclideanSpace.basisFun (Fin (d+1)) ℝ) hU s u _ hm).trans
  have hc := mul_nonneg
    (localDualityConstant_pos (d+1) s (EuclideanSpace.basisFun (Fin (d+1)) ℝ)).le
    (componentFourierSobolevNorm_nonneg (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
      (-(s : ℝ)) (SmallSupport.zeroExtend hU u))
  convert mul_le_mul_of_nonneg_left hn hc using 1
  ring

/-- Simultaneous positive and negative measured estimates for the actual
paired angular discrepancy, its literal adjoint and real compression. The
constants come from the fixed finite source producer before domains, varying
coefficients or history. The SAME source, common output, final threshold,
measurement masks and single identity subtraction occur in all eight clauses
(`measured-adjoint`, `negative-duality`, `resolved-angular-tail`). -/
theorem exists_selectedFinitePhysicalSource_measured_discrepancy_signed_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
    let A := (sourceCutMultiplier output ho.continuous hob).comp (selectedFiniteSourcePDO f L)
    let D := physicalPairedSectorSum {()} (fun _ : Unit ↦ A) - 1
    let T := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb D
    ∀ (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V),
      tsupport ν ⊆ U → tsupport μ ⊆ V →
    let J := localRetardedOperator hU V T
    let R := localRealCompression hU V T
    ∀ s,
      (∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
        MemRestrictionSobolev V s (J u) ∧
        restrictionSobolevNorm V s (J u) ≤ C s*restrictionSobolevNorm U s u) ∧
      (∀ v : LocalL2 V F, MemRestrictionSobolev V s v →
        MemRestrictionSobolev U s (J.adjoint v) ∧
        restrictionSobolevNorm U s (J.adjoint v) ≤ C s*restrictionSobolevNorm V s v) ∧
      (∀ u : LocalL2 U RF, MemRestrictionSobolev U s u →
        MemRestrictionSobolev V s (R u) ∧
        restrictionSobolevNorm V s (R u) ≤ (4*C s)*restrictionSobolevNorm U s u) ∧
      (∀ v : LocalL2 V RF, MemRestrictionSobolev V s v →
        MemRestrictionSobolev U s (R.adjoint v) ∧
        restrictionSobolevNorm U s (R.adjoint v) ≤ (4*C s)*restrictionSobolevNorm V s v) ∧
      (∀ (u : LocalL2 U F) (v : LocalL2 V F), MemRestrictionSobolev V s v →
        ‖inner ℂ (J u) v‖ ≤ (((d+1 : ℝ)*scalarLocalDualityConstant (d+1) s)*C s)*
          vectorFourierSobolevNorm (-(s : ℝ)) (SmallSupport.zeroExtend hU u)*
            restrictionSobolevNorm V s v) ∧
      (∀ (v : LocalL2 V F) (u : LocalL2 U F), MemRestrictionSobolev U s u →
        ‖inner ℂ (J.adjoint v) u‖ ≤ (((d+1 : ℝ)*scalarLocalDualityConstant (d+1) s)*C s)*
          vectorFourierSobolevNorm (-(s : ℝ)) (SmallSupport.zeroExtend hV v)*
            restrictionSobolevNorm U s u) ∧
      (∀ (u : LocalL2 U RF) (v : LocalL2 V RF), MemRestrictionSobolev V s v →
        |inner ℝ (R u) v| ≤
          (localDualityConstant (d+1) s (EuclideanSpace.basisFun (Fin (d+1)) ℝ)*(4*C s))*
            componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
              (-(s : ℝ)) (SmallSupport.zeroExtend hU u)*restrictionSobolevNorm V s v) ∧
      (∀ (v : LocalL2 V RF) (u : LocalL2 U RF), MemRestrictionSobolev U s u →
        |inner ℝ (R.adjoint v) u| ≤
          (localDualityConstant (d+1) s (EuclideanSpace.basisFun (Fin (d+1)) ℝ)*(4*C s))*
            componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
              (-(s : ℝ)) (SmallSupport.zeroExtend hV v)*restrictionSobolevNorm U s u) := by
  obtain ⟨C, hC, hbounds⟩ := exists_selectedFinitePhysicalSource_measured_discrepancy_bounds
    f L hL output ho hoc hob μ ν hμ hν hμc hνc hμb hνb
  refine ⟨C, hC, ?_⟩
  intro A D T U V hU hV hνU hμV J R s
  have hp := hbounds U V hU hV hνU hμV s
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, ?_, ?_, ?_, ?_⟩
  · exact source_complex_order_zero_pairing hU hV T s (C s) hp.2.1
  · intro v u hu
    have hh := source_complex_order_zero_pairing hV hU T.adjoint s (C s)
      (by simpa only [J, localRetardedOperator_adjoint hV hU,
        ContinuousLinearMap.adjoint_adjoint] using hp.1) v u hu
    simpa only [J, localRetardedOperator_adjoint hU hV] using hh
  · exact source_real_order_zero_pairing hU R s (4*C s) hp.2.2.2
  · exact source_real_order_zero_pairing hV R.adjoint s (4*C s)
      (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hp.2.2.1)

end JanetCartan.RegularSector.FiniteAssembly
