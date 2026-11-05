module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Physical
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Pairing

/-!
# Physical measured estimates from the finite constructor's exact signature

These deductions use the same T throughout. The parent supplies the selected
finite direct residual and its existing positive Fourier estimates. In its
application `high s` is exactly
`1+cNorm K (s-1+sectorLowOrder d) Q+cNorm K (s-1+sectorLowOrder d) B`.
No analytic premise beyond that constructor output is introduced here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev Pseudodifferential ArbitraryAccuracy Realization
open Characteristic.RetardedLocalization ArbitraryAccuracy.ResidualLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Both orientations of the literal physical pair and its real compression
satisfy the measured additive positive profile, including `s=0` and the
`L² → H¹` endpoint. All constants precede the operator, coefficient quantities,
domains and inputs (`sector-theorem-residual`, `finite-gap-theorem`). -/
theorem exists_measuredOperator_physical_positive_constants
    (χout χin : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χin)
    (hoc : HasCompactSupport χout) (hic : HasCompactSupport χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) :
    ∃ D : ℕ → ℝ, (∀ s, 1 ≤ D s) ∧
      ∀ (T : H →L[ℂ] H) (cost high : ℕ → ℝ),
      (∀ s, 0 ≤ cost s) → (∀ s, 0 ≤ high s) →
      (∀ s, ∀ W : H →L[ℂ] H, (W = T ∨ W = T.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤
            cost s*(vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u+high s*‖u‖)) →
      ∀ (U V : Set E) (hU : MeasurableSet U) (_hV : MeasurableSet V),
      tsupport χin ⊆ U → tsupport χout ⊆ V →
      let S := measuredOperator χout χin ho.continuous hi.continuous hob hib T
      let P := localRetardedOperator hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ S))
      let R := localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ S))
      ∀ s,
      (∀ u : LocalL2 U F, MemRestrictionSobolev U (s-1) u →
        MemRestrictionSobolev V s (P u) ∧ restrictionSobolevNorm V s (P u) ≤
          (5*(D s*cost s))*(restrictionSobolevNorm U (s-1) u+high s*‖u‖)) ∧
      (∀ v : LocalL2 V F, MemRestrictionSobolev V (s-1) v →
        MemRestrictionSobolev U s (P.adjoint v) ∧ restrictionSobolevNorm U s (P.adjoint v) ≤
          (5*(D s*cost s))*(restrictionSobolevNorm V (s-1) v+high s*‖v‖)) ∧
      (∀ u : LocalL2 U RF, MemRestrictionSobolev U (s-1) u →
        MemRestrictionSobolev V s (R u) ∧ restrictionSobolevNorm V s (R u) ≤
          (8*(D s*cost s))*(restrictionSobolevNorm U (s-1) u+high s*‖u‖)) ∧
      (∀ v : LocalL2 V RF, MemRestrictionSobolev V (s-1) v →
        MemRestrictionSobolev U s (R.adjoint v) ∧ restrictionSobolevNorm U s (R.adjoint v) ≤
          (8*(D s*cost s))*(restrictionSobolevNorm V (s-1) v+high s*‖v‖)) := by
  obtain ⟨D, hD, hpos⟩ := exists_measuredOperator_paired_restriction_constants (q := q)
    χout χin ho hi hoc hic hob hib
  refine ⟨D, hD, ?_⟩
  intro T cost high hc hh hT U V hU hV hsi hso S P R s
  specialize hpos T cost high
  specialize hpos hc hh
  specialize hpos hT
  specialize hpos U V hU hV hsi hso s
  obtain ⟨hf, ha⟩ := hpos
  have hA := mul_nonneg (zero_le_one.trans (hD s)) (hc s)
  have hp := local_physicalPair_restriction_tame_bounds hU hV S (s-1) s
    (D s*cost s) (high s) hA (hh s) hf ha
  have hr := localRealCompression_physicalPair_restriction_tame_bounds hU hV S (s-1) s
    (D s*cost s) (high s) hA (hh s) hf ha
  exact ⟨hp.1, hp.2, hr.1, hr.2⟩

/-- The physical measured pair and real compression both have the original
supported/restriction negative pairings and `H⁻¹ → L²` endpoints, in both literal
orientations. The analytic premise is exactly the finite direct constructor's
positive Fourier output, never a requested negative estimate or support field.
Sources: `negative-duality`, `finite-gap-theorem`, `measured-adjoint`. -/
theorem exists_measuredOperator_physical_negative_constants
    (χout χin : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χin)
    (hoc : HasCompactSupport χout) (hic : HasCompactSupport χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) :
    ∃ Dc Dr : ℕ → ℝ, (∀ k, 0 ≤ Dc k) ∧ (∀ k, 0 ≤ Dr k) ∧
      ∀ (T : H →L[ℂ] H) (cost high : ℕ → ℝ),
      (∀ s, 0 ≤ cost s) → (∀ s, 0 ≤ high s) →
      (∀ s, ∀ W : H →L[ℂ] H, (W = T ∨ W = T.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤
            cost s*(vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u+high s*‖u‖)) →
      ∀ (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V),
      tsupport χin ⊆ U → tsupport χout ⊆ V →
      let S := measuredOperator χout χin ho.continuous hi.continuous hob hib T
      let P := localRetardedOperator hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ S))
      let R := localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ S))
      (∀ k (u : LocalL2 U F) (v : LocalL2 V F), MemRestrictionSobolev V k v →
        ‖inner ℂ (P u) v‖ ≤ (Dc k*cost (k+1)*(1+high (k+1)))*
          vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u)*
            restrictionSobolevNorm V k v) ∧
      (∀ k (v : LocalL2 V F) (u : LocalL2 U F), MemRestrictionSobolev U k u →
        ‖inner ℂ (P.adjoint v) u‖ ≤ (Dc k*cost (k+1)*(1+high (k+1)))*
          vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hV v)*
            restrictionSobolevNorm U k u) ∧
      (∀ k (u : LocalL2 U RF) (v : LocalL2 V RF), MemRestrictionSobolev V k v →
        |inner ℝ (R u) v| ≤ (Dr k*cost (k+1)*(1+high (k+1)))*
          componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ)
            (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u)*restrictionSobolevNorm V k v) ∧
      (∀ k (v : LocalL2 V RF) (u : LocalL2 U RF), MemRestrictionSobolev U k u →
        |inner ℝ (R.adjoint v) u| ≤ (Dr k*cost (k+1)*(1+high (k+1)))*
          componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ)
            (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hV v)*restrictionSobolevNorm U k u) ∧
      (∀ u : LocalL2 U F, ‖P u‖ ≤ (Dc 0*cost 1*(1+high 1))*
        vectorFourierSobolevNorm (-1) (SmallSupport.zeroExtend hU u)) ∧
      (∀ v : LocalL2 V F, ‖P.adjoint v‖ ≤ (Dc 0*cost 1*(1+high 1))*
        vectorFourierSobolevNorm (-1) (SmallSupport.zeroExtend hV v)) ∧
      (∀ u : LocalL2 U RF, ‖R u‖ ≤ (Dr 0*cost 1*(1+high 1))*
        componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ) (-1)
          (SmallSupport.zeroExtend hU u)) ∧
      (∀ v : LocalL2 V RF, ‖R.adjoint v‖ ≤ (Dr 0*cost 1*(1+high 1))*
        componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ) (-1)
          (SmallSupport.zeroExtend hV v)) := by
  obtain ⟨D, hD, hpos⟩ := exists_measuredOperator_physical_positive_constants (q := q)
    χout χin ho hi hoc hic hob hib
  let Dc k := ((q : ℝ)*scalarLocalDualityConstant (d+1) (k+1))*(5*D (k+1))
  let Dr k := localDualityConstant (d+1) (k+1) (EuclideanSpace.basisFun (Fin q) ℝ)*(8*D (k+1))
  have hDc k : 0 ≤ Dc k := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg q) (scalarLocalDualityConstant_pos _ _).le)
    (mul_nonneg (by norm_num) (zero_le_one.trans (hD _)))
  have hDr k : 0 ≤ Dr k := mul_nonneg (localDualityConstant_pos _ _ _).le
    (mul_nonneg (by norm_num) (zero_le_one.trans (hD _)))
  refine ⟨Dc, Dr, hDc, hDr, ?_⟩
  intro T cost high hc hh hT U V hU hV hsi hso S P R
  let Q := physicalPairedSectorSum {()} (fun _ : Unit ↦ S)
  specialize hpos T cost high
  specialize hpos hc hh
  specialize hpos hT
  specialize hpos U V hU hV hsi hso
  have hp s := hpos s
  have hAc s : 0 ≤ 5*(D s*cost s) := mul_nonneg (by norm_num)
    (mul_nonneg (zero_le_one.trans (hD s)) (hc s))
  have hAr s : 0 ≤ 8*(D s*cost s) := mul_nonneg (by norm_num)
    (mul_nonneg (zero_le_one.trans (hD s)) (hc s))
  have hpf k := (hp (k+1)).1
  have hpa k := (hp (k+1)).2.1
  have hrf k := (hp (k+1)).2.2.1
  have hra k := (hp (k+1)).2.2.2
  simp only [Nat.add_sub_cancel] at hpf hpa hrf hra
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k u v hv
    simpa only [Dc, mul_assoc] using local_complex_negative_pairing_of_restriction_adjoint
      hU hV Q k (5*(D (k+1)*cost (k+1))) (high (k+1)) (hAc _) (hh _) (hpa k) u v hv
  · intro k v u hu
    have hf : ∀ u : LocalL2 U F, MemRestrictionSobolev U k u →
        MemRestrictionSobolev V (k+1) ((localRetardedOperator hV U Q.adjoint).adjoint u) ∧
        restrictionSobolevNorm V (k+1) ((localRetardedOperator hV U Q.adjoint).adjoint u) ≤
          (5*(D (k+1)*cost (k+1)))*(restrictionSobolevNorm U k u+high (k+1)*‖u‖) := by
      simpa only [localRetardedOperator_adjoint hV hU, ContinuousLinearMap.adjoint_adjoint] using hpf k
    have hn := local_complex_negative_pairing_of_restriction_adjoint hV hU Q.adjoint k
      (5*(D (k+1)*cost (k+1))) (high (k+1)) (hAc _) (hh _) hf v u hu
    simpa only [P, Q, localRetardedOperator_adjoint hU hV, Dc, mul_assoc] using hn
  · intro k u v hv
    simpa only [Dr, mul_assoc] using local_real_negative_pairing_of_restriction_adjoint
      hU R k (8*(D (k+1)*cost (k+1))) (high (k+1)) (hAr _) (hh _) (hra k) u v hv
  · intro k v u hu
    simpa only [Dr, mul_assoc] using local_real_negative_pairing_of_restriction_adjoint
      hV R.adjoint k (8*(D (k+1)*cost (k+1))) (high (k+1)) (hAr _) (hh _)
      (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hrf k) v u hu
  · intro u
    simpa only [Dc, Nat.zero_add, mul_assoc] using local_complex_negative_one_to_L2_of_restriction_adjoint
      hU hV Q (5*(D 1*cost 1)) (high 1) (hAc _) (hh _) (hpa 0) u
  · intro v
    have hf : ∀ u : LocalL2 U F, MemRestrictionSobolev U 0 u →
        MemRestrictionSobolev V 1 ((localRetardedOperator hV U Q.adjoint).adjoint u) ∧
        restrictionSobolevNorm V 1 ((localRetardedOperator hV U Q.adjoint).adjoint u) ≤
          (5*(D 1*cost 1))*(restrictionSobolevNorm U 0 u+high 1*‖u‖) := by
      simpa only [localRetardedOperator_adjoint hV hU, ContinuousLinearMap.adjoint_adjoint] using hpf 0
    have hn := local_complex_negative_one_to_L2_of_restriction_adjoint hV hU Q.adjoint
      (5*(D 1*cost 1)) (high 1) (hAc _) (hh _) hf v
    simpa only [P, Q, localRetardedOperator_adjoint hU hV, Dc, Nat.zero_add, mul_assoc] using hn
  · intro u
    simpa only [Dr, Nat.zero_add, mul_assoc] using local_real_negative_one_to_L2_of_restriction_adjoint
      hU hV R (8*(D 1*cost 1)) (high 1) (hAr _) (hh _) (hra 0) u
  · intro v
    simpa only [Dr, Nat.zero_add, mul_assoc] using local_real_negative_one_to_L2_of_restriction_adjoint
      hV hU R.adjoint (8*(D 1*cost 1)) (high 1) (hAr _) (hh _)
      (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hrf 0) v

end JanetCartan.RegularSector.FiniteAssembly
