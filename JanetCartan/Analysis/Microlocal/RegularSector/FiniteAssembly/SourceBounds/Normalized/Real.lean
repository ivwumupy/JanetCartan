module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.Normalized.Measured
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Pairing

/-!
# Signed real estimates for the normalized measured source

The actual complete source and its single identity subtraction are compressed
on the original measures. Genuine weak extensions transfer positive estimates;
the literal real adjoint then gives supported/restriction negative pairings.
The constants precede the final radial threshold and both domains.
Consumers: the real fixed response and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open FiniteMasks.ActualFamily NormalizedSolver Characteristic.EvolutionIntegral
open FourierIntegral LowBounds Pseudodifferential LocalSobolev
open Characteristic.RetardedLocalization ArbitraryAccuracy ResponseTransfer Realization
open ArbitraryAccuracy.ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

/-- Real compression subtracts the identity exactly once from the same
normalized characteristic-plus-elliptic source (`sector-theorem-identity`,
`resolved-angular-tail`). -/
theorem normalizedRealSource_sub_identity_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) :
    realSource f hK L output ho hob - 1 =
      realCompression (pairedSource f hK L output ho hob - 1) := by
  ext1 u
  simp [realSource, realCompression, realPart_inclusion]

/-- Weak-extension inclusion and real part preserve the order-zero
restriction estimate (`measured-adjoint`). -/
private theorem normalizedSource_real_restriction_bound
    {U V : Set E} (hU : MeasurableSet U) (T : H →L[ℂ] H)
    (s : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
      MemRestrictionSobolev V s (localRetardedOperator hU V T u) ∧
      restrictionSobolevNorm V s (localRetardedOperator hU V T u) ≤
        C*restrictionSobolevNorm U s u)
    (u : LocalL2 U RF) (hu : MemRestrictionSobolev U s u) :
    MemRestrictionSobolev V s (localRealCompression hU V T u) ∧
    restrictionSobolevNorm V s (localRealCompression hU V T u) ≤
      (4*C)*restrictionSobolevNorm U s u := by
  obtain ⟨hi, hni⟩ := compLp_restrictionSobolev_bound
    (euclideanComplexInclusion (ι := Fin (d+1))) hu
  obtain ⟨ht, hnt⟩ := hT _ hi
  obtain ⟨hr, hnr⟩ := compLp_restrictionSobolev_bound
    (euclideanRealPart (ι := Fin (d+1))) ht
  refine ⟨hr, ?_⟩
  have hi' : restrictionSobolevNorm U s
      (l2ComplexInclusion (volume.restrict U) u) ≤ 2*restrictionSobolevNorm U s u :=
    hni.trans (mul_le_mul_of_nonneg_right
      (by linarith [euclideanComplexInclusion_norm_le (ι := Fin (d+1))])
      restrictionSobolevNorm_nonneg)
  have hr' : restrictionSobolevNorm V s (localRealCompression hU V T u) ≤
      2*restrictionSobolevNorm V s
        (localRetardedOperator hU V T (l2ComplexInclusion (volume.restrict U) u)) :=
    hnr.trans (mul_le_mul_of_nonneg_right
      (by linarith [euclideanRealPart_norm_le (ι := Fin (d+1))])
      restrictionSobolevNorm_nonneg)
  exact hr'.trans ((mul_le_mul_of_nonneg_left
    (hnt.trans (mul_le_mul_of_nonneg_left hi' hC)) (by norm_num)).trans_eq (by ring))

/-- The literal real adjoint transfers the positive bound to the original
supported/restriction pairing (`negative-duality`). -/
private theorem normalizedSource_real_negative_pairing
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

/-- Uniform positive restriction bounds and negative pairings for the
actual normalized real measured discrepancy and its literal adjoint. The same
family, all physical masks and ONE identity subtraction occur in every clause.
No coefficient, terminal decay or operator estimate is assumed
(`negative-duality`, `measured-adjoint`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_normalizedRealSource_measured_discrepancy_signed_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ L : ℝ, f.radialThreshold ≤ L →
      ∀ (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V),
        tsupport ν ⊆ U → tsupport μ ⊆ V →
      let D := pairedSource f hK L output ho.continuous hob - 1
      let R := localRealCompression hU V
        (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb D)
      ∀ s,
        (∀ u : LocalL2 U RF, MemRestrictionSobolev U s u →
          MemRestrictionSobolev V s (R u) ∧
          restrictionSobolevNorm V s (R u) ≤ C s*restrictionSobolevNorm U s u) ∧
        (∀ v : LocalL2 V RF, MemRestrictionSobolev V s v →
          MemRestrictionSobolev U s (R.adjoint v) ∧
          restrictionSobolevNorm U s (R.adjoint v) ≤ C s*restrictionSobolevNorm V s v) ∧
        (∀ (u : LocalL2 U RF) (v : LocalL2 V RF), MemRestrictionSobolev V s v →
          |inner ℝ (R u) v| ≤
            (localDualityConstant (d+1) s (EuclideanSpace.basisFun (Fin (d+1)) ℝ)*C s)*
              componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
                (-(s : ℝ)) (SmallSupport.zeroExtend hU u)*restrictionSobolevNorm V s v) ∧
        (∀ (v : LocalL2 V RF) (u : LocalL2 U RF), MemRestrictionSobolev U s u →
          |inner ℝ (R.adjoint v) u| ≤
            (localDualityConstant (d+1) s (EuclideanSpace.basisFun (Fin (d+1)) ℝ)*C s)*
              componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
                (-(s : ℝ)) (SmallSupport.zeroExtend hV v)*restrictionSobolevNorm U s u) := by
  obtain ⟨A, hA, hb⟩ := exists_normalizedSource_measured_discrepancy_constants
    f hK output ho hoc hob μ ν hμ hν hμc hνc hμb hνb
  refine ⟨fun s ↦ 4*A s, fun s ↦ mul_nonneg (by norm_num) (hA s), ?_⟩
  intro L hL U V hU hV hνU hμV D R s
  let T := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb D
  have hf := normalizedSource_real_restriction_bound hU T s (hA s)
    (hb L hL U V hU hV hνU hμV s).1
  have ha : ∀ v : LocalL2 V RF, MemRestrictionSobolev V s v →
      MemRestrictionSobolev U s (R.adjoint v) ∧
        restrictionSobolevNorm U s (R.adjoint v) ≤ (4*A s)*restrictionSobolevNorm V s v := by
    intro v hv
    rw [show R = localRealCompression hU V T from rfl, localRealCompression_adjoint hU hV]
    exact normalizedSource_real_restriction_bound hV T.adjoint s (hA s)
      (by simpa only [localRetardedOperator_adjoint hU hV] using
        (hb L hL U V hU hV hνU hμV s).2) v hv
  exact ⟨hf, ha, normalizedSource_real_negative_pairing hU R s (4*A s) ha,
    normalizedSource_real_negative_pairing hV R.adjoint s (4*A s)
      (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hf)⟩

end JanetCartan.RegularSector.FiniteAssembly
