module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Positive

/-!
# Physical plus pairing with the actual measured masks

Conjugation preserves every real mask in its original position. On the genuine
restriction spaces, the literal physical pair retains the additive tame profile.
Consumers: `sector-theorem-residual`, `measured-adjoint`, `finite-gap-theorem`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev Pseudodifferential FourierIntegral.LowBounds Realization
open Characteristic.RetardedLocalization ArbitraryAccuracy.ResidualLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem star_compLp_eq {μ : Measure E} (u : Lp F 2 μ) :
    (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.compLp u = star u := by
  apply Lp.ext
  filter_upwards [(starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.coeFn_compLp u,
    Lp.coeFn_star u] with y hy hz
  exact hy.trans hz.symm

private theorem star_zeroExtend {U : Set E} (hU : MeasurableSet U) (u : LocalL2 U F) :
    star (SmallSupport.zeroExtend hU u) = SmallSupport.zeroExtend hU (star u) := by
  simpa only [star_compLp_eq] using
    compLp_zeroExtend (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap hU u

private theorem star_restrictL2 (U : Set E) (u : H) :
    restrictL2 U (star u) = star (restrictL2 U u) := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn U (star u), Lp.coeFn_star (restrictL2 U u),
    ae_restrict_of_ae (Lp.coeFn_star u), restrictL2_coeFn U u] with y hy hz hu hv
  rw [hy, hz, hu]
  simp only [Pi.star_apply, hv]

private theorem star_sourceCutMultiplier
    (χ : E → ℝ) (hχ : Continuous χ) (hb : ∀ y, ‖χ y‖ ≤ 1) (u : H) :
    star (sourceCutMultiplier χ hχ hb u) = sourceCutMultiplier χ hχ hb (star u) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (sourceCutMultiplier χ hχ hb u),
    sourceCutMultiplier_coeFn χ hχ hb u,
    sourceCutMultiplier_coeFn χ hχ hb (star u), Lp.coeFn_star u] with y hy hm hn hu
  simp only [Pi.star_apply] at hy hu
  rw [hy, hm, hn, hu]
  simp only [star_smul, Complex.star_def, Complex.conj_ofReal]

/-- Real masks retain their literal left and right positions under physical
conjugation (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem boundedConjugate_measuredOperator
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) (T : H →L[ℂ] H) :
    boundedConjugate (measuredOperator χout χin ho hi hob hib T) =
      measuredOperator χout χin ho hi hob hib (boundedConjugate T) := by
  ext1 u
  change star (sourceCutMultiplier χout ho hob (T (sourceCutMultiplier χin hi hib (star u)))) =
    sourceCutMultiplier χout ho hob (star (T (star (sourceCutMultiplier χin hi hib u))))
  rw [star_sourceCutMultiplier, star_sourceCutMultiplier]

/-- The physical `S+cSc` of a measured factor is literally the same masks
around the physical pair of T (`measured-adjoint`). -/
theorem physicalPair_measuredOperator
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) (T : H →L[ℂ] H) :
    physicalPairedSectorSum {()} (fun _ : Unit ↦ measuredOperator χout χin ho hi hob hib T) =
      measuredOperator χout χin ho hi hob hib
        (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) := by
  simp only [physicalPairedSectorSum, Finset.sum_singleton, boundedConjugate_measuredOperator]
  ext1 u
  exact (map_add (sourceCutMultiplier χout ho hob) _ _).symm

/-- Physical pairing commutes with the literal local conjugation, including
zero extension (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem localRetardedOperator_physicalPair_apply
    {U : Set E} (hU : MeasurableSet U) (V : Set E) (T : H →L[ℂ] H) (u : LocalL2 U F) :
    localRetardedOperator hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u =
      localRetardedOperator hU V T u + star (localRetardedOperator hU V T (star u)) := by
  simp only [physicalPairedSectorSum, Finset.sum_singleton]
  change restrictL2 V (T (SmallSupport.zeroExtend hU u) +
    star (T (star (SmallSupport.zeroExtend hU u)))) = _
  rw [map_add, star_zeroExtend, star_restrictL2]
  rfl

private theorem star_restriction_bound {U : Set E} {s : ℕ} {u : LocalL2 U F}
    (hu : MemRestrictionSobolev U s u) :
    MemRestrictionSobolev U s (star u) ∧
      restrictionSobolevNorm U s (star u) ≤ 2*restrictionSobolevNorm U s u := by
  let C := (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap
  have hC : ‖C‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖star v‖ ≤ 1*‖v‖
    simp only [norm_star, one_mul, le_refl]
  obtain ⟨hm, hn⟩ := compLp_restrictionSobolev_bound C hu
  rw [show C.compLp u = star u from star_compLp_eq u] at hm hn
  exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right (by linarith) restrictionSobolevNorm_nonneg)⟩

/-- The literal complex physical plus pair retains the additive tame estimate.
The factor five is fixed before T, orders and coefficients; no higher norm
is multiplied by `high` (`sector-theorem-residual`). -/
theorem local_physicalPair_restriction_tame_bound
    {U V : Set E} (hU : MeasurableSet U) (T : H →L[ℂ] H) (a b : ℕ)
    (A high : ℝ) (hA : 0 ≤ A) (hh : 0 ≤ high)
    (hT : ∀ u : LocalL2 U F, MemRestrictionSobolev U a u →
      MemRestrictionSobolev V b (localRetardedOperator hU V T u) ∧
        restrictionSobolevNorm V b (localRetardedOperator hU V T u) ≤
          A*(restrictionSobolevNorm U a u+high*‖u‖))
    (u : LocalL2 U F) (hu : MemRestrictionSobolev U a u) :
    MemRestrictionSobolev V b
      (localRetardedOperator hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ∧
    restrictionSobolevNorm V b
      (localRetardedOperator hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ≤
      (5*A)*(restrictionSobolevNorm U a u+high*‖u‖) := by
  obtain ⟨hm, hn⟩ := hT u hu
  obtain ⟨hi, hni⟩ := star_restriction_bound hu
  obtain ⟨hc, hnc⟩ := hT (star u) hi
  obtain ⟨ho, hno⟩ := star_restriction_bound hc
  have hnc' : restrictionSobolevNorm V b (localRetardedOperator hU V T (star u)) ≤
      A*(2*restrictionSobolevNorm U a u+high*‖u‖) := by
    rw [norm_star] at hnc
    exact hnc.trans (mul_le_mul_of_nonneg_left (add_le_add hni le_rfl) hA)
  rw [localRetardedOperator_physicalPair_apply]
  refine ⟨hm.add ho, (restrictionSobolevNorm_add_le hm ho).trans ?_⟩
  have hb := add_le_add hn (hno.trans (mul_le_mul_of_nonneg_left hnc' (by norm_num)))
  apply hb.trans
  nlinarith [mul_nonneg hA (mul_nonneg hh (norm_nonneg u))]

/-- The physical pair and its literal adjoint retain the same additive profile
on exchanged domains (`measured-adjoint`, `sector-theorem-residual`). -/
theorem local_physicalPair_restriction_tame_bounds
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H) (a b : ℕ) (A high : ℝ) (hA : 0 ≤ A) (hh : 0 ≤ high)
    (hf : ∀ u : LocalL2 U F, MemRestrictionSobolev U a u →
      MemRestrictionSobolev V b (localRetardedOperator hU V T u) ∧
        restrictionSobolevNorm V b (localRetardedOperator hU V T u) ≤
          A*(restrictionSobolevNorm U a u+high*‖u‖))
    (ha : ∀ v : LocalL2 V F, MemRestrictionSobolev V a v →
      MemRestrictionSobolev U b ((localRetardedOperator hU V T).adjoint v) ∧
        restrictionSobolevNorm U b ((localRetardedOperator hU V T).adjoint v) ≤
          A*(restrictionSobolevNorm V a v+high*‖v‖)) :
    let P := localRetardedOperator hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T))
    (∀ u : LocalL2 U F, MemRestrictionSobolev U a u →
      MemRestrictionSobolev V b (P u) ∧ restrictionSobolevNorm V b (P u) ≤
        (5*A)*(restrictionSobolevNorm U a u+high*‖u‖)) ∧
    (∀ v : LocalL2 V F, MemRestrictionSobolev V a v →
      MemRestrictionSobolev U b (P.adjoint v) ∧ restrictionSobolevNorm U b (P.adjoint v) ≤
        (5*A)*(restrictionSobolevNorm V a v+high*‖v‖)) := by
  refine ⟨local_physicalPair_restriction_tame_bound hU T a b A high hA hh hf, ?_⟩
  intro v hv
  rw [localRetardedOperator_adjoint hU hV, physicalPairedSectorSum_adjoint_eq]
  apply local_physicalPair_restriction_tame_bound hV T.adjoint a b A high hA hh _ v hv
  simpa only [localRetardedOperator_adjoint hU hV] using ha

/-- The physical measured pair has its actual supported zero extension,
with the same outer mask (`negative-duality`). -/
theorem zeroExtend_local_physical_measuredOperator
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hs : tsupport χout ⊆ V) (T : H →L[ℂ] H) (u : LocalL2 U F) :
    let P := physicalPairedSectorSum {()}
      (fun _ : Unit ↦ measuredOperator χout χin ho hi hob hib T)
    SmallSupport.zeroExtend hV (localRetardedOperator hU V P u) =
      P (SmallSupport.zeroExtend hU u) := by
  dsimp only
  rw [physicalPair_measuredOperator]
  exact zeroExtend_local_measuredOperator hU hV χout χin ho hi hob hib hs _ u

/-- The adjoint physical measured output is supported in the original source
domain, with masks in the literal reverse product (`measured-adjoint`). -/
theorem zeroExtend_local_physical_measuredOperator_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hs : tsupport χin ⊆ U) (T : H →L[ℂ] H) (v : LocalL2 V F) :
    let P := physicalPairedSectorSum {()}
      (fun _ : Unit ↦ measuredOperator χout χin ho hi hob hib T)
    SmallSupport.zeroExtend hU ((localRetardedOperator hU V P).adjoint v) =
      P.adjoint (SmallSupport.zeroExtend hV v) := by
  dsimp only
  rw [physicalPair_measuredOperator]
  exact zeroExtend_local_measuredOperator_adjoint hU hV χout χin ho hi hob hib hs _ v

private theorem zeroExtend_realCompression_of_supported
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H)
    (hT : ∀ u : LocalL2 U F,
      SmallSupport.zeroExtend hV (localRetardedOperator hU V T u) =
        T (SmallSupport.zeroExtend hU u)) (u : LocalL2 U (EuclideanSpace ℝ (Fin q))) :
    SmallSupport.zeroExtend hV (localRealCompression hU V T u) =
      realCompression T (SmallSupport.zeroExtend hU u) := by
  have ho := compLp_zeroExtend (euclideanRealPart (ι := Fin q)) hV
    (localRetardedOperator hU V T (l2ComplexInclusion (volume.restrict U) u))
  have hi := compLp_zeroExtend (euclideanComplexInclusion (ι := Fin q)) hU u
  change l2RealPart volume
      (SmallSupport.zeroExtend hV (localRetardedOperator hU V T
        (l2ComplexInclusion (volume.restrict U) u))) =
    SmallSupport.zeroExtend hV (localRealCompression hU V T u) at ho
  change l2ComplexInclusion volume (SmallSupport.zeroExtend hU u) =
    SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) at hi
  rw [← ho, hT, ← hi]
  rfl

/-- The real physical measured output equals the restriction of its actual
whole-space real compression, with exact zero extension (`negative-duality`). -/
theorem zeroExtend_real_physical_measuredOperator
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hs : tsupport χout ⊆ V) (T : H →L[ℂ] H)
    (u : LocalL2 U (EuclideanSpace ℝ (Fin q))) :
    let P := physicalPairedSectorSum {()}
      (fun _ : Unit ↦ measuredOperator χout χin ho hi hob hib T)
    SmallSupport.zeroExtend hV (localRealCompression hU V P u) =
      realCompression P (SmallSupport.zeroExtend hU u) :=
  zeroExtend_realCompression_of_supported hU hV _
    (zeroExtend_local_physical_measuredOperator hU hV χout χin ho hi hob hib hs T) u

/-- The real compressed adjoint has the exchanged supported zero-extension
identity (`measured-adjoint`, `negative-duality`). -/
theorem zeroExtend_real_physical_measuredOperator_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hs : tsupport χin ⊆ U) (T : H →L[ℂ] H)
    (v : LocalL2 V (EuclideanSpace ℝ (Fin q))) :
    let P := physicalPairedSectorSum {()}
      (fun _ : Unit ↦ measuredOperator χout χin ho hi hob hib T)
    SmallSupport.zeroExtend hU ((localRealCompression hU V P).adjoint v) =
      realCompression P.adjoint (SmallSupport.zeroExtend hV v) := by
  intro P
  rw [localRealCompression_adjoint hU hV]
  apply zeroExtend_realCompression_of_supported hV hU P.adjoint _ v
  intro u
  rw [← localRetardedOperator_adjoint hU hV]
  exact zeroExtend_local_physical_measuredOperator_adjoint hU hV χout χin ho hi hob hib hs T u

end JanetCartan.RegularSector.FiniteAssembly
