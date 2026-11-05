module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Restriction

/-!
# Transport of genuine restriction bounds from the selected chart

The chart domain for a physical set `U` is exactly `physicalCoordinates i ⁻¹' U`.
The existing weak-extension/Fourier comparisons and CoordinateSobolev's exact
Fourier invariance transfer bounds between these domains. The comparison
constant precedes the coordinate index, domain, operator and accuracy. No new
Sobolev scale or zero-extension regularity assumption is introduced.
Consumer: the restriction output of `ResidualLocalization.CompleteFactor` in
the selected finite factors (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open LocalSobolev Pseudodifferential ResidualLocalization
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization RegularSector.FiniteEvolution
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q
local notation "F" => EuclideanSpace ℂ (Fin q)

private theorem physicalPullback_symm_restriction_congr
    (i : Fin (d + 1)) (U : Set E) (hU : MeasurableSet U) {u v : H}
    (h : (u : E → F) =ᵐ[volume.restrict (physicalCoordinates i ⁻¹' U)] v) :
    ((physicalPullbackL2 i).symm u : E → F) =ᵐ[volume.restrict U]
      (physicalPullbackL2 i).symm v := by
  have hmp : MeasurePreserving (physicalCoordinates i).symm volume volume :=
    (measurePreserving_physicalCoordinates i).symm
      (physicalCoordinates i).toHomeomorph.toMeasurableEquiv
  have hc := hmp.quasiMeasurePreserving.ae
    ((ae_restrict_iff' (hU.preimage (physicalCoordinates i).continuous.measurable)).mp h)
  apply (ae_restrict_iff' hU).mpr
  filter_upwards [hc, physicalPullbackL2_symm_coeFn i u,
    physicalPullbackL2_symm_coeFn i v] with x hx hu hv
  intro hxU
  exact hu.trans ((hx (by simpa only [mem_preimage,
    ContinuousLinearEquiv.apply_symm_apply] using hxU)).trans hv.symm)

/-- Transfer restriction regularity from the correctly transformed chart
domain. Only the proved Fourier/restriction comparison constants occur, uniformly
over every selected coordinate (`app:ch_regular:eq:chain-tail`). -/
theorem exists_physicalPullback_restriction_transport_constant (d q m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin (d + 1)) (U : Set (Euclidean (d + 1)))
      (_hU : MeasurableSet U) (u : SpacetimeL2 d q),
      MemRestrictionSobolev (physicalCoordinates i ⁻¹' U) m
        (restrictL2 (physicalCoordinates i ⁻¹' U) u) →
      MemRestrictionSobolev U m (restrictL2 U ((physicalPullbackL2 i).symm u)) ∧
      restrictionSobolevNorm U m (restrictL2 U ((physicalPullbackL2 i).symm u)) ≤
        D * restrictionSobolevNorm (physicalCoordinates i ⁻¹' U) m
          (restrictL2 (physicalCoordinates i ⁻¹' U) u) := by
  obtain ⟨A, hA, hfourier⟩ := exists_vector_extension_fourier_constant (d + 1) q m
  obtain ⟨B, hB, hrestrict⟩ := vector_restrictionSobolev_nat_bounds (d + 1) q m
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro i U hU u hu
  have hext (e : SobolevExtension (physicalCoordinates i ⁻¹' U) m
      (restrictL2 (physicalCoordinates i ⁻¹' U) u)) :
      MemRestrictionSobolev U m (restrictL2 U ((physicalPullbackL2 i).symm u)) ∧
      restrictionSobolevNorm U m (restrictL2 U ((physicalPullbackL2 i).symm u)) ≤
        (B * A) * e.jetNorm := by
    obtain ⟨hm, hn⟩ := hfourier _ _ e
    have heL2 : (e.toL2 : Euclidean (d + 1) → EuclideanSpace ℂ (Fin q))
        =ᵐ[volume.restrict (physicalCoordinates i ⁻¹' U)] e.toFun :=
      ae_restrict_of_ae e.toL2_coeFn
    have he : (e.toL2 : Euclidean (d + 1) → EuclideanSpace ℂ (Fin q))
        =ᵐ[volume.restrict (physicalCoordinates i ⁻¹' U)] u :=
      heL2.trans (e.restrict_eq.trans (restrictL2_coeFn _ u))
    have hphysical := physicalPullback_symm_restriction_congr i U hU he
    obtain ⟨hmem, hnorm⟩ := hrestrict ((physicalPullbackL2 i).symm e.toL2)
      ((memVectorFourierSobolev_physicalPullbackL2_symm i m e.toL2).mpr hm) U
      (restrictL2 U ((physicalPullbackL2 i).symm u))
      (hphysical.trans (restrictL2_coeFn U _).symm)
    refine ⟨hmem, hnorm.trans ?_⟩
    rw [vectorFourierSobolevNorm_physicalPullbackL2_symm]
    exact (mul_le_mul_of_nonneg_left hn hB.le).trans_eq (mul_assoc _ _ _).symm
  refine ⟨(hext hu.some).1, ?_⟩
  rw [mul_comm (B * A)]
  apply (div_le_iff₀ (mul_pos hB hA)).mp
  apply le_csInf
  · exact ⟨hu.some.jetNorm, hu.some, rfl⟩
  · rintro _ ⟨e, rfl⟩
    exact (div_le_iff₀ (mul_pos hB hA)).mpr
      ((hext e).2.trans_eq (mul_comm _ _))

/-- A chart restriction estimate transports with one dimension/order constant.
The hypothesis is the actual per-chart output of `CompleteFactor`; the physical
domain pulls back by the SAME selected permutation (`app:ch_regular:eq:chain-tail`). -/
theorem exists_physicalOperator_restriction_transport_constant (d q m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin (d + 1))
      (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (U : Set (Euclidean (d + 1))) (_hU : MeasurableSet U) (C : ℝ),
      (∀ u, MemRestrictionSobolev (physicalCoordinates i ⁻¹' U) m
        (restrictL2 (physicalCoordinates i ⁻¹' U) (T u)) ∧
        restrictionSobolevNorm (physicalCoordinates i ⁻¹' U) m
          (restrictL2 (physicalCoordinates i ⁻¹' U) (T u)) ≤ C * ‖u‖) →
      ∀ u, MemRestrictionSobolev U m (restrictL2 U (physicalOperator i T u)) ∧
        restrictionSobolevNorm U m (restrictL2 U (physicalOperator i T u)) ≤
          (D * C) * ‖u‖ := by
  obtain ⟨D, hD, htransport⟩ := exists_physicalPullback_restriction_transport_constant d q m
  refine ⟨D, hD, ?_⟩
  intro i T U hU C hT u
  obtain ⟨hm, hn⟩ := hT (physicalPullbackL2 i u)
  obtain ⟨hmem, hnorm⟩ := htransport i U hU (T (physicalPullbackL2 i u)) hm
  refine ⟨hmem, hnorm.trans ?_⟩
  simpa only [LinearIsometryEquiv.norm_map, mul_assoc] using
    mul_le_mul_of_nonneg_left hn hD.le

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
