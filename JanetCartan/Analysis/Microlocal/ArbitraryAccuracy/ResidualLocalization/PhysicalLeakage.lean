module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.SobolevScale
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.FiberMaps
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope
/-!
# Physical plus pairing in the restriction Sobolev scale

The actual branch estimates give Fourier membership and norms. Their physical
`S + conjugate(S)` pairing is transferred to the existing restriction scale
by its proved Fourier comparison and real-linear weak-jet functoriality.
This algebraic step is applied to the primitive elapsed producer in
`GeometricIntegrated`; it is not itself an analytic localization producer.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open LocalSobolev RegularSector.Realization RegularSector.Characteristic.RetardedLocalization
open Pseudodifferential ResponseTransfer RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem starFiber_restrict (U : Set E) (u : H) :
    (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.compLp (restrictL2 U u) =
      restrictL2 U (star u) := by
  apply Lp.ext
  filter_upwards [(starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.coeFn_compLp (restrictL2 U u),
    restrictL2_coeFn U u, restrictL2_coeFn U (star u), ae_restrict_of_ae (Lp.coeFn_star u)]
    with x hx hy hz hu
  rw [hx, hy, hz, hu]
  rfl

private theorem physicalPair_leakage_eq (T Mi Mo : H →L[ℂ] H)
    (hi : ∀ u, Mi (star u) = star (Mi u)) (ho : ∀ u, Mo (star u) = star (Mo u)) (u : H) :
    (1 - Mo) ((T + boundedConjugate T) (Mi u)) =
      (1 - Mo) (T (Mi u)) + star ((1 - Mo) (T (Mi (star u)))) := by
  change (T (Mi u) + star (T (star (Mi u)))) -
    Mo (T (Mi u) + star (T (star (Mi u)))) = _
  simp only [map_add, ho, sub_apply, one_apply_eq_self,
    star_sub, hi]
  abel

/-- The physical plus-paired branch has a restriction Sobolev bound with a
constant depending only on dimension, channel count and order. The actual
factor estimate is produced in `GeometricIntegrated`, and reality of its
localizers is proved from even symbols by `LocalizerReality`. Both physical
masks stay in their original positions. Consumer: physical paired retarded
`hleak` in `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_physicalPair_fourier_restriction_comparison (d q m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (U : Set (Euclidean (d + 1))) (hU : MeasurableSet U)
      (T Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (_hi : ∀ u, Mi (star u) = star (Mi u)) (_ho : ∀ u, Mo (star u) = star (Mo u))
      (B : ℝ),
      (∀ u, MemVectorFourierSobolev (m : ℝ) ((1 - Mo) (T (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) (T (Mi u))) ≤ B * ‖u‖) →
      ∀ u,
        restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u))) ∈
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u)))) ≤ K * B * ‖u‖ := by
  obtain ⟨C, hC, hcompare⟩ := exists_restrictionScale_fourier_comparison (d + 1) q m
  let S := (starL' ℝ : EuclideanSpace ℂ (Fin q) ≃L[ℝ] EuclideanSpace ℂ (Fin q)).toContinuousLinearMap
  refine ⟨(‖S‖ + 2) * C, mul_pos (by positivity) hC, ?_⟩
  intro U hU T Mi Mo hi ho B hbound u
  let G := restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU
  let v := fun u ↦ restrictL2 U ((1 - Mo) (T (Mi u)))
  have hv u : v u ∈ G.level m ∧ G.gradeNorm m (v u) ≤ C * B * ‖u‖ := by
    obtain ⟨hm, hb⟩ := hcompare U hU _ (v u) (hbound u).1 (restrictL2_coeFn U _).symm
    exact ⟨hm, hb.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound u).2 hC.le)⟩
  obtain ⟨hs, hsb⟩ := compLp_restrictionSobolev_bound S (hv (star u)).1
  have he : restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u))) =
      v u + S.compLp (v (star u)) := by
    rw [physicalPair_leakage_eq T Mi Mo hi ho, map_add, ← starFiber_restrict]
  rw [he]
  refine ⟨(G.level m).add_mem (hv u).1 hs, ?_⟩
  have hsb' : G.gradeNorm m (S.compLp (v (star u))) ≤
      (‖S‖ + 1) * G.gradeNorm m (v (star u)) := by
    rw [restrictionSobolevScale_gradeNorm hU hs,
      restrictionSobolevScale_gradeNorm hU (hv (star u)).1]
    exact hsb
  apply (gradeNorm_add_le G (hv u).1 hs).trans
  have hb := hsb'.trans (mul_le_mul_of_nonneg_left (hv (star u)).2 (by positivity))
  rw [norm_star] at hb
  calc
    G.gradeNorm m (v u) + G.gradeNorm m (S.compLp (v (star u))) ≤
      C * B * ‖u‖ + (‖S‖ + 1) * (C * B * ‖u‖) := add_le_add (hv u).2 hb
    _ = ((‖S‖ + 2) * C) * B * ‖u‖ := by ring

/-- The actual real compression of the same physical pair has the same
fixed losses. This uses the existing real-part/inclusion fiber maps and
weak-extension norms, rather than a substitute real Sobolev scale. Consumer:
the real paired elapsed endpoint in `GeometricIntegrated`
(`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_realPhysicalPair_fourier_restriction_comparison (d q m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (U : Set (Euclidean (d + 1))) (hU : MeasurableSet U)
      (T Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (_hi : ∀ u, Mi (star u) = star (Mi u)) (_ho : ∀ u, Mo (star u) = star (Mo u))
      (B : ℝ), 0 ≤ B →
      (∀ u, MemVectorFourierSobolev (m : ℝ) ((1 - Mo) (T (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) (T (Mi u))) ≤ B * ‖u‖) →
      ∀ u : Lp (EuclideanSpace ℝ (Fin q)) 2 (volume : Measure (Euclidean (d + 1))),
        let v := l2RealPart (volume.restrict U)
          (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi (l2ComplexInclusion volume u)))))
        v ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m v ≤ K * B * ‖u‖ := by
  obtain ⟨C, hC, hcompare⟩ := exists_physicalPair_fourier_restriction_comparison d q m
  let R := euclideanRealPart (ι := Fin q)
  refine ⟨(‖R‖ + 1) * C, mul_pos (by positivity) hC, ?_⟩
  intro U hU T Mi Mo hi ho B hB hbound u v
  obtain ⟨hm, hb⟩ := hcompare U hU T Mi Mo hi ho B hbound (l2ComplexInclusion volume u)
  obtain ⟨hr, hrb⟩ := compLp_restrictionSobolev_bound R hm
  refine ⟨hr, ?_⟩
  change (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m
    (R.compLp _) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU hr]
  apply hrb.trans
  rw [← restrictionSobolevScale_gradeNorm hU hm]
  have hu : ‖l2ComplexInclusion volume u‖ ≤ ‖u‖ := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    exact (mul_le_mul_of_nonneg_right (l2ComplexInclusion_norm_le volume) (norm_nonneg u)).trans_eq (one_mul _)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hu (mul_nonneg hC.le hB))
  convert mul_le_mul_of_nonneg_left hb' (show 0 ≤ ‖R‖ + 1 by positivity) using 1; ring


end JanetCartan.ArbitraryAccuracy.ResidualLocalization
