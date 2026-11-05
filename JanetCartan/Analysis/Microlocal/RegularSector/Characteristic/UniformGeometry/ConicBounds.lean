module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveIntegerBounds.MixedJets

/-!
# Uniform conic mixed bounds from the local second phase jet

The constants precede the chart and depend only on a fixed local C² budget.
`UniformGeometry.exists_uniform_fieldRoot_twoTimeHamiltonPhase` produces this
budget from the original coefficient's fixed C³ bound. This closes the temporal
shear input of `EvolutionIntegral.exists_elapsedPhase_mixed_bounds` without
using compactness separately for each coefficient field.

Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformGeometry
open FourierIntegral EvolutionIntegral ConicPhase
variable {d : ℕ}

/-- The raw joint mixed jet of the continued phase is bounded uniformly on
the whole cone by the same local second jet. Homogeneity removes the radius;
the fixed normalization map supplies the remaining constant. Consumer:
`exists_retardedOperator_of_primitive_data`, and the temporal shear bound of
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_conicPhase_mixed_le_local_cNorm
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε) :
    ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
      (fun v : ℝ × ℝ × Euclidean d ↦ curriedPhase ℓ C v.1 v.2.1 v.2.2 ζ)
      (x 0, x 0 - r, spatialPart x)) η‖ ≤
        jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε 1 1) 2 *
          cNorm (closedBall (z.1, z) (2 * ε)) 2 (twoTimePhase C) := by
  let J := bufferedJetSet ℓ z ε 1 1
  let U := budgetCoordinates ⁻¹' domain ℓ C.target
  have hU : IsOpen U := (isOpen_domain ℓ C.open_target).preimage budgetCoordinates.continuous
  have hJU : J ⊆ U := fun p hp ↦
    ⟨(bufferedJetSet_normalizes ℓ hε.le (by norm_num : (0 : ℝ) < 1)).1 p hp,
      hbuffer ((bufferedJetSet_normalizes ℓ hε.le (by norm_num : (0 : ℝ) < 1)).2 hp)⟩
  have hsu : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (curriedPhase ℓ C)) U :=
    contDiffOn_jointPhase_curriedExtend ℓ C.open_target hs
  have hsub : bufferedBase z ε ×ˢ angularCone ℓ z.2.2 ε ⊆ U := by
    intro p hp
    exact ⟨hp.2.1, hbuffer (localPatch_bufferedBase_subset z ε
      ⟨hp.1, ball_subset_ball (by linarith : ε ≤ 2 * ε) hp.2.2⟩)⟩
  let θ := (ℓ η)⁻¹ • η
  have hθ : ℓ θ = 1 := by simp [θ, hη.1.ne']
  have hθD : θ ∈ angularCone ℓ z.2.2 ε := by
    exact smul_mem_angularCone hη (inv_pos.mpr hη.1)
  have hp : (x 0, x 0 - r, spatialPart x) ∈ bufferedBase z ε :=
    elapsed_mem_bufferedBase hε hr hx
  have hpJ : ((x 0, x 0 - r, spatialPart x), θ) ∈ J := by
    refine ⟨?_, ?_⟩
    · simpa only [bufferedBase, mem_ball, Prod.dist_eq, max_lt_iff,
        mem_closedBall, mem_prod] using
        (show dist (x 0) z.1 ≤ 2 * ε ∧ dist (x 0 - r) z.1 ≤ 2 * ε ∧
          dist (spatialPart x) z.2.1 ≤ 2 * ε from by
          have hp' : dist (x 0) z.1 < 2 * ε ∧ dist (x 0 - r) z.1 < 2 * ε ∧
              dist (spatialPart x) z.2.1 < 2 * ε := by
            simpa only [bufferedBase, mem_ball, Prod.dist_eq, max_lt_iff] using hp
          exact ⟨hp'.1.le, hp'.2.1.le, hp'.2.2.le⟩)
    · exact ⟨(1, θ), ⟨⟨le_rfl, le_rfl⟩, ball_subset_closedBall hη.2, hθ⟩, one_smul ℝ θ⟩
  have hm := norm_twoTimePhase_mixed_le_of_normalized_cover (curriedPhase ℓ C)
    (show IsOpen (bufferedBase z ε) from isOpen_ball) (isOpen_angularCone ℓ z.2.2 ε)
    (fun _ ha _ hη ↦ smul_mem_angularCone hη ha) (hsu.mono hsub)
    (fun a ha p _ η _ ↦ extend_smul ℓ (twoTimePhase C) (budgetCoordinates (p, η)) ha)
    (isCompact_bufferedJetSet ℓ z ε 1 1) hU hJU hsu hp
    ⟨ℓ η, hη.1, θ, hθD, hpJ, (smul_inv_smul₀ hη.1.ne' η).symm⟩ (by norm_num : 2 ≤ 2)
  apply hm.trans
  rw [show curriedPhase ℓ C = curriedExtend ℓ (twoTimePhase C) from rfl]
  simpa only [normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C)
    (by norm_num : (0 : ℝ) < 1)] using
    (cNorm_normalizedTwoTimePhase_phase_le ℓ C hs
      (isCompact_bufferedJetSet ℓ z ε 1 1) (isCompact_closedBall _ _) hbuffer
      (bufferedJetSet_normalizes ℓ hε.le (by norm_num : (0 : ℝ) < 1)).1
      (bufferedJetSet_normalizes ℓ hε.le (by norm_num : (0 : ℝ) < 1)).2
      (by norm_num : (0 : ℝ) < 1) 2)

/-- Fixed mixed and Frobenius inverse constants before the chart varies.
The precise low-jet producer is the order-two conclusion of
`exists_uniform_fieldRoot_twoTimeHamiltonPhase`, using its original C³
coefficient input. No coefficient-dependent compactness is used
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_uniform_conic_mixed_bounds (ℓ : Euclidean d →L[ℝ] ℝ)
    (z : RootState (Euclidean d)) {ε : ℝ} (hε : 0 < ε) (N : ℝ) :
    ∃ κ > (0 : ℝ), ∃ B > (0 : ℝ), ∃ L > (0 : ℝ),
      ∀ (h : RootState (Euclidean d) → ℝ)
        (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
        closedBall (z.1, z) (2 * ε) ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
        (∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) →
        cNorm (closedBall (z.1, z) (2 * ε)) 2 (twoTimePhase C) ≤ N →
        (∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε, ∀ η ∈ angularCone ℓ z.2.2 ε,
          ‖fun j : Fin d ↦ partialDeriv
            (elapsedTimeDerivative (curriedPhase ℓ C) r (x 0, spatialPart x)) η j‖ ≤ L) ∧
        ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε,
          ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ angularCone ℓ z.2.2 ε →
          IsUnit (mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det ∧
          κ ≤ |(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det| ∧
          ‖(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ)⁻¹‖ ≤ B := by
  let L := 1 + jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε 1 1) 2 * |N|
  have hL : 0 < L := by
    have := jetBoundConstant_pos ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε 1 1) 2
    dsimp [L]
    positivity
  obtain ⟨κ, hκ, B, hB, hb⟩ := exists_elapsedPhase_mixed_bounds d L
  refine ⟨κ, hκ, B, hB, L, hL, ?_⟩
  intro h Φ C hbuffer hs hdiff hnear hN
  have ht (r) (hr : r ∈ Icc 0 ε) (x) (hx : x ∈ elapsedPhysicalBox z ε)
      (η) (hη : η ∈ angularCone ℓ z.2.2 ε) :
      ‖fun j : Fin d ↦ partialDeriv
        (elapsedTimeDerivative (curriedPhase ℓ C) r (x 0, spatialPart x)) η j‖ ≤ L := by
    have hm := norm_conicPhase_mixed_le_local_cNorm ℓ hε hbuffer hs hr hx hη
    have hpoint (ζ) (hζ : ζ ∈ angularCone ℓ z.2.2 ε) :
        ContDiffAt ℝ ∞ (SymbolBudgets.jointPhase (curriedPhase ℓ C))
          ((x 0, x 0 - r, spatialPart x), ζ) :=
      (contDiffOn_jointPhase_curriedExtend ℓ C.open_target hs).contDiffAt
        (((isOpen_domain ℓ C.open_target).preimage budgetCoordinates.continuous).mem_nhds
          ⟨hζ.1, hbuffer (elapsedPoint_mem_twoTime_buffer hε hr hx hζ.2)⟩)
    apply (norm_elapsedTimeDerivative_row_le (curriedPhase ℓ C) r x η
      (isOpen_angularCone ℓ z.2.2 ε) hη hpoint).trans
    apply hm.trans
    have hjet := (jetBoundConstant_pos ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε 1 1) 2).le
    have hle := mul_le_mul_of_nonneg_left (hN.trans (le_abs_self N)) hjet
    dsimp [L]
    linarith
  exact ⟨ht, hb (curriedPhase ℓ C) ε (elapsedPhysicalBox z ε) (angularCone ℓ z.2.2 ε)
    (isOpen_angularCone ℓ z.2.2 ε)
    (fun _ hr _ hx _ hη ↦ contDiffAt_curriedPhase_elapsed ℓ hε hbuffer hs hr hx hη)
    (fun _ hr _ hx _ hη ↦ norm_mixedPhaseMatrix_phase_sub_one_le ℓ hε hbuffer hs hdiff hnear hr hx hη)
    ht⟩

end JanetCartan.RegularSector.Characteristic.UniformGeometry
