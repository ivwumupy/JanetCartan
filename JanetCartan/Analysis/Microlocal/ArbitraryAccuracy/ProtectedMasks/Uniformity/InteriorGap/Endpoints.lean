module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.InteriorGap.Residuals

/-!
# Correction to the original zero-energy segment

For the interior branch of `app:ch_regular:lem:finite-chain`, change only
the temporal covectors of the exact elapsed graph. The root state, the
whole root trajectory, the physical buffer and the original elapsed time
are unchanged. The consumer is the uniform interior mask gap.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open EvolutionIntegratedLocalization EvolutionLocalization FiniteChain.Graph

variable {d : ℕ}

/-- Changing the suspension energy costs at most the change in energy,
independently of the root (`app:ch_regular:lem:finite-chain`).
Consumer: the two zero-energy endpoint corrections. -/
theorem dist_rootSuspensionState_energy_le (h : RootState (Euclidean d) → ℝ)
    (v : RootState (Euclidean d)) (a b : ℝ) :
    dist (rootSuspensionState h a v) (rootSuspensionState h b v) ≤ |a - b| := by
  calc
    _ = ‖timeSpacePoint (a - b) (0 : Euclidean d)‖ := by
      simp [rootSuspensionState, dist_eq_norm, timeSpacePoint_sub]
    _ ≤ |a - b| := by simpa using norm_timeSpacePoint_le (a - b) (0 : Euclidean d)

private theorem restore_source_energy (h : RootState (Euclidean d) → ℝ)
    (a : Euclidean (d + 1) × Euclidean (d + 1)) :
    rootSuspensionState h (rootSuspension h a) (spacetimeRootState a) = a := by
  simp [rootSuspensionState, rootSuspension, spacetimeRootState, timeSpacePoint_coordinates]

/-- The localized endpoints are within three full derivative norms of the
same exact zero-energy flow endpoints, for either orientation
(`app:ch_regular:eq:joint-stationary`). No Lipschitz estimate for a varying
coefficient or flow is required. Consumer: `exists_nearby_maskedZeroEnergyRelation`. -/
theorem dist_zeroEnergy_endpoints_le_jointElapsedPhase_fderiv
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) (x y : Euclidean (d + 1)) (r : ℝ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    let v := spacetimeRootState (elapsedInputBase C r p.1.1 p.2.1, p.2.1)
    let G := ‖fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p)‖
    dist (originalSource backward (y, p.2.2.1) (x, p.2.2.2))
      (rootSuspensionState h 0 v) ≤ 3 * G ∧
    dist (originalTarget backward (y, p.2.2.1) (x, p.2.2.2))
      (rootSuspensionState h 0 (Φ (v, r))) ≤ 3 * G := by
  let a := (elapsedInputBase C r p.1.1 p.2.1, p.2.1)
  let b := (p.1.1, elapsedOutputCovector h Φ C r p.1.1 p.2.1)
  let G := ‖fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p)‖
  have hG : 0 ≤ G := norm_nonneg _
  have he : |rootSuspension h a| ≤ G :=
    abs_source_energy_le_jointElapsedPhase_fderiv backward x y r p hphase
  have ha : dist a (rootSuspensionState h 0 (spacetimeRootState a)) ≤ G := by
    calc
      _ = dist (rootSuspensionState h (rootSuspension h a) (spacetimeRootState a))
          (rootSuspensionState h 0 (spacetimeRootState a)) := by rw [restore_source_energy]
      _ ≤ |rootSuspension h a - 0| := dist_rootSuspensionState_energy_le _ _ _ _
      _ ≤ G := by simpa using he
  have hb : dist b (rootSuspensionState h 0 (Φ (spacetimeRootState a, r))) ≤ G := by
    have hf := (forwardRelation_elapsedChartPhase_flow hC hq hclock hphase
      ((forwardRelation_elapsedChartPhase_iff hphase).mpr ⟨rfl, rfl⟩)).1
    change b = rootSuspensionState h (rootSuspension h a) (Φ (spacetimeRootState a, r)) at hf
    rw [hf]
    exact (dist_rootSuspensionState_energy_le _ _ _ _).trans (by simpa using he)
  suffices hs : dist (originalSource backward (y, p.2.2.1) (x, p.2.2.2)) a ≤ 2 * G ∧
      dist (originalTarget backward (y, p.2.2.1) (x, p.2.2.2)) b ≤ 2 * G by
    constructor
    · exact (dist_triangle _ a _).trans ((add_le_add hs.1 ha).trans (by ring_nf; rfl))
    · exact (dist_triangle _ b _).trans ((add_le_add hs.2 hb).trans (by ring_nf; rfl))
  cases backward
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := forward_elapsed_residual_bounds x y r p hphase
    change dist (y, p.2.2.1) a ≤ 2 * G ∧ dist (x, p.2.2.2) b ≤ 2 * G
    have hbase : ‖y - elapsedInputBase C r p.1.1 p.2.1‖ ≤ 2 * G := by
      rw [norm_sub_rev]
      have ht := norm_sub_le_norm_sub_add_norm_sub (elapsedInputBase C r p.1.1 p.2.1) p.1.2 y
      linarith
    simp only [a, b, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, max_le_iff]
    refine ⟨⟨hbase, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith
    · linarith
    · rw [norm_sub_rev]
      linarith
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := reverse_elapsed_residual_bounds x y r p hphase
    change dist (x, p.2.2.2) a ≤ 2 * G ∧ dist (y, p.2.2.1) b ≤ 2 * G
    have hbase : ‖x - elapsedInputBase C r p.1.1 p.2.1‖ ≤ 2 * G := by
      have ht := norm_sub_le_norm_sub_add_norm_sub x p.1.2 (elapsedInputBase C r p.1.1 p.2.1)
      linarith
    simp only [a, b, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, max_le_iff]
    refine ⟨⟨hbase, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [norm_sub_rev]
      linarith
    · rw [norm_sub_rev]
      linarith
    · linarith

/-- Correct both endpoints to the unit-mask zero-energy relation, preserving
the original whole segment, root buffers, physical buffer and elapsed interval
(`app:ch_regular:lem:finite-chain`). The unit masks enlarge only the proof
relation; the operators' physical amplitude masks are unchanged.
Consumer: the uniform interior mask-margin contradiction. -/
theorem exists_nearby_maskedZeroEnergyRelation
    {e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))} {Δ : ℝ}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) (x y : Euclidean (d + 1)) {r : ℝ} (hr : r ∈ Icc 0 Δ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hsegment : ((elapsedInputBase C r p.1.1 p.2.1, p.2.1), r) ∈
      elapsedSegmentCarrier e h Φ U K W) :
    ∃ a b, maskedZeroEnergyRelation e h Φ U K W (fun _ ↦ 1) (fun _ ↦ 1) Δ backward a b ∧
      dist (y, p.2.2.1) a ≤ 3 * ‖fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p)‖ ∧
      dist (x, p.2.2.2) b ≤ 3 * ‖fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p)‖ := by
  let v := spacetimeRootState (elapsedInputBase C r p.1.1 p.2.1, p.2.1)
  let a := rootSuspensionState h 0 v
  let b := rootSuspensionState h 0 (Φ (v, r))
  have hc : (a, r) ∈ elapsedSegmentCarrier e h Φ U K W := by
    simpa only [elapsedSegmentCarrier, mem_ofPred_eq, a,
      spacetimeRootState_rootSuspensionState, v] using hsegment
  have ha : rootSuspension h a = 0 := rootSuspension_rootSuspensionState _ _ _
  have hb : b = rootSuspensionState h 0 (Φ (spacetimeRootState a, r)) := by simp [a, b]
  have hm : ∀ z : Euclidean (d + 1), z ∈ tsupport (fun _ : Euclidean (d + 1) ↦ (1 : ℂ)) :=
    fun _ ↦ subset_closure one_ne_zero
  have hd := dist_zeroEnergy_endpoints_le_jointElapsedPhase_fderiv hC backward x y r p hq hclock hphase
  cases backward
  · exact ⟨a, b, ⟨r, hr, hc, hm _, hm _, ha, hb⟩, hd⟩
  · exact ⟨b, a, ⟨r, hr, hc, hm _, hm _, ha, hb⟩, hd.2, hd.1⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
