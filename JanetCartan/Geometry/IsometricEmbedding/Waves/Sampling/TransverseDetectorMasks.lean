module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.TransverseDetectorNormals

/-!
# Carrier masks on the already selected full detector cover

Use the exact labels and local radii returned by the retained analytic
construction. The carrier plateaus and angular covering balls have the same
label throughout; no second finite subcover is selected. These masks feed
`carrierSubsetWeight` and the finite-copy quantifier of
`exists_actual_retained_joint_sampling_transport_realization`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff Classical

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalConic SeparatedSampling

/-- Retain the actual finite cover chosen after the local analytic radii.
Construct smooth carrier plateaus on those SAME labels and prove coverage
of every nonzero original transverse detector value. The returned weights
have one common sampling cube. Their subset refinement preserves the original
carrier weight and feeds `sum_carrierSubsetWeight_jointSubsetKernel_prefix_normal`
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem exists_transverseDetector_weights_on_retained_cover
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Z : Set (Euclidean 3)) (a : Euclidean (n - 1) → ℂ)
    (ha : ∀ t : ℝ, 0 < t → ∀ η, a (t • η) = a η)
    (r d : transverseDetectorIncidenceSupport T Z a → ℝ)
    (hd : ∀ w, 0 < d w)
    (localWeight : transverseDetectorIncidenceSupport T Z a → Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → localWeight w z = 1)
    (labels : Finset (transverseDetectorIncidenceSupport T Z a))
    (hcover : ∀ w ∈ transverseDetectorIncidenceSupport T Z a, ∃ i : labels,
      w.1 ∈ ball i.1.1.1 (d i.1 / 2) ∧
      normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2) ∈
        ball (normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
          (angularWidth (n := n)
            (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) ∧
      localWeight i.1 w.1.ofLp = 1) :
    ∃ B > (0 : ℝ), ∃ b : labels → Point → ℝ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i) ∧ PatchBounds (b i) B 1) ∧
      (∀ i z, b i z ≠ 0 → localWeight i.1 z = 1) ∧
      ∀ z ∈ Z, ∀ η : Euclidean (n - 1), η ≠ 0 → a η ≠ 0 → ∃ i : labels,
        b i z.ofLp = 1 ∧ normalize η ∈
          ball (normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
            (angularWidth (n := n)
              (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) := by
  classical
  obtain ⟨B, hB, b, hbs, hbc, hbb, hbone, _hbsupp, hbplateau⟩ :=
    exists_joint_cover_carrier_weights (fun i : labels ↦ i.1.1.1)
      (fun i ↦ d i.1) (fun i ↦ hd i.1) (fun i ↦ localWeight i.1) (fun i ↦ hplateau i.1)
  refine ⟨B, hB, b, fun i ↦ ⟨hbs i, hbc i, hbb i⟩, hbplateau, ?_⟩
  intro z hz η hη haη
  have hi : (z, normalize η) ∈ Z ×ˢ detectorDirectionSupport a :=
    ⟨hz, normalize_mem_detectorDirectionSupport a ha hη haη⟩
  rw [← image_transverseDetectorIncidenceSupport T Z a] at hi
  obtain ⟨w, hw, he⟩ := hi
  obtain ⟨i, hz', hdir, _hlocal⟩ := hcover w hw
  have hzeq : w.1 = z := congrArg Prod.fst he
  have hηeq : normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2) =
      normalize η := congrArg Prod.snd he
  rw [hzeq] at hz'
  rw [hηeq] at hdir
  exact ⟨i, hbone i z.ofLp (ball_subset_closedBall hz'), hdir⟩

end JanetCartan.Sampling
