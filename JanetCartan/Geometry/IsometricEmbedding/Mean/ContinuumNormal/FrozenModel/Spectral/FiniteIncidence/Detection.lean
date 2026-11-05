module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FiniteIncidence.LocalData
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence.Detection

/-!
# Detection for every root family at one smaller tolerance

Unlike a second invocation of the root constructor, this result applies to the
same roots selected for the conic inverse and positive weights. It is consumed
by the finite frozen incidence construction
(`app:ch_seed:eq:seed-actual-detection`, `app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase

/-- Choose the root-error and primitive frame thresholds before the frame,
and prove full image-plus-detector detection at physical zero for every SAME
constructed root family at a smaller tolerance. The carrier comparison is
produced from the retained Hamilton family, not assumed
(`app:ch_seed:eq:seed-actual-detection`). -/
theorem exists_same_root_frozen_detection_threshold {n : ℕ}
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {R : IncidenceRefinement D} (hR : R.IsValid)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {b : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hb : 0 ≤ b) {c εmax : ℝ} (hc : 0 < c) (hemax : 0 < εmax) :
    ∃ ε₀ δ cdet : ℝ, 0 < ε₀ ∧ ε₀ ≤ εmax ∧ 0 < δ ∧ 0 < cdet ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ Q x i - cubeStress n i) < δ) →
        ∀ (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (T i).family.threshold)
          {s B ε : ℝ}, 0 < s → ε ≤ ε₀ →
        ∀ g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
            Euclidean n × Euclidean n → ℝ,
          IsConstructedIncidenceRootFamily D R s c B ε Q
            (fun j a ↦ (T ⟨j, a⟩).carrier ⟨Q, hQ, hlow ⟨j, a⟩⟩) g →
          ∀ j, ∀ k ∈ closedBall (R.center j) (R.radius j), ∀ v : Euclidean n,
            cdet * ‖v‖ ^ 2 ≤ ‖imageChannel (pencil (Q 0) k) v‖ ^ 2 +
              ∑ a, ⟪quadratic (Q 0)
                ((T ⟨R.sourceChart j, a⟩).carrierGradient ⟨Q, hQ, hlow _⟩ 0
                  (incidenceParameter (D.roots (R.sourceChart j) a (R.center j))
                    (g j a (0, k)))), v⟫_ℝ ^ 2 := by
  classical
  obtain ⟨cdet, ddet, hcdet, hddet, hdetect⟩ := exists_refined_frozen_detection_threshold hD hR
  let ε₀ := min εmax (c * ddet / 2)
  have he₀ : 0 < ε₀ := lt_min hemax (by positivity)
  have herr : ε₀ / c < ddet := by
    have he : ε₀ ≤ c * ddet / 2 := min_le_right _ _
    apply (div_lt_iff₀ hc).mpr
    nlinarith
  let J := (j : Fin D.chartCount) × Fin (D.patchCount j)
  choose di hdi hgrad using fun i : J ↦ (T i).exists_carrier_joint_comparison_threshold
    (hD.2.2.2.2.1 i.1 i.2).1 (half_pos hddet)
  obtain ⟨dgrad, hdgrad, hdgradi⟩ := Pi.exists_forall_pos_add_lt hdi
  let d := min dgrad (ddet / 2)
  have hd : 0 < d := lt_min hdgrad (half_pos hddet)
  refine ⟨ε₀, d / 14, cdet, he₀, min_le_left _ _, by positivity, hcdet, ?_⟩
  intro Q hQ hclose hlow s B ε hs hε g hg
  have hreg : ∀ x ∈ closedBall (0 : Euclidean n) b,
      ContDiffAt ℝ 6 (Q - fun _ ↦ cubeStress n) x := fun x hx ↦
    ((hQ.contDiffAt (hU.mem_nhds (hBU hx))).sub contDiffAt_const).of_le (by simp)
  have hglobal : cNorm (closedBall (0 : Euclidean n) b) 6 (Q - fun _ ↦ cubeStress n) < d := by
    apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _) hreg hd
    convert hclose using 1; norm_num
  have hlocal (i : J) : cNorm (closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) < di i := by
    have hi : dgrad < di i := by simpa using hdgradi i
    exact (cNorm_mono_set_of_contDiffAt (hframe i) (isCompact_closedBall _ _) hreg).trans_lt
      ((hglobal.trans_le (min_le_left _ _)).trans hi)
  have hcovector (j) {k : Euclidean n} (hk : k ∈ closedBall (R.center j) (R.radius j)) :
      k ∈ ball (R.center j) (2 * R.radius j) :=
    closedBall_subset_ball (by linarith [hR.1 j]) hk
  intro j k hk v
  apply hdetect j (X := Unit) (fun _ ↦ Q 0)
    (fun _ a ↦ (T ⟨R.sourceChart j, a⟩).carrierGradient ⟨Q, hQ, hlow _⟩ 0)
    (fun _ a k ↦ incidenceParameter (D.roots (R.sourceChart j) a (R.center j))
      (g j a (0, k))) _ _ _ _ () k hk v
  · intro _ a k hk i
    exact ((hg j a).2.2.1 (0, k)
      ⟨by simpa using (show 0 < 3 * s by positivity), hcovector j hk⟩).2.1 i |>.le
  · intro _
    have hv : ‖Q 0 - cubeStress n‖ ≤
        cNorm (closedBall (0 : Euclidean n) b) 6 (Q - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _) hreg
          (mem_closedBall_self hb) (by omega : 0 ≤ 6)
    exact (hv.trans_lt (hglobal.trans_le (min_le_right _ _))).trans (half_lt_self hddet)
  · intro _ a w hw
    exact (hgrad ⟨R.sourceChart j, a⟩ ⟨Q, hQ, hlow _⟩ (hlocal _) 0
      (by simpa using (T ⟨R.sourceChart j, a⟩).physicalRadius_pos) w hw).1.trans_lt
        (half_lt_self hddet)
  · intro _ a k hk
    exact (((hg j a).2.2.1 (0, k)
      ⟨by simpa using (show 0 < 3 * s by positivity), hcovector j hk⟩).2.2.2.2.2.2.1.trans
        (div_le_div_of_nonneg_right hε hc.le)).trans_lt herr

end JanetCartan.ContinuumNormal.FrozenModel
