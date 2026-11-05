module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence.Roots
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence.Detection

/-!
# Constructed incidence roots and full detection

Step 3 of `app:ch_seed:prop:seed-actual-menu`, including
`app:ch_seed:eq:seed-actual-detection`, for the SAME canonical carriers of
the supplied quantitative Hamilton family. All low analytic inputs are
discharged from primitive componentwise frame `C⁶` closeness. Higher root jets
and the final reserve-six estimate are separate consequences.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open FrozenMenu CurrentFullPhase

/-- Construct jointly smooth interior incidence roots, with zero spectators,
uniqueness, uniform transversality, root-position and first-derivative bounds,
and the full image-channel detector at those SAME roots and canonical
carriers. The refinement and all positive constants precede the frame,
higher norms and accuracy. Smoothness holds on `ball 0 (3*r)` and detection
on `closedBall 0 (2*r)`; the compact covector buffers contain the smaller
balls covering the sphere (`app:ch_seed:prop:seed-actual-menu`, Step 3;
`app:ch_seed:eq:seed-actual-detection`). -/
theorem exists_constructed_incidence_detection {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {b r : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hr : 0 < r) (hradius : ∀ i, 3 * r < (T i).physicalRadius) (hrb : 3 * r < b) :
    ∃ R : IncidenceRefinement D, R.IsValid ∧ ∃ η c B ε cdet δ : ℝ,
      0 < η ∧ 0 < c ∧ 0 < B ∧ 0 < ε ∧ 0 < cdet ∧ 0 < δ ∧
      (∀ j a, ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a), ∀ i : Fin 3,
        |incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) t i| + η <
          (D.patches (R.sourceChart j) a).radius) ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
        (∀ j, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ Q x j - cubeStress n j) < δ) →
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) <
              (T i).family.threshold,
        ∃ g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
            Euclidean n × Euclidean n → ℝ,
          IsConstructedIncidenceRootFamily D R r c B ε Q
            (fun j a ↦ (T ⟨j, a⟩).carrier ⟨Q, hQ, hlow ⟨j, a⟩⟩) g ∧
          ∀ j, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
          ∀ k ∈ closedBall (R.center j) (R.radius j), ∀ s : Euclidean n,
            cdet * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (Q x) k) s‖ ^ 2 +
              ∑ a, ⟪quadratic (Q x)
                ((T ⟨R.sourceChart j, a⟩).carrierGradient
                  ⟨Q, hQ, hlow ⟨R.sourceChart j, a⟩⟩ x
                  (incidenceParameter (D.roots (R.sourceChart j) a (R.center j))
                    (g j a (x, k)))), s⟫_ℝ ^ 2 := by
  classical
  obtain ⟨R, hR, η, c, B, εmax, hη, hc, hB, hemax, hbuffer, hroots⟩ :=
    exists_constructed_incidence_roots hD T hBU hframe hradius hrb
  obtain ⟨cdet, ddet, hcdet, hddet, hdetect⟩ := exists_refined_frozen_detection_threshold hD hR
  let ε := min εmax (c * ddet / 2)
  have hε : 0 < ε := lt_min hemax (by positivity)
  have hεmax : ε ≤ εmax := min_le_left _ _
  have hrooterror : ε / c < ddet := by
    have hh : ε ≤ c * ddet / 2 := min_le_right _ _
    apply (div_lt_iff₀ hc).mpr
    nlinarith
  obtain ⟨droot, hdroot, hconstruct⟩ := hroots ε hε hεmax
  let J := (j : Fin D.chartCount) × Fin (D.patchCount j)
  choose di hdi hgrad using fun i : J ↦ (T i).exists_carrier_joint_comparison_threshold
    (hD.2.2.2.2.1 i.1 i.2).1 (half_pos hddet)
  obtain ⟨dgrad, hdgrad, hdgradi⟩ := Pi.exists_forall_pos_add_lt hdi
  let d := min dgrad (ddet / 2)
  have hd : 0 < d := lt_min hdgrad (half_pos hddet)
  let δ := min droot (d / 14)
  have hδ : 0 < δ := lt_min hdroot (by positivity)
  refine ⟨R, hR, η, c, B, ε, cdet, δ, hη, hc, hB, hε, hcdet, hδ, hbuffer, ?_⟩
  intro Q hQ hclose
  obtain ⟨hlow, g, hg⟩ := hconstruct Q hQ (fun j ↦ (hclose j).trans_le (min_le_left _ _))
  have hreg : ∀ x ∈ closedBall (0 : Euclidean n) b,
      ContDiffAt ℝ 6 (Q - fun _ ↦ cubeStress n) x := fun x hx ↦
    ((hQ.contDiffAt (hU.mem_nhds (hBU hx))).sub contDiffAt_const).of_le (by simp)
  have hglobal : cNorm (closedBall (0 : Euclidean n) b) 6 (Q - fun _ ↦ cubeStress n) < d := by
    apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _) hreg hd
    intro j
    convert (hclose j).trans_le (min_le_right droot (d / 14)) using 1; norm_num
  have hlocal (i : J) : cNorm (closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) < di i := by
    have hi : dgrad < di i := by simpa using hdgradi i
    exact (cNorm_mono_set_of_contDiffAt (hframe i) (isCompact_closedBall _ _) hreg).trans_lt
      ((hglobal.trans_le (min_le_left _ _)).trans hi)
  have hphysical {x : Euclidean n} (hx : x ∈ closedBall (0 : Euclidean n) (2 * r)) :
      x ∈ ball (0 : Euclidean n) (3 * r) := closedBall_subset_ball (by linarith) hx
  have hcovector (j) {k : Euclidean n} (hk : k ∈ closedBall (R.center j) (R.radius j)) :
      k ∈ ball (R.center j) (2 * R.radius j) := closedBall_subset_ball (by linarith [hR.1 j]) hk
  refine ⟨hlow, g, hg, ?_⟩
  intro j x hx k hk s
  let X := {x : Euclidean n // x ∈ closedBall (0 : Euclidean n) (2 * r)}
  apply hdetect j (X := X) (fun x ↦ Q x.1)
    (fun x a ↦ (T ⟨R.sourceChart j, a⟩).carrierGradient ⟨Q, hQ, hlow _⟩ x.1)
    (fun x a k ↦ incidenceParameter (D.roots (R.sourceChart j) a (R.center j))
      (g j a (x.1, k))) _ _ _ _ ⟨x, hx⟩ k hk s
  · intro x a k hk i
    exact ((hg j a).2.2.1 (x.1, k) ⟨hphysical x.2, hcovector j hk⟩).2.1 i |>.le
  · intro x
    have hxb : x.1 ∈ closedBall (0 : Euclidean n) b :=
      ball_subset_closedBall (ball_subset_ball hrb.le (hphysical x.2))
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      hreg hxb (by omega : 0 ≤ 6)
    have hv : ‖Q x.1 - cubeStress n‖ ≤
        cNorm (closedBall (0 : Euclidean n) b) 6 (Q - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hb
    exact (hv.trans_lt (hglobal.trans_le (min_le_right _ _))).trans (half_lt_self hddet)
  · intro x a w hw
    have hh := hgrad ⟨R.sourceChart j, a⟩ ⟨Q, hQ, hlow _⟩ (hlocal _)
      x.1 (ball_subset_ball (hradius _).le (hphysical x.2)) w hw
    exact hh.1.trans_lt (half_lt_self hddet)
  · intro x a k hk
    exact ((hg j a).2.2.1 (x.1, k) ⟨hphysical x.2, hcovector j hk⟩).2.2.2.2.2.2.1.trans_lt
      hrooterror

end JanetCartan.ActualCarriers
