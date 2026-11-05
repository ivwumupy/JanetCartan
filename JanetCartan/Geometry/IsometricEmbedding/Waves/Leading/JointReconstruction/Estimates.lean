module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.Estimates.Range

/-!
# Uniform joint estimates for the actual canonical reconstruction

The reconstruction deduction in `app:ch_waves:eq:joint-tame` uses a fixed
compact range of physical second jets and fixed joint `C¹` covector bounds.
The same actual principal normal, reconstruction and principal matrix obey a
sum of single high norms, with respective input losses two, one and zero.
Constants precede the varying open chart domains and fields. The parent
geometric construction must supply the physical compact range from its
primitive low bounds and separate metric and normal gaps.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.LeadingWave.JointReconstruction

set_option maxSynthPendingDepth 5

open GeometricProfile AmbientResponse

/-- The joint reconstruction deduction for `app:ch_waves:eq:joint-tame`.
The compact physical second-jet range is an explicit conditional input;
`jointJetRange` supplies the remaining compact factors from the fixed `C¹`
bounds. The actual output fields use the same canonical normal completion
and physical covector slices. No global smoothness or output bound is assumed. -/
theorem exists_cNorm_joint_reconstruction_le_of_compact_range
    {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {T : Set (SecondJet (Euclidean n) (Euclidean N))} (hT : IsCompact T)
    (hTi : ∀ J ∈ T, Function.Injective J.1)
    (hTr : ∀ J ∈ T, Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N))) (M : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (Euclidean n)) (V : Set Z), IsOpen U → IsOpen V →
      Metric.closedBall a.1 ρ ⊆ U → Metric.closedBall a.2 ρ ⊆ V →
      ∀ (F : Euclidean n → Euclidean N) (b ξ : Euclidean n × Z → Euclidean n),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞ b (U ×ˢ V) → ContDiffOn ℝ ∞ ξ (U ×ˢ V) →
      MapsTo (secondJet F) (Metric.closedBall a.1 ρ) T →
      cNorm (Metric.closedBall a ρ) 1 b ≤ M → cNorm (Metric.closedBall a ρ) 1 ξ ≤ M →
      cNorm (Metric.closedBall a ρ) r
          (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) +
        cNorm (Metric.closedBall a ρ) r
          (fun p ↦ reconstruction F (canonicalNormalCompletion F) (fun y ↦ b (y, p.2)) p.1) +
        cNorm (Metric.closedBall a ρ) r
          (fun p ↦ principalMatrix
            (principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) (ξ p)) ≤
        C * (1 + cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
          cNorm (Metric.closedBall a ρ) (r + 1) b + cNorm (Metric.closedBall a ρ) r ξ) := by
  have ht := isCompact_jointJetRange hT M
  have hi (q : JointJet n N) (hq : q ∈ jointJetRange T M) := hTi q.1.1 hq.1.1
  have hr (q : JointJet n N) (hq : q ∈ jointJetRange T M) := hTr q.1.1 hq.1.1
  obtain ⟨Cn, hCn, hnormal⟩ :=
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ ht (le_refl r)
      (fun q hq ↦ (contDiffAt_principalNormalValue (hi q hq) (hr q hq)).of_le (by simp))
  obtain ⟨Cv, hCv, hreconstruction⟩ :=
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ ht (le_refl r)
      (fun q hq ↦ (contDiffAt_reconstructionValue (hi q hq) (hr q hq)).of_le (by simp))
  obtain ⟨Cm, hCm, hmatrix⟩ :=
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ ht (le_refl r)
      (fun q hq ↦ (contDiffAt_principalMatrixValue (hi q hq) (hr q hq)).of_le (by simp))
  refine ⟨(Cn + Cv + Cm) * (r + 1), by positivity, ?_⟩
  intro U V hU hV hKU hKV F b ξ hF hFi hFr hb hξ hFT hbM hξM
  have hKUV : Metric.closedBall a ρ ⊆ U ×ˢ V := by
    rw [← closedBall_prod_same a.1 a.2 ρ]
    exact Set.prod_mono hKU hKV
  have hjt := mapsTo_jointJet_range a ρ hFT
    (fun p hp ↦ (hb.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp))
    (fun p hp ↦ (hξ.contDiffAt ((hU.prod hV).mem_nhds (hKUV hp))).of_le (by simp)) hbM hξM
  have hj := contDiffOn_jointJet hU hV hF hb hξ
  have hn := hnormal (U ×ˢ V) (hU.prod hV) hKUV (jointJet F b ξ) hj hjt
  have hv := hreconstruction (U ×ˢ V) (hU.prod hV) hKUV (jointJet F b ξ) hj hjt
  have hm := hmatrix (U ×ˢ V) (hU.prod hV) hKUV (jointJet F b ξ) hj hjt
  have hen := GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun p hp ↦ (jointJet_fields_eventuallyEq ξ hU hV hF hb hFi hFr (hKUV hp)).1) r
  have hev := GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun p hp ↦ (jointJet_fields_eventuallyEq ξ hU hV hF hb hFi hFr (hKUV hp)).2.1) r
  have hem := GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun p hp ↦ (jointJet_fields_eventuallyEq ξ hU hV hF hb hFi hFr (hKUV hp)).2.2) r
  rw [hen] at hn
  change cNorm (Metric.closedBall a ρ) r
    (fun p ↦ reconstructionJetValue (jointJet F b ξ p).1) ≤ _ at hv
  rw [hev] at hv
  rw [hem] at hm
  have hsum := add_le_add (add_le_add hn hv) hm
  have hjet := cNorm_jointJet_le a ρ hU hV hKU hKV hF hb hξ r
  have hhigh : 1 + cNorm (Metric.closedBall a ρ) r (jointJet F b ξ) ≤
      (r + 1 : ℝ) * (1 + cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
        cNorm (Metric.closedBall a ρ) (r + 1) b + cNorm (Metric.closedBall a ρ) r ξ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  calc
    _ ≤ (Cn + Cv + Cm) * (1 + cNorm (Metric.closedBall a ρ) r (jointJet F b ξ)) := by
      simpa only [add_mul] using hsum
    _ ≤ (Cn + Cv + Cm) * ((r + 1 : ℝ) *
        (1 + cNorm (Metric.closedBall a.1 ρ) (r + 2) F +
          cNorm (Metric.closedBall a ρ) (r + 1) b + cNorm (Metric.closedBall a ρ) r ξ)) :=
      mul_le_mul_of_nonneg_left hhigh (by positivity)
    _ = _ := by ring

end JanetCartan.LeadingWave.JointReconstruction
