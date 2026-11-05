module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood.JetComparison

/-!
# Primitive stress differences at a fixed positive reference

For `paper-v2.tex`, `app:ch_background:prop:bg-frame` and
`app:ch_osc:prop:osc-normal`, Step 4'. The consumer is the comparison of the
SAME retained Hamilton charts in `FamilyInputs.PositiveReference`.

The whole projected-stress array, in its actual finite-product norm, depends
continuously on the immersion with loss two. The compact second-jet range is
derived from the stipulated low bound and the separate metric and normal gaps.
This is a primitive geometric estimate, not continuity of an output family.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ProjectedStressFrame CurrentGeometricNeighborhood
open HamiltonPhase.CompositionContinuity

/-- The full actual projected frame is continuous at any fixed admissible
immersion in every finite norm, with input order `m + 2`. The tolerance is
chosen before the varying immersion. The low bound and the two gaps supply
the common compact range; no stress comparison is assumed. Consumed by the
Hamilton symbol comparison for `app:ch_background:prop:bg-frame` and
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_projectedStress_sub_tolerance {n N : ℕ}
    {K U : Set (Euclidean n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F₀ : Euclidean n → Euclidean N} (hF₀ : ContDiffOn ℝ ∞ F₀ U)
    (hi₀ : IsImmersionOn F₀ U) {C₀ κmet κnormal : ℝ}
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm K 4 F₀ ≤ C₀)
    (hmet₀ : ∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ K, ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean N,
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U →
      cNorm K 4 F ≤ C₀ →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm K (m + 2) (F - F₀) < δ →
      cNorm K m (projectedStress F - projectedStress F₀) < ε := by
  let L := admissibleStressJets n N (2 * C₀) κmet (max 1 (κnormal ^ 2)⁻¹)
  let a : StressJet n N → Fin n → MetricTensor n :=
    fun J i ↦ jetStress (cubeStress n i) J
  have hL : IsCompact L := isCompact_admissibleStressJets _ hκmet _
  have ha : ∀ J ∈ L, ContDiffAt ℝ m a J := by
    intro J hJ
    apply contDiffAt_pi.mpr
    intro i
    exact (contDiffAt_jetStress (isUnit_jetMetric_of_lower_bound hκmet hJ.2.1)
      (isUnit_jetAmbient_of_lower_bound hJ.2.2) _).of_le (by simp)
  have hjet₀ : ∀ x ∈ K, ContDiffAt ℝ m (stressJet F₀) x :=
    fun x hx ↦ ((contDiffOn_stressJet hU hF₀).contDiffAt
      (hU.mem_nhds (hKU hx))).of_le (by simp)
  have hrange₀ : MapsTo (stressJet F₀) K L := by
    intro x hx
    exact stressJet_mem_admissibleStressJets hK
      (fun y hy ↦ hF₀.contDiffAt (hU.mem_nhds (hKU hy))) hκnormal hlow₀ hx
      (hi₀ x (hKU hx)) (hmet₀ x hx) (hnormal₀ x hx)
  obtain ⟨d, hd, hcomp⟩ := exists_cNorm_comp_sub_lt hK hL ha hjet₀ hrange₀ hε
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro F hF hi hlow hmet hnormal hsmall
  have hrange : MapsTo (stressJet F) K L := by
    intro x hx
    exact stressJet_mem_admissibleStressJets hK
      (fun y hy ↦ hF.contDiffAt (hU.mem_nhds (hKU hy))) hκnormal hlow hx
      (hi x (hKU hx)) (hmet x hx) (hnormal x hx)
  have hdiff : cNorm K m (stressJet F - stressJet F₀) < d := by
    have hb := cNorm_stressJet_sub_le hK hU hKU hF hF₀ m
    linarith
  have hc := hcomp a (stressJet F) ha
    (fun x hx ↦ ((contDiffOn_stressJet hU hF).contDiffAt
      (hU.mem_nhds (hKU hx))).of_le (by simp)) hrange
    (by simpa only [sub_self, cNorm_zero] using hd) hdiff
  have heq : cNorm K m (a ∘ stressJet F - a ∘ stressJet F₀) =
      cNorm K m (projectedStress F - projectedStress F₀) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro x hx
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    funext i
    exact congrArg₂ (· - ·)
      (jetStress_stressJet ((hF.contDiffAt (hU.mem_nhds hy)).of_le (by simp))
        (hi y hy) i)
      (jetStress_stressJet ((hF₀.contDiffAt (hU.mem_nhds hy)).of_le (by simp))
        (hi₀ y hy) i)
  rwa [heq] at hc

/-- Primitive immersion closeness preserves the fixed reference's strict frame
margin while making the full frame difference small at the requested order.
This supplies the admissible projected-frame inputs of the SAME Hamilton and
positive-null-transport constructions. The finite input order and tolerance
precede `F`; `η` may be the transport constructor's threshold or the retained
Hamilton family's threshold. Source: `app:ch_background:prop:bg-frame` and
`app:ch_seed:rem:seed-map-topology`. -/
theorem exists_admissible_projectedStress_sub_tolerance {n N : ℕ}
    {K U : Set (Euclidean n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F₀ : Euclidean n → Euclidean N} (hF₀ : ContDiffOn ℝ ∞ F₀ U)
    (hi₀ : IsImmersionOn F₀ U) (hrank₀ : HasFullNormalRankOn F₀ U)
    {C₀ κmet κnormal η : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm K 4 F₀ ≤ C₀)
    (hmet₀ : ∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ K, ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    (hmargin : cNorm K 6 (projectedStress F₀ - fun _ ↦ cubeStress n) < η)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean N,
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K 4 F ≤ C₀ →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm K (max 8 (m + 2)) (F - F₀) < δ →
      cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η ∧
      cNorm K m (projectedStress F - projectedStress F₀) < ε := by
  obtain ⟨d, hd, hdiff⟩ := exists_projectedStress_sub_tolerance hK hU hKU hF₀ hi₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ m hε
  obtain ⟨d₆, hd₆, hdiff₆⟩ := exists_projectedStress_sub_tolerance hK hU hKU hF₀ hi₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ 6 (sub_pos.mpr hmargin)
  refine ⟨min d d₆, lt_min hd hd₆, ?_⟩
  intro F hF hi hrank hlow hmet hnormal hsmall
  have hm := hdiff F hF hi hlow hmet hnormal
    ((cNorm_mono_order (le_max_right _ _)).trans_lt
      (hsmall.trans_le (min_le_left _ _)))
  have h₆ := hdiff₆ F hF hi hlow hmet hnormal
    ((cNorm_mono_order (le_max_left 8 (m + 2))).trans_lt
      (hsmall.trans_le (min_le_right _ _)))
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hQ₀ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF₀ hi₀ hrank₀)
  have htri := cNorm_add_le_of_contDiffAt hK (r := 6)
    (f := projectedStress F - projectedStress F₀)
    (g := projectedStress F₀ - fun _ ↦ cubeStress n)
    (fun x hx ↦ ((hQ.sub hQ₀).contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
    (fun x hx ↦ ((hQ₀.sub contDiffOn_const).contDiffAt
      (hU.mem_nhds (hKU hx))).of_le (by simp))
  rw [sub_add_sub_cancel] at htri
  exact ⟨by linarith, hm⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
