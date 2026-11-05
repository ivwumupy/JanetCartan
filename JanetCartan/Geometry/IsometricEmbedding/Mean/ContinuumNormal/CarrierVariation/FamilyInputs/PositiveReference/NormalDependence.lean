module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.CoefficientDependence
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.NormalField

/-!
# Primitive dependence of the same canonical carrier normal

Consumer: `FamilyInputs.PositiveReference`, for `app:ch_background:prop:bg-frame`
and `app:ch_osc:prop:osc-normal`, Step 4'. The normal is the literal coefficient
of `CanonicalCarrier.coefficientsOfCarrier_data` in
`app:ch_background:eq:bg-full-complex-amplitude`.

The finite formula uses the canonical second-jet inverse, the actual adjugate
column, the retained Hamilton gradient and the literal scalar amplitude. Its
compact jet range follows from the low immersion budget and the separate metric
and normal gaps. The other compact factors follow from reference closeness.
No continuity of the normal or compact containment of varying inputs is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport CoefficientBounds
open ProjectedStressFrame GeometricProfile LeadingWave.JointReconstruction
open ContinuumRow ContinuumRow.CanonicalCarrier
open FullPhaseCharts.InverseEstimates

private abbrev NormalInput (n N : ℕ) := StressJet n N × (Input n × ℝ)

private def normalInputValue {n N : ℕ} (col : Fin n) (p : NormalInput n N) : Euclidean N :=
  p.2.2 • principalNormalValue ((p.1, right col p.2.1, 0), p.2.1.2)

private theorem smoothAt_normalInputValue {n N : ℕ} (col : Fin n)
    {p : NormalInput n N} (hi : Function.Injective p.1.1)
    (hrank : Set.range (secondJetNormalMap p.1) =
      ((LinearMap.range p.1.1.toLinearMap)ᗮ : Set (Euclidean N))) :
    ContDiffAt ℝ ∞ (normalInputValue col) p := by
  unfold normalInputValue
  have hq : ContDiffAt ℝ ∞ (fun q : NormalInput n N ↦
      ((q.1, right col q.2.1, (0 : Euclidean n →L[ℝ] Euclidean n)), q.2.1.2)) p :=
    (contDiffAt_fst.prodMk
      (((smooth_right col).contDiffAt.comp p contDiffAt_snd.fst).prodMk
        contDiffAt_const)).prodMk contDiffAt_snd.fst.snd
  have hn := contDiffAt_principalNormalValue (n := n) (N := N)
    (q := ((p.1, right col p.2.1, 0), p.2.1.2)) hi hrank
  have hs : ContDiffAt ℝ ∞ (fun q : NormalInput n N ↦ q.2.2) p := contDiffAt_snd.snd
  exact hs.smul (ContDiffAt.comp (g := @principalNormalValue n N) p hn hq)

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Finite-order primitive differences control the SAME canonical normal on
any fixed compact physical/carrier domain, in particular
`CoefficientNormCharts.field.carrier`. The threshold precedes all varying
immersions, projected frames, flow maps and initial amplitudes. The exact
orders are `m + 2` for the immersion and `m` for the other three inputs.

The scalar-difference producer is
`NullFlowDependence.exists_cNorm_carrier_transport_sub_lt`; frame differences
come from `exists_projectedStress_sub_tolerance`, and gradient differences
from `HamiltonDependence`. Smoothness of the literal scalar is supplied by
`ActualAmplitude.exists_projected_local_positive_amplitude`, after the fixed
carrier relabeling. The parent must instantiate these
producers for its same retained maps and common buffers. This implication
does not assert the immersion-only theorem.

Source: `app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_normalField_primitive_sub_tolerance
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} {KF : Set (Euclidean n)}
    {L : Set (Euclidean n × CarrierParameter)}
    (hK : IsCompact K) (hKF : IsCompact KF) (hL : IsCompact L)
    (hKFU : KF ⊆ U) (hKU : K ⊆ inputDomain T)
    (hx : MapsTo Prod.fst K KF)
    (hLK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) L K)
    (Q₀ : _) {F₀ : Euclidean n → Euclidean N}
    (_hQ₀ : Q₀.1 = projectedStress F₀)
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (hrank₀ : HasFullNormalRankOn F₀ U)
    {M κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm KF 4 F₀ ≤ M)
    (hmet₀ : ∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ KF, ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    (row col : Fin n)
    (Φ₀ Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial₀ : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hα₀ : ∀ p ∈ L, ContDiffAt ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        carrierScalarAmplitude T Q₀ F₀ row col Φ₀ Y₀ initial₀ (p.1, parameter p.2)) p)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q (F : Euclidean n → Euclidean N)
      (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
      Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm KF 4 F ≤ M →
      (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      (∀ p ∈ L, ContDiffAt ℝ ∞
        (fun p : Euclidean n × CarrierParameter ↦
          carrierScalarAmplitude T Q F row col Φ Y initial (p.1, parameter p.2)) p) →
      cNorm KF (m + 2) (F - F₀) + cNorm KF m (Q.1 - Q₀.1) +
        cNorm K m (fun w ↦ T.carrierGradient Q w.1 w.2 - T.carrierGradient Q₀ w.1 w.2) +
        cNorm L m ((fun p : Euclidean n × CarrierParameter ↦
          carrierScalarAmplitude T Q F row col Φ Y initial (p.1, parameter p.2)) -
          (fun p ↦ carrierScalarAmplitude T Q₀ F₀ row col Φ₀ Y₀ initial₀
            (p.1, parameter p.2))) < δ →
      cNorm L m (Function.uncurry (normalField T Q F row col Φ Y initial) -
        Function.uncurry (normalField T Q₀ F₀ row col Φ₀ Y₀ initial₀)) < ε := by
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hxL : MapsTo Prod.fst L KF := fun p hp ↦ hx (hLK hp)
  let v Q (F : Euclidean n → Euclidean N) (α : Euclidean n × CarrierParameter → ℝ)
      (p : Euclidean n × CarrierParameter) : NormalInput n N :=
    (stressJet F p.1, actualInput T Q (ψ p), α p)
  let α₀ := fun p : Euclidean n × CarrierParameter ↦
    carrierScalarAmplitude T Q₀ F₀ row col Φ₀ Y₀ initial₀ (ψ p)
  have hjet (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U) p (hp : p ∈ L) :
      ContDiffAt ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ stressJet F p.1) p :=
    ((contDiffOn_stressJet hU hF).contDiffAt
      (hU.mem_nhds (hKFU (hxL hp)))).comp p contDiffAt_fst
  have hinput Q p (hp : p ∈ L) : ContDiffAt ℝ ∞ (actualInput T Q ∘ ψ) p :=
    ((smooth_actualInput T hP Q).contDiffAt
      ((isOpen_inputDomain T).mem_nhds (hKU (hLK hp)))).comp p hψ.contDiffAt
  have hv Q F hF α (hα : ∀ p ∈ L, ContDiffAt ℝ ∞ α p) p (hp : p ∈ L) :
      ContDiffAt ℝ ∞ (v Q F α) p :=
    (hjet F hF p hp).prodMk ((hinput Q p hp).prodMk (hα p hp))
  have hv₀ := hv Q₀ F₀ hF₀ α₀ hα₀
  let S := boundedSecondJetGaps n N (2 * M) κmet κnormal
  let R := cNorm L 0 (v Q₀ F₀ α₀) + 1
  let W : Set (NormalInput n N) := S ×ˢ closedBall 0 R
  have hW : IsCompact W :=
    (isCompact_boundedSecondJetGaps (2 * M) κnormal hκmet).prod (isCompact_closedBall ..)
  have ha : ∀ p ∈ W, ContDiffAt ℝ m (normalInputValue col) p := by
    intro p hp
    have hi := firstJet_injective_of_metricEnergyGap hκmet hp.1.2.1
    exact (smoothAt_normalInputValue col hi
      (secondJetNormalMap_range_of_projected_gap hi hκnormal hp.1.2.2)).of_le (by simp)
  have hS (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
      (hlow : cNorm KF 4 F ≤ M)
      (hmet : ∀ x ∈ KF, ∀ u, κmet * ‖u‖ ^ 2 ≤ ‖fderiv ℝ F x u‖ ^ 2)
      (hnormal : ∀ x ∈ KF, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖)
      p (hp : p ∈ L) : stressJet F p.1 ∈ S := by
    have hb := norm_stressJet_le_cNorm_four hKF
      (fun x hx ↦ hF.contDiffAt (hU.mem_nhds (hKFU hx))) (hxL hp)
    exact secondJet_mem_boundedSecondJetGaps
      ((hF.contDiffAt (hU.mem_nhds (hKFU (hxL hp)))).of_le (by simp))
      (hi _ (hKFU (hxL hp))) (hb.trans (mul_le_mul_of_nonneg_left hlow (by norm_num)))
      (hmet _ (hxL hp)) (hnormal _ (hxL hp))
  have hnorm₀ p (hp : p ∈ L) : ‖v Q₀ F₀ α₀ p‖ ≤ cNorm L 0 (v Q₀ F₀ α₀) := by
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun p hp ↦ (hv₀ p hp).of_le (by simp)) hp (le_refl 0)
    simpa only [norm_iteratedFDeriv_zero] using hb
  have hr₀ : MapsTo (v Q₀ F₀ α₀) L W := by
    intro p hp
    refine ⟨hS F₀ hF₀ hi₀ hlow₀ hmet₀ hnormal₀ p hp, ?_⟩
    rw [mem_closedBall_zero_iff]
    exact (norm_snd_le _).trans ((hnorm₀ p hp).trans (by dsimp [R]; linarith))
  obtain ⟨d, hd, hcomp⟩ := HamiltonPhase.CompositionContinuity.exists_cNorm_comp_sub_lt
    hL hW ha (fun p hp ↦ (hv₀ p hp).of_le (by simp)) hr₀ hε
  obtain ⟨B, hB, hb⟩ := exists_actualInput_sub_bound T hP hK hKF hKFU hKU hx
  obtain ⟨E, hE, he⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := Input n) hL hK (fun _ _ ↦ hψ.contDiffAt) hLK
  obtain ⟨D, hD, hj⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := StressJet n N) hL hKF (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hxL
  let A := 2 * D m + E m * (B m + 1) + 1
  have hA : 0 < A := by
    have := hD m
    have := hE m
    have := hB m
    dsimp [A]
    positivity
  refine ⟨min 1 d / A, div_pos (lt_min zero_lt_one hd) hA, ?_⟩
  intro Q F Φ Y initial _hQ hF hi hrank hlow hmet hnormal hα hsmall
  let α := fun p : Euclidean n × CarrierParameter ↦
    carrierScalarAmplitude T Q F row col Φ Y initial (ψ p)
  have hvF := hv Q F hF α hα
  have hjb : cNorm L m ((fun p : Euclidean n × CarrierParameter ↦ stressJet F p.1) -
      (fun p ↦ stressJet F₀ p.1)) ≤ 2 * D m * cNorm KF (m + 2) (F - F₀) := by
    have hh := hj (stressJet F - stressJet F₀) (fun x hx ↦
      ((contDiffOn_stressJet hU hF).sub (contDiffOn_stressJet hU hF₀)).contDiffAt
        (hU.mem_nhds (hKFU hx))) m
    exact (hh.trans (mul_le_mul_of_nonneg_left
      (CurrentGeometricNeighborhood.cNorm_stressJet_sub_le hKF hU hKFU hF hF₀ m)
      (hD m).le)).trans_eq (by ring)
  have hib : cNorm L m (actualInput T Q ∘ ψ - actualInput T Q₀ ∘ ψ) ≤
      E m * (B m * cNorm KF m (Q.1 - Q₀.1) + cNorm K m (fun w ↦
        T.carrierGradient Q w.1 w.2 - T.carrierGradient Q₀ w.1 w.2)) := by
    have hh := he (actualInput T Q - actualInput T Q₀) (fun w hw ↦
      ((smooth_actualInput T hP Q).sub (smooth_actualInput T hP Q₀)).contDiffAt
        ((isOpen_inputDomain T).mem_nhds (hKU hw))) m
    exact hh.trans (mul_le_mul_of_nonneg_left (hb Q Q₀ m) (hE m).le)
  have hp₂ := cNorm_prodMk_le_on L hL m
    (fun p hp ↦ ((hinput Q p hp).sub (hinput Q₀ p hp)).of_le (by simp))
    (fun p hp ↦ ((hα p hp).sub (hα₀ p hp)).of_le (by simp))
  have hp₁ := cNorm_prodMk_le_on L hL m
    (fun p hp ↦ ((hjet F hF p hp).sub (hjet F₀ hF₀ p hp)).of_le (by simp))
    (fun p hp ↦ ((hvF p hp).snd.sub (hv₀ p hp).snd).of_le (by simp))
  have hvb : cNorm L m (v Q F α - v Q₀ F₀ α₀) ≤
      2 * D m * cNorm KF (m + 2) (F - F₀) +
        (E m * (B m * cNorm KF m (Q.1 - Q₀.1) + cNorm K m (fun w ↦
          T.carrierGradient Q w.1 w.2 - T.carrierGradient Q₀ w.1 w.2)) +
          cNorm L m (α - α₀)) :=
    hp₁.trans (add_le_add hjb (hp₂.trans (add_le_add hib le_rfl)))
  have hvs : cNorm L m (v Q F α - v Q₀ F₀ α₀) < min 1 d := by
    have hsmall' := (lt_div_iff₀ hA).mp hsmall
    have hf := cNorm_nonneg KF (m + 2) (F - F₀)
    have hq := cNorm_nonneg KF m (Q.1 - Q₀.1)
    have hg := cNorm_nonneg K m (fun w ↦
      T.carrierGradient Q w.1 w.2 - T.carrierGradient Q₀ w.1 w.2)
    have hs := cNorm_nonneg L m (α - α₀)
    change (cNorm KF (m + 2) (F - F₀) + cNorm KF m (Q.1 - Q₀.1) +
      cNorm K m (fun w ↦ T.carrierGradient Q w.1 w.2 - T.carrierGradient Q₀ w.1 w.2) +
      cNorm L m (α - α₀)) * A < min 1 d at hsmall'
    apply hvb.trans_lt
    apply lt_of_le_of_lt _ hsmall'
    have hDm := (hD m).le
    have hEm := (hE m).le
    have hBm := (hB m).le
    dsimp [A]
    nlinarith [mul_nonneg hDm (add_nonneg hq (add_nonneg hg hs)),
      mul_nonneg hEm (add_nonneg hf hs),
      mul_nonneg (mul_nonneg hEm hBm) (add_nonneg hf (add_nonneg hg hs))]
  have hr : MapsTo (v Q F α) L W := by
    intro p hp
    refine ⟨hS F hF hi hlow hmet hnormal p hp, ?_⟩
    rw [mem_closedBall_zero_iff]
    have herr := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun p hp ↦ ((hvF p hp).sub (hv₀ p hp)).of_le (by simp)) hp (Nat.zero_le m)
    rw [norm_iteratedFDeriv_zero] at herr
    change ‖v Q F α p - v Q₀ F₀ α₀ p‖ ≤ cNorm L m (v Q F α - v Q₀ F₀ α₀) at herr
    have ht : ‖v Q F α p‖ ≤ ‖v Q F α p - v Q₀ F₀ α₀ p‖ + ‖v Q₀ F₀ α₀ p‖ := by
      calc
        ‖v Q F α p‖ = ‖(v Q F α p - v Q₀ F₀ α₀ p) + v Q₀ F₀ α₀ p‖ := by
          congr 1
          exact (sub_add_cancel (v Q F α p) (v Q₀ F₀ α₀ p)).symm
        _ ≤ _ := norm_add_le (v Q F α p - v Q₀ F₀ α₀ p) (v Q₀ F₀ α₀ p)
    exact (norm_snd_le _).trans (ht.trans ((add_le_add herr (hnorm₀ p hp)).trans
      (by dsimp only [R]; linarith only [hvs.trans_le (min_le_left 1 d)])))
  have hout := hcomp (normalInputValue col) (v Q F α) ha
    (fun p hp ↦ (hvF p hp).of_le (by simp)) hr
    (by simpa only [sub_self, cNorm_zero] using hd) (hvs.trans_le (min_le_right _ _))
  have hid Q (F : Euclidean n → Euclidean N) Φ Y initial
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
      (hrank : HasFullNormalRankOn F U) p (hp : p ∈ L) :
      (normalInputValue col ∘ v Q F (fun p ↦
        carrierScalarAmplitude T Q F row col Φ Y initial (ψ p))) =ᶠ[𝓝 p]
      Function.uncurry (normalField T Q F row col Φ Y initial) := by
    have hmem : ∀ᶠ q : Euclidean n × CarrierParameter in 𝓝 p, q.1 ∈ U :=
      continuous_fst.continuousAt.eventually (hU.mem_nhds (hKFU (hxL hp)))
    filter_upwards [hmem] with q hq
    change normalInputValue col (v Q F (fun p ↦
      carrierScalarAmplitude T Q F row col Φ Y initial (ψ p)) q) =
      normalField T Q F row col Φ Y initial q.1 q.2
    refine Eq.trans ?_ (normalField_eq_scalar_smul T Q F row col Φ Y initial q.1 q.2).symm
    dsimp only [normalInputValue, v, ψ]
    apply congrArg (fun z : Euclidean N ↦
      carrierScalarAmplitude T Q F row col Φ Y initial (q.1, parameter q.2) • z)
    exact LinearMap.congr_fun (secondJetNormalInverse_eq_of_contDiffAt
      ((hF.contDiffAt (hU.mem_nhds hq)).of_le (by simp)) (hi _ hq) (hrank _ hq)) _
  have he : cNorm L m (normalInputValue col ∘ v Q F α -
      normalInputValue col ∘ v Q₀ F₀ α₀) =
      cNorm L m (Function.uncurry (normalField T Q F row col Φ Y initial) -
        Function.uncurry (normalField T Q₀ F₀ row col Φ₀ Y₀ initial₀)) := by
    apply cNorm_eq_of_eventuallyEq _ m
    intro p hp
    exact (hid Q F Φ Y initial hF hi hrank p hp).sub
      (hid Q₀ F₀ Φ₀ Y₀ initial₀ hF₀ hi₀ hrank₀ p hp)
  rwa [he] at hout

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
