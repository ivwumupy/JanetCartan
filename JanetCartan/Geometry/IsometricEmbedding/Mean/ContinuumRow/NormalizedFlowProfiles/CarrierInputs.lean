module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedFlowProfiles.FrameBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.Inputs

/-!
# Normalized source inputs to the retained Hamilton carriers

Apply the joint source-frame profiles to the literal supplied quantitative
family. The family, its doubled parameter domain and the compact coefficient
set are fixed before the source scale. These are the primitive inputs for the
null direction and the normalized carrier estimates in
`app:ch_background:prop:bg-normalized` and `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedFlowProfiles
open ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport NullTransport.CoefficientBounds

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Admit every sufficiently small actual source dilation to the supplied
Hamilton family, with a single sequence of frame bounds before the scale.
An arbitrary extra low coefficient tolerance is retained on the whole closure
of the working domain. No phase or flow hypothesis is needed
(`app:ch_background:prop:bg-normalized`, `app:lem:common-hamilton-phase`). -/
theorem exists_admitted_source_frame_profiles (H : FlatReference n)
    (hbounded : Bornology.IsBounded U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∃ (A : ℕ → ℝ), (∀ m, 0 < A m) ∧
      ∃ Q : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) σ₀ →
        {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold},
        (∀ σ hσ, (Q σ hσ).1 = projectedStress (sourceDilation H.map σ)) ∧
        (∀ σ hσ, IsImmersionOn (sourceDilation H.map σ) U ∧
          HasFullNormalRankOn (sourceDilation H.map σ) U ∧
          cNorm (closure U) 6 ((Q σ hσ).1 - fun _ ↦ cubeStress n) < ε) ∧
        (∀ σ hσ x, x ∈ closure U → ContDiffAt ℝ ∞ (Q σ hσ).1 x) ∧
        ∀ m σ hσ,
          cNorm (closure U) m ((Q σ hσ).1 - fun _ ↦ cubeStress n) ≤ A m * σ ∧
          cNorm (closure U) m (Q σ hσ).1 ≤ A m ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
            (Q σ hσ).1 ≤ A m := by
  classical
  obtain ⟨s, hs, hs1, hg, hb⟩ := exists_source_frame_profiles H hbounded
  choose A hA hbound using hb
  let d := min ε T.family.threshold
  have hd : 0 < d := lt_min hε T.family.threshold_pos
  let σ₀ := min s (d / (2 * A 6))
  have hσ₀ : 0 < σ₀ := lt_min hs (by have := hA 6; positivity)
  have hcap {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) s :=
    ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hlow {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) :
      cNorm (closure U) 6
        (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < d := by
    apply ((hbound 6 σ (hcap hσ)).1).trans_lt
    have hh := (le_div_iff₀ (show 0 < 2 * A 6 by have := hA 6; positivity)).mp
      (hσ.2.trans (min_le_right _ _))
    nlinarith
  have hlocal {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) :
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) <
          T.family.threshold := by
    apply (cNorm_mono_set_of_contDiffAt (hphysical.trans subset_closure)
      hbounded.isCompact_closure ?_).trans_lt ((hlow hσ).trans_le (min_le_right _ _))
    intro x hx
    exact (((hg σ (hcap hσ)).2.2 x hx).sub contDiffAt_const).of_le (by simp)
  let Q (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) :=
    (⟨projectedStress (sourceDilation H.map σ),
      fun x hx ↦ ((hg σ (hcap hσ)).2.2 x (subset_closure hx)).contDiffWithinAt,
      hlocal hσ⟩ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  refine ⟨σ₀, hσ₀, (min_le_left _ _).trans hs1, A, hA, Q, fun _ _ ↦ rfl,
    fun σ hσ ↦ ⟨(hg σ (hcap hσ)).1, (hg σ (hcap hσ)).2.1,
      (hlow hσ).trans_le (min_le_left _ _)⟩,
    fun σ hσ ↦ (hg σ (hcap hσ)).2.2, ?_⟩
  intro m σ hσ
  refine ⟨(hbound m σ (hcap hσ)).1, (hbound m σ (hcap hσ)).2, ?_⟩
  exact (cNorm_mono_set_of_contDiffAt (hphysical.trans subset_closure)
    hbounded.isCompact_closure
    (fun x hx ↦ ((hg σ (hcap hσ)).2.2 x hx).of_le (by simp))).trans
      (hbound m σ (hcap hσ)).2

/-- Uniform high bounds for the primitive pair of frame and retained carrier
gradient, from its frame norm alone. This avoids the unnormalized normal gap
in the immersion-level tame bound. The compact coefficient set can be the
original doubled cell, and its center is arbitrary
(`app:ch_waves:eq:joint-tame`, `app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_actualInput_frame_bound {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean n × Euclidean 3) (ρ : ℝ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hc : closedBall a ρ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧ ∀ Q m,
      cNorm (closedBall a ρ) m (actualInput T Q) ≤ B m *
        (1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
          (m + 2) Q.1) := by
  obtain ⟨D, hD, hd⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := Fin n → MetricTensor n) (isCompact_closedBall a ρ) (isCompact_closedBall _ _)
    (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  obtain ⟨A, hA, ha⟩ := T.exists_carrierGradient_frame_bound hP (isCompact_closedBall a ρ) hc
  refine ⟨fun m ↦ (m + 1) * (D m + A m),
    fun m ↦ mul_pos (by positivity) (add_pos (hD m) (hA m)), ?_⟩
  intro Q m
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hphysical (hx hw), (hc hw).1⟩, (hc hw).2⟩
  have hp := cNorm_pair_le a m (isOpen_inputDomain T) hdom
    (Q.2.1.comp contDiffOn_fst (fun _ hw ↦ hw.1.1))
    ((T.carrierGradient_smooth hP Q).mono fun _ hw ↦ ⟨hw.1.2, hw.2⟩)
  have hframe := hd Q.1
    (fun x hx ↦ Q.2.1.contDiffAt (hU.mem_nhds (hphysical hx))) m
  have ho : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m Q.1 ≤
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m + 2) Q.1 :=
    cNorm_mono_order (by omega)
  have hf := hframe.trans (mul_le_mul_of_nonneg_left ho (hD m).le)
  have hg := ha Q m
  change cNorm (closedBall a ρ) m (actualInput T Q) ≤ _ at hp
  apply hp.trans
  have hinner : cNorm (closedBall a ρ) m (fun w ↦ Q.1 w.1) +
      cNorm (closedBall a ρ) m (fun w ↦ T.carrierGradient Q w.1 w.2) ≤
      (D m + A m) * (1 + cNorm
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m + 2) Q.1) := by
    dsimp only [Function.comp_def] at hf
    nlinarith [hD m]
  exact (mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ m + 1)).trans_eq
    (by ring)

end JanetCartan.ContinuumRow.NormalizedFlowProfiles
