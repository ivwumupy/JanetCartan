module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.SeedAdmission

/-!
# A common source interval for the retained finite family

For `app:ch_background:prop:bg-normalized` and `new:lem:scaling`, the finite
minimum is taken before choosing the source scale. Every scale in the resulting
interval admits the seed and all its positive contractions to the SAME families.
Thus an initializer may choose its one source scale below this cap, retaining
the original analytic source and every other initialized margin. The additional
margin can include the thresholds of `exists_retained_seed_common_conic_charts`
and `exists_projected_null_coefficients`.

The transverse premise concerns each retained state ball. Its producer is the
frozen transverse construction, retained through the quantitative patch choice;
a gap on an unrelated root neighborhood does not establish this premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers CurrentFullPhase FrozenPhaseReference HamiltonPhase
open ProjectedStressFrame NormalizedBackground.SourceGeometry SourceMatching

/-- One common cap, before the initialized source scale, for all retained
patches and all their subsequent positive source contractions. In particular
the origin frame is exactly `cubeStress`, as required by the common conic
producer. The arbitrary margins `ε a` may include the conic and null-column
thresholds. No equality between independently chosen existential scales is
used. Consumer: same-seed conic/primitive assembly for
`app:ch_osc:prop:osc-normal`, Step 4', and `app:ch_background:eq:bg-Nsigma`. -/
theorem exists_finite_retained_source_scale_interval
    {n : ℕ} {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (hbounded : Bornology.IsBounded U)
    {P : A → FrozenMenu.Patch n} (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    {γ ε : A → ℝ} (hγ : ∀ a, 0 < γ a) (hε : ∀ a, 0 < ε a)
    (hgap : ∀ a, ∀ z ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      γ a ≤ |⟪(frozenSymbol n).hp z, (T a).data.adapted.normal⟫_ℝ|) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧ ∀ ρ ∈ Ioc (0 : ℝ) cap,
      let F := sourceDilation G.map ρ
      ContDiff ℝ ∞ F ∧ (∀ x, inducedMetric F x = 1) ∧
      IsImmersionOn F U ∧ HasFullNormalRankOn F U ∧
      ∀ a : A,
        ∃ Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (T a).family.threshold},
          Q₀.1 = projectedStress F ∧ Q₀.1 0 = cubeStress n ∧
          cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            (Q₀.1 - fun _ ↦ cubeStress n) < ε a ∧
          (∀ z ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
            ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z,
              (T a).data.adapted.normal⟫_ℝ ≠ 0) ∧
          ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
            IsImmersionOn (sourceDilation F σ) U ∧
            HasFullNormalRankOn (sourceDilation F σ) U ∧
            ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
              cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
                (Q - fun _ ↦ cubeStress n) < (T a).family.threshold},
              Qσ.1 = projectedStress (sourceDilation F σ) ∧
              EqOn ((T a).currentChart Qσ).coordinates
                (sourceCoordinates ((T a).currentChart Q₀).coordinates σ) (T a).target ∧
              EqOn (phase ((T a).currentChart Qσ).coordinates)
                (sourcePhase (phase ((T a).currentChart Q₀).coordinates) σ) (T a).target ∧
              ∀ m : ℕ,
                EqOn (iteratedFDeriv ℝ m (phase ((T a).currentChart Qσ).coordinates))
                  (iteratedFDeriv ℝ m
                    (sourcePhase (phase ((T a).currentChart Q₀).coordinates) σ)) (T a).target := by
  classical
  choose δ hδ htrans using fun a ↦
    exists_retained_seed_transverse_threshold (T a) (hphysical a) (hγ a) (hgap a)
  let d := fun a ↦ min (ε a) (min (T a).family.threshold (δ a))
  obtain ⟨e, he, hed⟩ := (finite_range d).isCompact.exists_forall_le' continuousOn_id
    (by rintro x ⟨a, rfl⟩; exact lt_min (hε a) (lt_min (T a).family.threshold_pos (hδ a)))
  obtain ⟨cap, hcap, hcap1, hscale⟩ := exists_joint_stress_scale_interval G hbounded he
  have hsmall (a : A) (s : ℝ) (hs : 0 < s) (hscap : s ≤ cap) :
      cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation G.map s) - fun _ ↦ cubeStress n) < d a := by
    apply (cNorm_mono_set_of_contDiffAt ((hphysical a).trans subset_closure)
      hbounded.isCompact_closure ?_).trans_lt
      ((hscale s hs hscap).2.2.2.trans_le (hed _ ⟨a, rfl⟩))
    intro x hx
    exact (((hscale s hs hscap).2.2.1 x hx).sub contDiffAt_const).of_le (by simp)
  refine ⟨cap, hcap, hcap1, ?_⟩
  intro ρ hρ
  let F := sourceDilation G.map ρ
  have hg := hscale ρ hρ.1 hρ.2
  refine ⟨contDiff_sourceDilation G.contDiff,
    inducedMetric_sourceDilation_eq_one hρ.1 G.contDiff G.inducedMetric_eq_one,
    hg.1, hg.2.1, ?_⟩
  intro a
  have hlow : cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < (T a).family.threshold :=
    (hsmall a ρ hρ.1 hρ.2).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  let Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T a).family.threshold} :=
    ⟨projectedStress F, fun x hx ↦ (hg.2.2.1 x (subset_closure hx)).contDiffWithinAt, hlow⟩
  have ht : ∀ z ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, (T a).data.adapted.normal⟫_ℝ ≠ 0 :=
    fun z hz ↦ (htrans a Q₀ ((hsmall a ρ hρ.1 hρ.2).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))) z hz).2
  refine ⟨Q₀, rfl, ?_, (hsmall a ρ hρ.1 hρ.2).trans_le (min_le_left _ _), ht, ?_⟩
  · funext i
    change projectedStress (sourceDilation G.map ρ) 0 i = cubeStress n i
    rw [projectedStress_sourceDilation hρ.1 G.contDiff 0]
    · simpa only [smul_zero] using projectedStress_flatReference_zero G i
    · simpa only [smul_zero] using G.fullNormalRank 0
        (mem_ball_self (G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius))
  · intro σ hσ hσ1
    have hm : 0 < ρ * σ := mul_pos hρ.1 hσ
    have hmcap : ρ * σ ≤ cap := (mul_le_of_le_one_right hρ.1.le hσ1).trans hρ.2
    have heq : sourceDilation F σ = sourceDilation G.map (ρ * σ) := by
      funext x
      simp only [F, sourceDilation, smul_smul, mul_inv_rev]
    have hgs := hscale (ρ * σ) hm hmcap
    have hqs : cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation F σ) - fun _ ↦ cubeStress n) < (T a).family.threshold := by
      rw [heq]
      exact (hsmall a (ρ * σ) hm hmcap).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))
    let Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < (T a).family.threshold} :=
      ⟨projectedStress (sourceDilation F σ), heq.symm ▸
        (show ContDiffOn ℝ ∞ (projectedStress (sourceDilation G.map (ρ * σ))) U from
          fun x hx ↦ (hgs.2.2.1 x (subset_closure hx)).contDiffWithinAt), hqs⟩
    exact ⟨heq.symm ▸ hgs.1, heq.symm ▸ hgs.2.1, Qσ, rfl,
      projected_current_chart_source_dilation (T a) Q₀ Qσ
        (contDiff_sourceDilation G.contDiff) hg.2.1 (hphysical a) rfl ht hσ hσ1 rfl⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
