module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase.Bounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Angular

/-!
# A common frequency compact for the original full phase

The frozen Hamilton momenta on the original source and independent parameter
compact have a positive margin in the supplied protected angular set. The
primitive momentum comparison transfers them into one fixed compact before
the current frame varies. Reflection uses this same compact. This supplies
the full-source graph input of the initial right-localizer estimate and the
frequency input of the original terminal-mask constructor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.InitialSourceLocalization

open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ActualCarriers.FrozenPhaseReference
open LeadingWave.FullModulation ProtectedFlow ArbitraryAccuracy.ProtectedMasks

variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d

/-- The SAME original full phase, including every independent covector in
the retained parameter compact, has its physical graph in a fixed symmetric
frequency compact. The primitive frame threshold and the compact precede the
current frame. The only angular input concerns the fixed frozen momenta;
current graph inclusion follows from the published momentum comparison
(`app:ch_regular:thm:no-return`, `app:ch_regular:eq:source-tail`). -/
theorem exists_retained_fullPhase_source_frequency_compact
    (T : PatchQuantitativeFamily P U hU)
    {S : Set E} (hS : IsCompact S) {Cpar : Set Par} (hCpar : IsCompact Cpar)
    (hsource : S ×ˢ Cpar ⊆ domain T)
    {Ω : Set E} (hΩsym : ∀ ξ ∈ Ω, -ξ ∈ Ω)
    (hfrozen : ∀ w ∈ S ×ˢ Cpar,
      normalizedCovector (T.reference.chart.chartMomentum (w.1,(0,w.2.2))) ∈ interior Ω) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ Ksource : Set E, IsCompact Ksource ∧
      (∀ ξ ∈ Ksource, -ξ ∈ Ksource) ∧
      (∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω) ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
      ∀ x ∈ S, ∀ c ∈ Cpar,
        (x, gradient (fun y ↦ phase T Q y c.2) x) ∈ S ×ˢ Ksource := by
  let ψ := (zeroEnergyInclusion (n := d+1)).comp physicalCovectorProjection
  let J := ψ '' (S ×ˢ Cpar)
  have hJ : IsCompact J := (hS.prod hCpar).image ψ.continuous
  have hJt : J ⊆ T.target := by
    rintro _ ⟨w,hw,rfl⟩
    exact (inclusion_mem_ball T (w := (w.1,w.2.2))).mpr (hsource hw)
  have hmomentum := (T.reference.chart.contDiffOn_chartMomentum
    T.reference.momentum_smooth T.reference.coordinates_smooth).continuousOn.mono hJt
  let Kf := T.reference.chart.chartMomentum '' J
  have hKf : IsCompact Kf := hJ.image_of_continuousOn hmomentum
  let O := (fun ξ : E ↦ ((0 : E),ξ)) ⁻¹' physicalProtectedRegion Ω
  have hO : IsOpen O := (isOpen_physicalProtectedRegion Ω).preimage
    (continuous_const.prodMk continuous_id)
  have hfO : Kf ⊆ O := by
    rintro ξ ⟨q,⟨w,hw,rfl⟩,rfl⟩
    have ha := T.reference.chart.source_admissible _
      (T.reference.chart.maps_to_source (ψ w) (hJt ⟨w,hw,rfl⟩))
    exact ⟨(mem_frozenSymbol_domain _).mp (T.reference.flow.state_mem _ ha.1 _ ha.2),
      hfrozen w hw⟩
  obtain ⟨ε,hε,hbuffer⟩ := hKf.exists_cthickening_subset_open hO hfO
  obtain ⟨δ,hδ,hcomparison⟩ := T.family.exists_momentum_comparison_threshold hε
  let Kpos := cthickening ε Kf
  let Ksource := Kpos ∪ Neg.neg '' Kpos
  have hKpos : IsCompact Kpos := hKf.cthickening
  have hfreq (ξ : E) (hξ : ξ ∈ Kpos) : ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω :=
    ⟨(hbuffer hξ).1,interior_subset (hbuffer hξ).2⟩
  refine ⟨min δ T.family.threshold,lt_min hδ T.family.threshold_pos,
    min_le_right _ _,Ksource,hKpos.union (hKpos.image continuous_neg),?_,?_,?_⟩
  · intro ξ hξ
    rcases hξ with hξ | ⟨η,hη,rfl⟩
    · exact Or.inr ⟨ξ,hξ,rfl⟩
    · change -(-η) ∈ Kpos ∪ Neg.neg '' Kpos
      simpa only [neg_neg,mem_union] using (Or.inl hη : η ∈ Kpos ∨ η ∈ Neg.neg '' Kpos)
  · intro ξ hξ
    rcases hξ with hξ | ⟨η,hη,rfl⟩
    · exact hfreq ξ hξ
    · refine ⟨neg_ne_zero.mpr (hfreq η hη).1,?_⟩
      simpa only [normalizedCovector,norm_neg,smul_neg] using hΩsym _ (hfreq η hη).2
  · intro Q hQ x hx c hc
    have hw : (x,c) ∈ S ×ˢ Cpar := ⟨hx,hc⟩
    have hq := hJt ⟨(x,c),hw,rfl⟩
    have hb := (hcomparison Q (hQ.trans_le (min_le_left _ _)) (ψ (x,c))
      (ball_subset_closedBall hq)).1
    refine ⟨hx,Or.inl ?_⟩
    change phaseGradient T Q x c.2 ∈ Kpos
    have hwphase := hsource hw
    dsimp only [domain,physicalCovectorProjection,mem_preimage,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply] at hwphase
    have he : phaseGradient T Q x c.2 = (T.currentChart Q).chartMomentum (ψ (x,c)) :=
      phaseGradient_eq_chartMomentum T Q hwphase
    rw [he]
    exact mem_cthickening_of_dist_le _ _ _ _
      ⟨ψ (x,c),⟨(x,c),hw,rfl⟩,rfl⟩ (by rw [dist_eq_norm]; exact hb.le)

end JanetCartan.InitialSourceLocalization
