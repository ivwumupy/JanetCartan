module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.Gap
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Masks

/-!
# Protected masks and the full conic interior gap

The finite radial menu, compact initial buffers, copied ODEs and primitive
root controls are instantiated into the existing mask constructor. All
geometric and gap constants precede the current coefficient field.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization

variable {d : ℕ}

/-- Construct the expanded finite proof family, its actual nested physical
masks, and a positive full-gradient gap on the entire fixed radial carrier.
The SAME root, conic phase, physical factors, physical buffer and original
elapsed interval are used. This is a finite proof cover, with no partition
or modification of the operators.

The original fixed ball controls, smooth homogeneous root, global normalized
speed bound, flow, inverse chart and inverse segments are projections of
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`. In its application
`R = 3ρ`, `rFlow = 3ρ/2`, and `constructor_source_radius_nesting` supplies the
strict source buffer. `RootFamily.fieldDomain_smul` supplies radial domain
invariance. The comparison inputs are the SAME initialized no-return inputs
required by `exists_uniform_nested_physicalDirectLocalizers`. Finite selection
of these original charts and comparison data remains with the arbitrary-
accuracy parent; no mask margin or conic gap is an assumption here.

Consumer: the conic strengthening of `exists_uniform_nested_localization_data`
and `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular:thm:no-return`). -/
theorem exists_uniform_radial_nested_localizers_and_gap
    {J κI : Type*} [Finite J] [Fintype κI]
    (eI : Module.Basis κI ℝ (ℝ × JointVariables (Euclidean (d + 1)))) (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (z : J → RootState (Euclidean d)) (εroot G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    {B Ω Γ : Set (Euclidean (d + 1))} (hB : IsCompact B) (hΓ : IsClosed Γ)
    {r M c C Lx κ Δ ε : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) (hC : 0 < C) (hLx : 0 ≤ Lx)
    (hκ : 0 < κ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hSB : ∀ p ∈ S, p.1 ∈ B) (hBball : B ⊆ ball 0 (2 * r))
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω)
    (hΩΓ : Ω ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hSV : S ⊆ V) (N : ℕ)
    (R rFlow T σ γ aPhase bPhase : J → ℝ)
    (hγ : ∀ j, 0 < γ j) (haPhase : ∀ j, 0 < aPhase j)
    (hσ : ∀ j, 0 ≤ σ j) (hσr : ∀ j, σ j < rFlow j) (hσR : ∀ j, σ j ≤ R j) :
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ a b Rbase δI : ℝ) (H : ℕ → ℝ),
      0 < θ ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2 * r)) 3 Q ≤ M →
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        IsClosed W → W ⊆ closedBall 0 (2 * r) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j, closedBall (z j) (R j) ⊆ D j) →
        (∀ j w, w ∈ D j → ∀ s : ℝ, 0 < s →
          (w.1, (w.2.1, s • w.2.2)) ∈ D j ∧ h j (w.1, (w.2.1, s • w.2.2)) = s * h j w) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j v, v ∈ closedBall (z j) (R j) →
          v.2.2 ∈ closedBall (z j).2.2 (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ closedBall (z j) (R j) →
          (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B ∩ W) →
        (∀ j v, v ∈ D j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (R j) (rFlow j) (T j) (Φ j)) → (∀ j, Δ < T j) →
      ∀ Cphase : J → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
        (∀ j, (Cphase j : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
          twoTimeProjection (Φ j)) →
        (∀ j, (Cphase j).source = ball ((z j).1, z j) (σ j)) →
        (∀ j, closedBall ((z j).1, z j) (2 * γ j) ⊆ (Cphase j).target) →
        (∀ j q, q ∈ (Cphase j).target → HasFDerivAt (twoTimePhase (Cphase j))
          (twoTimePhaseDifferential (h j) (Φ j) (Cphase j) q) q) →
        (∀ j q, q ∈ (Cphase j).target → ∀ t ∈ uIcc q.2.1 q.1,
          twoTimeState (Φ j) (t, ((Cphase j).symm q).2) ∈ closedBall (z j) (R j) ∧
            (twoTimeState (Φ j) (t, ((Cphase j).symm q).2)).1 = t) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ω, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ Γ) →
        let irad := fun k : (j : J) × Fin (n j) ↦ i k.1
        let hrad := fun k : (j : J) × Fin (n j) ↦ h k.1
        let Φrad := fun k : (j : J) × Fin (n j) ↦
          radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
        let Ur := fun k : (j : J) × Fin (n j) ↦ Urad k.1 k.2
        let Kr := fun k : (j : J) × Fin (n j) ↦
          rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' '' closedBall (z k.1) (R k.1)
        let Ractual := physicalDirectRelation irad hrad Φrad Ur Kr W
          (fun k ↦ χsource k.1) (fun k ↦ χout k.1) Δ
        let Runit := physicalDirectRelation irad hrad Φrad Ur Kr W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
        ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
          (∀ k, IsBufferedLocalizer (m k)
            (reachableAt Ractual S k.val)
            (physicalProtectedRegion Γ)) ∧
          IsBufferedLocalizer (m 0) S V ∧
          cthickening θ (tsupport (m 0)) ⊆ V ∧
          (∀ k, cthickening θ (reachableAt
            Ractual S k.val) ⊆
              interior {p | m k p = 1}) ∧
          (∀ k, cthickening θ (tsupport (m k)) ⊆
            (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
              physicalProtectedRegion Γ) ∧
          (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ Ractual p q →
              closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ k j, IsBufferedLocalizer
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' reachableAt
              Ractual S k.val)
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion Γ)) ∧
          (∀ k j, tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
            closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∧
          (∀ k j l p, ‖iteratedFDeriv ℝ l
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ Runit p q →
                closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          ∀ (k : Fin N) (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
          ∀ (x y : Euclidean (d + 1)) (r' : ℝ) (p : JointVariables (Euclidean (d + 1))),
            r' ∈ Icc 0 Δ → r' ≤ γ j →
            p.1.1 0 ∈ closedBall (z j).1 (γ j / 2) →
            spatialPart p.1.1 ∈ closedBall (z j).2.1 (γ j / 2) →
            spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (ℓ j) (z j).2.2
              (γ j / 2) (aPhase j) (bPhase j) →
            (y, p.2.2.1) ∈ cthickening (θ / 2)
              (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k.castSucc))) →
            (x, p.2.2.2) ∈ tsupport
              (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) (m k.succ) q) →
            δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
              (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y) (r', p) ∧
            ∀ Gext : TwoTimePoint (Euclidean d) → ℝ,
              (∀ q ∈ ConicPhase.domain (ℓ j) (closedBall ((z j).1, z j) (2 * γ j)),
                Gext =ᶠ[𝓝 q] ConicPhase.phase (ℓ j) (Cphase j)) →
              δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
                (SymbolBudgets.normalizedTwoTimePhase Rf
                  (fun t s v η ↦ Gext (t, (s, (v, η))))) x y) (r', p) := by
  classical
  choose n cRad hcRad zj rj Rj Urad hgeom hcover using fun j ↦
    exists_finite_radial_chart_buffers (ℓ j) (z j) (hγ j) (haPhase j)
      (b := bPhase j) (hσ j) (hσr j) (hσR j)
  let E := (j : J) × Fin (n j)
  obtain ⟨θ, a, b, Rbase, H, hθ, ha, hab, hRbase, hH, hconstruct⟩ :=
    exists_uniform_nested_physicalDirectLocalizers
      (fun k : E ↦ (cRad k.1 k.2)⁻¹ • ℓ k.1)
      (fun k : E ↦ cRad k.1 k.2 • (z k.1).2.2)
      (fun k : E ↦ cRad k.1 k.2 * εroot k.1)
      (fun k : E ↦ cRad k.1 k.2 * G k.1)
      (fun k ↦ mul_nonneg (hcRad k.1 k.2).le (hG k.1))
      hS hB hΓ hr hM hc hC hLx hκ hΔ hε hSB hBball hsource hΩΓ hV hSV N
  obtain ⟨δI, hδI, hgap⟩ := exists_uniform_conic_interior_phaseGradientSquare_gap hθ eI
    n ℓ z γ σ R aPhase bPhase cRad hcRad Urad hγ haPhase hσR hcover
  refine ⟨n, cRad, hcRad, Urad, θ, a, b, Rbase, δI, H,
    hθ, ha, hab, hRbase, hδI, hH, ?_⟩
  intro Q hQ hQM i h Φ D W χsource χout hWclosed hW hD hh hRD hhom hroot
    hprimitive hbase hspeed hflow htime Cphase hCphase hCsource htarget hdiff hsegments
    I g charts hgr hderiv hnorm hcomparison hangular
  let irad : E → Fin (d + 1) := fun k ↦ i k.1
  let hrad : E → RootState (Euclidean d) → ℝ := fun k ↦ h k.1
  let Φrad : E → RootState (Euclidean d) × ℝ → RootState (Euclidean d) :=
    fun k ↦ radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
  let Ur : E → Set (RootState (Euclidean d)) := fun k ↦ Urad k.1 k.2
  let Kr : E → Set (RootState (Euclidean d)) := fun k ↦
    rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' '' closedBall (z k.1) (R k.1)
  have hUK (k : E) : Ur k ⊆ Kr k := (hgeom k.1 k.2).2.2.2.2.2.2.1
  have hKrD (k : E) : Kr k ⊆ D k.1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hhom k.1 w (hRD k.1 hw) _ (hcRad k.1 k.2)).1
  have hUcompact (k : E) : IsCompact (Ur k) := (hgeom k.1 k.2).2.2.2.1
  have hKcompact (k : E) : IsCompact (Kr k) :=
    (isCompact_closedBall _ _).image (rootRadialEquiv _ _).continuous
  have hprad (k : E) : ∀ v ∈ Ur k ∪ Kr k,
      v.2.2 ∈ closedBall (cRad k.1 k.2 • (z k.1).2.2) (cRad k.1 k.2 * εroot k.1) ∧
      (1 / 2 : ℝ) ≤ ((cRad k.1 k.2)⁻¹ • ℓ k.1) v.2.2 ∧
      |hrad k v| ≤ ((cRad k.1 k.2)⁻¹ • ℓ k.1) v.2.2 * (cRad k.1 k.2 * G k.1) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (union_subset (hUK k) Subset.rfl) hv
    obtain ⟨hfreq, hsection, hvalue⟩ := hprimitive k.1 w hw
    refine ⟨radial_frequency_mem_closedBall (hcRad k.1 k.2) hfreq, ?_, ?_⟩
    · simpa only [radial_section_apply] using hsection
    · rw [radial_section_apply]
      change |h k.1 (rootRadialEquiv _ _ w)| ≤ _
      rw [rootRadialEquiv_apply, (hhom k.1 w (hRD k.1 hw) _ (hcRad k.1 k.2)).2,
        abs_mul, abs_of_pos (hcRad k.1 k.2)]
      exact (mul_le_mul_of_nonneg_left hvalue (hcRad k.1 k.2).le).trans_eq (by ring)
  have hbrad (k : E) : ∀ v ∈ Ur k ∪ Kr k,
      (coordinateSplit (irad k)).symm (v.1, v.2.1) ∈ B := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (union_subset (hUK k) Subset.rfl) hv
    exact (hbase k.1 w hw).1
  have hfrad (k : E) : ODE.IsSmoothFlowOn (rootHamiltonField (hrad k))
      (zj k.1 k.2) (Rj k.1 k.2) (rj k.1 k.2) (T k.1) (Φrad k) := by
    obtain ⟨_, _, _, _, _, _, _, hclosed, hopen, hrange⟩ := hgeom k.1 k.2
    exact isSmoothFlowOn_radialFlow (hD k.1) (hh k.1) (hhom k.1) (hcRad k.1 k.2)
      (hflow k.1) (hRD k.1) hclosed hopen hrange
  obtain ⟨m, hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet,
    hactual, _, _, _, hunit⟩ :=
    hconstruct Q hQ hQM irad hrad Φrad Ur Kr (fun k ↦ D k.1) W
      (fun k ↦ χsource k.1) (fun k ↦ χout k.1)
      hUcompact hKcompact hWclosed (fun k ↦ (hUK k).trans (hKrD k)) hKrD hW
      (fun k ↦ hD k.1) (fun k ↦ hh k.1) (fun k ↦ hroot k.1) hprad hbrad
      (fun k v hv ↦ hspeed k.1 v (hKrD k hv))
      (fun k ↦ zj k.1 k.2) (fun k ↦ Rj k.1 k.2) (fun k ↦ rj k.1 k.2) (fun k ↦ T k.1)
      hfrad (fun k ↦ htime k.1) (fun k ↦ (hgeom k.1 k.2).2.2.2.2.1)
      I g charts hgr hderiv hnorm hcomparison hangular
  refine ⟨m, hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet, hactual,
    ?_, ?_, ?_, hunit, ?_⟩
  · exact fun k j ↦ IsBufferedLocalizer.canonicalProofLocalizer (coordinateSplit (i j)) (hm k)
  · intro k j
    exact canonicalProofLocalizer_support_bounds (i j)
      (fun p hp ↦ (hshoulder k (self_subset_cthickening _ hp)).1)
  · intro k j l p
    rw [norm_iteratedFDeriv_canonicalProofLocalizer]
    exact hjet k l _
  · intro k j backward Rf hRf x y r' p hr' hrγ ht hy hη hin hout
    have hgap' := hgap i h Φ Cphase D W Δ hCphase hCsource htarget hRD
      (fun j w hw ↦ (hbase j w hw).2)
      (fun j w hw s hs ↦ (hhom j w hw s hs).2) hdiff hsegments
      (m k.castSucc) (m k.succ) (hunit k) j backward Rf hRf x y r' p
      hr' hrγ ht hy hη hin hout
    refine ⟨hgap', fun Gext hGext ↦ ?_⟩
    have hdom := elapsedChartPoint_mem_conic_boundary_buffer (ℓ j) (z j) (hγ j)
      (haPhase j) p ⟨hr'.1, hrγ⟩ ht hy hη
    rw [(phaseGradientSquare_normalized_extension_eq
      (fun k ↦ (eI k).2) eI (ℓ j) (Cphase j)
      hGext hRf backward x y (r', p) hdom).1]
    exact hgap'

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
