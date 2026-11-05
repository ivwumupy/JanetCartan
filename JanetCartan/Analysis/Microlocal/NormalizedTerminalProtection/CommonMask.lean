module

public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.PrescribedShoulders
public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.PrescribedMasks
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalCommonMask

/-!
# The common normalized-source mask and its even nested proof masks

The geometric carrier is chosen first. The published normalized-source theorem
then supplies one final mask, its actual bounded right quantizations and both
literal source estimates. The reflected shoulder producer and the even cutoff
menu are applied to that very mask. Constants precede current coefficients and
histories, and no independent final masks or operator projections are identified.
The actual initialized selected-family application remains separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius NNReal ENNReal

namespace JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection

open ProtectedMasks SelectedEvenProofMasks RegularSector.Characteristic
open ActualCarriers HamiltonPhase ProtectedFlow PhaseCover FiniteChain.Graph
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open EvolutionIntegratedLocalization RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FourierIntegral LowBounds

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "L2Space" => Lp CV 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Choose one realized terminal mask before the varying selected family,
frequencies and histories. Both corrected source orientations and all real
quadratures obey the published terminal estimates on it. Every finite depth of
even nested proof masks has its complete closed shoulders inside this SAME
terminal plateau, by applying the reflected root/flow/comparison producers.
The original source buffer, all diagonals, full segments and elapsed interval
are retained. This joins the primitive geometric inputs to `hBnear` without
assuming protection of the desired chains
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_common_normalizedSource_terminal_even_masks
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    (hSsym : ∀ p ∈ S, physicalCovectorReflection p ∈ S)
    {B Ω Γ : Set (Euclidean (d + 1))} (hB : IsCompact B)
    (hΓ : IsCompact Γ) (hΓsym : ∀ ξ ∈ Γ, -ξ ∈ Γ)
    {r c C ε : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε)
    (hSB : ∀ p ∈ S, p.1 ∈ B) (hBball : B ⊆ ball 0 (2 * r))
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω)
    (hΩΓ : Ω ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ a > (0 : ℝ), ∃ b > a, ∃ εterminal > (0 : ℝ),
    ∃ (mi : LocalizerSymbol (d+1)) (δfinal lo hiR Rbase : ℝ) (Djet : ℕ → ℝ)
      (Mterminal : {ρ : ℝ // 1 ≤ ρ} → L2Space →L[ℂ] L2Space),
      IsBufferedLocalizer mi (protectedAnnularCarrier (cthickening 1 B) a b εterminal Γ)
        (physicalProtectedRegion Γ) ∧
      0 < δfinal ∧ 0 < lo ∧ lo < hiR ∧ 0 < Rbase ∧
      tsupport mi ⊆ closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus lo hiR ∧
      (∀ k, 0 ≤ Djet k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Djet k) ∧
      (∀ S ⊆ protectedAnnularCarrier (cthickening 1 B) a b εterminal Γ,
        cthickening δfinal S ⊆ interior {p | mi p = 1}) ∧
      (∀ ρ u, Mterminal ρ u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ.1 mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ {Ω : Set E} {x₀ : E} {RQ C₀ : ℝ} {A₀ : Fin (d+1) → MetricTensor (d+1)}
        (f : ActualMaskFamily Ω x₀ RQ A₀ Γ C₀) (L₀ : ℝ), f.radialThreshold ≤ L₀ →
      ∀ (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (_hoc : HasCompactSupport output)
        (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
        (χ₃ : ContDiffBump x₀) (U : Set E), IsOpen U →
        tsupport (χ₃ : E → ℝ) ⊆ U → U ⊆ ball x₀ f.physicalRadius →
        (∀ y ∈ U, output y = 1) →
      ∃ C Cr : ℕ → ℕ → ℝ, (∀ s q, 0 ≤ C s q) ∧ (∀ s q, 0 ≤ Cr s q) ∧
        ∀ (ρ : {ρ : ℝ // 1 ≤ ρ}) (L : ℝ), 1 ≤ L → L ≤ ρ.1 →
        ∀ χ₂ : ContDiffBump x₀, (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) →
        ∀ (s q : ℕ) (D : Set E) (hD : MeasurableSet D)
          (W : Set E) (hW : MeasurableSet W) (u : LocalL2 D CV) (backward : Bool),
          let w := SmallSupport.zeroExtend hD (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u)
          let S := pairedSource f hΓ L₀ output ho.continuous
            (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
          let P := if backward then S.adjoint else S
          let v := restrictL2 W ((P-1) (Mterminal ρ w))
          (v ∈ (restrictionSobolevScale W CV hW).level s ∧
            (restrictionSobolevScale W CV hW).gradeNorm s v ≤
              C s q * ρ.1^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ.1)^q * ‖u‖) ∧
          ∀ c : ℂ, ‖c‖ = 1 →
            let vr := l2RealPart (volume.restrict W) (c • v)
            vr ∈ (restrictionSobolevScale W RV hW).level s ∧
            (restrictionSobolevScale W RV hW).gradeNorm s vr ≤
              Cr s q * ρ.1^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ.1)^q * ‖u‖) ∧
    ∀ (N : ℕ) {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (εroot G : J → ℝ) (_ : ∀ j, 0 ≤ G j),
    ∀ {M Lx κ Δ : ℝ}, 0 ≤ M → 0 ≤ Lx → 0 < κ → 0 ≤ Δ →
      ∃ θ > (0 : ℝ), ∃ Hjet : ℕ → ℝ, (∀ k, 0 ≤ Hjet k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2 * r)) 3 Q ≤ M →
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        (∀ j, IsCompact (U j)) → (∀ j, IsCompact (K j)) → IsClosed W →
        (∀ j, U j ⊆ D j) → (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 (2 * r) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ U j ∪ K j →
          (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
        (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
      ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
        (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
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
        let Ractual := reflectedProofRelation
          (physicalDirectRelation i h Φ U K W χsource χout Δ)
        ∃ m : Fin (N+1) → LocalizerSymbol (d+1),
          (∀ k y ξ, m k (y, -ξ) = m k (y, ξ)) ∧
          (∀ k, IsBufferedLocalizer (m k) (reachableAt Ractual S k.val)
            (physicalProtectedRegion Γ)) ∧
          IsBufferedLocalizer (m 0) S V ∧
          cthickening θ (tsupport (m 0)) ⊆ V ∧
          (∀ k, cthickening θ (reachableAt Ractual S k.val) ⊆
            interior {p | m k p = 1}) ∧
          (∀ k, cthickening θ (tsupport (m k)) ⊆ interior {p | mi p = 1}) ∧
          (∀ k, tsupport (m k) ⊆
            closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus lo hiR) ∧
          (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ Hjet l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ Ractual p q → closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ k p, p ∈ tsupport (m k) → closedBall p θ ⊆ interior {p | mi p = 1}) := by
  obtain ⟨a, ha, b, hab, εterminal, hεterminal, hshoulders⟩ :=
    exists_uniform_reflected_prescribed_terminal_shoulders hS hB hr hc hC hε
      hSB hBball hsource hΩΓ hV hSV
  obtain ⟨mi, δfinal, lo, hiR, Rbase, Djet, Mterminal, hm, hδfinal, hlo, hhiR,
    hRbase, hsupp, hDjet, hjets, hplateau, hright, hsourceBound⟩ :=
    SignedProductEstimates.exists_common_normalizedSource_terminal_localizer
      (b := b) hB.cthickening hΓ hΓsym ha hεterminal
  refine ⟨a, ha, b, hab, εterminal, hεterminal, mi, δfinal, lo, hiR, Rbase,
    Djet, Mterminal, hm, hδfinal, hlo, hhiR, hRbase, hsupp, hDjet, hjets,
    hplateau, hright, hsourceBound, ?_⟩
  intro N J _ ℓ η₀ εroot G hG M Lx κ Δ hM hLx hκ hΔ
  obtain ⟨δ, hδ, hprop⟩ := hshoulders mi δfinal hδfinal
    (hplateau _ Subset.rfl) N ℓ η₀ εroot G hG hM hLx hκ hΔ
  obtain ⟨Hjet, hHjet, hcut⟩ :=
    exists_uniform_even_masks_inside_prescribed_terminal mi hm.compactSupport hδ N
  refine ⟨δ/8, by positivity, Hjet, hHjet, ?_⟩
  intro Q hQ hQM i h Φ U K D W χsource χout hU hK hWclosed hUD hKD hW
    hD hh hroot hprimitive hbase hgap z Rflow rFlow T hflow htime hUflow
    I g charts hgr hderiv hnorm hcover hbuffer Ractual
  let R := physicalDirectRelation i h Φ U K W χsource χout Δ
  have hR : IsCompact {pq : (E × E) × (E × E) | R pq.1 pq.2} := by
    apply isCompact_physicalDirectRelation i h Φ U K D W χsource χout Δ
      hU hK hWclosed hUD hKD (fun j ↦ (hh j).continuousOn)
    intro j
    apply (hflow j).continuous.mono
    intro v hv
    exact ⟨hUflow j hv.1, ⟨by linarith [hv.2.1, htime j], hv.2.2.trans (htime j).le⟩⟩
  have hp := (hprop δ hδ.le le_rfl).2 Q hQ hQM i h Φ U K D W χsource χout
    hU hK hWclosed hUD hKD hW hD hh hroot hprimitive hbase hgap
    z Rflow rFlow T hflow htime hUflow I g charts hgr hderiv hnorm hcover hbuffer
  obtain ⟨m, hsmooth, hrange, hcompact, heven, hreach, _, hsupport,
    hterminal, hjet, hnest, hfinal⟩ := hcut R S hR hS hSsym hp
  have hterminalSupport (k : Fin (N+1)) : tsupport (m k) ⊆ tsupport mi := by
    intro p hp'
    apply subset_tsupport mi
    have hone : mi p = 1 := interior_subset (s := {p | mi p = 1})
      (hterminal k (self_subset_cthickening _ hp'))
    change mi p ≠ 0
    rw [hone]
    exact one_ne_zero
  have hreachable (k : Fin (N+1)) : cthickening (δ/8) (reachableAt Ractual S k.val) ⊆
      interior {p | m k p = 1} :=
    (cthickening_subset_of_subset _ (reachableAt_subset_bufferedReachableAt Ractual S δ k.val)).trans
      (hreach k)
  have hfirst : cthickening (δ/8) (tsupport (m 0)) ⊆ V :=
    (hsupport 0).trans (hprop δ hδ.le le_rfl).1
  refine ⟨m, heven, ?_, ?_, hfirst, hreachable, hterminal,
    fun k ↦ (hterminalSupport k).trans hsupp, hjet, hnest, hfinal⟩
  · exact fun k ↦ ⟨hsmooth k, hrange k, hcompact k,
      (hterminalSupport k).trans hm.support_subset,
      fun p hp' ↦ hreachable k (self_subset_cthickening _ hp')⟩
  · exact ⟨hsmooth 0, hrange 0, hcompact 0,
      fun p hp' ↦ hfirst (self_subset_cthickening _ hp'),
      fun p hp' ↦ hreach 0 (self_subset_cthickening _ hp')⟩

end JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection
