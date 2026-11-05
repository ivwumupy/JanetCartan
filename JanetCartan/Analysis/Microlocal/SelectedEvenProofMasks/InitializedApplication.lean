module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.SelectedApplication

/-!
# Even proof masks on the original initialized selected solver

The same map-preserving lift supplies the coefficient extension and its common
C³ budget. The same selected root/flow certificates and initialized comparison
charts feed the even constructor. All quantitative choices precede the current
map and finite history; no inverse or finite operator family is selected again.
Sources: `app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open SelectedSectorProtection
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.UniformAmplitudes
open RegularSector.FiniteAssembly RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic.EvolutionIntegral
open ProtectedMasks ProtectedMasks.ConicInterior ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
variable {d : ℕ} {r M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)

/-- Initialized selection with the physical annulus preceding the phase
band. In particular the literal direct residual's bounded dilations may be
computed between these two choices. All masks, gaps and constants still
precede the varying current map and finite history
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selectedSector_even_nested_proof_masks_with_prior_annulus
    (f : ActualMaskFamily univ (0 : E) r A₀ K M)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (Gref : FlatReference (d+1)) {b B δ dmap : ℝ} (hbB : b < B) (hδ : 0 < δ)
    (extension : BallExtension.Parameters E) (hp0 : extension.center = 0)
    (hpb : extension.radius ≤ b) (m₀ : ℕ)
    (lift : PrimitiveMapNeighborhood Gref B (m₀+2) dmap →
      ProjectedImmersionNeighborhood (embeddingDimension (d+1)) (ball 0 B) (closedBall 0 b) δ)
    (hsame : ∀ F, (lift F).1 = F.1)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    {Ω₀ Ωsource Γ : Set E} (hΓ : IsCompact Γ)
    {c C Lx ε : ℝ}
    (hr : 0 < r) (hcgraph : 0 < c) (hCgraph : 0 < C) (hLx : 0 ≤ Lx) (hε : 0 < ε)
    (hΩ₀ : Ω₀ ⊆ interior Ωsource) (hΩΓ : Ωsource ⊆ interior Γ)
    (hΩsym : ∀ ξ ∈ Ωsource, -ξ ∈ Ωsource)
    (χ₂ : E → ℝ) (hχ₂ : HasCompactSupport χ₂)
    (hχ₂support : tsupport χ₂ ⊆ ball 0 f.physicalRadius)
    {Ksource : Set E} (hKsource : IsCompact Ksource)
    (hsourceFrequency : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω₀)
    {V : Set (E × E)} (hV : IsOpen V) (hSV : tsupport χ₂ ×ˢ Ksource ⊆ V)
    (hreflectV : physicalCovectorReflection '' (tsupport χ₂ ×ˢ Ksource) ⊆ V)
    (output : E → ℝ) (N : ℕ) :
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z : J → Z := fun p : J ↦ ((coordinateSplit (i p) (0 : E)).1,
      ((coordinateSplit (i p) (0 : E)).2, (coordinateSplit (i p) p.val.val).2))
    let εroot := fun p : J ↦ (f.chart p).coefficientRadius
    let QF := fun F : PrimitiveMapNeighborhood Gref B (m₀+2) dmap ↦
      extendedProjectedStress extension (lift F).1
    let hQF : ∀ F, ContDiff ℝ ∞ (QF F) := fun F ↦
      selected_initialized_extendedPencil_contDiff hbB extension hp0 hpb (lift F)
    EqOn f.inputMask 1 (tsupport χ₂) ∧
    ∃ a > (0 : ℝ), ∃ b > a, ∀ (aPhase bPhase : J → ℝ), (∀ p, 0 < aPhase p) →
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ Rbase εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < θ ∧ 0 < Rbase ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      0 < εcollar ∧ 0 < δT ∧ (∀ j, εcollar ≤ (f.chart j).maskRadius) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      ∀ F : PrimitiveMapNeighborhood Gref B (m₀ + 2) dmap,
      let Q : E → Fin (d+1) → MetricTensor (d+1) := QF F
      let hQ : ContDiff ℝ ∞ Q := hQF F
      let h : J → Z → ℝ := fun p : f.centers ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
      let D : J → Set Z := fun p : f.centers ↦ fieldDomain (coordinateSplit (i p)) univ (ℓ p)
        (z p).2.2 (εroot p)
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP),
        (∀ p, SelectedProtectionData (f.chart p) (T p) (speed p) (G p) (rootCost p)
          Q (Φ p) (Cphase p)) →
        (∀ p, ContDiffOn ℝ ∞ (h p) (D p)) →
        (∀ p w, w ∈ D p → ∀ t : ℝ, 0 < t →
          h p (w.1, (w.2.1, t • w.2.2)) = t * h p w) →
        (∀ p, (Cphase p : TP → TP) = twoTimeProjection (Φ p)) →
        (∀ p, (Cphase p).source = ball ((z p).1, z p) (f.chart p).sourceRadius) →
        (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cphase p).target) →
        (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cphase p)) (Cphase p).target) →
        (∀ p q, q ∈ (Cphase p).target → HasFDerivAt (twoTimePhase (Cphase p))
          (twoTimePhaseDifferential (h p) (Φ p) (Cphase p) q) q) →
        (∀ p w, w ∈ ball (z p) (f.chart p).sourceRadius →
          twoTimePhase (Cphase p) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, 3*r < (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ωsource, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ interior Γ \ cubeBadSubspaceUnion (d+1)) →
        Q = extendedProjectedStress extension F.1 ∧
        SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase
          n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase := by
  intro J i ℓ z εroot QF hQF
  obtain ⟨Mglobal, hMglobal, hbudget⟩ :=
    exists_uniform_extendedProjectedStress_cNorm_three_bound
      (N := embeddingDimension (d+1)) isOpen_ball (isCompact_closedBall (0 : E) b)
      (closedBall_subset_ball hbB) extension
      (by rw [hp0]; exact closedBall_subset_closedBall hpb) hδ (2*r)
  obtain ⟨hrecut, a, ha, bfreq, hab, hselect⟩ :=
    exists_selectedSector_even_nested_proof_masks_of_coefficient_bound_with_prior_annulus f isOpen_univ
      T speed G rootCost hc hradii eT eI hΓ hr hMglobal hcgraph hCgraph hLx hε
      (closedBall_subset_ball (by linarith)) hΩΓ hΩsym χ₂ hχ₂ hχ₂support
      (hχ₂support.trans (selected_physical_core_subset_coefficient_ball f))
      hKsource (fun ξ hξ ↦ ⟨(hsourceFrequency ξ hξ).1, hΩ₀ (hsourceFrequency ξ hξ).2⟩)
      hV hSV hreflectV output N
  refine ⟨hrecut, a, ha, bfreq, hab, ?_⟩
  intro aPhase bPhase haPhase
  obtain ⟨n, cRad, hcRad, Urad, θ, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, hconstruct⟩ := hselect aPhase bPhase haPhase
  refine ⟨n, cRad, hcRad, Urad, θ, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, ?_⟩
  intro F Q hQ h D Φ Cphase hd hh hhom hCphase hCsource htarget hsmooth hdiff hdiag
    I g charts hgr hderiv hnorm hcover hbuffer
  exact ⟨congrArg (extendedProjectedStress extension) (hsame F),
    hconstruct Q hQ (hbudget (lift F)) Φ Cphase hd hh hhom hCphase hCsource
      htarget hsmooth hdiff hdiag I g charts (fun j ↦ by have := hgr j; linarith)
      hderiv hnorm hcover (fun p hp ξ hξ ↦ interior_subset ((hbuffer p hp hξ).1))⟩

/-- The full original initialized selected-mask conclusion, strengthened by
covector evenness on its actual witnesses. The uniform coefficient budget is
proved from the retained lift, before the current map. Symmetry of the retained
source angular neighborhood is an output of initialized signed no-return.
The original source buffer must also contain the reflected source; this is
necessary for any even plateau and follows, for example, from the SAME source
cutoff's evenness via `reflected_source_product_subset`.

The proof constructs one radial proof refinement and one even mask family,
retaining both orientations, source recuts, canonical grades, conic extensions
and positive interior/boundary gaps. It assumes none of these conclusions
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selectedSector_even_nested_proof_masks
    (f : ActualMaskFamily univ (0 : E) r A₀ K M)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (Gref : FlatReference (d+1)) {b B δ dmap : ℝ} (hbB : b < B) (hδ : 0 < δ)
    (extension : BallExtension.Parameters E) (hp0 : extension.center = 0)
    (hpb : extension.radius ≤ b) (m₀ : ℕ)
    (lift : PrimitiveMapNeighborhood Gref B (m₀+2) dmap →
      ProjectedImmersionNeighborhood (embeddingDimension (d+1)) (ball 0 B) (closedBall 0 b) δ)
    (hsame : ∀ F, (lift F).1 = F.1)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    {Ω₀ Ωsource Γ : Set E} (hΓ : IsCompact Γ)
    {c C Lx ε : ℝ}
    (hr : 0 < r) (hcgraph : 0 < c) (hCgraph : 0 < C) (hLx : 0 ≤ Lx) (hε : 0 < ε)
    (hΩ₀ : Ω₀ ⊆ interior Ωsource) (hΩΓ : Ωsource ⊆ interior Γ)
    (hΩsym : ∀ ξ ∈ Ωsource, -ξ ∈ Ωsource)
    (χ₂ : E → ℝ) (hχ₂ : HasCompactSupport χ₂)
    (hχ₂support : tsupport χ₂ ⊆ ball 0 f.physicalRadius)
    {Ksource : Set E} (hKsource : IsCompact Ksource)
    (hsourceFrequency : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω₀)
    {V : Set (E × E)} (hV : IsOpen V) (hSV : tsupport χ₂ ×ˢ Ksource ⊆ V)
    (hreflectV : physicalCovectorReflection '' (tsupport χ₂ ×ˢ Ksource) ⊆ V)
    (output : E → ℝ) (N : ℕ)
    (aPhase bPhase : f.centers → ℝ) (haPhase : ∀ p, 0 < aPhase p) :
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z : J → Z := fun p : J ↦ ((coordinateSplit (i p) (0 : E)).1,
      ((coordinateSplit (i p) (0 : E)).2, (coordinateSplit (i p) p.val.val).2))
    let εroot := fun p : J ↦ (f.chart p).coefficientRadius
    let QF := fun F : PrimitiveMapNeighborhood Gref B (m₀+2) dmap ↦
      extendedProjectedStress extension (lift F).1
    let hQF : ∀ F, ContDiff ℝ ∞ (QF F) := fun F ↦
      selected_initialized_extendedPencil_contDiff hbB extension hp0 hpb (lift F)
    EqOn f.inputMask 1 (tsupport χ₂) ∧
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ a b Rbase εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < θ ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      0 < εcollar ∧ 0 < δT ∧ (∀ j, εcollar ≤ (f.chart j).maskRadius) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      ∀ F : PrimitiveMapNeighborhood Gref B (m₀ + 2) dmap,
      let Q : E → Fin (d+1) → MetricTensor (d+1) := QF F
      let hQ : ContDiff ℝ ∞ Q := hQF F
      let h : J → Z → ℝ := fun p : f.centers ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
      let D : J → Set Z := fun p : f.centers ↦ fieldDomain (coordinateSplit (i p)) univ (ℓ p)
        (z p).2.2 (εroot p)
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP),
        (∀ p, SelectedProtectionData (f.chart p) (T p) (speed p) (G p) (rootCost p)
          Q (Φ p) (Cphase p)) →
        (∀ p, ContDiffOn ℝ ∞ (h p) (D p)) →
        (∀ p w, w ∈ D p → ∀ t : ℝ, 0 < t →
          h p (w.1, (w.2.1, t • w.2.2)) = t * h p w) →
        (∀ p, (Cphase p : TP → TP) = twoTimeProjection (Φ p)) →
        (∀ p, (Cphase p).source = ball ((z p).1, z p) (f.chart p).sourceRadius) →
        (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cphase p).target) →
        (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cphase p)) (Cphase p).target) →
        (∀ p q, q ∈ (Cphase p).target → HasFDerivAt (twoTimePhase (Cphase p))
          (twoTimePhaseDifferential (h p) (Φ p) (Cphase p) q) q) →
        (∀ p w, w ∈ ball (z p) (f.chart p).sourceRadius →
          twoTimePhase (Cphase p) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, 3*r < (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ωsource, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ interior Γ \ cubeBadSubspaceUnion (d+1)) →
        Q = extendedProjectedStress extension F.1 ∧
        SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase
          n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase := by
  dsimp only
  obtain ⟨hrecut, a, ha, bfreq, hab, h⟩ :=
    exists_selectedSector_even_nested_proof_masks_with_prior_annulus f T speed G rootCost hc
      hradii Gref hbB hδ extension hp0 hpb m₀ lift hsame eT eI hΓ hr hcgraph hCgraph hLx
      hε hΩ₀ hΩΓ hΩsym χ₂ hχ₂ hχ₂support hKsource hsourceFrequency hV hSV hreflectV output N
  obtain ⟨n, cRad, hcRad, Urad, θ, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hmask⟩ := h aPhase bPhase haPhase
  exact ⟨hrecut, n, cRad, hcRad, Urad, θ, a, bfreq, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, ha, hab, hmask⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
