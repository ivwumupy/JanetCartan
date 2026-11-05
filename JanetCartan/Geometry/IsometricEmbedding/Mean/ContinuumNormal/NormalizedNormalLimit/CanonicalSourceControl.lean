module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourcePdo
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourceForward
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.SourceCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceLabels

/-!
# Normalized PDO convergence for the retained canonical inverse family

Apply the source estimates to the supplied retained seed and the literal
canonical current/frozen inverses. All forward regularity, original-domain
footpoint facts and global radial geometry are derived. The remaining local
geometry consists of the projections retained by finite incidence selection.
-/

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection FrozenModel RetainedFrozen
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry
open CarrierVariation.FamilyInputs.PositiveReference CarrierVariation.FamilyInputs.WideDensity
open PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- Derive full-amplitude and PDO convergence using the frozen geometry of
ONE admitted positive source on the same supplied family. Exact zero-scale
transport, canonical inverse and Jacobian matching transfers that geometry to
the original seed. No spectral geometry or extra smallness of the unscaled
seed is required. The anchor is only a member used in this proof; the reference,
row, masks, original density domain and zero-limit amplitude remain unchanged.
The other inputs are the selector's current/frozen geometric projections.

Absolute budgets precede tolerance and the cap precedes source scale and every
original `μ+14` density. Consumers: the finite normalized normal comparison and
actual coercivity (`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem exists_retained_canonical_source_reflectedPdo_control_of_frozen_source
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ωflow : Set (Euclidean n × Euclidean 3)} (hΩflow : IsOpen Ωflow)
    {zCell : Euclidean 3} {ρc Rc Bflow τflow : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ωflow)
    (hΩpatch : Ωflow ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τflow) (hτR : τflow ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ωflow (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {L Mc R : ℝ} (hL : 0 < L) (hMc : 0 < Mc) (hR : 0 < R)
    (hforward : cNorm (Icc (-τflow) τflow ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 seed.forward ≤ Mc)
    (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hWinput : W ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω)
    (hcontains : ∀ p ∈ K, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hseg : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    {η gap sourceCap : ℝ} (hη : 0 < η) (hgap : 0 < gap) (hsourceCap : 0 < sourceCap)
    (hcap1 : sourceCap ≤ 1) (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (Qcurrent : ℝ → {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (hframe : ∀ σ ∈ Ioc (0 : ℝ) sourceCap,
      (Qcurrent σ).1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (Qanchor : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {anchor : ℝ} (hanchor : 0 < anchor) (hanchor1 : anchor ≤ 1)
    (hanchorFrame : Qanchor.1 = ProjectedStressFrame.projectedStress (sourceDilation F anchor))
    (hfrozen : RetainedSpectralGeometry T Qanchor zRoot ηb r a ∧
      Ω ⊆ frozenSymbolDomain T Qanchor zRoot ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse T Qanchor zRoot ηb r (6 * a))) Q K ∧
      MapsTo (fun q ↦ inverseCoordinates (frozenSymbolInverse T Qanchor zRoot ηb r (6 * a))
        (normalizeOutputRadius (1 / 4) q)) Ω K ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Qanchor 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Qanchor 0) p) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb r' a', normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (normalizedTransportPosition T Qanchor 0) p) ∈ Q))
    (hcurrent : ∀ σ ∈ Ioc (0 : ℝ) sourceCap,
      RetainedSpectralGeometry T (Qcurrent σ) zRoot ηb r a ∧
      Ω ⊆ symbolDomain T (Qcurrent σ) zRoot ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (symbolInverse T (Qcurrent σ) zRoot ηb r (6 * a))) Q K ∧
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse T (Qcurrent σ) zRoot ηb r (6 * a))
        (normalizeOutputRadius (1 / 4) q)) Ω K ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T (Qcurrent σ))) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T (Qcurrent σ)) p) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb r' a', normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (transportPosition T (Qcurrent σ)) p) ∈ Q)) :
    let μ := 2 * (n + 1)
    let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let d := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
        ha' hcell angular FixedCutoffs.highFrequency σ) (FixedCutoffs.physical ha' 1)
    let J := fun σ ↦ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T seed.Q σ)
    let u := fun σ ↦ if σ = 0 then frozenSymbolInverse T seed.Q zRoot ηb r (6 * a)
      else symbolInverse T (Qcurrent σ) zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    let b := fun σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {d σ with normal := fun p ↦ Real.sqrt (1 + v
          (sourceDensityFootpointExtension T seed.inverse (σ, p))) • (d σ).normal p}
        (J σ) (u σ) Ω S
    ∃ B > (0 : ℝ), ∀ ε > 0, ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (μ + 14) v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let pair := fun t : Fin 2 ↦ b (![σ, 0] t) v
      (∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair 0 ξ z i j - pair 1 ξ z i j) μ ε) ∧
      ∃ hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (pair t)),
      ∃ hs : ∀ t ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ pair t ξ z i j),
      ∃ hB : ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t ξ z i j) μ B,
      let Aop := fun t ↦ vectorTwoPositionL2Operator (by have := row.isLt; omega)
        (4 * a') (pair t) (hb t) (hs t) B (hB t)
      ‖Aop 0 - Aop 1‖ ≤ ε ∧ ‖transferOperator (Aop 0) - transferOperator (Aop 1)‖ ≤ ε ∧
        ‖realOutputCompression (transferOperator (Aop 0)) -
          realOutputCompression (transferOperator (Aop 1))‖ ≤ ε := by
  classical
  intro μ angular d J u S b
  have hn : 0 < n := by have := row.isLt; omega
  have ha : 0 < a := ha'.trans_le haa
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  let Wr := radialInputDomain W
  have hWr : IsOpen Wr := isOpen_radialInputDomain hW
  have hKWr : K ⊆ Wr := hKW.trans (subset_radialInputDomain W)
  have hendr := fun side ↦ mapsTo_densityEndpoint_radialInputDomain side (hend side)
  have hfreqr : ∀ p ∈ Wr, p.2.2 ≠ 0 := fun p hp ↦
    (radialInputDomain_subset_symbolInputDomain hWinput hp).2.2.1
  have hmask : ∀ p ∈ Wr, FixedCutoffs.physical ha' 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical ha' 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ conicMaskSupport zRoot ηb r' a' :=
    fun p hp hx hy hang ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' (hfreqr p hp) hx hy hang
  obtain ⟨e₀, he₀, hjoint⟩ := exists_source_augmented_smooth_on_retained_buffer
    T seed.Q hP hV hVP hW hIt hIIt (fun t ht ↦ (hseg t ht).mono_right hD)
  let e := min (e₀ / 2) sourceCap
  have he : 0 < e := lt_min (half_pos he₀) hsourceCap
  have hesource : e ≤ sourceCap := min_le_right _ _
  have hee₀ : e ≤ e₀ := (min_le_left _ _).trans (half_le_self he₀.le)
  have hjoint' : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T seed.Q q.1) q.2)
        (Ioo (-e) e ×ˢ Wr) :=
    hjoint.mono (prod_mono (Ioo_subset_Ioo (neg_le_neg hee₀) hee₀) Subset.rfl)
  have hmaskInput : conicMaskSupport zRoot ηb r' a' ⊆ frozenInputDomain zRoot ηb r (6 * a) := by
    intro p hp
    have hinput := (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num))) hp
    exact ⟨⟨hinput.1.1, mem_ball_self (by positivity), mem_ball_self (by positivity)⟩, hinput.2⟩
  obtain ⟨hu0, hrange0, hmap0, heq0, hhalf0, hgap0, hJ0, hJpos0, hupper0,
      hscale0, hJscale0, hpunct0, hshell0⟩ := retained_seed_frozen_comparison_geometry_of_source
    T seed.Q Qanchor hF hrank hphysical seed.frame_eq htrans hanchor hanchor1 hanchorFrame
    hP hηb hr ha hquarter hfrozen.1 hKW hWinput hQ hQΩ hfrozen.2.1 hne hcone
    hfrozen.2.2.1 hfrozen.2.2.2.1 A hfrozen.2.2.2.2.1 hfrozen.2.2.2.2.2.1 hmaskInput
    hfrozen.2.2.2.2.2.2
  have hpositive (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) sourceCap) :=
    retained_source_canonical_comparison_geometry T seed.Q (Qcurrent σ) hP hF hrank
      hphysical seed.frame_eq htrans hσ.1 (hσ.2.trans hcap1) (hframe σ hσ) hRT hV hVP
      hηb hr hr' ha' hrr haa har' hquarter houter (hcurrent σ hσ).1 hKW hWinput
      hQ hQΩ (hcurrent σ hσ).2.1 hne hcone (hcurrent σ hσ).2.2.1
      (hcurrent σ hσ).2.2.2.1 A (hcurrent σ hσ).2.2.2.2.1 (hcurrent σ hσ).2.2.2.2.2.1
      (hcurrent σ hσ).2.2.2.2.2.2
  have hfamily : ∀ σ ∈ Ico (0 : ℝ) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T seed.Q σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T seed.Q σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, gap ≤ J σ p) := by
    intro σ hσ
    by_cases hz : σ = 0
    · subst σ
      simpa only [u, ↓reduceIte] using
        And.intro hu0 ⟨hrange0, heq0, hhalf0, hgap0⟩
    · have hp := hpositive σ ⟨lt_of_le_of_ne hσ.1 (Ne.symm hz), hσ.2.le.trans hesource⟩
      simpa only [u, ite_eq_right hz] using
        And.intro hp.2.1 ⟨hp.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1⟩
  have hglobal : ∀ σ ∈ Icc (0 : ℝ) e,
      ContDiffOn ℝ ∞ (J σ) Wr ∧ (∀ p ∈ Wr, J σ p ≠ 0) ∧
      MapsTo (inverseCoordinates (u σ)) Ω Wr ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T seed.Q σ) ''
        conicMaskSupport zRoot ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ q ∈ Ω, ‖(u σ q).2‖ ≤ 2 * ‖q.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
        u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) q)) = t * J σ (inverseCoordinates (u σ) q)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = 1 / 4 → ∀ v ∈ S,
        (p, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T seed.Q σ) ''
          conicMaskSupport zRoot ηb r' a') ∪
          closure (augmentedTransportGradient (normalizedTransportPosition T seed.Q 0) ''
            conicMaskSupport zRoot ηb r' a') → (p, v) ∈ Q) := by
    intro σ hσ
    by_cases hz : σ = 0
    · subst σ
      simp only [u, ↓reduceIte]
      exact ⟨hJ0, fun p hp ↦ (hJpos0 p hp).ne', hmap0, hpunct0, hupper0,
        fun t ht q _ ↦ hscale0 t ht q, hJscale0,
        fun p hp v _ hv ↦ hshell0 (p, v) (hv.elim id id) hp⟩
    · have hσp : σ ∈ Ioc (0 : ℝ) sourceCap :=
        ⟨lt_of_le_of_ne hσ.1 (Ne.symm hz), hσ.2.trans hesource⟩
      obtain ⟨_, _, _, hmap, _, _, _, hJ, hJpos, _, hscale, hJscale, hpunct, hshell⟩ := hpositive σ hσp
      obtain ⟨_, _, G, β, cJ, V₀, L₀, _, _, _, _, hInv, htransverse, _⟩ := (hcurrent σ hσp).1
      simp only [u, ite_eq_right hz]
      exact ⟨hJ, fun p hp ↦ (hJpos p hp).ne', hmap, hpunct,
        fun q hq ↦ symbolInverse_norm_le_two T (Qcurrent σ) hηb hr hInv htransverse
          ((hcurrent σ hσp).2.1 hq),
        fun t ht q _ ↦ hscale t ht q, hJscale,
        fun p hp v _ hv ↦ hv.elim (fun hv ↦ hshell (p, v) hv hp) (fun hv ↦ hshell0 (p, v) hv hp)⟩
  obtain ⟨hY, _, hzeroLabel, hparam, _⟩ := exists_retained_chart_source_primitive_convergence_on_outputCylinder
    hP T hΩflow hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
      hR hRT hRU hV hVP hflow D (D.field.ball_subset.trans hD) a' ha' hcell angular FixedCutoffs.highFrequency
  have hmaps := fun p hp ↦ seed.small_subset ((outputCylinder_spec hRc hτ).2 (hflow (x := p) hp))
  obtain ⟨_, hscalar, _, _, _, _, _, _⟩ := seed.scalar_spec hτ (fun _ ↦ 1)
    contDiffOn_const (fun _ _ ↦ zero_lt_one)
  have hscalar' := hscalar.comp
    (contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn hmaps
  have hsource : ∀ σ ∈ Ioc (0 : ℝ) 1,
      MapsTo (densityFootpoint T (sourceTransportFlow seed.inverse σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
    intro σ hσ p hp
    apply sourceDensityFootpoint_mem_original_ball_of_forward_cNorm T hL hRc hτ hMc
      seed hforward (hflow hp) (hlabel p hp) _ hσ.1 hσ.2
    change |(adaptedCoordinates T.data.adapted p.1).1| < L / (64 * Mc)
    rw [adaptedCoordinates_apply]
    have ht := abs_real_inner_le_norm T.data.adapted.normal p.1
    rw [T.data.adapted.normal_unit, one_mul] at ht
    exact (ht.trans_lt (mem_ball_zero_iff.mp hp.1)).trans_le hRtime
  have hsmoothAngular : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦
      angular p.1 p.2) := angularMask_smooth ..
  have hargs := exists_source_reflectedPdo_control_nonneg
    T seed.Q F row col seed.forward seed.inverse ha' hcell angular FixedCutoffs.highFrequency
    hP seed.frame_eq hF.contDiffOn hi hrank hR hRT hRU hV hVP hscalar' hY hzeroLabel hparam
    hL zero_lt_one hsource D hD hsmoothAngular FixedCutoffs.highFrequency_smooth
    (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht) (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
    hK hconv hWr hKWr hQ hΩ hQΩ hcontains A he hgap hjoint' hfamily he hendr hfreqr
    hη hfreq (conicMaskSupport zRoot ηb r' a') hmask (isCompact_closedBall _ _)
    (by norm_num : (0 : ℝ) ≤ 2) hquarter (by norm_num) hcone hglobal hn
  obtain ⟨B, hB, hpdos⟩ := hargs
  refine ⟨B, hB, ?_⟩
  intro ε hε
  obtain ⟨sp, hsp, hspe, hsp1, hpdo⟩ := hpdos ε hε
  obtain ⟨sa, hsa, _, _, hamp⟩ := exists_source_fullAmplitude_sqrtFootpoints_tolerance_nonneg
    T seed.Q F row col seed.forward seed.inverse ha' hcell angular FixedCutoffs.highFrequency
    hP seed.frame_eq hF.contDiffOn hi hrank hR hRT hRU hV hVP hscalar' hY hzeroLabel hparam
    hL zero_lt_one hsource D hD hsmoothAngular FixedCutoffs.highFrequency_smooth
    (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht) (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
    hK hconv hWr hKWr hQ hΩ hQΩ hcontains A he hgap hjoint' hfamily he hendr hfreqr
    hη hfreq (conicMaskSupport zRoot ηb r' a') hmask (isCompact_closedBall _ _)
    (by norm_num : (0 : ℝ) ≤ 2) hquarter (by norm_num) hcone hglobal ε hε
  refine ⟨min sp sa, lt_min hsp hsa, (min_le_left _ _).trans (hspe.trans hesource),
    (min_le_left _ _).trans hsp1, ?_⟩
  intro σ hσ v hv hvm hpos pair
  refine ⟨fun i j ↦ (hamp σ ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩ (μ + 14)
    (by omega) v hv hvm hpos i j).2, ?_⟩
  exact hpdo σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩ v hv hvm hpos


/-- Instantiate normalized full-amplitude and PDO convergence on the SAME
retained seed, positive current frames and canonical inverses. The original
ODE-cylinder and C¹ forward bound prove the scalar ranges on `L/8`; no smaller
scalar domain is chosen. Joint forward smoothness and every full-cone
Jacobian, inverse-range and support input are conclusions of the retained
geometry, not analytic convergence premises. The local geometric premises
are projections of `exists_finite_incidence_comparison_inputs` on the fixed
selection; its actual admitted frames are supplied by
`exists_finite_seed_source_density_carriers`.

One absolute budget precedes tolerance, source scale and all original
`μ+14` positive densities. The returned cap gives both the full reflected
amplitude difference through `μ=2*(n+1)` and the literal real-compressed PDO
norm difference. Consumer: the positive-source comparison in actual normal
coercivity, followed by SourceInverse. The genuine zero-limit realization
remains with `SourceDensityLimitRealization`; it is not identified with the
origin-frozen density (`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem exists_retained_canonical_source_reflectedPdo_control
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ωflow : Set (Euclidean n × Euclidean 3)} (hΩflow : IsOpen Ωflow)
    {zCell : Euclidean 3} {ρc Rc Bflow τflow : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ωflow)
    (hΩpatch : Ωflow ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τflow) (hτR : τflow ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ωflow (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {L Mc R : ℝ} (hL : 0 < L) (hMc : 0 < Mc) (hR : 0 < R)
    (hforward : cNorm (Icc (-τflow) τflow ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 seed.forward ≤ Mc)
    (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hWinput : W ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω)
    (hcontains : ∀ p ∈ K, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hseg : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    {η gap sourceCap : ℝ} (hη : 0 < η) (hgap : 0 < gap) (hsourceCap : 0 < sourceCap)
    (hcap1 : sourceCap ≤ 1) (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (Qcurrent : ℝ → {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (hframe : ∀ σ ∈ Ioc (0 : ℝ) sourceCap,
      (Qcurrent σ).1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (hfrozen : RetainedSpectralGeometry T seed.Q zRoot ηb r a ∧
      Ω ⊆ frozenSymbolDomain T seed.Q zRoot ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse T seed.Q zRoot ηb r (6 * a))) Q K ∧
      MapsTo (fun q ↦ inverseCoordinates (frozenSymbolInverse T seed.Q zRoot ηb r (6 * a))
        (normalizeOutputRadius (1 / 4) q)) Ω K ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T seed.Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T seed.Q 0) p) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb r' a', normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (normalizedTransportPosition T seed.Q 0) p) ∈ Q))
    (hcurrent : ∀ σ ∈ Ioc (0 : ℝ) sourceCap,
      RetainedSpectralGeometry T (Qcurrent σ) zRoot ηb r a ∧
      Ω ⊆ symbolDomain T (Qcurrent σ) zRoot ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (symbolInverse T (Qcurrent σ) zRoot ηb r (6 * a))) Q K ∧
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse T (Qcurrent σ) zRoot ηb r (6 * a))
        (normalizeOutputRadius (1 / 4) q)) Ω K ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T (Qcurrent σ))) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T (Qcurrent σ)) p) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb r' a', normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (transportPosition T (Qcurrent σ)) p) ∈ Q)) :
    let μ := 2 * (n + 1)
    let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let d := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
        ha' hcell angular FixedCutoffs.highFrequency σ) (FixedCutoffs.physical ha' 1)
    let J := fun σ ↦ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T seed.Q σ)
    let u := fun σ ↦ if σ = 0 then frozenSymbolInverse T seed.Q zRoot ηb r (6 * a)
      else symbolInverse T (Qcurrent σ) zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    let b := fun σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {d σ with normal := fun p ↦ Real.sqrt (1 + v
          (sourceDensityFootpointExtension T seed.inverse (σ, p))) • (d σ).normal p}
        (J σ) (u σ) Ω S
    ∃ B > (0 : ℝ), ∀ ε > 0, ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (μ + 14) v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let pair := fun t : Fin 2 ↦ b (![σ, 0] t) v
      (∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair 0 ξ z i j - pair 1 ξ z i j) μ ε) ∧
      ∃ hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (pair t)),
      ∃ hs : ∀ t ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ pair t ξ z i j),
      ∃ hB : ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t ξ z i j) μ B,
      let Aop := fun t ↦ vectorTwoPositionL2Operator (by have := row.isLt; omega)
        (4 * a') (pair t) (hb t) (hs t) B (hB t)
      ‖Aop 0 - Aop 1‖ ≤ ε ∧ ‖transferOperator (Aop 0) - transferOperator (Aop 1)‖ ≤ ε ∧
        ‖realOutputCompression (transferOperator (Aop 0)) -
          realOutputCompression (transferOperator (Aop 1))‖ ≤ ε := by
  have hunit : sourceDilation F 1 = F := by
    funext x
    simp only [sourceDilation, inv_one, one_smul]
  have hanchorFrame : seed.Q.1 = ProjectedStressFrame.projectedStress (sourceDilation F 1) :=
    hunit.symm ▸ seed.frame_eq
  exact exists_retained_canonical_source_reflectedPdo_control_of_frozen_source
    hP T hΩflow hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
    hL hMc hR hforward hRT hRU hRtime hV hVP hflow hlabel D hD hηb hr hr' ha' hrr haa har' hcell houter
    hK hconv hW hKW hWinput hQ hΩ hQΩ hne hcone hcontains hIt hIIt hseg hend
    hη hgap hsourceCap hcap1 hfreq A Qcurrent hframe seed.Q zero_lt_one le_rfl hanchorFrame hfrozen hcurrent

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
