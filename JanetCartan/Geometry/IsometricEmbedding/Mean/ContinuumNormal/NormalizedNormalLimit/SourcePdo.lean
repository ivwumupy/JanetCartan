module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourceRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.DensityLimitBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourceNormal

/-!
# Constructed normalized reflected PDO controls

The current and zero-source full amplitudes have derived smoothness, fixed
support and one absolute bound before source scale and density. The literal
physical, transferred and real-compressed PDO differences become small on
one source cap, using the original scalar domain and derivative reserve.
-/

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport NormalizedBackground.SourceGeometry
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity AmplitudeBound Pseudodifferential PeriodicLocalL2

/-- A small full-amplitude difference and the proved zero-source bound give
one absolute budget for both members, at the original PDO reserve
(app:ch_background:eq:bg-full-complex-amplitude, bg-uniform-normalized). -/
private theorem source_pair_bound_of_difference
    {n : ℕ} (b : Fin 2 → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (b t)))
    {B tol : ℝ} (htol : tol ≤ 1)
    (hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b 1 ξ z i j) (2 * (n + 1) + 1) B)
    (hd : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b 0 ξ z i j - b 1 ξ z i j) (2 * (n + 1)) tol) :
    ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b t ξ z i j) (2 * (n + 1)) (B + 1) := by
  have hentry (t : Fin 2) (i j : Fin n) (ξ : Euclidean n) :
      ContDiff ℝ ∞ (fun z ↦ b t ξ z i j) :=
    ((matrixEntryEvaluation i j).contDiff.comp (hb t)).comp (contDiff_const.prodMk contDiff_id)
  intro t i j ξ is his z
  fin_cases t
  · have he := euclideanCoordinateDerivList_add
      ((hentry 0 i j ξ).sub (hentry 1 i j ξ)) (hentry 1 i j ξ) is
    simp only [sub_add_cancel] at he
    apply (congrArg norm (congrFun he z)).le.trans
    exact (norm_add_le _ _).trans ((add_le_add
      ((hd i j ξ is his z).trans htol) (hB i j ξ is (by omega) z)).trans_eq (add_comm 1 B))
  · exact (hB i j ξ is (by omega) z).trans (le_add_of_nonneg_right zero_le_one)

/-- Construct both literal full reflected PDOs on the same normalized source
family, deriving their joint smoothness, common support box and density-uniform
absolute derivative budget. The existing PDO estimate then proves arbitrarily
small physical, transferred and real-compressed normal differences through
exactly mu = 2*(n+1). The absolute budget is chosen before the tolerance; each
source cap is chosen before scale and the original mu+14 density class.
Inverse geometry is needed only on the nonnegative source interval.

This discharges the smoothness/support/absolute-bound inputs previously left
in `exists_source_reflectedNormal_tolerance` and `exists_source_family_half_gap`.
The geometry is the existing same-family conic constructor's output. Literal
carrier-normal identities are supplied by normalized selection and retained
matching; no row-norm convergence or analytic amplitude bound is assumed.
Sources: app:ch_background:prop:bg-normalized, bg-full-complex-amplitude,
bg-real-symbol and app:ch_osc:prop:osc-normal, Step 4'. -/
theorem exists_source_reflectedPdo_control_nonneg
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2))
    (hh : ContDiff ℝ ∞ high)
    (hhighZero : ∀ r, r ≤ 1 → high r = 0) (hhighOne : ∀ r, 2 ≤ r → high r = 1)
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hrange : ∀ p ∈ K, D.Contains p)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ico (0 : ℝ) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p))
    {sourceCap : ℝ} (hsourceCap : 0 < sourceCap)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    (hfreqW : ∀ p ∈ W, p.2.2 ≠ 0)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, FixedCutoffs.physical hr 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical hr 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hglobal : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      let Z := normalizedTransportPosition T Q₀
      let J := fun t ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z t)
      ContDiffOn ℝ ∞ (J σ) W ∧ (∀ p ∈ W, J σ p ≠ 0) ∧
      MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (closure (augmentedTransportGradient (Z σ) '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u σ (scaleFrequency t p.1, p.2) = ((u σ p).1, t • (u σ p).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) p)) = t * J σ (inverseCoordinates (u σ) p)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (augmentedTransportGradient (Z σ) '' Zmask) ∪
          closure (augmentedTransportGradient (Z 0) '' Zmask) → (p, v) ∈ Q))
    (hn : 0 < n) :
    let μ := 2 * (n + 1)
    let a := fun σ ↦ coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q₀ σ)
    let foot := fun σ p ↦ sourceDensityFootpointExtension T Y (σ, p)
    let b := fun σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {(a σ) with normal := fun p ↦ Real.sqrt (1 + v (foot σ p)) • (a σ).normal p}
        (J σ) (u σ) Ω S
    ∃ B > (0 : ℝ), ∀ ε > 0, ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (μ + 14) v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let pair := fun t : Fin 2 ↦ b (![σ, 0] t) v
      ∃ hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (pair t)),
      ∃ hs : ∀ t ξ i j, SupportedInCenteredBox (4 * r) (fun z ↦ pair t ξ z i j),
      ∃ hB : ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t ξ z i j) μ B,
      let A := fun t ↦ vectorTwoPositionL2Operator hn (4 * r) (pair t) (hb t) (hs t) B (hB t)
      ‖A 0 - A 1‖ ≤ ε ∧ ‖transferOperator (A 0) - transferOperator (A 1)‖ ≤ ε ∧
        ‖realOutputCompression (transferOperator (A 0)) -
          realOutputCompression (transferOperator (A 1))‖ ≤ ε := by
  intro μ a J foot b
  have h0e : (0 : ℝ) ∈ Ico (0 : ℝ) e := ⟨le_rfl, he⟩
  obtain ⟨hu0, huK0, hright0, _, hgap0⟩ := hfamily 0 h0e
  obtain ⟨hJ0, hJne0, hmap0, hbuffer0, hupper0, huScale0, hJScale0, hshell0⟩ :=
    hglobal 0 ⟨le_rfl, hsourceCap.le⟩
  obtain ⟨B0, hB0, hzeroBound⟩ := exists_sourceDensityLimit_reflected_bounds
    T Q₀ F row col Φ Y hr hcell angular high hP hseed hF hi hrank
    hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource D hD ha hh hhighZero hhighOne
    (u 0) hK hW hKW hQ hΩ hQΩ hS hη hδ hfreq hrange hu0 huK0 hmap0 hend hfreqW
    Zmask hmask hCupper hℓ hlow hupper0 hcone huScale0
    hJ0 hJne0 hgap0 hright0 hbuffer0 hJScale0
    (fun p hp z hz hmem ↦ hshell0 p hp z hz (Or.inl hmem))
  let regularCap := min sourceCap (e / 2)
  have hregularCap : 0 < regularCap := lt_min hsourceCap (half_pos he)
  have hgeometry : ∀ σ ∈ Icc (0 : ℝ) regularCap,
      let Z := normalizedTransportPosition T Q₀ σ
      let Jσ := transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) Z
      ContDiffOn ℝ ∞ Jσ W ∧ (∀ p ∈ W, Jσ p ≠ 0) ∧
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (∀ p ∈ Ω, transportAveragedGradient Z (inverseCoordinates (u σ) p) = p.1.2.2) ∧
      (closure (augmentedTransportGradient Z '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) := by
    intro σ hσ
    have hσe : σ ∈ Ico (0 : ℝ) e := ⟨hσ.1,
      (hσ.2.trans (min_le_right _ _)).trans_lt (half_lt_self he)⟩
    have hg := hglobal σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
    exact ⟨hg.1, hg.2.1, (hfamily σ hσe).1, hg.2.2.1,
      (hfamily σ hσe).2.2.1, hg.2.2.2.1, hg.2.2.2.2.1⟩
  obtain ⟨sc, hsc, hscSource, hsc1, hregular⟩ := exists_source_fullAmplitudes_contDiff
    T Q₀ F row col Φ Y hr hcell angular high hP hseed hF hi hrank
    hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource D hD ha hh hhighZero
    hΩ hregularCap hend hfreqW Zmask hmask hS hCupper hℓ hlow hgeometry
  refine ⟨B0 + 1, by positivity, ?_⟩
  intro ε hε
  let Kpdo := (n : ℝ) ^ 2 * fixedBoxAmplitudeConstant n (4 * r)
  have hKpdo : 0 ≤ Kpdo := mul_nonneg (sq_nonneg _) (fixedBoxAmplitudeConstant_nonneg _ _)
  let tol := min 1 (ε / (Kpdo + 1))
  have htol : 0 < tol := lt_min zero_lt_one (div_pos hε (by positivity))
  obtain ⟨sa, hsa, hsaSource, _, hsmall⟩ := exists_source_fullAmplitude_sqrtFootpoints_tolerance_nonneg
    T Q₀ F row col Φ Y hr hcell angular high hP hseed hF hi hrank
    hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource D hD ha hh hhighZero hhighOne
    hK hconv hW hKW hQ hΩ hQΩ hrange A he hδ hjoint hfamily
    hsourceCap hend hfreqW hη hfreq Zmask hmask hS hCupper hℓ hlow hcone hglobal tol htol
  refine ⟨min sc sa, lt_min hsc hsa, (min_le_right _ _).trans hsaSource,
    (min_le_left _ _).trans hsc1, ?_⟩
  intro σ hσ v hv hvm hpos pair
  have hσc : σ ∈ Icc (0 : ℝ) sc := ⟨hσ.1.le, hσ.2.trans (min_le_left _ _)⟩
  have hσa : σ ∈ Ioc (0 : ℝ) sa := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hpair : ∀ t, ContDiff ℝ ∞ (Function.uncurry (pair t)) ∧
      ∀ ξ i j, SupportedInCenteredBox (4 * r) (fun z ↦ pair t ξ z i j) := by
    intro t
    fin_cases t
    · exact (hregular σ hσc v hv hpos).2
    · exact (hregular 0 ⟨le_rfl, hsc.le⟩ v hv hpos).2
  have hbpair := fun t ↦ (hpair t).1
  have hspair := fun t ↦ (hpair t).2
  have hbase : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair 1 ξ z i j) (μ + 1) B0 :=
    (hzeroBound v hv hvm hpos false).2.2
  have hd : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ pair 0 ξ z i j - pair 1 ξ z i j) μ tol :=
    fun i j ↦ (hsmall σ hσa (μ + 14) (by omega) v hv hvm hpos i j).2
  have hab : ∀ t i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ pair t ξ z i j) μ (B0 + 1) :=
    source_pair_bound_of_difference pair hbpair (min_le_left _ _) hbase hd
  refine ⟨hbpair, hspair, hab, ?_⟩
  have hsDiff : ∀ ξ i j, SupportedInCenteredBox (4 * r)
      (fun z ↦ (pair 0 - pair 1) ξ z i j) := by
    intro ξ i j z hz
    by_cases hzero : pair 0 ξ z i j = 0
    · exact hspair 1 ξ i j z (by
        simpa only [Pi.sub_apply, Matrix.sub_apply, hzero, zero_sub, neg_ne_zero] using hz)
    · exact hspair 0 ξ i j z hzero
  have hbounds := vectorTwoPositionL2Operator_sub_bounds hn (4 * r) (pair 0) (pair 1)
    (hbpair 0) (hbpair 1) ((hbpair 0).sub (hbpair 1)) (hspair 0) (hspair 1) hsDiff
    (B0 + 1) (B0 + 1) tol (hab 0) (hab 1) μ le_rfl hd
  have hbudget : (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * r) * tol) ≤ ε := by
    rw [← mul_assoc]
    change Kpdo * tol ≤ ε
    have htolBound := mul_le_mul_of_nonneg_left
      (show tol ≤ ε / (Kpdo + 1) from min_le_right _ _) (by positivity : 0 ≤ Kpdo + 1)
    rw [mul_div_cancel₀ ε (by positivity : Kpdo + 1 ≠ 0)] at htolBound
    nlinarith only [htol, htolBound]
  exact ⟨hbounds.1.trans hbudget, hbounds.2.1.trans hbudget, hbounds.2.2.trans hbudget⟩

/-- Preserve the original through-zero PDO interface by specializing the
nonnegative-scale construction. The same source, density class and literal
PDO operators are retained (`app:ch_background:prop:bg-normalized`,
`bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem exists_source_reflectedPdo_control
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2))
    (hh : ContDiff ℝ ∞ high)
    (hhighZero : ∀ r, r ≤ 1 → high r = 0) (hhighOne : ∀ r, 2 ≤ r → high r = 1)
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hrange : ∀ p ∈ K, D.Contains p)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p))
    {sourceCap : ℝ} (hsourceCap : 0 < sourceCap)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    (hfreqW : ∀ p ∈ W, p.2.2 ≠ 0)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, FixedCutoffs.physical hr 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical hr 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hglobal : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      let Z := normalizedTransportPosition T Q₀
      let J := fun t ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z t)
      ContDiffOn ℝ ∞ (J σ) W ∧ (∀ p ∈ W, J σ p ≠ 0) ∧
      MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (closure (augmentedTransportGradient (Z σ) '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u σ (scaleFrequency t p.1, p.2) = ((u σ p).1, t • (u σ p).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) p)) = t * J σ (inverseCoordinates (u σ) p)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (augmentedTransportGradient (Z σ) '' Zmask) ∪
          closure (augmentedTransportGradient (Z 0) '' Zmask) → (p, v) ∈ Q))
    (hn : 0 < n) :
    let μ := 2 * (n + 1)
    let a := fun σ ↦ coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q₀ σ)
    let foot := fun σ p ↦ sourceDensityFootpointExtension T Y (σ, p)
    let b := fun σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {(a σ) with normal := fun p ↦ Real.sqrt (1 + v (foot σ p)) • (a σ).normal p}
        (J σ) (u σ) Ω S
    ∃ B > (0 : ℝ), ∀ ε > 0, ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (μ + 14) v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let pair := fun t : Fin 2 ↦ b (![σ, 0] t) v
      ∃ hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (pair t)),
      ∃ hs : ∀ t ξ i j, SupportedInCenteredBox (4 * r) (fun z ↦ pair t ξ z i j),
      ∃ hB : ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t ξ z i j) μ B,
      let A := fun t ↦ vectorTwoPositionL2Operator hn (4 * r) (pair t) (hb t) (hs t) B (hB t)
      ‖A 0 - A 1‖ ≤ ε ∧ ‖transferOperator (A 0) - transferOperator (A 1)‖ ≤ ε ∧
        ‖realOutputCompression (transferOperator (A 0)) -
          realOutputCompression (transferOperator (A 1))‖ ≤ ε := by
  exact exists_source_reflectedPdo_control_nonneg
    T Q₀ F row col Φ Y hr hcell angular high hP hseed hF hi hrank
    hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource D hD ha hh hhighZero hhighOne
    hK hconv hW hKW hQ hΩ hQΩ hrange A he hδ hjoint
    (fun σ hσ ↦ hfamily σ ⟨(neg_neg_of_pos he).trans_le hσ.1, hσ.2⟩)
    hsourceCap hend hfreqW hη hfreq Zmask hmask hS hCupper hℓ hlow hcone hglobal hn

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
