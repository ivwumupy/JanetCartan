module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.CoveredAnnularJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AnnularCriticalCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.AnnularInput
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Amplitudes

/-!
# Selected full-source annular histories on the original covered band

The same selected radial band already has diagonal frequency coverage. Use it
together with the stationary frequency gap to bound the normalized annular
amplitudes on the full critical carrier. No enlargement of the original
amplitude band is needed. Both original orientations, complete Q/B, physical
masks, and doubled cutoff remain literal.
-/

 @[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RegularSector.Characteristic ConicPhase ConicAmplitude AmplitudeBounds
open EvolutionIntegral SymbolBudgets UniformEvolution
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAssembly RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RetainedFactors FullSourceEnvelopes DirectEvolution AnnularSobolev
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
  {A₀ : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d+1)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- The original selected amplitude band suffices for every full-source
annular history jet. The supplied diagonal coverage is the same witness
returned with its raw symbol budgets by the physical retarded constructor.
The stationary frequency gap controls the change of normalization; there are
no extra radial-band comparisons. Constants precede histories and frequencies,
and both literal orientations retain `L^(j+2-Rstar)`, with complete B and shifts
ten/nine (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_fullSource_annular_history_profiles_of_coverage
    (f : ActualMaskFamily Ω x RQ A₀ K₀ M) (p : f.centers)
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hreserve : Rstar + 10 ≤ rStar)
    (horder : displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin)
    (hsrc : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    {ε aperture g Rad ra rb : ℝ} (hε : 0 < ε)
    (hεbuffer : ε ≤ (f.chart p).bufferRadius / 8)
    (hAp : 0 < aperture) (hg : 0 < g) (hRad : 0 < Rad)
    (c₀ : Par) (s : ℝ)
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (π : E → ℂ) (hπ : ContDiff ℝ ∞ π)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) :
    let c := f.chart p
    let z : RootState (Euclidean d) := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    let O := retainedOpenAnnularFrequencyCarrier c.radialSection z.2.2 (ε/2) aperture g Rad
    let Dcrit := retainedOpenIntegrationDomain z ε O
    let Kcrit := (closure (elapsedPhysicalBox z ε) ×ˢ closedBall c₀ (2*s)) ×ˢ closure Dcrit
    RetainedConstruction.DiagonalFrequencyCoverage c.radialSection z.2.2
      (c.bufferRadius/2) ra rb (selectedEndpointMultiplier f p threshold) →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Aamp : ℕ → ℝ, (∀ j, 0 ≤ Aamp j) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let Q := extendedProjectedStress ext (finiteHistoryMap Gref.map u)
      let B := reducedZerothProjection (d+1) ∘
        extendedReducedCoefficients ext (fun _ _ ↦ 0) (finiteHistoryMap Gref.map u)
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (chart : OpenPartialHomeomorph TC TC) (angular : Euclidean d → ℝ),
      (∀ k : Fin 3, ContDiff ℝ ∞ (collared c.radialSection (if k = 0 then 0 else 1)
        angular (selectedBufferedAmplitude f p Q B Φ chart k))) →
      let W := selectedConicAmplitude f p Q B Φ chart angular
      (∀ k : Fin 3, ∀ j,
        BoundedTwoTimeOrderSeminorm (if k = 0 then 0 else 1)
          (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j (W k) ∧
        twoTimeOrderSeminorm (if k = 0 then 0 else 1)
          (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j (W k) ≤
            D j * (1 + cNorm (closedBall x RQ) (j+10) Q + cNorm (closedBall x RQ) (j+9) B)) →
      ∀ t ∈ Icc 0 (3*c.maskRadius/4), ∀ lam : ℝ, 1 ≤ lam →
      ∀ o : Fin 2, ∀ adj : Bool, ∀ j, ∀ v ∈ Kcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (orientedAnnularAmplitude Par adj
          (if o = 0 then W 0 + W 1 else W 2)
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointMultiplier f p threshold) π t lam (-(o.val : ℤ)))) v‖ ≤
            Aamp j * currentCoefficientScale R₀ n ^ (j + 2 - Rstar) := by
  intro c z O Dcrit Kcrit hcoverage
  let K : Set ((E × Euclidean 3) × CW) :=
    (closure (elapsedPhysicalBox z ε) ×ˢ closedBall c₀.1 (2*s)) ×ˢ closure Dcrit
  have hgeometry := retained_critical_carrier_amplitude_geometry c.radialSection z
    hε hεbuffer hAp hg hRad (isCompact_closedBall c₀.1 (2*s))
  have hK : IsCompact K := hgeometry.1
  let δgap := (g/2)/(1+‖c.radialSection‖)
  have hδgap : 0 < δgap := div_pos (half_pos hg) (by positivity)
  have hgap : ∀ v ∈ K, δgap ≤ ‖spatialPart v.2.snd‖ := by
    intro v hv
    apply (div_le_iff₀ (by positivity : 0 < 1+‖c.radialSection‖)).mpr
    have hlo := (hgeometry.2.2.2.2 v hv).1
    have hup := c.radialSection.le_opNorm (spatialPart v.2.snd)
    rw [Real.norm_eq_abs] at hup
    have hh := hlo.trans ((le_abs_self _).trans hup)
    nlinarith only [hh,norm_nonneg (spatialPart v.2.snd)]
  let χo := endpointOutputMask f p output
  let χs := chartInputMask f p
  let β := selectedEndpointMultiplier f p threshold
  have ho : ContDiff ℝ ∞ χo :=
    Complex.ofRealCLM.contDiff.comp (houtput.comp (ResidualCoordinates.physicalCoordinates c.index).contDiff)
  have hs : ContDiff ℝ ∞ χs := (chartPhysicalMasks_properties f p).2.1
  have hβ : ContDiff ℝ ∞ β := (selectedEndpointMultiplier_bounds f p threshold).1
  obtain ⟨S,hS,AQ,AB,hAQ,hAB,hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles Gref hr hrR hR ext
      hextcenter hextradius (reserve := Rstar+8) (by omega) (by omega) horder
  let cost := fun j ↦ physicalAnnularMaskConstant K j χo χs (f.angularMask p) c.index threshold π *
    (max 1 δgap⁻¹)^(j+1) * D j
  have hcost : ∀ j, 0 ≤ cost j := fun j ↦ mul_nonneg
    (mul_nonneg (physicalAnnularMaskConstant_nonneg ..) (by positivity)) (hD j)
  let Aamp := fun j ↦ (2 : ℝ)^(j+1) * cost j * (1 + AQ (j+10) + AB (j+9))
  have hAamp : ∀ j, 0 ≤ Aamp j := fun j ↦ mul_nonneg
    (mul_nonneg (by positivity) (hcost j))
    (add_nonneg (add_nonneg zero_le_one (hAQ _)) (hAB _))
  refine ⟨S,hS,Aamp,hAamp,?_⟩
  intro R₀ hR₀ n u ell hu Q B Φ chart angular hsm W hbudget t ht lam hlam o adj j v hv
  have hL := one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) n
  obtain ⟨_,_,hprofiles⟩ := hcoeff R₀ hR₀ n u ell hu
  obtain ⟨hQ,hB⟩ := hprofiles (closedBall x RQ) (isCompact_closedBall x RQ)
  have hq : cNorm (closedBall x RQ) (j+10) Q ≤
      AQ (j+10) * currentCoefficientScale R₀ n ^ (j+2-Rstar) := by
    simpa only [show j+10-(Rstar+8) = j+2-Rstar by omega] using hQ (j+10)
  have hb : cNorm (closedBall x RQ) (j+9) B ≤
      AB (j+9) * currentCoefficientScale R₀ n ^ (j+2-Rstar) :=
    (hB (j+9)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega)) (hAB _))
  have hpair : 1 + cNorm (closedBall x RQ) (j+10) Q + cNorm (closedBall x RQ) (j+9) B ≤
      (1 + AQ (j+10) + AB (j+9)) * currentCoefficientScale R₀ n ^ (j+2-Rstar) := by
    have h1 := one_le_pow₀ hL (n := j+2-Rstar)
    nlinarith only [hq,hb,h1]
  have hW (k : Fin 3) : ContDiff ℝ ∞ (jointAmplitude (W k)) :=
    (hsm k).comp (contDiff_fst.fst.prodMk
      (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  have htime : t ∈ Icc 0 (c.bufferRadius/2) :=
    ⟨ht.1, by have hp := c.bufferRadius_pos; linarith [ht.2,hsrc]⟩
  let Wo := if o = 0 then W 0 + W 1 else W 2
  have hWo : ContDiff ℝ ∞ (jointAmplitude Wo) := by
    by_cases h : o = 0
    · have he : Wo = W 0 + W 1 := ite_eq_left h
      rw [he]
      exact (hW 0).add (hW 1)
    · simpa only [Wo, ite_eq_right h] using hW 2
  have hraw : BoundedTwoTimeOrderSeminorm o.val
      (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j Wo ∧
      twoTimeOrderSeminorm o.val (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j Wo ≤
        (2*D j) * (1 + cNorm (closedBall x RQ) (j+10) Q + cNorm (closedBall x RQ) (j+9) B) := by
    fin_cases o
    · simpa [Wo] using solver_coefficient_bound (closedBall x RQ) Q B
        (isCompact_bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb)
        (hW 0) (hW 1) D (by simpa using hbudget 0) (by simpa using hbudget 1) j
    · have h := hbudget 2 j
      simp only [show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte] at h
      refine ⟨h.1,h.2.trans ?_⟩
      have hn : 0 ≤ 1 + cNorm (closedBall x RQ) (j+10) Q + cNorm (closedBall x RQ) (j+9) B :=
        add_nonneg (add_nonneg zero_le_one (cNorm_nonneg ..)) (cNorm_nonneg ..)
      nlinarith only [hD j,hn]
  have hforward (w : (E × Euclidean 3) × CW) (hw : w ∈ K) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (normalizedAnnularElapsedAmplitude
        (P := Euclidean 3) Wo χo χs β π t lam (-(o.val : ℤ)))) w‖ ≤
      (2*cost j*(1+AQ (j+10)+AB (j+9))) * currentCoefficientScale R₀ n ^ (j+2-Rstar) := by
    have hc := retained_physical_annular_cNorm_le_of_diagonal_coverage hK c.radialSection z
      (half_pos c.bufferRadius_pos) hδgap hgeometry.2.2.2.1 hgap Wo hWo χo χs ho hs
      (f.angularMask p) (f.angularMask_smooth p) c.index hthreshold hcoverage π hπ
      (closedBall x RQ) Q B (fun k ↦ 2*D k) o.val j hraw.1 hraw.2 htime hlam
    have hreg := contDiff_normalizedAnnularElapsedAmplitude (p := 3) Wo χo χs β π
      hWo ho hs hβ hπ t (zero_lt_one.trans_le hlam).ne' o.val
    apply (norm_iteratedFDeriv_le_cNorm hK (hreg.of_le (by simp)) hw le_rfl).trans
    apply hc.trans
    calc
      _ ≤ physicalAnnularMaskConstant K j χo χs (f.angularMask p) c.index threshold π *
          (max 1 δgap⁻¹)^(j+1) * (2*D j) *
          (1+cNorm (closedBall x RQ) (j+10) Q+cNorm (closedBall x RQ) (j+9) B) := by
        have ho : o.val ≤ 1 := by omega
        have hpow := pow_le_pow_right₀ (le_max_left (1 : ℝ) δgap⁻¹)
          (show j+o.val ≤ j+1 by omega)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
            (physicalAnnularMaskConstant_nonneg ..)) (mul_nonneg (by norm_num) (hD j)))
          (add_nonneg (add_nonneg zero_le_one (cNorm_nonneg ..)) (cNorm_nonneg ..))
      _ = (2*cost j) * (1+cNorm (closedBall x RQ) (j+10) Q+cNorm (closedBall x RQ) (j+9) B) := by
        dsimp only [cost]; ring
      _ ≤ (2*cost j) * ((1+AQ (j+10)+AB (j+9))*currentCoefficientScale R₀ n^(j+2-Rstar)) :=
        mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num) (hcost j))
      _ = _ := by ring
  let w : (E × Euclidean 3) × CW := ((v.1.1,v.1.2.1),v.2)
  have hw : w ∈ K := by
    refine ⟨⟨hv.1.1,?_⟩,hv.2⟩
    have hparam : max (dist v.1.2.1 c₀.1) (dist v.1.2.2 c₀.2) ≤ 2*s := hv.1.2
    exact (le_max_left _ _).trans hparam
  have hproj := (fullSource_annularAmplitude_jets_support adj Wo χo χs β π hWo ho hs hβ hπ
    t (zero_lt_one.trans_le hlam).ne' o.val).1 j v
  apply hproj.trans
  cases adj
  · apply (hforward w hw).trans
    have hpow : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
    have hpos : 0 ≤ 2*cost j*(1+AQ (j+10)+AB (j+9))*currentCoefficientScale R₀ n^(j+2-Rstar) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hcost j))
        (add_nonneg (add_nonneg zero_le_one (hAQ _)) (hAB _)))
        (pow_nonneg (zero_le_one.trans hL) _)
    calc
      _ ≤ 2^j * (2*cost j*(1+AQ (j+10)+AB (j+9))*currentCoefficientScale R₀ n^(j+2-Rstar)) :=
        le_mul_of_one_le_left hpos hpow
      _ = _ := by dsimp only [Aamp]; rw [pow_succ]; ring
  · have hadj := norm_iteratedFDeriv_normalizedAdjointAnnularElapsedAmplitude_le
      Wo χo χs β π hWo ho hs hβ hπ t (zero_lt_one.trans_le hlam).ne' o.val j w
    apply hadj.trans
    apply (mul_le_mul_of_nonneg_left (hforward _
      (annularCarrierSwap_mem_closed_critical_carrier z ε (closedBall c₀.1 (2*s)) O hw))
      (by positivity)).trans_eq
    dsimp only [Aamp]
    rw [pow_succ]
    ring

/-- The original incidence closure inherits both normalized annular
history profiles using the SAME physical frequency coverage and original
amplitude band. The free covector, masks, both shoulders, full B, entire
elapsed interval and reserve subtraction are preserved. The existing
retarded producer supplies the required diagonal coverage along with the raw
symbol budgets (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_incidence_annular_history_profiles_of_coverage
    (f : ActualMaskFamily Ω x RQ A₀ K₀ M) (p : f.centers)
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hreserve : Rstar + 10 ≤ rStar)
    (horder : displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin)
    (hsrc : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    {ε aperture g Rad ra rb : ℝ} (hε : 0 < ε)
    (hεbuffer : ε ≤ (f.chart p).bufferRadius / 8)
    (hAp : 0 < aperture) (hg : 0 < g) (hRad : 0 < Rad)
    {A : Set Par} (hA : IsCompact A)
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (π : E → ℂ) (hπ : ContDiff ℝ ∞ π)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) :
    let c := f.chart p
    let z : RootState (Euclidean d) := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    let O := retainedOpenAnnularFrequencyCarrier c.radialSection z.2.2 (ε/2) aperture g Rad
    let Dcrit := retainedOpenIntegrationDomain z ε O
    let Kcrit := (closure (elapsedPhysicalBox z ε) ×ˢ A) ×ˢ closure Dcrit
    RetainedConstruction.DiagonalFrequencyCoverage c.radialSection z.2.2
      (c.bufferRadius/2) ra rb (selectedEndpointMultiplier f p threshold) →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Aamp : ℕ → ℝ, (∀ j, 0 ≤ Aamp j) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let Q := extendedProjectedStress ext (finiteHistoryMap Gref.map u)
      let B := reducedZerothProjection (d+1) ∘
        extendedReducedCoefficients ext (fun _ _ ↦ 0) (finiteHistoryMap Gref.map u)
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (chart : OpenPartialHomeomorph TC TC) (angular : Euclidean d → ℝ),
      (∀ k : Fin 3, ContDiff ℝ ∞ (collared c.radialSection (if k = 0 then 0 else 1)
        angular (selectedBufferedAmplitude f p Q B Φ chart k))) →
      let W := selectedConicAmplitude f p Q B Φ chart angular
      (∀ k : Fin 3, ∀ j,
        BoundedTwoTimeOrderSeminorm (if k = 0 then 0 else 1)
          (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j (W k) ∧
        twoTimeOrderSeminorm (if k = 0 then 0 else 1)
          (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j (W k) ≤
            D j * (1 + cNorm (closedBall x RQ) (j+10) Q + cNorm (closedBall x RQ) (j+9) B)) →
      ∀ t ∈ Icc 0 (3*c.maskRadius/4), ∀ lam : ℝ, 1 ≤ lam →
      ∀ o : Fin 2, ∀ adj : Bool, ∀ j, ∀ v ∈ Kcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (orientedAnnularAmplitude Par adj
          (if o = 0 then W 0 + W 1 else W 2)
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointMultiplier f p threshold) π t lam (-(o.val : ℤ)))) v‖ ≤
            Aamp j * currentCoefficientScale R₀ n ^ (j + 2 - Rstar) := by
  intro c z O Dcrit Kcrit hcoverage
  obtain ⟨bound,hbound⟩ := hA.exists_bound_of_continuousOn
    (f := fun c : Par ↦ c) continuous_id.continuousOn
  let s := (|bound| + 1) / 2
  have hball : A ⊆ closedBall (0 : Par) (2*s) := by
    intro c hc
    change dist c 0 ≤ 2*s
    rw [dist_zero_right]
    have hh := hbound c hc
    dsimp only [s]
    linarith [le_abs_self bound]
  obtain ⟨S₀,hS₀,Aamp,hAamp,hprofile⟩ :=
    exists_selected_fullSource_annular_history_profiles_of_coverage f p Gref hr hrR hR ext
      hextcenter hextradius hreserve horder hsrc hε hεbuffer hAp hg hRad
      (0 : Par) s output houtput threshold hthreshold π hπ D hD hcoverage
  refine ⟨S₀,hS₀,Aamp,hAamp,?_⟩
  intro R₀ hR₀ n u ell hu Q B Φ chart angular hsm W hbudget t ht lam hlam o adj j v hv
  exact hprofile R₀ hR₀ n u ell hu Φ chart angular hsm hbudget t ht lam hlam o adj j v
    ⟨⟨hv.1.1,hball hv.1.2⟩,hv.2⟩


end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
