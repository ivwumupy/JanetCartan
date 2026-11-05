module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.RetainedJets
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.LocalQuadratures
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets

/-!
# Initial localization of the original retained full reduced source

The actual full cubic strain and physical phase producers supply all analytic
source bounds. The given first even right mask has a plateau around the same
original phase graph. The single identity subtraction acts on the original
restriction and zero extension. Constants and integration orders precede the
frame, scalar, full covector, source frequency and proof mask.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.InitialSourceLocalization
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame ResponsePrimarySources
open ResponseSourceExtension Sampling.BackgroundModulation ResponseTransfer ResponseTransfer.SourceNegative
open FiniteChain.Graph JanetCartan.Localization LocalSobolev ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic.RetardedLocalization
variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp CV 2 (volume : Measure E)

/-- The original retained reduced source has arbitrary initial localization
accuracy, with its full cubic amplitude budget `τ^3`. The phase and amplitude
jets are conclusions of their actual producers. Only the original graph's
geometric inclusion in the first-mask plateau remains explicit; the two real
quadratures use this SAME bounded right localizer and the original measure.
The physical phase jet of order one supplies the uniform gradient upper bound.
All constants and finite mask orders precede the varying data
(`app:ch_regular:eq:source-tail`, `app:ch_response:eq:response-graded-reduced`). -/
theorem exists_retained_reducedSource_initial_accuracy_from_profiles
    (hn : 5 ≤ d+1) (T : PatchQuantitativeFamily P U hU)
    (center : E × Par) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : MapsTo Prod.fst (closedBall center ρ) K)
    (hstate : closedBall (0 : E) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hΓ : ∀ j, 0 ≤ Γ j)
    {core chart : Set E} (χenv : OutputCutoff core chart) (hchart : IsOpen chart)
    (χsrc ηred : E → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc)
    (hcχsrc : HasCompactSupport χsrc) (hηred : ContDiff ℝ ∞ ηred)
    {V : Set Par} (hV : IsOpen V) (hproduct : chart ×ˢ V ⊆ closedBall center ρ)
    {Cpar : Set Par} (hCpar : IsCompact Cpar) (hCV : Cpar ⊆ V)
    (hsource : tsupport χsrc ×ˢ Cpar ⊆ domain T)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1)
    (δmask : ℝ) (hδmask : 0 < δmask) (Dmask : ℕ → ℝ)
    (hDmask : ∀ j, 0 ≤ Dmask j) :
    ∃ q : ℕ → ℝ → ℕ, ∃ Binitial : ℕ → ℝ → ℝ,
      (∀ s accuracy, 0 ≤ Binitial s accuracy) ∧
      ∀ (F : E → Euclidean (embeddingDimension (d+1)))
        (Q : {Q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
        (row col : Fin (d+1)) (Φ Y : ℝ × (Euclidean d × Par) → Euclidean d × Par)
        (r : Euclidean d × Euclidean 3 → ℝ) (Kr : Set (Euclidean d × Euclidean 3))
        (Ω : Set (E × Par)),
        Q.1 = projectedStress F →
        IsOpen Ω → closedBall center ρ ⊆ Ω → MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x, κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress (d+1) i) <
          ambientStrainFrameThreshold hn) →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
          (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x,w.2) •
            nullvector T Q col (x,w.2)) w.1 = 0) →
        (∀ j, cNorm (closedBall center ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ j * (1 + cNorm K (j+14) F + cNorm Kr (j+14) r)) →
        ∀ (RF Rr : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 16 ≤ RF → 16 ≤ Rr → ∀ τ : ℝ, 0 < τ →
          L ≤ τ⁻¹ ^ (1-ν) → ∀ c ∈ Cpar,
          let datum := fun x ↦ ηred x • ((1/2 : ℝ) • complexStressContraction (Q.1 x)
            (fullStrainEnvelope T Q F row col Φ Y r χenv τ c x))
          let source := modulatedSource χsrc (fun x ↦ phase T Q x c.2) datum τ⁻¹
          ∃ hm : MemLp source 2 volume, ∀ (s : ℕ) (accuracy : ℝ),
          ∀ (m : LocalizerSymbol (d+1)), ContDiff ℝ ∞ m → HasCompactSupport m →
          (∀ j, j ≤ q s accuracy → ∀ p, ‖iteratedFDeriv ℝ j m p‖ ≤ Dmask j) →
          (∀ y ξ, m (y,-ξ) = m (y,ξ)) →
          ∀ (S : Set (E × E)), cthickening δmask S ⊆ interior {p | m p = 1} →
          (∀ x ∈ tsupport χsrc, (x, gradient (fun y ↦ phase T Q y c.2) x) ∈ S) →
          ∀ (Mloc : H →L[ℂ] H),
          (∀ v : H, Mloc v =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (rightLocalizer τ⁻¹ m (fun y ↦ (v y).ofLp) x)) →
          ∀ (W : Set E) (hW : MeasurableSet W), tsupport χsrc ⊆ W →
          ∀ ζ : ℂ, ‖ζ‖ = 1 →
          let h := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hm.toLp source))
          let e := h - localRealCompression hW W Mloc h
          e ∈ (restrictionSobolevScale W RV hW).level s ∧
            (restrictionSobolevScale W RV hW).gradeNorm s e ≤
              Binitial s accuracy * τ^3 * (τ⁻¹)^(-accuracy) := by
  have hJ : IsCompact (tsupport χsrc ×ˢ Cpar) := hcχsrc.prod hCpar
  obtain ⟨θ,hθ,_,_hcθ,hsθ,hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hJ (isOpen_domain T) hsource
  obtain ⟨Pphase,hP,hphaseGrade⟩ := exists_fullPhase_physical_grades
    (N := embeddingDimension (d+1)) T hJ hsource hK hKU hstate M hκmet hκnormal AF hAF
  have hphaseSmooth (Q) := contDiff_retainedPhaseExtension T Q hθ hsθ
  have hphaseEq (Q) (c) (hc : c ∈ Cpar) (x) (hx : x ∈ tsupport χsrc) :=
    retainedPhaseExtension_physical_eventuallyEq T Q (hplateau ⟨hx,hc⟩)
  obtain ⟨Cenv,hCenv,hjets⟩ := exists_retained_reducedSource_initial_jet_profiles
    hn T center hρ hK hKU hball M hκmet hκnormal AF Ar Γ hAF hAr hΓ
    χenv hchart χsrc ηred hχsrc hηred hV hproduct
  choose q B hB hb using fun (s : ℕ) (accuracy : ℝ) ↦
    exists_initialSource_restriction_accuracy_constant_finite (r := d+1)
      (tsupport χsrc) hcχsrc δmask (Pphase 0+1) hδmask Pphase Dmask Cenv
      (fun j ↦ (hP j).le) hDmask hCenv
      0 s hν accuracy
  refine ⟨q,fun s accuracy ↦ 2 * B s accuracy,
    fun s accuracy ↦ mul_nonneg (by norm_num) (hB s accuracy),?_⟩
  intro F Q row col Φ Y r Kr Ω hQ hΩ hballΩ hΩK hphase hF hi hrank hFM
    hmet hnormal hframe hscalar hnull htransport hcorrection RF Rr L hpF hpr hL hRF hRr
    τ hτ hscale c hc datum source
  have hlow : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress (d+1)) < T.family.threshold := by
    simpa only [hQ] using Q.property.2
  have hQeq : (⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank),hlow⟩ :
      {Q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold}) = Q := Subtype.ext hQ.symm
  let φ := fun x ↦ retainedPhaseExtension T Q θ x c
  have hφ : ContDiff ℝ ∞ φ := (hphaseSmooth Q).comp
    (contDiff_id.prodMk contDiff_const)
  have hphaseJets (x) (hx : x ∈ tsupport χsrc) (j : ℕ) :
      ‖iteratedFDeriv ℝ (j+1) φ x‖ ≤ Pphase j * L^j := by
    rw [show iteratedFDeriv ℝ (j+1) φ x =
        iteratedFDeriv ℝ (j+1) (fun y ↦ phase T Q y c.2) x from
      iteratedFDeriv_retainedPhaseExtension_eq T Q (hplateau ⟨hx,hc⟩) (j+1)]
    have hh := hphaseGrade F hF hi hrank
      ((cNorm_mono_order (by norm_num : 4 ≤ 14)).trans hFM) hmet hnormal hlow
      RF 0 L hL hRF hpF (x,c) ⟨hx,hc⟩ j
    simpa only [hQeq] using hh
  have hupper (x) (hx : x ∈ tsupport χsrc) : ‖fderiv ℝ φ x‖ ≤ Pphase 0 := by
    simpa only [Nat.reduceAdd,norm_iteratedFDeriv_one,pow_zero,mul_one] using
      hphaseJets x hx 0
  let a := fun x ↦ χsrc x • datum x
  let ajoint := fun w : E × Par ↦ χsrc w.1 • (ηred w.1 • ((1/2 : ℝ) •
    complexStressContraction (Q.1 w.1) (fullStrainEnvelope T Q F row col Φ Y r χenv τ w.2 w.1)))
  obtain ⟨hasmooth,hajets⟩ := hjets F Q row col Φ Y r Kr Ω hQ hΩ hballΩ hΩK
    hphase hF hi hrank hFM hmet hnormal hframe hscalar hnull htransport hcorrection
    RF Rr L hpF hpr hL hRF hRr τ hτ
  have ha : ContDiff ℝ ∞ a := by
    rw [← contDiffOn_univ]
    exact hasmooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun x _ ↦ ⟨mem_univ x,hCV hc⟩)
  have haj y j : ‖iteratedFDeriv ℝ j a y‖ ≤ Cenv j * τ^3 * L^j :=
    (RawPrimary.AmplitudeGrades.norm_iteratedFDeriv_physical_slice_le
      (isOpen_univ.prod hV) hasmooth ⟨mem_univ y,hCV hc⟩ j).trans
      (hajets (y,c) ⟨mem_univ y,hCV hc⟩ j)
  have has : tsupport a ⊆ tsupport χsrc := tsupport_smul_subset_left _ _
  have heq : source = fun y ↦ phaseOscillation (fun z ↦ τ⁻¹ * φ z) y • a y := by
    funext y
    by_cases hy : χsrc y = 0
    · simp only [source,modulatedSource,a,hy,zero_smul,smul_zero]
    · have hφeq := hphaseEq Q c hc y (subset_tsupport χsrc hy)
      change χsrc y • (carrier τ⁻¹ (fun x ↦ phase T Q x c.2) y • datum y) = _
      have hcarrier : carrier τ⁻¹ (fun x ↦ phase T Q x c.2) y =
          phaseOscillation (fun z ↦ τ⁻¹ * φ z) y := by
        simp only [carrier_eq_phaseOscillation,phaseOscillation,φ,← hφeq.self_of_nhds]
      rw [hcarrier]
      exact smul_comm _ _ _
  have hsm : ContDiff ℝ ∞ source := by
    rw [heq]
    exact ((Complex.ofRealCLM.contDiff.comp (hφ.const_smul τ⁻¹)).mul
      contDiff_const).cexp.smul ha
  have hsc : HasCompactSupport source := by
    rw [heq]
    have hac : HasCompactSupport a := hcχsrc.of_isClosed_subset (isClosed_tsupport a) has
    exact hac.smul_left
      (f := phaseOscillation (fun z ↦ τ⁻¹ * φ z))
  have hm : MemLp source 2 volume := hsm.continuous.memLp_of_hasCompactSupport hsc
  have hlam : 1 ≤ τ⁻¹ := by
    have hh : (1 : ℝ) ^ (1-ν) ≤ τ⁻¹ ^ (1-ν) := by
      simpa only [Real.one_rpow] using hL.trans hscale
    exact (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by linarith)).mp hh
  refine ⟨hm,?_⟩
  intro s accuracy m hmSmooth hmc hmjet heven S hmaskPlateau hgraph Mloc hMloc W hW hχW ζ hζ h e
  let Uφ := {x : E | ‖fderiv ℝ φ x‖ < Pphase 0+1}
  have hUφ : IsOpen Uφ := isOpen_lt (hφ.continuous_fderiv (by simp)).norm continuous_const
  have hKφ : tsupport χsrc ⊆ Uφ := fun x hx ↦ (hupper x hx).trans_lt (by linarith)
  have hgraph' : ∀ x ∈ tsupport a, (x, gradient φ x) ∈ S := by
    intro x hx
    have hh : φ =ᶠ[𝓝 x] (fun y ↦ phase T Q y c.2) := hphaseEq Q c hc x (has hx)
    change (x, (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) ∈ S
    rw [hh.fderiv_eq]
    exact hgraph x (has hx)
  have hu : hm.toLp source =ᵐ[volume] fun y ↦
      phaseOscillation (fun z ↦ τ⁻¹ * φ z) y • a y :=
    hm.coeFn_toLp.trans (Filter.Eventually.of_forall (congrFun heq))
  obtain ⟨hmem,hbound⟩ := hb s accuracy m hmSmooth hmc φ a hUφ hKφ
    hφ.contDiffOn ha.contDiffOn has (show 0 ≤ τ^3 by positivity)
    hL hlam hscale hgraph' hmaskPlateau (fun _ hx ↦ le_of_lt hx) hmjet
    (fun x hx j _ _ ↦ hphaseJets x (has hx) j)
    (fun x _ j _ ↦ by simpa only [pow_zero,mul_one,mul_assoc] using haj x j)
    Mloc hMloc (hm.toLp source) hu W hW
  have he : e = l2RealPart (volume.restrict W)
      (ζ • restrictL2 W (hm.toLp source - Mloc (hm.toLp source))) :=
    local_initialSource_modulated_quadrature_defect τ⁻¹ m heven Mloc hMloc
      χsrc (fun x ↦ phase T Q x c.2) datum hm hW hχW ζ
  rw [he]
  obtain ⟨hrmem,hrbound⟩ := initial_quadrature_restriction_scale_bound W hW s _ hmem ζ hζ
  exact ⟨hrmem,hrbound.trans ((mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring))⟩

/-- The original retained reduced source has arbitrary initial localization
accuracy, with its full cubic amplitude budget `τ^3`. The phase and amplitude
jets are conclusions of their actual producers. Only the original graph's
geometric inclusion in the first-mask plateau remains explicit; the two real
quadratures use this SAME bounded right localizer and the original measure.
All constants and finite mask orders precede the varying data
(`app:ch_regular:eq:source-tail`, `app:ch_response:eq:response-graded-reduced`). -/
theorem exists_retained_reducedSource_initial_accuracy_constants
    (hn : 5 ≤ d+1) (T : PatchQuantitativeFamily P U hU)
    (center : E × Par) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : MapsTo Prod.fst (closedBall center ρ) K)
    (hstate : closedBall (0 : E) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hΓ : ∀ j, 0 ≤ Γ j)
    {core chart : Set E} (χenv : OutputCutoff core chart) (hchart : IsOpen chart)
    (χsrc ηred : E → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc)
    (hcχsrc : HasCompactSupport χsrc) (hηred : ContDiff ℝ ∞ ηred)
    {V : Set Par} (hV : IsOpen V) (hproduct : chart ×ˢ V ⊆ closedBall center ρ)
    {Cpar : Set Par} (hCpar : IsCompact Cpar) (hCV : Cpar ⊆ V)
    (hsource : tsupport χsrc ×ˢ Cpar ⊆ domain T)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1)
    (δmask : ℝ) (hδmask : 0 < δmask) (Dmask : ℕ → ℝ)
    (hDmask : ∀ j, 0 ≤ Dmask j) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ q : ℕ → ℝ → ℕ, ∃ Binitial : ℕ → ℝ → ℝ,
      (∀ s accuracy, 0 ≤ Binitial s accuracy) ∧
      ∀ (F : E → Euclidean (embeddingDimension (d+1)))
        (Q : {Q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
        (row col : Fin (d+1)) (Φ Y : ℝ × (Euclidean d × Par) → Euclidean d × Par)
        (r : Euclidean d × Euclidean 3 → ℝ) (Kr : Set (Euclidean d × Euclidean 3))
        (Ω : Set (E × Par)),
        Q.1 = projectedStress F →
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
        IsOpen Ω → closedBall center ρ ⊆ Ω → MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x, κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress (d+1) i) <
          ambientStrainFrameThreshold hn) →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
          (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x,w.2) •
            nullvector T Q col (x,w.2)) w.1 = 0) →
        (∀ j, cNorm (closedBall center ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ j * (1 + cNorm K (j+14) F + cNorm Kr (j+14) r)) →
        ∀ (RF Rr : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 16 ≤ RF → 16 ≤ Rr → ∀ τ : ℝ, 0 < τ →
          L ≤ τ⁻¹ ^ (1-ν) → ∀ c ∈ Cpar,
          let datum := fun x ↦ ηred x • ((1/2 : ℝ) • complexStressContraction (Q.1 x)
            (fullStrainEnvelope T Q F row col Φ Y r χenv τ c x))
          let source := modulatedSource χsrc (fun x ↦ phase T Q x c.2) datum τ⁻¹
          ∃ hm : MemLp source 2 volume, ∀ (s : ℕ) (accuracy : ℝ),
          ∀ (m : LocalizerSymbol (d+1)), ContDiff ℝ ∞ m → HasCompactSupport m →
          (∀ j, j ≤ q s accuracy → ∀ p, ‖iteratedFDeriv ℝ j m p‖ ≤ Dmask j) →
          (∀ y ξ, m (y,-ξ) = m (y,ξ)) →
          ∀ (S : Set (E × E)), cthickening δmask S ⊆ interior {p | m p = 1} →
          (∀ x ∈ tsupport χsrc, (x, gradient (fun y ↦ phase T Q y c.2) x) ∈ S) →
          ∀ (Mloc : H →L[ℂ] H),
          (∀ v : H, Mloc v =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (rightLocalizer τ⁻¹ m (fun y ↦ (v y).ofLp) x)) →
          ∀ (W : Set E) (hW : MeasurableSet W), tsupport χsrc ⊆ W →
          ∀ ζ : ℂ, ‖ζ‖ = 1 →
          let h := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hm.toLp source))
          let e := h - localRealCompression hW W Mloc h
          e ∈ (restrictionSobolevScale W RV hW).level s ∧
            (restrictionSobolevScale W RV hW).gradeNorm s e ≤
              Binitial s accuracy * τ^3 * (τ⁻¹)^(-accuracy) := by
  obtain ⟨q,B,hB,hestimate⟩ := exists_retained_reducedSource_initial_accuracy_from_profiles
    hn T center hρ hK hKU hball hstate M hκmet hκnormal AF Ar Γ hAF hAr hΓ
    χenv hchart χsrc ηred hχsrc hcχsrc hηred hV hproduct hCpar hCV hsource
    hν hν1 δmask hδmask Dmask hDmask
  refine ⟨T.family.threshold,T.family.threshold_pos,le_rfl,q,B,hB,?_⟩
  intro F Q row col Φ Y r Kr Ω hQ _hclose
  exact hestimate F Q row col Φ Y r Kr Ω hQ

end JanetCartan.InitialSourceLocalization
