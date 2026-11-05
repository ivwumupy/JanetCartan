module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareAdmission
public import JanetCartan.Iteration.PhysicalSampling.HistoryBudgets
public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredProtectionApplication
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedOriginalScaleMargins

/-!
# The bare physical row on the same original Schwartz history

Its constant and its two numerical clocks are chosen before the history. The
label, visited node, rate, physical cutoff, angular detector, and both annular
copies in the resulting kernel are the original ones. There is no division by
a sampling weight (`app:ch_mean_pairs:eq:block-fields`, `new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.PhysicalSampling.OriginalBare
open PhysicalSeed PhysicalNormalInverse PhysicalInitialization PhysicalPrimary PhysicalScalarChannel
open ActualCarriers.CurrentFullPhase ProjectedStressFrame ContinuumRow RawInputPartition PhysicalSamplingShells SeparatedSampling

variable {d : ℕ} (hn : 5 ≤ d+1) (pOrder : ℕ)
  (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean (d+1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : OriginalPatchIndex hn → Euclidean (d+1)) (hk : ∀ a, k a ≠ 0)
  (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (d+1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ) (hmargin : ∀ j ∈ orders, 0 < margin j)
  (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j) (cap : ℝ) (hcap : 0 < cap)
  (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap) (other : StrongExtraCaps hn)

local notation "E" => Euclidean (d+1)
local notation "H" => ReferenceBoundary.H hn εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap
local notation "user" => userCap hn other
local notation "merged" => samplingCappedExtra hn pOrder user
local notation "capped" => strongCappedExtra hn merged
set_option quotPrecheck false in
local notation "sel(" f ")" => f hn εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap capped
set_option quotPrecheck false in
local notation "act(" f ")" => f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap user
set_option quotPrecheck false in
local notation "bare(" f ")" => f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap other
local notation "Row" => act(OriginalWeights.Index)
set_option quotPrecheck false in
local notation "pa(" i ")" => (⟨i.1.1.1.1,i.2⟩ : OriginalPatchIndex hn)
set_option quotPrecheck false in
local notation "T(" i ")" => OriginalBoundary.T hn pa(i)
set_option quotPrecheck false in
local notation "cell(" i ")" => sel(SelectedBoundary.cell) i.1.1 i.2
set_option quotPrecheck false in
local notation "z₀(" i ")" => (OriginalBoundary.D hn).roots i.1.1.1.1 i.2 i.1.1.1.2
set_option quotPrecheck false in
local notation "ρ(" i ")" => originalSamplingRadius hn i.1.1 i.2 cell(i)
set_option quotPrecheck false in
local notation "χ₀(" i ")" => FixedCutoffs.physical (n := d+1) (sel(SelectedBoundary.ha') i) 0
set_option quotPrecheck false in
local notation "center(" i ")" => ((0 : E), (z₀(i), (T(i)).reference.spatialPatch z₀(i)))

/-- The single cap selection proves both required support certificates of the
actual bare physical bump; neither is an input about a subsequently chosen row. -/
theorem cutoff_support (i : Row) :
    tsupport (χ₀(i) : E → ℝ) ⊆ closedBall 0 (radius hn pa(i) / 4) ∧
    Function.support (χ₀(i) : E → ℝ) ⊆ closedBall 0 ((ρ(i)).1 / 2) := by
  have h := (sel(SelectedBoundary.fact22) i).trans
    ((h_cappedExtra_le_userExtra hn merged i.1.1 i.2 cell(i)).trans
      (samplingCappedExtra_le_user hn pOrder i.1.1 i.2 cell(i) user))
  change sel(SelectedBoundary.a') i ≤ min _ (min _ _) at h
  have h₁ := (h.trans (min_le_right _ _)).trans (min_le_left _ _)
  have h₂ := (h.trans (min_le_right _ _)).trans (min_le_right _ _)
  have ht : tsupport (χ₀(i) : E → ℝ) ⊆ closedBall 0 (2 * sel(SelectedBoundary.a') i) := by
    simpa using (FixedCutoffs.physical_tsupport (n := d+1) (sel(SelectedBoundary.ha') i) (0 : Fin 3)).trans ball_subset_closedBall
  exact ⟨ht.trans (closedBall_subset_closedBall (by linarith only [h₁])),
    ((subset_tsupport _).trans ht).trans (closedBall_subset_closedBall (by linarith only [h₂]))⟩

/-- The actual colored rate of the same event satisfies the second native
ceiling, fixed before choosing the stage. Use the last *valid* fine band. -/
theorem exists_rate_threshold :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀ ≥ S, ∀ s : ℕ,
      let t := historyScale R₀ growthExponent s
      let J := cutoffCount (t ^ fineExponent)
      ∀ (i : Row) (c : Fin 3 → Fin (pOrder+1)),
        let τ := (act(OriginalColoredProtectionApplication.Rcolor) (i,c) * t^carrierExponent)⁻¹
        0 < τ ∧ ∀ j : Fin J, τ * (2:ℝ)^j.val ≤ min (ceiling hn pa(i)) ((ρ(i)).1/8) := by
  let e := fun i : Row ↦ min (ceiling hn pa(i)) ((ρ(i)).1/8)
  have he (i : Row) : 0 < e i := lt_min (ceiling_pos hn _) (div_pos (ρ(i)).2 (by norm_num))
  have hP := fun i : Row ↦ ((OriginalBoundary.hD hn).2.2.2.2.1 i.1.1.1.1 i.2).1
  obtain ⟨S,hS,all⟩ := Sampling.exists_corrected_sampling_originalScale_threshold
    (fun i : Row ↦ T(i)) hP (ρ := fun i ↦ (ρ(i)).1) (e := e) (fun i ↦ (ρ(i)).2) he
    (show (0:ℝ)<1 from zero_lt_one) 0
  refine ⟨S,hS,?_⟩
  intro R₀ hR s t J i c τ
  have hRone : 1 ≤ R₀ := (by norm_num : (1:ℝ) ≤ 2).trans (hS.trans hR)
  have ht : 1 ≤ t := hRone.trans (le_historyScale hRone s)
  have hf : 1 ≤ t^fineExponent := Real.one_le_rpow ht (by norm_num [fineExponent,meanSlack])
  have hle : t^fineExponent ≤ t^(1+meanSlack) :=
    Real.rpow_le_rpow_of_exponent_le ht (by norm_num [fineExponent,meanSlack])
  let r := fun (i : Row) (c : Fin 3 → Fin (pOrder+1)) ↦ act(OriginalColoredProtectionApplication.Rcolor) (i,c)
  have hr : ∀ i c, 1 ≤ r i c := fun i c ↦ act(OriginalColoredProtectionApplication.radial_ge_one) (i,c)
  obtain ⟨hτ,_,hj⟩ := (all R₀ hR s).2.2.2.2 pOrder r hr i c
  exact ⟨hτ, fun j ↦ (hj ⟨j.val,j.isLt.trans_le (cutoffCount_mono hf hle)⟩).trans (min_le_left _ _)⟩

/-- The actual frame and individual scalar operator at this visited point.
There is no hypothesis that the resulting physical scalar norm is bounded. -/
def RowAction (F : E → Euclidean (embeddingDimension (d+1))) (J : ℕ)
    (i : Row) (z : Point) (τ C : ℝ) : Prop :=
  ∃ Q : {Q : E → Fin (d+1) → MetricTensor (d+1) //
    ContDiffOn ℝ ∞ Q (ball 0 (OriginalBoundary.R hn)) ∧
    cNorm (closedBall (0:E) (T(i)).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (d+1)) < (T(i)).family.threshold},
    Q.1 = projectedStress F ∧
    ∃ T₀ : Lp ℂ 2 (annularShellMeasure (n := d+1) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure E), ‖T₀‖ ^ 2 ≤ C ∧
      ∀ f, T₀ f =ᵐ[volume] fun x ↦ ∫ u,
        originalBareNativeKernel (T(i)) Q χ₀(i) center(i) (ρ(i)).2
          (sel(SelectedBoundary.hηb) i) (sel(SelectedBoundary.hr') i) τ (WithLp.toLp 2 z) x u * f u
            ∂annularShellMeasure (n := d+1) (refinedRadius (J := J))

/-- Before choosing `R₀` select the actual 36 constant for each original
incidence. Afterwards produce the bare row on EVERY active scalar point at
the exact full-band ceiling and original colored rate, uniformly in the single
physical Schwartz history (`app:ch_mean_pairs:eq:block-fields`). -/
theorem exists_on_history (hεbare : εframe ≤ frameMargin hn / (2*(6+1:ℝ)) / 2)
    {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hreserve : 20*((d+1)+1)+5 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d+1) +
      bandExponent*((rStar:ℝ)+((d+1:ℕ):ℝ)/2)+2 < (kMin:ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : Row → ℝ, (∀ i, 0 < C i) ∧
    ∀ R₀ ≥ S, ∀ (s : ℕ) (u : Fin s → SchwartzMap E (Euclidean (embeddingDimension (d+1))))
      (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let t := historyScale R₀ growthExponent s
      let F := RevisedGlobal.finiteMap (sourceDilation (H).map σ) u
      let J := cutoffCount (t^fineExponent)
      ∀ (i : Row) (c : Fin 3 → Fin (pOrder+1)) (z : Point), act(OriginalScalarCutoffs.β) i z ≠ 0 →
        bare(RowAction) F J i z ((act(OriginalColoredProtectionApplication.Rcolor) (i,c)*t^carrierExponent)⁻¹) (C i) := by
  let G := sourceDilationReference H hσ hσone
  have hR : OriginalBoundary.R hn < G.domain.chartRadius := by
    change OriginalBoundary.R hn < (H).domain.chartRadius
    rw [ReferenceBoundary.fact5 hn εframe hεframe qext hqcenter hqradius k hk hkD
      p orders margin extendedMargin hmargin hextendedMargin cap hcap]
    exact OriginalBoundary.R_lt_chartRadius hn
  obtain ⟨Sg,hSg,M,_,κ,hκ,geom⟩ := exists_scalar_physical_history_budgets G (OriginalBoundary.b_pos hn)
    (OriginalBoundary.b_lt_R hn) hR hB hreserve horder
  obtain ⟨Sf,_,frame⟩ := exists_frame_on_history hn εframe hεframe qext hqcenter hqradius k hk hkD
    p orders margin extendedMargin hmargin hextendedMargin cap hcap hεbare hσ hσone hB (by omega : 14 ≤ rStar) horder
  obtain ⟨Sr,_,rates⟩ := bare(exists_rate_threshold)
  have factory (i : Row) := continuation hn pa(i) χ₀(i) (bare(cutoff_support) i).1
    (sel(SelectedBoundary.hηb) i) (sel(SelectedBoundary.hr') i)
    (isCompact_closedBall (0:E) (OriginalBoundary.b hn)) (closedBall_subset_ball (OriginalBoundary.b_lt_R hn))
    (original_frameBall_subset hn pa(i)) M (show (0:ℝ)<1/4 by norm_num) hκ
  choose C hC applyC using factory
  refine ⟨max Sg (max Sf Sr),hSg.trans (le_max_left _ _),C,hC,?_⟩
  intro R₀ hR₀ s u ell hu t F J i c z hz
  have hgeom := geom R₀ ((le_max_left _ _).trans hR₀) s u ell hu
  have hraw := frame R₀ ((le_max_left _ _).trans ((le_max_right _ _).trans hR₀)) s u ell hu pa(i)
  obtain ⟨hF,hi,hRank,hM,hmet,hnorm⟩ := hgeom
  have hweak : cNorm (closedBall (0:E) (OriginalBoundary.b hn)) (20*((d+1-1)+1)+5) F ≤ M :=
    (cNorm_mono_order (by omega)).trans hM
  obtain ⟨low,now⟩ := applyC i F hF hi hRank hweak hmet hnorm hraw
  let Q : {q : E → Fin (d+1) → MetricTensor (d+1) //
      ContDiffOn ℝ ∞ q (ball 0 (OriginalBoundary.R hn)) ∧
      cNorm (closedBall (0:E) (T(i)).data.localReference.stateRadius) 6
        (q - fun _ ↦ cubeStress (d+1)) < (T(i)).family.threshold} :=
    ⟨projectedStress F,contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hRank),low⟩
  let τ := (act(OriginalColoredProtectionApplication.Rcolor) (i,c)*t^carrierExponent)⁻¹
  obtain ⟨hτ,hj⟩ := rates R₀ ((le_max_right _ _).trans ((le_max_right _ _).trans hR₀)) s i c
  have hroot := act(OriginalAdmission.root_mem) i.1.1 i.2
  have hwork := originalSamplingRadius_spec hn i.1.1 i.2 cell(i) hroot
  have hz' := OriginalChoices.Scalar.hβ_geometry (p := pOrder) hn i.1.1 i.2 cell(i) hroot z hz
  obtain ⟨T₀,hT,hact,_⟩ := now center(i) (ρ(i)).2 hwork.2.2.2.1 hwork.2.1
    (bare(cutoff_support) i).2 _ hz'.2 hz'.1 J hτ.ne'
    (fun j ↦ ⟨mul_nonneg hτ.le (by positivity),(hj j).trans (min_le_left _ _)⟩)
    (fun j ↦ by rw [abs_of_nonneg (mul_nonneg hτ.le (by positivity))]; exact (hj j).trans (min_le_right _ _))
  exact ⟨Q,rfl,T₀,hT,hact⟩

end JanetCartan.PhysicalSampling.OriginalBare
