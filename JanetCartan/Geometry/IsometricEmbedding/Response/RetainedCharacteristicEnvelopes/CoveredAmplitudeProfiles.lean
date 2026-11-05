module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.CompleteAmplitudeProfiles
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.RetainedConstruction.Coverage
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointBounds

/-!
# Complete supported amplitude grades on the original selected band

The physical retarded constructor already retains diagonal frequency coverage
on the same radial band as its amplitudes. That coverage also normalizes every
elapsed joint derivative. The contraction preserves every derivative order,
so no additional tail-band comparison is required. Both selected factors use
the original Q/B budgets, with the full residual and physical multiplier.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral SymbolBudgets
open RegularSector.FinitePdo.RetainedConstruction
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "JPoint" => SymbolBudgets.TwoTimePoint d

/-- The retained diagonal frequency coverage also controls every complete
elapsed joint amplitude jet, on the SAME radial band. Its dilation is at least
one, so pulling derivatives back loses no constant. Consumer: the complete
frequency input of `fullSource_physical_incidence_solver_residual_envelopes`
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_complete_amplitude_jet_le_of_diagonal_coverage
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)}
    {ε εband src ra rb : ℝ} (hε : 0 < ε) (hsrc : src ≤ ε) (hεband : ε ≤ εband)
    {β : E → ℂ} (hcoverage : DiagonalFrequencyCoverage ℓ z.2.2 εband ra rb β)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (j : ℕ) (hbudget : BoundedTwoTimeOrderSeminorm 0
      (bufferedJetSet ℓ z εband ra rb) j W)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z (ε / 2)) (hξ : ξ ∈ tsupport β) :
    ‖iteratedFDeriv ℝ j (jointAmplitude W) (elapsedPoint t ((x, 0), ξ))‖ ≤
      twoTimeOrderSeminorm 0 (bufferedJetSet ℓ z εband ra rb) j W := by
  obtain ⟨R,hR,η,hη,he,_⟩ := hcoverage ξ hξ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let N : JPoint →L[ℝ] JPoint :=
    (ContinuousLinearMap.fst ℝ _ _).prod (R⁻¹ • ContinuousLinearMap.snd ℝ _ _)
  have hN : ‖N‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change max ‖v.1‖ ‖R⁻¹ • v.2‖ ≤ 1 * ‖v‖
    rw [one_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
    exact max_le (norm_fst_le v) ((mul_le_of_le_one_left (norm_nonneg _)
      (inv_le_one_of_one_le₀ hR)).trans (norm_snd_le v))
  have hs : ContDiff ℝ ∞ (twoTimeOrderField 0 R W) := by
    simp only [twoTimeOrderField, pow_zero, one_smul]
    exact hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))
  have hcomp : twoTimeOrderField 0 R W ∘ N = jointAmplitude W := by
    funext v
    change R ^ 0 • jointAmplitude W (v.1, R • (R⁻¹ • v.2)) = _
    simp only [pow_zero, one_smul, smul_inv_smul₀ hRpos.ne']
  have hjet := Pseudodifferential.norm_iteratedFDeriv_comp_linear_le N
    (twoTimeOrderField 0 R W) hs j (elapsedPoint t ((x, 0), ξ))
  rw [hcomp] at hjet
  have hnorm := hjet.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg N) hN))
  have htε : t ∈ Icc (0 : ℝ) ε := ⟨ht.1, by linarith only [ht.2,hsrc,hε]⟩
  have hxε : x ∈ elapsedPhysicalBox z ε :=
    ⟨ball_subset_ball (by linarith) hx.1,ball_subset_ball (by linarith) hx.2⟩
  have hb := elapsed_mem_bufferedBase hε htε hxε
  have hb' : (x 0, (x 0-t, spatialPart x)) ∈
      closedBall z.1 (2*εband) ×ˢ (closedBall z.1 (2*εband) ×ˢ
        closedBall z.2.1 (2*εband)) := by
    have hh := closedBall_subset_closedBall (by linarith : 2*ε ≤ 2*εband)
      (ball_subset_closedBall hb)
    simpa only [mem_prod, mem_closedBall, Prod.dist_eq, max_le_iff] using hh
  have hmem : N (elapsedPoint t ((x,0),ξ)) ∈ bufferedJetSet ℓ z εband ra rb := by
    change ((elapsedPoint t ((x,0),ξ)).1, R⁻¹ • (elapsedPoint t ((x,0),ξ)).2) ∈ _
    rw [elapsedPoint_eq,he,inv_smul_smul₀ hRpos.ne']
    exact ⟨hb',hη⟩
  exact hnorm.trans ((norm_iteratedFDeriv_le_cNorm
    (isCompact_bufferedJetSet ℓ z εband ra rb)
    (hs.of_le (by simp : (j : ℕ∞ω) ≤ ∞)) hmem le_rfl).trans
      (cNorm_twoTimeOrderField_le hbudget hR))

open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAssembly RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RetainedFactors FullSourceEnvelopes DirectEvolution AnnularSobolev
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open ConicAmplitude AmplitudeBounds
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
  {A₀ : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- The original diagonal coverage supplies the complete-frequency bounds
for the SAME selected solver and full residual, without any additional radial
band comparison. Reserve twelve pays shifts ten/nine of the original Q/B
budgets; constants precede every admitted history and frequency. The multiplier
remains the physical cutoff at `2*threshold`, including its full shoulder.
Consumers: the complementary part of the retained full-source envelope and the
complete normalized response (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_selected_history_supported_amplitude_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K₀ M) (p : f.centers)
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hreserve : 12 ≤ rStar)
    (horder : displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {ε ra rb : ℝ} (hε : 0 < ε)
    (hεbuffer : ε ≤ (f.chart p).bufferRadius / 2)
    (hsrc : (f.chart p).maskRadius ≤ ε)
    (threshold : ℝ)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) :
    let c := f.chart p
    let z : RootState (Euclidean d) := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    RetainedConstruction.DiagonalFrequencyCoverage c.radialSection z.2.2
      (c.bufferRadius/2) ra rb (selectedEndpointMultiplier f p threshold) →
    ∃ S₀ : ℝ, 2 ≤ S₀ ∧ ∃ Bamp : ℕ → ℝ, (∀ j, 0 ≤ Bamp j) ∧
      ∀ R₀, S₀ ≤ R₀ →
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
      ∀ t ∈ Icc 0 (3*c.maskRadius/4),
      ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      ∀ j y, y ∈ elapsedPhysicalBox z (ε/2) → ∀ o : Fin 2,
        ‖iteratedFDeriv ℝ j (jointAmplitude (if o = 0 then W 0 + W 1 else W 2))
          (elapsedPoint t ((y, 0), ξ))‖ ≤ Bamp j * currentCoefficientScale R₀ n ^ j := by
  intro c z hcoverage
  obtain ⟨S₀,hS₀,AQ,AB,hAQ,hAB,hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles Gref hr hrR hR ext
      hextcenter hextradius (reserve := 10) (by omega) hreserve horder
  let Bamp := fun j ↦ (2 * D j) * (1 + AQ (j+10) + AB (j+9))
  have hBamp j : 0 ≤ Bamp j := mul_nonneg (mul_nonneg (by norm_num) (hD j))
    (add_nonneg (add_nonneg zero_le_one (hAQ _)) (hAB _))
  refine ⟨S₀,hS₀,Bamp,hBamp,?_⟩
  intro R₀ hR₀ n u ell hu Q B Φ chart angular hsm W hbudget t ht ξ hξ j y hy o
  have hL := one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) n
  obtain ⟨hq,hb⟩ := (hcoeff R₀ hR₀ n u ell hu).2.2
    (closedBall x RQ) (isCompact_closedBall x RQ)
  have hq' : cNorm (closedBall x RQ) (j+10) Q ≤ AQ (j+10) * currentCoefficientScale R₀ n ^ j := by
    simpa only [Nat.add_sub_cancel] using hq (j+10)
  have hb' : cNorm (closedBall x RQ) (j+9) B ≤ AB (j+9) * currentCoefficientScale R₀ n ^ j :=
    (hb (j+9)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (hAB _))
  have hpair : 1 + cNorm (closedBall x RQ) (j+10) Q + cNorm (closedBall x RQ) (j+9) B ≤
      (1 + AQ (j+10) + AB (j+9)) * currentCoefficientScale R₀ n ^ j := by
    have h1 := one_le_pow₀ hL (n := j)
    nlinarith only [hq',hb',h1]
  have hW (k : Fin 3) : ContDiff ℝ ∞ (jointAmplitude (W k)) :=
    (hsm k).comp (contDiff_fst.fst.prodMk
      (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  have hsum := solver_coefficient_bound (closedBall x RQ) Q B
    (isCompact_bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb)
    (hW 0) (hW 1) D (by simpa using hbudget 0) (by simpa using hbudget 1) j
  have hres := hbudget 2 j
  simp only [show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hres
  have hz := correction_order_zero_bound (hW 2) hres.1
  by_cases ho : o = 0
  · rw [ite_eq_left ho]
    apply ((retained_complete_amplitude_jet_le_of_diagonal_coverage c.radialSection hε hsrc hεbuffer hcoverage
      (W 0 + W 1) ((hW 0).add (hW 1)) j hsum.1 ht hy hξ).trans hsum.2).trans
    exact (mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num) (hD j))).trans_eq
      (by dsimp only [Bamp]; ring)
  · rw [ite_eq_right ho]
    apply ((retained_complete_amplitude_jet_le_of_diagonal_coverage c.radialSection hε hsrc hεbuffer hcoverage
      (W 2) (hW 2) j hz.1 ht hy hξ).trans (hz.2.trans hres.2)).trans
    apply (mul_le_mul_of_nonneg_left hpair (hD j)).trans
    dsimp only [Bamp]
    have hnn : 0 ≤ D j * (1+AQ (j+10)+AB (j+9)) * currentCoefficientScale R₀ n ^ j :=
      mul_nonneg (mul_nonneg (hD j)
        (add_nonneg (add_nonneg zero_le_one (hAQ _)) (hAB _)))
        (pow_nonneg (zero_le_one.trans hL) _)
    nlinarith only [hnn]


end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
