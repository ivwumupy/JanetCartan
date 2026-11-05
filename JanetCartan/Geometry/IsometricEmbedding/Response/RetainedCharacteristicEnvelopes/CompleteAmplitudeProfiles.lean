module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectedAmplitudeProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedGraphFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AnnularCriticalCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.AnnularInput
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Amplitudes

/-!
# Complete-frequency history bounds for the original selected amplitudes

The complementary part of the envelope retains the full multiplier support.
Normalize each covector into the original fixed tail band, apply the selected
symbol budgets, and substitute the concrete history coefficient profiles.
The full zeroth coefficient and the original shifts ten/nine are retained.
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

/-- The SAME selected solver and full residual have complete-frequency
joint amplitude bounds on the entire elapsed interval. The original raw symbol
costs are the outputs of `ProtectedConstruction.FullSource`; reserve twelve
pays the coefficient shifts ten and nine. The two tail-band comparisons must
be supplied by that producer on its original `ra,rb` witnesses. No amplitude
jet or envelope conclusion is an additional premise
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_history_complete_amplitude_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K₀ M) (p : f.centers)
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hreserve : 12 ≤ rStar)
    (horder : displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {ε aperture ra rb : ℝ} (hε : 0 < ε)
    (hεbuffer : ε ≤ (f.chart p).bufferRadius / 2)
    (hAp : 0 ≤ aperture) (hsrc : (f.chart p).maskRadius ≤ ε)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) :
    let c := f.chart p
    let z : RootState (Euclidean d) := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    ra ≤ (1/3)/(1 + aperture + ‖z.2.2‖ + ε) →
    1 + ‖c.radialSection‖ ≤ rb →
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
      ∀ ξ ∈ retainedFrequencyDomain c.radialSection z ε aperture (1/2),
      ∀ j y, y ∈ elapsedPhysicalBox z (ε/2) → ∀ o : Fin 2,
        ‖iteratedFDeriv ℝ j (jointAmplitude (if o = 0 then W 0 + W 1 else W 2))
          (elapsedPoint t ((y, 0), ξ))‖ ≤ Bamp j * currentCoefficientScale R₀ n ^ j := by
  intro c z hra hrb
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
  let a := (1/3)/(1+aperture+‖z.2.2‖+ε)
  let Jtail := bufferedJetSet c.radialSection z ε a (1+‖c.radialSection‖)
  have htail k m : BoundedTwoTimeOrderSeminorm (if k = 0 then 0 else 1) Jtail m (W k) ∧
      twoTimeOrderSeminorm (if k = 0 then 0 else 1) Jtail m (W k) ≤
        D m * (1 + cNorm (closedBall x RQ) (m+10) Q + cNorm (closedBall x RQ) (m+9) B) := by
    obtain ⟨hf,hle⟩ := retained_amplitude_restriction_band c.radialSection z hεbuffer hra hrb
      (hW k) (hbudget k m).1
    exact ⟨hf, hle.trans (hbudget k m).2⟩
  have hsum := solver_coefficient_bound (closedBall x RQ) Q B
    (isCompact_bufferedJetSet c.radialSection z ε a (1+‖c.radialSection‖))
    (hW 0) (hW 1) D (by simpa using htail 0) (by simpa using htail 1) j
  have hres := htail 2 j
  simp only [show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hres
  have hz := correction_order_zero_bound (hW 2) hres.1
  by_cases ho : o = 0
  · rw [ite_eq_left ho]
    apply ((retained_complete_amplitude_jet_le c.radialSection hε hsrc hAp
      (W 0 + W 1) ((hW 0).add (hW 1)) j hsum.1 ht hy hξ).trans hsum.2).trans
    exact (mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num) (hD j))).trans_eq
      (by dsimp only [Bamp]; ring)
  · rw [ite_eq_right ho]
    apply ((retained_complete_amplitude_jet_le c.radialSection hε hsrc hAp
      (W 2) (hW 2) j hz.1 ht hy hξ).trans (hz.2.trans hres.2)).trans
    apply (mul_le_mul_of_nonneg_left hpair (hD j)).trans
    dsimp only [Bamp]
    have hnn : 0 ≤ D j * (1+AQ (j+10)+AB (j+9)) * currentCoefficientScale R₀ n ^ j :=
      mul_nonneg (mul_nonneg (hD j)
        (add_nonneg (add_nonneg zero_le_one (hAQ _)) (hAB _)))
        (pow_nonneg (zero_le_one.trans hL) _)
    nlinarith only [hnn]

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
