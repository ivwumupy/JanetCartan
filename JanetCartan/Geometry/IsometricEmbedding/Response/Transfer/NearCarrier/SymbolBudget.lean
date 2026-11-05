module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.LowOperator
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Amplitude
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.WeightedJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds.Carrier

/-!
# Physical symbol budgets for selected modified amplitudes

The consumer is the low L² step of `app:ch_response:eq:direct-envelope-profile`.
An amplitude supported in `‖δ‖ ≤ b * ρ` is normalized in the displacement
variable alone. Joint normalized jets control the actual full source-symbol
budget, with a constant independent of `ρ ≥ 1`. Both physical positions and
all cutoff shoulders remain in the differentiated function. The final theorem
derives the budget of a differential expression from its primitive jets; a
modified-amplitude or operator estimate is never an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NearCarrierSymbol
open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles FirstOutputJets SourceExpansion FullLowBounds
open IsometricEmbedding.Response.NearCarrier
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Recover the physical-displacement amplitude from its normalized function.
The two physical positions are fixed by this map. Consumer: the realization
family in `app:ch_response:eq:direct-envelope-profile`. -/
def physicalAmplitudeOfNormalized (ρ : ℝ) (a : Point n → Mat) : FullAmplitude n r :=
  fun x y δ ↦ a ((x, y), ρ⁻¹ • δ)

/-- Normalization and physical recovery are inverse for nonzero frequency,
including every mask in the amplitude (`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedField_physicalAmplitudeOfNormalized {ρ : ℝ} (hρ : ρ ≠ 0)
    (a : Point n → Mat) :
    normalizedField ρ (uncurry (physicalAmplitudeOfNormalized ρ a)) = a := by
  funext p
  simp [normalizedField, uncurry, physicalAmplitudeOfNormalized, smul_smul, hρ]

/-- Physical recovery preserves smoothness of the complete normalized field.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_physicalAmplitudeOfNormalized (ρ : ℝ) {a : Point n → Mat}
    (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (uncurry (physicalAmplitudeOfNormalized ρ a)) :=
  ha.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))

/-- The fixed normalized selector support becomes exactly a radius proportional
to frequency. In particular the closed shoulders are retained for the symbol
conversion (`app:ch_response:eq:direct-envelope-profile`). -/
theorem support_physicalAmplitudeOfNormalized {ρ b : ℝ} (hρ : 0 < ρ)
    {a : Point n → Mat} (hs : ∀ p ∈ tsupport a, ‖p.2‖ ≤ b) :
    ∀ p ∈ tsupport (uncurry (physicalAmplitudeOfNormalized ρ a)), ‖p.2‖ ≤ b * ρ := by
  intro p hp
  have hm := tsupport_comp_subset_preimage a
    (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)) hp
  have h := hs (p.1, ρ⁻¹ • p.2) hm
  dsimp only at h
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)] at h
  exact (inv_mul_le_iff₀ hρ).mp h |>.trans_eq (mul_comm ρ b)

/-- The selected amplitude is the physical recovery of its literal normalized
full expression. The shift is in physical covectors and the original two
positions are unchanged. This identifies the initial primitive for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem physicalAmplitudeOfNormalized_selected (A : FullAmplitude n r)
    (ζ : E) {ρ : ℝ} (hρ : ρ ≠ 0) (q : E → ℂ) :
    physicalAmplitudeOfNormalized ρ
      (fun p : Point n ↦ q p.2 • A p.1.1 p.1.2 (ρ • (ζ + p.2))) =
      forwardSelectedAmplitude A ζ ρ (fun δ ↦ q (ρ⁻¹ • δ)) := by
  funext x y δ
  simp [physicalAmplitudeOfNormalized, forwardSelectedAmplitude, selectedAmplitude,
    smul_add, smul_smul, hρ]

/-- One normalized covector derivative pays exactly one physical radius.
This is the conversion used before applying the low calculus in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem weighted_jet_le_normalized_jet
    {A : FullAmplitude n r} (hA : ContDiff ℝ ∞ (uncurry A))
    {ρ : ℝ} (hρ : 0 < ρ) (w : List (Coordinate n)) (x y δ : E) :
    ρ ^ frequencyOrder w * ‖jet w A x y δ‖ ≤
      ‖iteratedFDeriv ℝ w.length (normalizedField ρ (uncurry A))
        ((x, y), ρ⁻¹ • δ)‖ := by
  have h := norm_transportMixedJet_weight_le w.length hρ isOpen_univ
    (hA.of_le (by simp)).contDiffOn ((x, y), ρ⁻¹ • δ) (mem_univ _)
    (frequencySlots w) (fun i ↦ coordinateDirection (w.get i))
    (coordinateDirection_slots w) (fun i ↦ (norm_coordinateDirection (w.get i)).le)
  rw [card_frequencySlots] at h
  have he := jet_eq_iteratedFDeriv isOpen_univ hA.contDiffOn w
    (p := ((x, y), δ)) (mem_univ _)
  simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, ← he, uncurry] at h
  convert h using 1
  unfold PrimitiveProfiles.normalizedField uncurry
  rfl

/-- The full physical source-symbol budget follows from finite normalized
joint jets on the closed selector support. The factor `(1+b)^N` is fixed
before frequency, amplitude size, and datum. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasFullSourceSymbolBound_of_normalized_jets
    {A : FullAmplitude n r} (hA : ContDiff ℝ ∞ (uncurry A))
    {ρ b B : ℝ} (hρ : 1 ≤ ρ) (hb : 0 ≤ b) (hB : 0 ≤ B) (N : ℕ)
    (hs : ∀ p ∈ tsupport (uncurry A), ‖p.2‖ ≤ b * ρ)
    (hj : ∀ j ≤ N, ∀ p, ‖iteratedFDeriv ℝ j (normalizedField ρ (uncurry A)) p‖ ≤ B) :
    HasFullSourceSymbolBound A N ((1 + b) ^ N * B) := by
  have ha : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2) :=
    hA.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  have hB' : 0 ≤ (1 + b) ^ N * B := mul_nonneg (pow_nonneg (by linarith) _) hB
  have hw : ∀ w : List (Coordinate n), w.length ≤ N → ∀ x y δ,
      (1 + ‖δ‖) ^ frequencyOrder w * ‖jet w A x y δ‖ ≤ (1 + b) ^ N * B := by
    intro w hw x y δ
    by_cases hp : ((x, y), δ) ∈ tsupport (uncurry A)
    · have hscale : 1 + ‖δ‖ ≤ (1 + b) * ρ := by
        have := hs ((x, y), δ) hp
        dsimp only at this
        nlinarith
      have horder : frequencyOrder w ≤ N :=
        List.countP_le_length.trans hw
      calc
        _ ≤ ((1 + b) * ρ) ^ frequencyOrder w * ‖jet w A x y δ‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale _)
            (norm_nonneg _)
        _ = (1 + b) ^ frequencyOrder w * (ρ ^ frequencyOrder w * ‖jet w A x y δ‖) := by
          rw [mul_pow]; ring
        _ ≤ (1 + b) ^ frequencyOrder w * B :=
          mul_le_mul_of_nonneg_left
            ((weighted_jet_le_normalized_jet hA (lt_of_lt_of_le zero_lt_one hρ) w x y δ).trans
              (hj w.length hw _)) (pow_nonneg (by linarith) _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) horder) hB
    · have hz : jet w A x y δ = 0 :=
        image_eq_zero_of_notMem_tsupport (f := uncurry (jet w A))
          (fun hm ↦ hp (tsupport_jet_subset w A hm))
      simpa only [hz, norm_zero, mul_zero] using hB'
  simpa only [one_pow, one_mul] using hasFullSourceSymbolBound_of_weighted_jets
    ha N (fun δ ↦ 1 + ‖δ‖) (c := 1) le_rfl hB' (fun _ ↦ by simp) hw

/-- The actual modified full amplitude has precisely the `L^k` budget needed
by `FullLow`. The equality identifies its normalized function with the literal
differential expression, not with a claimed bound. Only primitive jets through
`c+k` are used, with the paper's strict reserve `R > c+2`. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasFullSourceSymbolBound_of_expression
    {ι : Type*} (a : ι → Point n → Mat) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (e : AmplitudeExpression (Point n) Mat ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R k : ℕ) (hR : c + 2 < R) (hcost : e.derivativeCost ≤ k)
    {L ρ b : ℝ} (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (hb : 0 ≤ b)
    (hj : ∀ i j, j ≤ c + k → ∀ p,
      ‖iteratedFDeriv ℝ j (a i) p‖ ≤ M i j * L ^ (j + 2 - R))
    {A : FullAmplitude n r} (hA : ContDiff ℝ ∞ (uncurry A))
    (he : normalizedField ρ (uncurry A) = e.evaluate a)
    (hs : ∀ p ∈ tsupport (uncurry A), ‖p.2‖ ≤ b * ρ) :
    HasFullSourceSymbolBound A c
      (((1 + b) ^ c * e.lowJetConstant M c) * L ^ k) := by
  rw [mul_assoc]
  apply hasFullSourceSymbolBound_of_normalized_jets hA hρ hb
    (mul_nonneg (e.lowJetConstant_nonneg M hM c) (pow_nonneg (zero_le_one.trans hL) _)) c hs
  intro j hje p
  rw [he]
  exact e.norm_lowJet_evaluate_le M hM c R k hR hcost L hL a ha hj j hje p

/-- Apply the symbol budget directly to physical recovery of the actual
modified expression. Its normalized identity and closed selector support are
proved above, so neither is an extra analytic hypothesis. This is the low
input for the normalized operator family in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasFullSourceSymbolBound_physical_expression
    {ι : Type*} (a : ι → Point n → Mat) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (e : AmplitudeExpression (Point n) Mat ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R k : ℕ) (hR : c + 2 < R) (hcost : e.derivativeCost ≤ k)
    {L ρ b : ℝ} (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (hb : 0 ≤ b)
    (hj : ∀ i j, j ≤ c + k → ∀ p,
      ‖iteratedFDeriv ℝ j (a i) p‖ ≤ M i j * L ^ (j + 2 - R))
    (hs : ∀ p ∈ tsupport (e.evaluate a), ‖p.2‖ ≤ b) :
    HasFullSourceSymbolBound (physicalAmplitudeOfNormalized ρ (e.evaluate a)) c
      (((1 + b) ^ c * e.lowJetConstant M c) * L ^ k) := by
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  exact hasFullSourceSymbolBound_of_expression a ha e M hM c R k hR hcost hL hρ hb hj
    (contDiff_physicalAmplitudeOfNormalized ρ (e.contDiff_evaluate a ha))
    (normalizedField_physicalAmplitudeOfNormalized hρpos.ne' _)
    (support_physicalAmplitudeOfNormalized hρpos hs)

end JanetCartan.ResponseTransfer.NearCarrierSymbol
