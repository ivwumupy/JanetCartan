module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Support
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.LocalIntegral

/-!
# The actual normalized external source jet

For `app:ch_response:lem:energy-carrier-jets`, the external variable is the
pair of carrier parameter and output position. The phase is the entire
physical phase, or the entire demodulated phase. Its normalization is applied
AFTER differentiation. The consumer is `norm_annularSourceIntegral_le`.

These algebraic, support and regularity deductions require no bound on a
modified amplitude. Quantitative profiles must still be derived from the
original phase, symbol, masks and envelope.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open JanetCartan.Localization
open Complement.ParameterDerivatives

variable {P Z F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Actual external derivative with its unchanged phase removed afterwards.
Source: `app:ch_response:lem:energy-carrier-jets`. In particular a demodulated
phase must include the output carrier before taking `iteratedFDeriv`. -/
def normalizedExternalJet (ψ : P → Z → ℝ) (u : P → Z → F)
    (j : ℕ) (v : Fin j → P) (p : P) (z : Z) : F :=
  phaseOscillation (fun y => -ψ p y) z •
    iteratedFDeriv ℝ j (fun q => phaseOscillation (ψ q) z • u q z) p v

/-- Normalization exactly reconstructs the original differentiated integrand
of `app:ch_response:lem:energy-carrier-jets`. -/
theorem phaseOscillation_smul_normalizedExternalJet
    (ψ : P → Z → ℝ) (u : P → Z → F)
    (j : ℕ) (v : Fin j → P) (p : P) (z : Z) :
    phaseOscillation (ψ p) z • normalizedExternalJet ψ u j v p z =
      iteratedFDeriv ℝ j (fun q => phaseOscillation (ψ q) z • u q z) p v := by
  simp only [normalizedExternalJet, smul_smul, phaseOscillation, Complex.ofReal_neg]
  rw [← Complex.exp_add]
  simp

/-- At external order zero the actual normalized jet is precisely the
original vector amplitude (`app:ch_response:lem:energy-carrier-jets`). -/
theorem normalizedExternalJet_zero (ψ : P → Z → ℝ) (u : P → Z → F)
    (v : Fin 0 → P) (p : P) : normalizedExternalJet ψ u 0 v p = u p := by
  funext z
  simp only [normalizedExternalJet, iteratedFDeriv_zero_apply, smul_smul,
    phaseOscillation, Complex.ofReal_neg]
  rw [← Complex.exp_add]
  simp

/-- Pointwise normalization preserves the external derivative norm. This
identity alone supplies no bounds for its positive source derivatives.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_normalizedExternalJet (ψ : P → Z → ℝ) (u : P → Z → F)
    (j : ℕ) (v : Fin j → P) (p : P) (z : Z) :
    ‖normalizedExternalJet ψ u j v p z‖ =
      ‖iteratedFDeriv ℝ j (fun q => phaseOscillation (ψ q) z • u q z) p v‖ := by
  simp only [normalizedExternalJet, norm_smul, norm_phaseOscillation, one_mul]

/-- A locally zero original amplitude gives zero actual normalized external
jets. This is used outside the common source support and on selector plateaus.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem normalizedExternalJet_eq_zero_of_eventuallyEq
    (ψ : P → Z → ℝ) (u : P → Z → F) (j : ℕ) (v : Fin j → P)
    (p : P) (z : Z) (hu : (fun q => u q z) =ᶠ[𝓝 p] fun _ => 0) :
    normalizedExternalJet ψ u j v p z = 0 := by
  have he : (fun q => phaseOscillation (ψ q) z • u q z) =ᶠ[𝓝 p] fun _ => (0 : F) := by
    filter_upwards [hu] with q hq
    simp only [hq, smul_zero]
  unfold normalizedExternalJet
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  cases j <;> simp

variable [NormedAddCommGroup Z]

/-- Every normalized external jet retains the same closed source support,
without regularity assumptions on the phase away from that support. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem tsupport_normalizedExternalJet_subset
    {V : Set P} {S : Set Z} (hV : IsOpen V) (hS : IsClosed S)
    (ψ : P → Z → ℝ) (u : P → Z → F)
    (hs : ∀ q ∈ V, tsupport (u q) ⊆ S)
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    tsupport (normalizedExternalJet ψ u j v p) ⊆ S := by
  apply closure_minimal _ hS
  intro z hz
  by_contra hzs
  apply hz
  apply normalizedExternalJet_eq_zero_of_eventuallyEq
  filter_upwards [hV.mem_nhds hp] with q hq
  exact image_eq_zero_of_notMem_tsupport (fun h => hzs (hs q hq h))

variable [NormedSpace ℝ Z]

/-- Source derivatives also retain the fixed support used by
`norm_annularSourceIntegral_le`; its volume is independent of both orders.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem tsupport_iteratedFDeriv_normalizedExternalJet_subset
    {V : Set P} {S : Set Z} (hV : IsOpen V) (hS : IsClosed S)
    (ψ : P → Z → ℝ) (u : P → Z → F)
    (hs : ∀ q ∈ V, tsupport (u q) ⊆ S)
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) (k : ℕ) :
    tsupport (iteratedFDeriv ℝ k (normalizedExternalJet ψ u j v p)) ⊆ S :=
  (tsupport_iteratedFDeriv_subset k).trans
    (tsupport_normalizedExternalJet_subset hV hS ψ u hs j v hp)

/-- Original joint smoothness on a neighborhood of the fixed support suffices
for the literal oscillating amplitude globally in the source variable. No
extension of the phase or change of the literal function is made.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_oscillatingAmplitude_localized
    {V : Set P} {U S : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U)
    {ψ : P → Z → ℝ} {u : P → Z → F}
    (hψ : ContDiffOn ℝ ∞ (Function.uncurry ψ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ univ))
    (hs : ∀ q ∈ V, tsupport (u q) ⊆ S) :
    ContDiffOn ℝ ∞ (fun q : P × Z => phaseOscillation (ψ q.1) q.2 • u q.1 q.2)
      (V ×ˢ univ) := by
  intro q hq
  by_cases hz : q.2 ∈ U
  · have hp := hψ.contDiffAt ((hV.prod hU).mem_nhds ⟨hq.1, hz⟩)
    have ha := hu.contDiffAt ((hV.prod isOpen_univ).mem_nhds hq)
    exact ((((Complex.ofRealCLM.contDiff.contDiffAt.comp q hp).mul
      contDiffAt_const).cexp).smul ha).contDiffWithinAt
  · have hn : q.2 ∉ S := fun h => hz (hSU h)
    have he : (fun w : P × Z => phaseOscillation (ψ w.1) w.2 • u w.1 w.2)
        =ᶠ[𝓝 q] fun _ => (0 : F) := by
      filter_upwards [continuousAt_fst.preimage_mem_nhds (hV.mem_nhds hq.1),
        continuousAt_snd.preimage_mem_nhds (hS.isOpen_compl.mem_nhds hn)] with w hw hwz
      have ha : u w.1 w.2 = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hwz (hs w.1 hw h))
      rw [ha, smul_zero]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

/-- The normalized external jet is source-smooth, using only original joint
regularity and one common support. This supplies the smoothness premise of
`norm_annularSourceIntegral_le` at every fixed external order.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiff_normalizedExternalJet
    {V : Set P} {U S : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U)
    {ψ : P → Z → ℝ} {u : P → Z → F}
    (hψ : ContDiffOn ℝ ∞ (Function.uncurry ψ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ univ))
    (hs : ∀ q ∈ V, tsupport (u q) ⊆ S)
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    ContDiff ℝ ∞ (normalizedExternalJet ψ u j v p) := by
  have hj := contDiffOn_oscillatingAmplitude_localized hV hU hS hSU hψ hu hs
  have hd := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => P) F v).contDiff
    |>.comp_contDiffOn (contDiffOn_parameterIteratedFDeriv hV hj j)
  have hdz := hd.comp (s := U) (contDiffOn_const.prodMk contDiffOn_id)
    (fun z _ => ⟨hp, mem_univ z⟩)
  have hpz : ContDiffOn ℝ ∞ (ψ p) U :=
    hψ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨hp, hz⟩)
  apply contDiff_of_contDiffOn_support_neighborhood hU _
    ((tsupport_normalizedExternalJet_subset hV hS ψ u hs j v hp).trans hSU)
  exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn hpz.neg).mul
    contDiffOn_const).cexp).smul hdz

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
