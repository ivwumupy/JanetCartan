module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Grades
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.FullAmplitude

/-!
# Source bounds after exact external-jet normalization

The actual normalized derivative equals a finite vector polynomial before any
source differentiation. This gives fixed frequency and scale losses for each
external order. The parent amplitude construction must still produce the
original joint amplitude profile for the literal elapsed symbol times envelope.
No bound on the normalized derivative itself is assumed here.

Consumer: `norm_annularSourceIntegral_le` in
`app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open Complement.ParameterDerivatives.MixedGrades JanetCartan.Localization
variable {P Z F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Exact finite expansion of the normalized actual derivative, with the
phase removed after differentiation. The frequency degree is at most `j`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem normalizedExternalJet_scaled_eq_polynomial
    {V : Set P} (hV : IsOpen V) {φ : P → Z → ℝ} {u : P → Z → F}
    (ρ : ℝ) (z : Z)
    (hφ : ContDiffOn ℝ ∞ (fun p => φ p z) V)
    (hu : ContDiffOn ℝ ∞ (fun p => u p z) V)
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    normalizedExternalJet (fun q y => ρ * φ q y) u j v p z =
      ∑ b : CarrierJetBranch j, (ρ : ℂ) ^ carrierJetDegree b •
        vectorCarrierCoefficient (fun q => Complex.I * (φ q z : ℂ))
          (fun q => u q z) j v b p := by
  have hc : ContDiffOn ℝ ∞ (fun p => Complex.I * (φ p z : ℂ)) V :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)
  have he (q : P) : Complex.exp ((ρ : ℂ) * (Complex.I * (φ q z : ℂ))) =
      phaseOscillation (fun y => ρ * φ q y) z := by
    unfold phaseOscillation
    congr 1
    push_cast
    ring
  have h := iteratedFDeriv_exp_smul_eq_vectorCarrierPolynomial hV hc hu (ρ : ℂ) j v hp
  simp_rw [he] at h
  unfold normalizedExternalJet
  rw [h, smul_smul]
  simp only [phaseOscillation, ← Complex.exp_add, Complex.ofReal_neg]
  simp

/-- Quantitative source derivatives of the ACTUAL normalized external jet,
uniform over all unit external direction tuples. At fixed `j`, the losses
are `ρ^j K^j`, independent of source order `k` and integration order `N`.
The source dependence is one factor `K^k`. The phase and original amplitude
profiles are consumed only through `k+j`; no modified profile is an input.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_normalizedExternalJet_source_le
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {φ : P → Z → ℝ} {u : P → Z → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (H Q : ℕ → ℝ) (hH : ∀ k, 0 ≤ H k) (hQ : ∀ k, 0 ≤ Q k)
    {K A ρ : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hρ : 1 ≤ ρ)
    (j : ℕ) (v : Fin j → P) (hv : ∀ i, ‖v i‖ ≤ 1)
    {p : P} (hp : p ∈ V) {z : Z} (hz : z ∈ U) (k : ℕ)
    (hphase : ∀ m ≤ k + j,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (p, z)‖ ≤ H m * K ^ m)
    (hamplitude : ∀ m ≤ k + j,
      ‖iteratedFDeriv ℝ m (Function.uncurry u) (p, z)‖ ≤ Q m * A * K ^ m) :
    ‖iteratedFDeriv ℝ k (normalizedExternalJet (fun q y => ρ * φ q y) u j v p) z‖ ≤
      externalJetBudget H Q j k * (A * ρ ^ j * K ^ j) * K ^ k := by
  let ψ : P → Z → ℂ := fun q y => Complex.I * (φ q y : ℂ)
  have hψ : ContDiffOn ℝ ∞ (Function.uncurry ψ) (V ×ˢ U) :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)
  let f : P × Z → F := fun q => ∑ b : CarrierJetBranch j,
    (ρ : ℂ) ^ carrierJetDegree b •
      vectorCarrierCoefficient (fun p => ψ p q.2) (fun p => u p q.2) j v b q.1
  have hf : ContDiffOn ℝ ∞ f (V ×ˢ U) :=
    ContDiffOn.sum fun b _ =>
      (contDiffOn_vectorCarrierCoefficient_joint hV hU hψ hu j v b).const_smul _
  have he : normalizedExternalJet (fun q y => ρ * φ q y) u j v p =ᶠ[𝓝 z]
      fun y => f (p, y) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact normalizedExternalJet_scaled_eq_polynomial hV ρ y
      (hφ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun q hq => ⟨hq, hy⟩))
      (hu.comp (contDiffOn_id.prodMk contDiffOn_const) (fun q hq => ⟨hq, hy⟩)) j v hp
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  let T : Z →L[ℝ] P × Z := (0 : Z →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Z)
  have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one (fun y => by simp [T, Prod.norm_def])
  have hr : ‖iteratedFDeriv ℝ k (fun y => f (p, y)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (p, z)‖ := by
    simpa [T] using norm_iteratedFDeriv_affine_contraction_le T hT (p, (0 : Z))
      (hV.prod hU) hf k (x := z) (by simpa [T] using And.intro hp hz)
  apply hr.trans
  have hb := norm_iteratedFDeriv_vectorCarrierPolynomial_joint_le hV hU hψ hu
    H Q hH hQ hK hA hρ ⟨hp, hz⟩ (k + j)
    (fun m hm => (norm_iteratedFDeriv_imaginaryPhase
      (hφ.contDiffAt ((hV.prod hU).mem_nhds ⟨hp, hz⟩)) m).le.trans (hphase m hm))
    hamplitude j v hv k le_rfl
  exact hb.trans_eq (by simp only [pow_add]; ring)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
