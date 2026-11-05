module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.NormalizedBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.UniformJetLimit.BranchBounds

/-!
# Scalar phase / original amplitude splitting

For `app:ch_response:lem:energy-carrier-jets`, split the external directions
before taking source derivatives. The original amplitude then uses external
orders only through the requested order. Consumer: the mixed source estimate
in `AmplitudeJets.MixedBounds`, subsequently `norm_annularSourceIntegral_le`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open Complement.ParameterDerivatives JanetCartan.Localization
variable {P Z F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem contDiffOn_jointExternalDeriv
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {f : P × Z → G} (hf : ContDiffOn ℝ ∞ f (V ×ˢ U)) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun q : P × Z =>
      iteratedFDeriv ℝ j (fun p => f (p, q.2)) q.1) (V ×ˢ U) := by
  induction j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Prod.mk.eta] using
      (continuousMultilinearCurryFin0 ℝ P G).symm.contDiff.comp_contDiffOn hf
  | succ j ih =>
    have hd := JanetCartan.contDiffOn_parameterFDeriv hV hU ih
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Prod.mk.eta] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => P) G).symm.contDiff
        |>.comp_contDiffOn hd

/-- Original joint smoothness gives source smoothness of each evaluated
external amplitude jet on the original open source neighborhood.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_originalExternalJet_source
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {u : P → Z → F} (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    ContDiffOn ℝ ∞ (fun z => iteratedFDeriv ℝ j (fun q => u q z) p v) U := by
  have hd := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => P) F v).contDiff
    |>.comp_contDiffOn (contDiffOn_jointExternalDeriv hV hU hu j)
  exact hd.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨hp, hz⟩)

/-- Local source smoothness of the actual normalized jet, deduced from the
original phase and amplitude, with no normalized-jet regularity premise.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_normalizedExternalJet_source
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {ψ : P → Z → ℝ} {u : P → Z → F}
    (hψ : ContDiffOn ℝ ∞ (Function.uncurry ψ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    ContDiffOn ℝ ∞ (normalizedExternalJet ψ u j v p) U := by
  have ho : ContDiffOn ℝ ∞
      (fun q : P × Z => phaseOscillation (ψ q.1) q.2 • u q.1 q.2) (V ×ˢ U) :=
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn hψ).mul contDiffOn_const).cexp).smul hu
  have hd := contDiffOn_originalExternalJet_source hV hU
    (u := fun q z => phaseOscillation (ψ q) z • u q z) ho j v hp
  have hψp := hψ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨hp, hz⟩)
  exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn hψp.neg).mul
    contDiffOn_const).cexp).smul hd

/-- Joint regularity only near the common closed support suffices for global
source smoothness of the normalized jet, as needed by source integration.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiff_normalizedExternalJet_of_support_neighborhood
    {V : Set P} {U S : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U)
    {ψ : P → Z → ℝ} {u : P → Z → F}
    (hψ : ContDiffOn ℝ ∞ (Function.uncurry ψ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (hs : ∀ q ∈ V, tsupport (u q) ⊆ S)
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    ContDiff ℝ ∞ (normalizedExternalJet ψ u j v p) :=
  contDiff_of_contDiffOn_support_neighborhood hU
    (contDiffOn_normalizedExternalJet_source hV hU hψ hu j v hp)
    ((tsupport_normalizedExternalJet_subset hV hS ψ u hs j v hp).trans hSU)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Exact external Leibniz expansion: normalization acts only on the scalar
phase jet. Every vector factor is an actual jet of the original amplitude.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem normalizedExternalJet_eq_scalar_leibniz
    {V : Set P} (hV : IsOpen V) {ψ : P → Z → ℝ} {u : P → Z → F}
    (z : Z) (hψ : ContDiffOn ℝ ∞ (fun p => ψ p z) V)
    (hu : ContDiffOn ℝ ∞ (fun p => u p z) V)
    (j : ℕ) (v : Fin j → P) {p : P} (hp : p ∈ V) :
    normalizedExternalJet ψ u j v p z =
      ((parameterLeibnizSplittings (List.ofFn v)).map (fun s =>
        normalizedExternalJet ψ (fun _ _ => (1 : ℂ)) s.1.length s.1.get p z •
          parameterListJet (fun q => u q z) s.2 p)).sum := by
  have hc : ContDiffOn ℝ ∞ (fun q => phaseOscillation (ψ q) z) V :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn hψ).mul contDiffOn_const).cexp
  unfold normalizedExternalJet
  rw [← parameterListJet_ofFn, parameterListJet_smul _ _ hV hc hu _ hp,
    List.smul_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_def, smul_eq_mul, mul_one, parameterListJet, smul_smul]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
