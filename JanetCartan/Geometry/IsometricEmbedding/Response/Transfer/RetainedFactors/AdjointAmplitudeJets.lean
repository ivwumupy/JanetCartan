module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AmplitudeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseBranches.Initial

/-!
# Literal adjoint amplitude jets on the same retained carrier

Exchange the two physical positions and conjugate-transpose the full original
amplitude. The parameter and covector are fixed. The mixed product norm costs
at most `2^j` at derivative order `j`, a constant independent of all scales.
The actual closed critical carrier is invariant under this exchange. Consumer:
the `hαjet` input of the literal-adjoint integrated envelope endpoint in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic EvolutionIntegral DirectEvolution AnnularSobolev
variable {d p q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean p
local notation "Joint" => (E × Par) × CarrierVariables (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- Exchange the physical positions in the literal adjoint, retaining the
parameter and frequency (`app:ch_response:eq:fixed-factor-transfer`). -/
def annularCarrierSwap : Joint →L[ℝ] Joint :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v ↦ ((v.2.fst, v.1.2), WithLp.toLp 2 (v.1.1, v.2.snd))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The position exchange has a fixed norm cost only. The direct calculus
uses a Hilbert norm on its integration variables and a max norm on the outer
pair, so the exchange is not silently treated as an isometry
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_annularCarrierSwap_le : ‖annularCarrierSwap (d := d) (p := p)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have hx := (norm_fst_le v.1).trans (norm_fst_le v)
  have hc := (norm_snd_le v.1).trans (norm_fst_le v)
  have hz := (WithLp.norm_fst_le E v.2).trans (norm_snd_le v)
  have hθ := (WithLp.norm_snd_le E v.2).trans (norm_snd_le v)
  have hp : ‖WithLp.toLp 2 (v.1.1, v.2.snd)‖ ≤ 2 * ‖v‖ := by
    have he : WithLp.toLp 2 (v.1.1, v.2.snd) =
        WithLp.toLp 2 (v.1.1, (0 : E)) + WithLp.toLp 2 ((0 : E), v.2.snd) := by
      simp only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [he]
    exact (norm_add_le _ _).trans (by
      rw [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd]
      linarith only [hx, hθ])
  change max (max ‖v.2.fst‖ ‖v.1.2‖) ‖WithLp.toLp 2 (v.1.1, v.2.snd)‖ ≤ _
  exact max_le ((max_le hz hc).trans (by nlinarith only [norm_nonneg v])) hp

/-- The enlarged closed carrier of `CappedConstruction` is invariant under
the literal physical exchange; no independently selected adjoint carrier is
needed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem annularCarrierSwap_mem_closed_critical_carrier
    (z : RootState (Euclidean d)) (ε : ℝ) (Param : Set (Euclidean p)) (O : Set E)
    {v : Joint}
    (hv : v ∈ (closure (elapsedPhysicalBox z ε) ×ˢ Param) ×ˢ
      closure (retainedOpenIntegrationDomain z ε O)) :
    annularCarrierSwap v ∈ (closure (elapsedPhysicalBox z ε) ×ˢ Param) ×ˢ
      closure (retainedOpenIntegrationDomain z ε O) := by
  have he : closure (retainedOpenIntegrationDomain z ε O) =
      WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
        (closure (elapsedPhysicalBox z ε) ×ˢ closure O) := by
    rw [retainedOpenIntegrationDomain, ← ContinuousLinearEquiv.preimage_closure,
      closure_prod_eq]
  rw [he] at hv ⊢
  exact ⟨⟨hv.2.1, hv.1.2⟩, hv.1.1, hv.2.2⟩

/-- Every joint derivative of the actual normalized adjoint is controlled by
the original forward derivative at the exchanged point. Both physical masks,
the original multiplier and annular shoulders are conjugated in their literal
order. The real frequency normalization commutes with conjugate transpose
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_normalizedAdjointAnnularElapsedAmplitude_le
    (W : TwoTimeAmplitude d q) (χout χsource β π : E → ℂ)
    (hW : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude W))
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hπ : ContDiff ℝ ∞ π)
    (t : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (o j : ℕ) (v : Joint) :
    ‖iteratedFDeriv ℝ j (Function.uncurry
      (normalizedAdjointAnnularElapsedAmplitude (P := Par) W χout χsource β π t lam
        (-(o : ℤ)))) v‖ ≤
      2 ^ j * ‖iteratedFDeriv ℝ j (Function.uncurry
        (normalizedAnnularElapsedAmplitude (P := Par) W χout χsource β π t lam
          (-(o : ℤ)))) (annularCarrierSwap v)‖ := by
  let J : Mat ≃ₗᵢ[ℝ] Mat := {
    Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ with
    norm_map' := Matrix.frobenius_norm_conjTranspose }
  let f := Function.uncurry
    (normalizedAnnularElapsedAmplitude (P := Par) W χout χsource β π t lam (-(o : ℤ)))
  have he : Function.uncurry
      (normalizedAdjointAnnularElapsedAmplitude (P := Par) W χout χsource β π t lam (-(o : ℤ))) =
      J ∘ (f ∘ annularCarrierSwap) := by
    funext w
    change (lam ^ (-(o : ℤ)))⁻¹ •
      (annularElapsedAmplitude W χout χsource β π t lam w.2.fst w.1.1 (lam • w.2.snd)).conjTranspose =
      ((lam ^ (-(o : ℤ)))⁻¹ •
        annularElapsedAmplitude W χout χsource β π t lam w.2.fst w.1.1 (lam • w.2.snd)).conjTranspose
    simp only [Matrix.conjTranspose_smul, star_trivial]
  rw [he, J.norm_iteratedFDeriv_comp_left]
  have hf := contDiff_normalizedAnnularElapsedAmplitude (p := p)
    W χout χsource β π hW ho hs hβ hπ t hlam o
  rw [annularCarrierSwap.iteratedFDeriv_comp_right hf v (by simp)]
  exact ((iteratedFDeriv ℝ j f (annularCarrierSwap v)).norm_compContinuousLinearMap_le _).trans
    (by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) norm_annularCarrierSwap_le j) (norm_nonneg _)).trans_eq
          (mul_comm _ _))

end JanetCartan.ResponseTransfer.RetainedFactors
