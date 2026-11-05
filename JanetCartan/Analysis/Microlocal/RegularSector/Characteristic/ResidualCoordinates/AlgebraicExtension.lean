module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.ConicComplement

/-!
# Smoothness of the supported algebraic symbol

The entire symbol `b₋₁ σ β` is smooth, including at the cone vertex and the
edge of the complement chart. The proof uses zero germs of the ORIGINAL
source, radial and right multiplier masks. Thus all physical derivatives
still act on the complete product; no extension commutator is dropped.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- Smoothness of the normalized source state away from the radial denominator.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiffAt_normalizedRootState (ℓ : Euclidean d →L[ℝ] ℝ)
    {p : E × Euclidean d} (hp : ℓ p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : E × Euclidean d ↦ rootState q.1 ((ℓ q.2)⁻¹ • q.2)) p :=
  (((coordinateSplit 0).contDiff.comp contDiff_fst).fst.contDiffAt).prodMk
    ((((coordinateSplit 0).contDiff.comp contDiff_fst).snd.contDiffAt).prodMk
      (((ℓ.contDiff.comp contDiff_snd).contDiffAt.inv hp).smul contDiffAt_snd))

/-- The supported source symbol has global joint smoothness because the
auxiliary frequency plateau is supported inside the positive radial chart.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_conicSourceSymbol
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ) :
    ContDiff ℝ ∞ (Function.uncurry (conicSourceSymbol ℓ ρ σ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 ∈ tsupport ρ
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hρ.contDiffAt.comp p contDiffAt_snd)).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (hσ.contDiffAt.comp p (contDiffAt_normalizedRootState ℓ (hsρ hp).ne')))
  · apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
      (continuous_snd.continuousAt (x := p))
    filter_upwards [hz] with q hq
    simp only [Function.comp_apply, Pi.zero_apply] at hq
    simp [Function.uncurry, conicSourceSymbol, hq]

/-- Global smoothness of the SAME supported conic inverse product. The
physical and normalized-frequency supports lie in the neighborhood constructed
by `exists_common_complement_neighborhood`. The original right multiplier is
unchanged, and the source datum is the one used in the transported columns.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_conicAlgebraicSymbol
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    {Ω : Set E} {Q : E → Fin (d + 1) → Mat} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω)
    (r c : Fin (d + 1)) {X F : Set E}
    (hXF : X ×ˢ F ⊆ complementDomain i Q h r c D)
    (ρ : Euclidean d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hsσ : ∀ w ∈ tsupport σ, timeSpacePoint w.1 w.2.1 ∈ X)
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β)
    (hsβ : ∀ ξ ∈ tsupport β, normalizeCovector ℓ ξ ∈ F) :
    ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol
      (conicBminus ℓ i Q h r c) (conicSourceSymbol ℓ ρ σ) β)) := by
  have hg : ContDiff ℝ ∞ (fun p : E × E ↦ (p.1, spatialPart p.2)) :=
    contDiff_fst.prodMk ((coordinateSplit 0).contDiff.comp contDiff_snd).snd
  have hsource := (contDiff_conicSourceSymbol ℓ ρ hρ hsρ σ hσ).comp hg
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hb : p.2 ∈ tsupport β
  · by_cases hr : spatialPart p.2 ∈ tsupport ρ
    · have hℓ : ℓ (spatialPart p.2) ≠ 0 := (show 0 < ℓ (spatialPart p.2) from hsρ hr).ne'
      have hw := (contDiffAt_normalizedRootState ℓ hℓ).comp p hg.contDiffAt
      by_cases hwσ : rootState p.1 ((ℓ (spatialPart p.2))⁻¹ • spatialPart p.2) ∈ tsupport σ
      · have hx : p.1 ∈ X := by
          have he : timeSpacePoint (p.1 0) (spatialPart p.1) = p.1 :=
            timeSpaceMeasurableEquiv.symm_apply_apply p.1
          simpa only [rootState, he] using hsσ _ hwσ
        exact (hsource.contDiffAt.mul (hβ.contDiffAt.comp p contDiffAt_snd)).smul
          (contDiffAt_conicBminus ℓ i hQ hD hh hmap r c hℓ (hXF ⟨hx, hsβ p.2 hb⟩))
      · apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
        have hz := (notMem_tsupport_iff_eventuallyEq.mp hwσ).comp_tendsto hw.continuousAt
        filter_upwards [hz] with q hq
        simp only [Function.comp_apply, Pi.zero_apply] at hq
        simp [Function.uncurry, directAlgebraicSymbol, conicSourceSymbol, sourceSymbol, hq]
    · apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hr).comp_tendsto
        (((coordinateSplit 0).continuous.comp continuous_snd).snd.continuousAt (x := p))
      filter_upwards [hz] with q hq
      change ρ (spatialPart q.2) = 0 at hq
      simp [Function.uncurry, directAlgebraicSymbol, conicSourceSymbol, hq]
  · apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hb).comp_tendsto
      (continuous_snd.continuousAt (x := p))
    filter_upwards [hz] with q hq
    simp only [Function.comp_apply, Pi.zero_apply] at hq
    simp [Function.uncurry, directAlgebraicSymbol, hq]

/-- The auxiliary radial plateau leaves the ORIGINAL principal and algebraic
symbols unchanged after the right multiplier. The equality of entire symbol
functions also preserves every physical derivative in the third residual term.
The plateau is produced by `exists_conicFrequency_plateau` on the original
closed radial/angular carrier.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem conicSourceSymbol_mul_right_multiplier
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ)
    (σ : RootState (Euclidean d) → ℝ) (β : E → ℂ)
    (hρ : ∀ ξ, β ξ ≠ 0 → ρ (spatialPart ξ) = 1) (x ξ : E) :
    conicSourceSymbol ℓ ρ σ x (spatialPart ξ) * β ξ =
      sourceSymbol σ x ((ℓ (spatialPart ξ))⁻¹ • spatialPart ξ) * β ξ := by
  by_cases hξ : β ξ = 0
  · simp [hξ]
  · simp [conicSourceSymbol, hρ ξ hξ]

/-- Exact identity of the entire algebraic symbol before applying `P_x`.
Thus no derivatives of an auxiliary frequency plateau enter the physical
residual and the original multiplier order is preserved.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem conicAlgebraicSymbol_eq_on_frequency_plateau
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ)
    (σ : RootState (Euclidean d) → ℝ) (β : E → ℂ)
    (b : E → E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hρ : ∀ ξ, β ξ ≠ 0 → ρ (spatialPart ξ) = 1) :
    directAlgebraicSymbol b (conicSourceSymbol ℓ ρ σ) β =
      directAlgebraicSymbol b (fun x η ↦ sourceSymbol σ x ((ℓ η)⁻¹ • η)) β := by
  funext x ξ
  simp only [directAlgebraicSymbol, conicSourceSymbol_mul_right_multiplier ℓ ρ σ β hρ]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
