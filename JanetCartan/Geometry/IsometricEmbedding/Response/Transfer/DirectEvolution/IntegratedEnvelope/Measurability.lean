module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.CompactRealization

/-!
# Measurability of the same annular elapsed graphs

The literal forward and reverse compact kernels provide orbit measurability
from the original phase, amplitude, masks and annular cutoff. No test realization
or measurability hypothesis remains. Consumer: elapsed integration in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope
open FourierIntegral FourierIntegral.FullLowBounds
open RegularSector.Characteristic.EvolutionIntegral KernelIdentification
open AnnularSobolev JanetCartan.ResponseTransfer.Complement
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d r

/-- The frequency-rescaled annular cutoff is compactly supported for every
nonzero fixed frequency. The support may grow with that frequency; this lemma
introduces no quantitative cost (`app:ch_response:eq:direct-envelope-profile`). -/
theorem hasCompactSupport_rescaled_annularCutoff
    {lam : ℝ} (hlam : lam ≠ 0) {π : E → ℂ} (hπ : HasCompactSupport π) :
    HasCompactSupport (fun ξ ↦ π (lam⁻¹ • ξ)) := by
  apply HasCompactSupport.intro (hπ.image (show Continuous (fun ξ : E ↦ lam • ξ) from by fun_prop))
  intro ξ hξ
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  apply hξ
  exact ⟨lam⁻¹ • ξ, hp, by simp [smul_smul, hlam]⟩

variable (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ) {lam : ℝ} (hlam : lam ≠ 0)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (ha : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      a p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hπ : Continuous π) (hocs : HasCompactSupport χout)
    (hscs : HasCompactSupport χsource) (hπcs : HasCompactSupport π)

include hlam hΨ ha ho hs hβ hπ hocs hscs hπcs

/-- Both literal annular physical graph families have strongly measurable
orbits. All test realizations are constructed from the continuous original
data and compact masks; density supplies arbitrary L² inputs. No graph bound
or analytic operator premise is assumed. Source:
`app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem aestronglyMeasurable_annularPhysical_and_adjoint (μ : Measure ℝ) (u : H) :
    AEStronglyMeasurable (fun t ↦ fullGraphOperator (elapsedPhase Ψ t)
      (annularElapsedAmplitude a χout χsource β π t lam) u) μ ∧
    AEStronglyMeasurable (fun t ↦ (fullGraphOperator (elapsedPhase Ψ t)
      (annularElapsedAmplitude a χout χsource β π t lam)).adjoint u) μ := by
  let θ : E → ℂ := fun ξ ↦ π (lam⁻¹ • ξ)
  have hθ : Continuous θ := by fun_prop
  have hθcs : HasCompactSupport θ := hasCompactSupport_rescaled_annularCutoff hlam hπcs
  have hcS := continuous_elapsedPhase Ψ hΨ
  have hcA := continuous_cut_elapsedAmplitude a χout χsource β θ ha ho hs hβ hθ
  have hsupport := cut_elapsedAmplitude_eq_zero_off_support a χout χsource β θ
  have hreal (t : ℝ) := compact_fullGraphOperator_realizations (elapsedPhase Ψ t)
    (hcS.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))
    (annularElapsedAmplitude a χout χsource β π t lam)
    (hcA.comp (((continuous_const.prodMk continuous_fst.fst).prodMk
      continuous_fst.snd).prodMk continuous_snd)) hocs hscs hθcs (hsupport t)
  constructor
  · exact aestronglyMeasurable_compact_graph_apply _ _ hcS hcA hocs hscs hθcs
      hsupport _ μ (fun v ↦ Eventually.of_forall fun t ↦ (hreal t).1 v) u
  · apply aestronglyMeasurable_compact_reverse_apply _ _ hcS hcA.matrix_conjTranspose
      hocs hscs hθcs _ _ μ (fun v ↦ Eventually.of_forall fun t ↦ (hreal t).2 v) u
    intro t x y ξ h
    change (frequencyCutFullAmplitude θ (elapsedAmplitude a χout χsource β t) x y ξ).conjTranspose = 0
    rw [hsupport t x y ξ h, Matrix.conjTranspose_zero]

/-- Carrier conjugation preserves the proved measurability, for the SAME
annular envelope and its literal adjoint. The carrier and physical frequency
are fixed in this elapsed-time integration step
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem aestronglyMeasurable_annularEnvelope_and_adjoint
    (φ : E → ℝ) (hφ : Continuous φ) (μ : Measure ℝ) (u : H) :
    AEStronglyMeasurable (fun t ↦ annularEnvelopeOperator Ψ a χout χsource β π
      t lam φ hφ u) μ ∧
    AEStronglyMeasurable (fun t ↦ (annularEnvelopeOperator Ψ a χout χsource β π
      t lam φ hφ).adjoint u) μ := by
  have h := aestronglyMeasurable_annularPhysical_and_adjoint Ψ a χout χsource β π
    hlam hΨ ha ho hs hβ hπ hocs hscs hπcs μ (carrierMultiplication lam φ hφ u)
  constructor
  · exact (carrierMultiplication (-lam) φ hφ).continuous.comp_aestronglyMeasurable h.1
  · simp only [annularEnvelopeOperator_adjoint]
    exact (carrierMultiplication (-lam) φ hφ).continuous.comp_aestronglyMeasurable h.2

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope
