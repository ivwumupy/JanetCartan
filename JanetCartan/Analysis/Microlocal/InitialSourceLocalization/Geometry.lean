module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Masks
public import JanetCartan.Analysis.Microlocal.Localization.FourierPhase
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The initial source graph and the complementary right symbol

The first proof mask in `app:ch_regular:lem:finite-chain` is one on a
thickening of the actual physical source graph. This geometry excludes the
closed support of the complementary source amplitude and supplies the
nonstationary gap for its Fourier integral. The mask is never replaced by
a radial multiplier or by a left quantization.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
local notation "E" => Euclidean n

/-- The amplitude of the Fourier transform of the initial identity defect,
with the source base retained (`app:ch_regular:lem:finite-chain`). -/
def complementarySourceAmplitude (m : LocalizerSymbol n) (a : E → F) (η : E) : E → F :=
  fun y ↦ (1 - (m (y, η) : ℂ)) • a y

/-- The single identity subtraction preserves the original source support
(`app:ch_regular:eq:source-tail`). -/
theorem tsupport_complementarySourceAmplitude_subset
    (m : LocalizerSymbol n) (a : E → F) (η : E) :
    tsupport (complementarySourceAmplitude m a η) ⊆ tsupport a :=
  tsupport_smul_subset_right _ _

/-- A plateau at a physical source/frequency point excludes that source
point from the closed complementary-amplitude support. This uses a
neighborhood, not just pointwise cancellation (`app:ch_regular:lem:finite-chain`). -/
theorem notMem_tsupport_complementarySourceAmplitude_of_plateau
    (m : LocalizerSymbol n) (a : E → F) {y η : E}
    (hplateau : (y, η) ∈ interior {p | m p = 1}) :
    y ∉ tsupport (complementarySourceAmplitude m a η) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hpre := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
    (isOpen_interior.mem_nhds hplateau)
  filter_upwards [hpre] with z hz
  have hm : m (z, η) = 1 := interior_subset (s := {p | m p = 1}) hz
  simp only [complementarySourceAmplitude, hm, Complex.ofReal_one, sub_self, zero_smul,
    Pi.zero_apply]

/-- The common positive graph thickening gives a strict normalized
gradient gap on the CLOSED support of the actual complementary amplitude.
The source graph is the original one (`app:ch_regular:eq:source-tail`). -/
theorem gradient_gap_on_complementarySourceAmplitude
    (m : LocalizerSymbol n) (a : E → F) (φ : E → ℝ)
    {S : Set (E × E)} {δ : ℝ}
    (hgraph : ∀ y ∈ tsupport a, (y, gradient φ y) ∈ S)
    (hplateau : cthickening δ S ⊆ interior {p | m p = 1})
    (η y : E) (hy : y ∈ tsupport (complementarySourceAmplitude m a η)) :
    δ < ‖gradient φ y - η‖ := by
  by_contra h
  have hd : dist (y, η) (y, gradient φ y) ≤ δ := by
    simpa [Prod.dist_eq, dist_eq_norm, norm_sub_rev] using le_of_not_gt h
  exact notMem_tsupport_complementarySourceAmplitude_of_plateau m a
    (hplateau (mem_cthickening_of_dist_le _ _ _ _
      (hgraph y (tsupport_complementarySourceAmplitude_subset m a η hy)) hd)) hy

/-- Turn the normalized graph gap into the full-frequency gap used by
integration by parts, including arbitrarily large covectors
(`app:ch_regular:lem:finite-chain`, `app:ch_osc:prop:osc-source-shell`). -/
theorem normalized_gradient_gap_le_weighted
    {g η : E} {δ G : ℝ} (hδ : 0 < δ) (hg : ‖g‖ ≤ G)
    (hgap : δ ≤ ‖g - η‖) :
    δ / (1 + G + δ) * (1 + ‖η‖) ≤ ‖g - η‖ := by
  have hG : 0 ≤ G := (norm_nonneg _).trans hg
  have hden : 0 < 1 + G + δ := by positivity
  have hη : ‖η‖ ≤ G + ‖g - η‖ := by
    have h := norm_sub_le g (g - η)
    rw [sub_sub_cancel] at h
    exact h.trans (add_le_add hg le_rfl)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_left hgap (show 0 ≤ 1 + G by positivity),
    mul_le_mul_of_nonneg_left hη hδ.le]

/-- The physical phase uses exactly `rho dphi - xi`; the common graph
gap supplies the scale `rho + norm xi` with no change of Fourier convention
(`app:ch_regular:lem:finite-chain`). -/
theorem physical_fourier_gap_of_normalized_gradient_gap
    (φ : E → ℝ) {ρ δ G : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (ξ y : E) (hg : ‖fderiv ℝ φ y‖ ≤ G)
    (hgap : δ ≤ ‖gradient φ y - ρ⁻¹ • ξ‖) :
    δ / (1 + G + δ) * (ρ + ‖ξ‖) ≤
      ‖ρ • fderiv ℝ φ y - InnerProductSpace.toDual ℝ E ξ‖ := by
  have hn := normalized_gradient_gap_le_weighted hδ
    (show ‖gradient φ y‖ ≤ G by simpa [gradient] using hg) hgap
  have he : ρ • fderiv ℝ φ y - InnerProductSpace.toDual ℝ E ξ =
      ρ • InnerProductSpace.toDual ℝ E (gradient φ y - ρ⁻¹ • ξ) := by
    simp [gradient, map_sub, map_smul, smul_sub, smul_smul, hρ.ne']
  rw [he, norm_smul, Real.norm_of_nonneg hρ.le, LinearIsometryEquiv.norm_map]
  have h := mul_le_mul_of_nonneg_left hn hρ.le
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)] at h
  convert h using 1
  field_simp

end JanetCartan.InitialSourceLocalization
