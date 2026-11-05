module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedFourier
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureSource
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.SobolevScale

/-!
# Both real quadratures of the corrected source discrepancy

The actual normalized source is compressed from its own characteristic-plus-
elliptic pair. These identities retain that operator, both source cutoffs,
reflection and original zero extension. Consumers: the real and restricted
signed-source discrepancy in `app:ch_pairs:prop:pairs-lag-sum`, Steps 1–3.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver RegularSector.Realization
open ResponseTransfer.SourceNegative Pseudodifferential
open ArbitraryAccuracy.ResidualLocalization RegularSector.Characteristic.RetardedLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)
local notation "RH" => Lp RV 2 (volume : Measure E)

/-- The imaginary included real quadrature has zero real part
(`app:ch_response:eq:response-actual-solver-formula`). -/
private theorem realPart_imaginary_inclusion (u : RH) :
    l2RealPart volume (Complex.I • l2ComplexInclusion volume u) = 0 := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL (Complex.I • l2ComplexInclusion volume u),
    Lp.coeFn_smul Complex.I (l2ComplexInclusion volume u),
    euclideanComplexInclusion.coeFn_compLpL u, Lp.coeFn_zero RV 2 volume] with y hr hi hu hz
  change (l2RealPart volume (Complex.I • l2ComplexInclusion volume u)) y = _ at hr
  change (l2ComplexInclusion volume u) y = euclideanComplexInclusion (u y) at hu
  rw [hr, hi, Pi.smul_apply, hu, hz]
  ext i
  simp [euclideanRealPart_apply, euclideanComplexInclusion_apply]

/-- Real compression of the corrected source subtracts one identity. It is
not identified with the old unnormalized characteristic source
(`sector-theorem-identity`, `app:ch_pairs:prop:pairs-lag-sum`). -/
theorem normalizedSource_real_defect_eq_compression
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) :
    realSource f hK L₀ output ho hob - 1 =
      realCompression (pairedSource f hK L₀ output ho hob - 1) := by
  ext1 u
  simp [realSource, realCompression, realPart_inclusion]

/-- Every rotated real quadrature has the SAME corrected source error.
In particular `c=1` and `c=-I` cover both original quadratures
(`app:ch_pairs:eq:pairs-lag-one-error`, source contribution). -/
theorem normalizedSource_real_quadrature_defect
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (u : H) (c : ℂ) :
    (realSource f hK L₀ output ho hob - 1) (l2RealPart volume (c • u)) =
      l2RealPart volume (c • ((pairedSource f hK L₀ output ho hob - 1) u)) := by
  let P := pairedSource f hK L₀ output ho hob
  have hr (z : H) : l2RealPart volume (P z) =
      realSource f hK L₀ output ho hob (l2RealPart volume z) := by
    have he := realCompression_complex_extension P (normalizedPair_conjugation _) z
    rw [he, map_add, realPart_inclusion, realPart_imaginary_inclusion, add_zero]
    rfl
  rw [← map_smul]
  simp only [sub_apply, one_apply_eq_self, map_sub]
  change _ = l2RealPart volume (P (c • u)) - l2RealPart volume (c • u)
  rw [hr]

/-- Literal local compression of the corrected source error is the
restriction of its same global real quadrature. The original source cutoff
supplies zero-extension admission; its L² proof comes from the existing
signed-source producer (`resolved-angular-tail`, `pairs-lag-sum`). -/
theorem local_normalizedSource_modulated_quadrature_defect
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (χ φ : E → ℝ) (b : E → V) (ρ : ℝ) (hg : MemLp (modulatedSource χ φ b ρ) 2 volume)
    {W : Set E} (hW : MeasurableSet W) (hχW : tsupport χ ⊆ W) (Vout : Set E) (c : ℂ) :
    let u := hg.toLp (modulatedSource χ φ b ρ)
    let D := pairedSource f hK L₀ output ho hob - 1
    localRealCompression hW Vout D (l2RealPart (volume.restrict W) (c • restrictL2 W u)) =
      l2RealPart (volume.restrict Vout) (c • restrictL2 Vout (D u)) := by
  intro u D
  apply Lp.ext
  have he := localRealCompression_coeFn hW Vout D
    (l2RealPart (volume.restrict W) (c • restrictL2 W u))
  rw [zeroExtend_restrictL2_modulatedSource_real_quadrature hW χ φ b ρ hχW hg c,
    ← normalizedSource_real_defect_eq_compression f hK L₀ output ho hob,
    normalizedSource_real_quadrature_defect] at he
  have hr : l2RealPart (volume.restrict Vout) (c • restrictL2 Vout (D u)) =ᵐ[volume.restrict Vout]
      l2RealPart volume (c • D u) := by
    filter_upwards [euclideanRealPart.coeFn_compLpL (c • restrictL2 Vout (D u)),
      Lp.coeFn_smul c (restrictL2 Vout (D u)), restrictL2_coeFn Vout (D u),
      ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL (c • D u)),
      ae_restrict_of_ae (Lp.coeFn_smul c (D u))] with y hr hs hi hg hc
    change (l2RealPart (volume.restrict Vout) (c • restrictL2 Vout (D u))) y = _ at hr
    change (l2RealPart volume (c • D u)) y = _ at hg
    rw [hr, hs, Pi.smul_apply, hi, hg, hc, Pi.smul_apply]
  exact he.trans hr.symm

/-- The actual corrected real discrepancy contracts its complex Fourier
Sobolev norm, at any positive or negative order where it belongs. The
membership used here is proved by `exists_normalized_signed_source_discrepancy_constants`
(`pairs-lag-one-error`, both quadratures). -/
theorem normalizedSource_real_quadrature_sobolev_le
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (u : H) {s : ℝ}
    (hu : MemVectorFourierSobolev s ((pairedSource f hK L₀ output ho hob - 1) u))
    (c : ℂ) (hc : ‖c‖ = 1) :
    ArbitraryAccuracy.MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin (d+1)) ℝ) s
      ((realSource f hK L₀ output ho hob - 1) (l2RealPart volume (c • u))) ∧
    ArbitraryAccuracy.componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) s
      ((realSource f hK L₀ output ho hob - 1) (l2RealPart volume (c • u))) ≤
        vectorFourierSobolevNorm s ((pairedSource f hK L₀ output ho hob - 1) u) := by
  rw [normalizedSource_real_quadrature_defect]
  exact real_quadrature_fourierSobolev_bound hu c hc

end JanetCartan.SignedProductEstimates
