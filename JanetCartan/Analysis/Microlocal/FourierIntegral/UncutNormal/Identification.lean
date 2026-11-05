module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.CutoffSymbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.CrossLimit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.PdoLimit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactPDO
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CutoffGeometry

/-!
# Identifying the same uncut graph cross-normal

The actual compact cross-normal identities have two strong limits: the product
of the original graph and adjoint, and the existing full-amplitude matrix PDO.
Uniqueness of the limit proves their equality. The primitive construction supplies
the common symbol budget; no limiting identity or oscillatory majorant is assumed.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison LowBounds LowBounds.FrequencyCutoff Pseudodifferential
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Identification of the same two realized graphs with the bounded matrix PDO
of the full zero-extended, cycle-rescaled cross amplitude. All compact identities
and both strong limits are proved. The common symbol budgets are produced from
original jets by `exists_uniform_cycleCrossNormalSymbol_bounds`; the final
whole-image construction discharges the chart, realization and budget inputs.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem cross_eq_vectorTwoPositionL2Operator_of_realizes
    {X D : Set E} {S : E → E → ℝ} {A B : E → E → Mat}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables n)} {δ : ℝ}
    (chart : AveragedGradientChart S X D η J δ)
    (geometry : PrimitiveNormalGeometry X D S A B η J W K)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (Function.uncurry A)) (hB : Continuous (Function.uncurry B))
    {KA KB : Set E} (hKA : IsCompact KA) (hKB : IsCompact KB)
    (hsA : ∀ x u, x ∉ KA → A x u = 0) (hsB : ∀ x u, x ∉ KB → B x u = 0)
    (hcarrierA : ∀ x u, x ∉ X ∨ u ∉ D → A x u = 0)
    (hforward : ContinuousOn (normalForwardCoordinates S) (jointNormalCarrier A B))
    (hn : 0 < n) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A B η J) R M)
    (hcut : ∀ m, GraphNormalAmplitudeBounds
      (cycleCrossNormalSymbol D S (cutAmplitude A m) (cutAmplitude B m) η J) R M)
    (T U : H →L[ℂ] H)
    (hT : ∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ v ↦ A z v) u x))
    (hU : ∀ u : SchwartzMap E (Fin r → ℂ), U (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ v ↦ B z v) u x)) :
    T.comp U.adjoint = vectorTwoPositionL2Operator hn R
      (cycleCrossNormalSymbol D S A B η J) hb.smooth hb.support M hb.entry_bound := by
  have he (m : ℕ) := compactVectorGraph_cross_eq_vectorTwoPositionL2Operator chart hS
    (cutAmplitude_entry_continuous hA m) (cutAmplitude_entry_hasCompactSupport hKA hsA m)
    (cutAmplitude_entry_continuous hB m) (cutAmplitude_entry_hasCompactSupport hKB hsB m)
    (fun x u h ↦ by simp [cutAmplitude, hcarrierA x u h])
    (fun x u h ↦ by simp [cutAmplitude, geometry.right_output x u h])
    hn R M (hcut m)
    ((geometry.cutAmplitude m m).hasCompactSupport_cycleSymbol
      (cutAmplitude_hasCompactSupport hKA hsA m)
      (cutAmplitude_hasCompactSupport hKB hsB m)
      (hforward.mono (jointNormalCarrier_cutAmplitude_subset A B m m)))
  apply ContinuousLinearMap.ext
  intro f
  have hg := compactVectorGraph_cut_cross_tendsto_of_realizes
    hS hA hB hKA hKB hsA hsB T U hT hU f
  have hp := tendsto_vectorTwoPositionL2Operator_of_pointwise hn R M _ _ hcut hb
    (fun ξ z ↦ tendsto_const_nhds.congr' (by
      filter_upwards [cycleCrossNormalSymbol_cutAmplitude_eventually_eq D S A B η J ξ z]
        with m hm
      exact hm.symm)) f
  have he' (m : ℕ) := congrArg (fun V : H →L[ℂ] H ↦ V f) (he m)
  simp only [ContinuousLinearMap.comp_apply] at he'
  exact tendsto_nhds_unique hg (hp.congr (fun m ↦ (he' m).symm))

end JanetCartan.FourierIntegral.UncutNormal
