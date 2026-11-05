module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.OperatorLimit

/-!
# Strong convergence of the same compact cross graphs

The exact right-frequency factorizations yield a squared multiplier between
the two original graphs. This proves the strong cross limit required by
`app:ch_regular_base:eq:actual-normal-kernel`. The graph realizations are supplied
by `WholeImageGeometry.exists_graphL2_of_wholeImage_phase`; the identification of
the limit with the full-amplitude PDO remains a separate analytic obligation.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.UncutNormal

open LowBounds LowBounds.FrequencyCutoff

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The square of the actual compact-frequency multiplier converges strongly
to the identity. Consumer: the pure cross-normal in
`app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem multiplier_square_tendsto (f : H) :
    Tendsto (fun m ↦ multiplier m (multiplier m f)) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.mp (multiplier_tendsto f)).const_mul 2
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm _ hlim
  intro m
  rw [norm_norm]
  calc
    ‖multiplier m (multiplier m f) - f‖ =
        ‖multiplier m (multiplier m f - f) + (multiplier m f - f)‖ := by
      congr 1
      simp
    _ ≤ ‖multiplier m (multiplier m f - f)‖ + ‖multiplier m f - f‖ := norm_add_le _ _
    _ ≤ 2 * ‖multiplier m f - f‖ := by
      linarith [multiplier_norm_le m (multiplier m f - f)]

/-- The pure product of the actual compact graphs factors through the square
of the same frequency multiplier, before any spatial source multiplication.
The two Schwartz realizations are produced by the whole-image low-bound
construction. Source: `app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem compactVectorGraph_cut_cross_eq_comp
    {S : E → E → ℝ} {A B : E → E → Mat}
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (Function.uncurry A)) (hB : Continuous (Function.uncurry B))
    {KA KB : Set E} (hKA : IsCompact KA) (hKB : IsCompact KB)
    (hsA : ∀ x η, x ∉ KA → A x η = 0) (hsB : ∀ x η, x ∉ KB → B x η = 0)
    (T U : H →L[ℂ] H)
    (hT : ∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x))
    (hU : ∀ u : SchwartzMap E (Fin r → ℂ), U (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ B z η) u x)) (m : ℕ) :
    (compactVectorGraph hS (cutAmplitude_entry_continuous hA m)
      (cutAmplitude_entry_hasCompactSupport hKA hsA m)).comp
      (compactVectorGraph hS (cutAmplitude_entry_continuous hB m)
        (cutAmplitude_entry_hasCompactSupport hKB hsB m)).adjoint =
      T.comp ((multiplier m).comp ((multiplier m).comp U.adjoint)) := by
  exact (congrArg₂ (fun (F G : H →L[ℂ] H) ↦ F.comp G)
    (compactVectorGraph_cut_eq_comp hS hA hKA hsA T hT m)
    (compactVectorGraph_cut_adjoint_eq_comp hS hB hKB hsB U hU m)).trans
      (ContinuousLinearMap.comp_assoc T (multiplier m) ((multiplier m).comp U.adjoint))

/-- Strong convergence of the actual compact cross normals on every input.
The same bounded graphs occur in the limit; there is no newly chosen limiting
operator. The bounded graph realizations are the outputs of
`WholeImageGeometry.exists_graphL2_of_wholeImage_phase`. Source:
`app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem compactVectorGraph_cut_cross_tendsto_of_realizes
    {S : E → E → ℝ} {A B : E → E → Mat}
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (Function.uncurry A)) (hB : Continuous (Function.uncurry B))
    {KA KB : Set E} (hKA : IsCompact KA) (hKB : IsCompact KB)
    (hsA : ∀ x η, x ∉ KA → A x η = 0) (hsB : ∀ x η, x ∉ KB → B x η = 0)
    (T U : H →L[ℂ] H)
    (hT : ∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x))
    (hU : ∀ u : SchwartzMap E (Fin r → ℂ), U (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ B z η) u x)) (f : H) :
    Tendsto (fun m ↦ compactVectorGraph hS (cutAmplitude_entry_continuous hA m)
      (cutAmplitude_entry_hasCompactSupport hKA hsA m)
      ((compactVectorGraph hS (cutAmplitude_entry_continuous hB m)
        (cutAmplitude_entry_hasCompactSupport hKB hsB m)).adjoint f)) atTop
      (𝓝 (T (U.adjoint f))) := by
  have he (m : ℕ) := congrArg (fun V : H →L[ℂ] H ↦ V f)
    (compactVectorGraph_cut_cross_eq_comp hS hA hB hKA hKB hsA hsB T U hT hU m)
  simp only [ContinuousLinearMap.comp_apply] at he
  simp_rw [he]
  exact T.continuous.continuousAt.tendsto.comp (multiplier_square_tendsto (U.adjoint f))

end JanetCartan.FourierIntegral.UncutNormal
