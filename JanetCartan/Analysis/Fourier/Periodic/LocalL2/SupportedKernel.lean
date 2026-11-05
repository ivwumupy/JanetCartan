module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Transfer

/-!
# Compact input/output kernel transport

Support in the chart is checked on the literal Euclidean kernel for
`app:ch_background:defn:bg-row`. Thus the compactly supported operator's torus
realization agrees with transport through both chart maps. The only analytic
input is the bounded Euclidean operator and its kernel realization.
-/

@[expose] public noncomputable section
open MeasureTheory Set

namespace JanetCartan.PeriodicLocalL2
variable {n : ℕ} {𝕜 F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [NormedAddCommGroup G]
variable {K : Set (EuclideanSpace ℝ (Fin n))}

section Normed
variable [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [NormedSpace ℝ G]

/-- Output support of a literal physical kernel implies output support of its
L² realization (`app:ch_background:defn:bg-row`). -/
theorem kernelOperator_supported
    (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G)
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → F →L[𝕜] G)
    (hA : ∀ f, A f =ᵐ[volume] fun x ↦ ∫ y, k x y (f y))
    (hout : ∀ x ∉ K, ∀ y, k x y = 0) (f : EuclideanL2 n F) :
    ∀ᵐ x ∂volume, x ∉ K → A f x = 0 := by
  filter_upwards [hA f] with x hx hKx
  rw [hx]
  simp [hout x hKx]

/-- An input-supported kernel only uses chart data
(`app:ch_background:defn:bg-row`). -/
theorem kernelOperator_chartProjection (hK : MeasurableSet K)
    (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G)
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → F →L[𝕜] G)
    (hA : ∀ f, A f =ᵐ[volume] fun x ↦ ∫ y, k x y (f y))
    (hin : ∀ y ∉ K, ∀ x, k x y = 0) (f : EuclideanL2 n F) :
    A (chartProjection (𝕜 := 𝕜) hK f) = A f := by
  apply Lp.ext
  filter_upwards [hA (chartProjection (𝕜 := 𝕜) hK f), hA f] with x hx hx'
  rw [hx, hx']
  apply integral_congr_ae
  filter_upwards [chartProjection_coe (𝕜 := 𝕜) hK f] with y hy
  rw [hy]
  by_cases h : y ∈ K
  · rw [indicator_of_mem h]
  · simp [hin y h]

/-- A physical kernel supported in both chart variables is transported exactly
through the chart restriction and zero-extension maps
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem transferOperator_eq_chart_maps (hK : MeasurableSet K)
    (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G)
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → F →L[𝕜] G)
    (hA : ∀ f, A f =ᵐ[volume] fun x ↦ ∫ y, k x y (f y))
    (hout : ∀ x ∉ K, ∀ y, k x y = 0) (hin : ∀ y ∉ K, ∀ x, k x y = 0) :
    transferOperator A = chartToTorus hK ∘L A ∘L chartToEuclidean hK := by
  ext1 f
  change toTorus (𝕜 := 𝕜) (A (toEuclidean (𝕜 := 𝕜) f)) =
    toTorus (𝕜 := 𝕜) (chartProjection (𝕜 := 𝕜) hK
      (A (chartProjection (𝕜 := 𝕜) hK (toEuclidean (𝕜 := 𝕜) f))))
  rw [kernelOperator_chartProjection hK A k hA hin,
    chartProjection_eq_self hK _ (kernelOperator_supported A k hA hout _)]

end Normed

section Inner
variable [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
variable [CompleteSpace F] [CompleteSpace G] [NormedSpace ℝ G]

/-- The adjoint of a compact input/output kernel uses the reverse chart maps;
no torus adjoint formula is assumed (`app:ch_background:defn:bg-row`). -/
theorem transferOperator_adjoint_eq_chart_maps (hK : MeasurableSet K)
    (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G)
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → F →L[𝕜] G)
    (hA : ∀ f, A f =ᵐ[volume] fun x ↦ ∫ y, k x y (f y))
    (hout : ∀ x ∉ K, ∀ y, k x y = 0) (hin : ∀ y ∉ K, ∀ x, k x y = 0) :
    (transferOperator A).adjoint = chartToTorus hK ∘L A.adjoint ∘L chartToEuclidean hK := by
  rw [transferOperator_eq_chart_maps hK A k hA hout hin]
  simp only [ContinuousLinearMap.adjoint_comp, chartToEuclidean_adjoint,
    chartToTorus_adjoint, ContinuousLinearMap.comp_assoc]

end Inner
end JanetCartan.PeriodicLocalL2
