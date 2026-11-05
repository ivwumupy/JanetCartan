module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Identities
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.ChartMeasure

/-!
# Restriction to a fixed physical chart

Chart cutoffs for `app:ch_background:defn:bg-row`. A compact chart strictly
inside the open unit cell supplies the measurable-set and containment premises
below. The definitions require only measurability; the inverse and norm results
state containment and support explicitly.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.AmplitudeBound

namespace JanetCartan.PeriodicLocalL2
variable {n : ℕ} {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
variable {K : Set (EuclideanSpace ℝ (Fin n))}

/-- A chart strictly inside the centered open unit cell lies in the measurable
representative cell (`app:ch_background:defn:bg-row`). -/
theorem subset_halfOpenCell_of_strict (hK : ∀ x ∈ K, ∀ i, |x i| < (1 / 2 : ℝ)) :
    K ⊆ halfOpenCell n := by
  intro x hx i
  have h := abs_lt.mp (hK x hx i)
  exact ⟨h.1.le, by linarith [h.2]⟩

section Normed
variable [NormedSpace 𝕜 F]

/-- Lebesgue L² multiplication by the chart indicator
(`app:ch_background:defn:bg-row`). -/
def chartProjection (hK : MeasurableSet K) : EuclideanL2 n F →L[𝕜] EuclideanL2 n F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).indicator hK.nullMeasurableSet).toLp (K.indicator f)
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [((Lp.memLp (f + g)).indicator hK.nullMeasurableSet).coeFn_toLp,
          ((Lp.memLp f).indicator hK.nullMeasurableSet).coeFn_toLp,
          ((Lp.memLp g).indicator hK.nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp f).indicator hK.nullMeasurableSet).toLp _)
            (((Lp.memLp g).indicator hK.nullMeasurableSet).toLp _), Lp.coeFn_add f g] with x h h₁ h₂ h₃ h₄
        simp only [h, h₃, Pi.add_apply, h₁, h₂]
        by_cases hx : x ∈ K
        · simpa only [indicator_of_mem hx, Pi.add_apply] using h₄
        · simp only [indicator_of_notMem hx, add_zero]
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • f)).indicator hK.nullMeasurableSet).coeFn_toLp,
          ((Lp.memLp f).indicator hK.nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp f).indicator hK.nullMeasurableSet).toLp _), Lp.coeFn_smul c f]
          with x h h₁ h₂ h₃
        simp only [RingHom.id_apply, h, h₂, Pi.smul_apply, h₁]
        by_cases hx : x ∈ K
        · simpa only [indicator_of_mem hx, Pi.smul_apply] using h₃
        · simp only [indicator_of_notMem hx, smul_zero] }
    1 (fun f ↦ by
      change ‖((Lp.memLp f).indicator hK.nullMeasurableSet).toLp (K.indicator f)‖ ≤ 1 * ‖f‖
      rw [Lp.norm_toLp, one_mul, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
        (eLpNorm_indicator_le _ hK.nullMeasurableSet))

/-- The projection is the literal chart indicator (`app:ch_background:defn:bg-row`). -/
theorem chartProjection_coe (hK : MeasurableSet K) (f : EuclideanL2 n F) :
    chartProjection (𝕜 := 𝕜) hK f =ᵐ[volume] K.indicator f :=
  ((Lp.memLp f).indicator hK.nullMeasurableSet).coeFn_toLp

/-- The chart projection has chart support (`app:ch_background:defn:bg-row`). -/
theorem chartProjection_supported (hK : MeasurableSet K) (f : EuclideanL2 n F) :
    ∀ᵐ x ∂volume, x ∉ K → chartProjection (𝕜 := 𝕜) hK f x = 0 := by
  filter_upwards [chartProjection_coe (𝕜 := 𝕜) hK f] with x hx h
  rw [hx, indicator_of_notMem h]

/-- Chart projection fixes chart-supported data (`app:ch_background:defn:bg-row`). -/
theorem chartProjection_eq_self (hK : MeasurableSet K) (f : EuclideanL2 n F)
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) : chartProjection (𝕜 := 𝕜) hK f = f := by
  apply Lp.ext
  filter_upwards [chartProjection_coe (𝕜 := 𝕜) hK f, hf] with x hx hfx
  rw [hx]
  by_cases h : x ∈ K
  · exact indicator_of_mem h _
  · simp only [indicator_of_notMem h, hfx h]

/-- Restriction to the physical chart, then zero extension to the torus
(`app:ch_background:defn:bg-row`). -/
def chartToTorus (hK : MeasurableSet K) : EuclideanL2 n F →L[𝕜] PeriodicL2 n F :=
  toTorus ∘L chartProjection hK

/-- Restriction of torus data to the chart, then Euclidean zero extension
(`app:ch_background:defn:bg-row`). -/
def chartToEuclidean (hK : MeasurableSet K) : PeriodicL2 n F →L[𝕜] EuclideanL2 n F :=
  chartProjection hK ∘L toEuclidean.toContinuousLinearMap

/-- Literal chart zero extension on the torus (`app:ch_background:defn:bg-row`). -/
theorem chartToTorus_coe (hK : MeasurableSet K) (f : EuclideanL2 n F) :
    chartToTorus (𝕜 := 𝕜) hK f =ᵐ[volume] (K.indicator f) ∘ centeredTorusRepresentative := by
  exact (toTorus_coe (𝕜 := 𝕜) (chartProjection hK f)).trans
    (measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
      (chartProjection_coe (𝕜 := 𝕜) hK f).restrict)

/-- The Euclidean chart lift is literally zero outside the chart
(`app:ch_background:defn:bg-row`). -/
theorem chartToEuclidean_coe (hK : MeasurableSet K) (hcell : K ⊆ halfOpenCell n)
    (f : PeriodicL2 n F) :
    chartToEuclidean (𝕜 := 𝕜) hK f =ᵐ[volume] K.indicator (periodicLift f) := by
  filter_upwards [chartProjection_coe (𝕜 := 𝕜) hK (toEuclidean (𝕜 := 𝕜) f),
    toEuclidean_coe (𝕜 := 𝕜) f] with x hx hfx
  change chartProjection (𝕜 := 𝕜) hK (toEuclidean (𝕜 := 𝕜) f) x = _
  rw [hx]
  by_cases h : x ∈ K
  · simp only [indicator_of_mem h, hfx, indicator_of_mem (hcell h)]
  · simp only [indicator_of_notMem h]

/-- Chart-supported Euclidean fields retain their norm on the torus
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_chartToTorus_of_supported (hK : MeasurableSet K) (hcell : K ⊆ halfOpenCell n)
    (f : EuclideanL2 n F) (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ‖chartToTorus (𝕜 := 𝕜) hK f‖ = ‖f‖ := by
  change ‖toTorus (𝕜 := 𝕜) (chartProjection (𝕜 := 𝕜) hK f)‖ = _
  rw [chartProjection_eq_self hK f hf]
  exact norm_toTorus_of_supported f (hf.mono fun _ h hx ↦ h (fun hk ↦ hx (hcell hk)))

/-- Lifting a torus field supported in the chart gives physical chart support
(`app:ch_background:defn:bg-row`). -/
theorem toEuclidean_supported {f : PeriodicL2 n F}
    (hf : ∀ᵐ z ∂volume, z ∉ torusChart K → f z = 0) :
    ∀ᵐ x ∂volume, x ∉ K → toEuclidean (𝕜 := 𝕜) f x = 0 := by
  have h := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae hf)
  filter_upwards [toEuclidean_coe (𝕜 := 𝕜) f, h] with x hx hfx hKx
  rw [hx]
  by_cases hc : x ∈ halfOpenCell n
  · rw [indicator_of_mem hc]
    apply hfx hc
    simpa only [torusChart, mem_preimage, centeredTorusRepresentative_quotient hc] using hKx
  · exact indicator_of_notMem hc _

/-- The chart lift preserves the norm of chart-supported torus fields
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_chartToEuclidean_of_supported (hK : MeasurableSet K) (f : PeriodicL2 n F)
    (hf : ∀ᵐ z ∂volume, z ∉ torusChart K → f z = 0) :
    ‖chartToEuclidean (𝕜 := 𝕜) hK f‖ = ‖f‖ := by
  change ‖chartProjection (𝕜 := 𝕜) hK (toEuclidean (𝕜 := 𝕜) f)‖ = _
  rw [chartProjection_eq_self hK _ (toEuclidean_supported hf), toEuclidean.norm_map]

/-- The two chart maps are inverse on physical chart-supported fields
(`app:ch_background:defn:bg-row`). -/
theorem chartToEuclidean_chartToTorus (hK : MeasurableSet K)
    (hcell : K ⊆ halfOpenCell n) (f : EuclideanL2 n F)
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    chartToEuclidean (𝕜 := 𝕜) hK (chartToTorus (𝕜 := 𝕜) hK f) = f := by
  change chartProjection (𝕜 := 𝕜) hK
    (toEuclidean (𝕜 := 𝕜) (toTorus (𝕜 := 𝕜) (chartProjection (𝕜 := 𝕜) hK f))) = _
  rw [chartProjection_eq_self hK f hf,
    toEuclidean_toTorus f (hf.mono fun _ h hx ↦ h (fun hk ↦ hx (hcell hk))),
    chartProjection_eq_self hK f hf]

/-- The two chart maps are inverse on torus chart-supported fields
(`app:ch_background:defn:bg-row`). -/
theorem chartToTorus_chartToEuclidean (hK : MeasurableSet K) (f : PeriodicL2 n F)
    (hf : ∀ᵐ z ∂volume, z ∉ torusChart K → f z = 0) :
    chartToTorus (𝕜 := 𝕜) hK (chartToEuclidean (𝕜 := 𝕜) hK f) = f := by
  change toTorus (𝕜 := 𝕜) (chartProjection (𝕜 := 𝕜) hK
    (chartProjection (𝕜 := 𝕜) hK (toEuclidean (𝕜 := 𝕜) f))) = _
  rw [chartProjection_eq_self hK _ (toEuclidean_supported hf),
    chartProjection_eq_self hK _ (toEuclidean_supported hf), toTorus_toEuclidean]

end Normed

section Inner
variable [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Chart multiplication is self-adjoint (`app:ch_background:defn:bg-row`). -/
theorem chartProjection_adjoint (hK : MeasurableSet K) :
    (chartProjection (𝕜 := 𝕜) (F := F) hK).adjoint = chartProjection hK := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [chartProjection_coe (𝕜 := 𝕜) hK f,
    chartProjection_coe (𝕜 := 𝕜) hK g] with x hx hy
  rw [hx, hy]
  by_cases h : x ∈ K <;> simp [h]

/-- The chart restriction and zero extension are literal adjoints
(`app:ch_background:defn:bg-row`). -/
theorem chartToTorus_adjoint (hK : MeasurableSet K) :
    (chartToTorus (𝕜 := 𝕜) (F := F) hK).adjoint = chartToEuclidean hK := by
  simp only [chartToTorus, chartToEuclidean, ContinuousLinearMap.adjoint_comp,
    chartProjection_adjoint, toTorus_adjoint]

/-- The reverse chart adjoint identity (`app:ch_background:defn:bg-row`). -/
theorem chartToEuclidean_adjoint (hK : MeasurableSet K) :
    (chartToEuclidean (𝕜 := 𝕜) (F := F) hK).adjoint = chartToTorus hK := by
  rw [← chartToTorus_adjoint, ContinuousLinearMap.adjoint_adjoint]

end Inner
end JanetCartan.PeriodicLocalL2
