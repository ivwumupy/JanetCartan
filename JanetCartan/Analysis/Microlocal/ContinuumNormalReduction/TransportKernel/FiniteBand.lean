module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Entries
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.FiniteBand

/-!
# Absolute convergence of the finite carrier normal

The shared `FiniteCarrierKernelBounds` supplies measurability, compact initial
support and a pointwise bound. These imply the Fubini hypotheses for the matrix
normal action in `app:ch_background:eq:bg-full-complex-amplitude`. The bounds
must be instantiated by the compact carrier producer; no uncut bound is used.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}

private def initialSupport (h : FiniteCarrierKernelBounds d m) : Set (CarrierVariable n) :=
  h.carrierSupport ×ˢ Metric.closedBall 0 h.frequencyRadius

private theorem initialSupport_compact (h : FiniteCarrierKernelBounds d m) :
    IsCompact (initialSupport h) :=
  h.isCompact_carrierSupport.prod (isCompact_closedBall _ _)

private theorem maskedKernel_zero (h : FiniteCarrierKernelBounds d m)
    (x : Torus n) {u : CarrierVariable n} (hu : u ∉ initialSupport h) :
    maskedCarrierKernel d m x u = 0 := by
  apply h.eq_zero
  simpa only [initialSupport, Set.mem_prod, Metric.mem_closedBall, dist_zero_right,
    not_and_or, not_le] using hu

private theorem maskedKernel_entry_bound (h : FiniteCarrierKernelBounds d m)
    (x : Torus n) (u : CarrierVariable n) (i : Fin n) :
    ‖maskedCarrierKernel d m x u i‖ ≤ h.bound :=
  (PiLp.norm_apply_le _ _).trans (h.norm_le x u)

private theorem maskedKernel_entry_measurable (h : FiniteCarrierKernelBounds d m)
    (i : Fin n) : StronglyMeasurable
      (fun p : Torus n × CarrierVariable n ↦ maskedCarrierKernel d m p.1 p.2 i) :=
  (PiLp.continuous_apply 2 _ i).comp_stronglyMeasurable h.stronglyMeasurable

private theorem initialSupport_integrable (h : FiniteCarrierKernelBounds d m) :
    Integrable ((initialSupport h).indicator (fun _ ↦ (1 : ℂ))) (carrierMeasure n) := by
  apply IntegrableOn.integrable_indicator _ (initialSupport_compact h).measurableSet
  exact integrableOn_const (μ := volume) (initialSupport_compact h).measure_ne_top

/-- The literal normal density is absolutely integrable in the original initial
measure at every pair of positions (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integrable_carrierNormalDensity (h : FiniteCarrierKernelBounds d m)
    (x y : Torus n) (i j : Fin n) :
    Integrable (carrierNormalDensity d m x y i j) (carrierMeasure n) := by
  have hm : StronglyMeasurable (carrierNormalDensity d m x y i j) :=
    ((maskedKernel_entry_measurable h i).comp_measurable
    (measurable_const.prodMk measurable_id)).mul
    (((maskedKernel_entry_measurable h j).comp_measurable
      (measurable_const.prodMk measurable_id)).star)
  have hb : ∀ u, ‖carrierNormalDensity d m x y i j u‖ ≤ h.bound * h.bound := by
    intro u
    simp only [carrierNormalDensity, norm_mul, norm_star]
    exact mul_le_mul (maskedKernel_entry_bound h x u i) (maskedKernel_entry_bound h y u j)
      (norm_nonneg _) h.bound_nonneg
  apply ((initialSupport_integrable h).bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall hb)).congr
  apply Eventually.of_forall
  intro u
  by_cases hu : u ∈ initialSupport h
  · simp [Set.indicator_of_mem hu]
  · simp [carrierNormalDensity, maskedKernel_zero h y hu, Set.indicator_of_notMem hu]

/-- The first spectator Fubini premise follows from finite-band bounds and the
literal phase multiplication, rather than an assumed oscillatory integral
estimate (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integrable_phase_density (h : FiniteCarrierKernelBounds d m)
    {x y : Torus n} (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (i j : Fin n) :
    Integrable (fun u ↦ NormalComparison.oscillatoryFactor 1
      (carrierPhase d x u - carrierPhase d y u) *
        (normalDensityEntry d m x y u i j : ℂ)) (carrierMeasure n) := by
  apply (integrable_carrierNormalDensity h x y i j).congr
  exact Eventually.of_forall fun u ↦ regularizedKernel_product d m hx hy u i j

/-- Absolute integrability of the scalar product-input kernel, sufficient for
Fubini and every finite component sum in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem integrable_carrierNormalDensity_mul (h : FiniteCarrierKernelBounds d m)
    (x : Torus n) (i j : Fin n) {f : Torus n → ℂ} (hf : Integrable f) :
    Integrable (fun p : Torus n × CarrierVariable n ↦
      carrierNormalDensity d m x p.1 i j p.2 * f p.1)
      (volume.prod (carrierMeasure n)) := by
  have hm : StronglyMeasurable (fun p : Torus n × CarrierVariable n ↦
      carrierNormalDensity d m x p.1 i j p.2) :=
    ((maskedKernel_entry_measurable h i).comp_measurable
    (measurable_const.prodMk measurable_snd)).mul (maskedKernel_entry_measurable h j).star
  have hb : ∀ p : Torus n × CarrierVariable n,
      ‖carrierNormalDensity d m x p.1 i j p.2‖ ≤ h.bound * h.bound := by
    intro p
    simp only [carrierNormalDensity, norm_mul, norm_star]
    exact mul_le_mul (maskedKernel_entry_bound h x p.2 i)
      (maskedKernel_entry_bound h p.1 p.2 j) (norm_nonneg _) h.bound_nonneg
  apply ((hf.mul_prod (initialSupport_integrable h)).bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall hb)).congr
  apply Eventually.of_forall
  intro p
  by_cases hp : p.2 ∈ initialSupport h
  · simp [Set.indicator_of_mem hp]
  · simp [carrierNormalDensity, maskedKernel_zero h p.1 hp, Set.indicator_of_notMem hp]

/-- Each component of the literal masked adjoint has an absolutely convergent
output integral (`app:ch_background:eq:bg-realification`). -/
theorem integrable_maskedKernel_star_mul (h : FiniteCarrierKernelBounds d m)
    (u : CarrierVariable n) (j : Fin n) {f : Torus n → ℂ} (hf : Integrable f) :
    Integrable (fun y ↦ star (maskedCarrierKernel d m y u j) * f y) := by
  apply hf.bdd_mul (c := h.bound)
    (((maskedKernel_entry_measurable h j).comp_measurable
      (measurable_id.prodMk measurable_const)).star.aestronglyMeasurable)
  exact Eventually.of_forall fun y ↦ by
    change ‖star (maskedCarrierKernel d m y u j)‖ ≤ h.bound
    rw [norm_star]
    exact maskedKernel_entry_bound h y u j

/-- The entries used by the normal computation are exactly the mean-wave
owners' density; its slice Fubini theorem therefore applies directly
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem regularizedNormalEntry_eq_integral_carrierNormalDensity
    (x y : Torus n) (i j : Fin n) :
    regularizedNormalEntry d m x y i j =
      ∫ u, carrierNormalDensity d m x y i j u ∂carrierMeasure n := rfl

end JanetCartan.ContinuumRow.TransportKernel
