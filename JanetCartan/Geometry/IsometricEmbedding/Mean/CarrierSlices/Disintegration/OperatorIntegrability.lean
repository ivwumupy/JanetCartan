module
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration.Adjoint
import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis
import Mathlib.MeasureTheory.Measure.SeparableMeasure
/-!
# Operator integrability of finite-band carrier normals

For `app:ch_background:eq:bg-T` and `app:ch_waves:eq:sampling-prefix-normal`,
the literal bounded kernel determines strongly measurable operator-valued slices.
Their normal operators are Bochner integrable in operator norm, supplying the
integrability premise of `carrier_normal_eq_integral_of_integrable`.

The proof uses two successive L² spaces: torus-valued kernel columns, then their
transverse L² sections. Synthesis is continuous for the latter norm. The published
adjoint formula identifies this synthesis with the given slice operator using
only almost-everywhere equalities of quotient representatives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace JanetCartan.ContinuumRow

-- Measurable squared distances identify measurable L²-valued parameter families.
private theorem measurable_of_dist' {A B : Type*} [MeasurableSpace A]
    [MetricSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (f : A → B) (hf : ∀ b, Measurable (fun a ↦ dist (f a) b)) : Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  let I := {p : B × ℝ // Metric.ball p.1 p.2 ⊆ U}
  have heq : (⋃ p : I, Metric.ball p.1.1 p.1.2) = U := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun p ↦ p.2)
    · intro b hb
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU b hb
      exact Set.mem_iUnion.mpr ⟨⟨(b, r), hsub⟩, by simpa using hr⟩
  obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun p : I ↦ Metric.ball p.1.1 p.1.2) (fun _ ↦ Metric.isOpen_ball)
  rw [← heq, ← hcover, Set.preimage_iUnion₂]
  exact MeasurableSet.biUnion hT (fun p _ ↦ measurableSet_lt (hf p.1.1) measurable_const)

private theorem stronglyMeasurable_toL2 {A X E : Type*} [MeasurableSpace A]
    [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [SecondCountableTopology (Lp E 2 μ)]
    (K : A → X → E) (hm : StronglyMeasurable (Function.uncurry K))
    (hK : ∀ a, MemLp (K a) 2 μ) :
    StronglyMeasurable (fun a ↦ (hK a).toLp (K a)) := by
  let : MeasurableSpace (Lp E 2 μ) := borel _
  have : BorelSpace (Lp E 2 μ) := ⟨rfl⟩
  apply Measurable.stronglyMeasurable
  apply measurable_of_dist'
  intro b
  have hi : StronglyMeasurable (fun a ↦ ∫ x, ‖K a x - b x‖ ^ 2 ∂μ) :=
    ((hm.sub ((Lp.stronglyMeasurable b).comp_measurable measurable_snd)).norm.pow 2).integral_prod_right
  have heq (a) : dist ((hK a).toLp (K a)) b = Real.sqrt (∫ x, ‖K a x - b x‖ ^ 2 ∂μ) := by
    rw [dist_eq_norm]
    have hs : ‖(hK a).toLp (K a) - b‖ ^ 2 = ∫ x, ‖K a x - b x‖ ^ 2 ∂μ := by
      rw [JanetCartan.l2_vector_norm_sq_eq_integral (𝕜 := ℂ)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((hK a).toLp (K a)) b, (hK a).coeFn_toLp] with x h₁ h₂
      simp only [h₁, Pi.sub_apply, h₂]
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [heq]
  exact hi.measurable.sqrt

open SamplingKernelBounds
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
-- The existing unit-circle volume has mass one; no measure is replaced.
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩
variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}
variable (h : FiniteCarrierKernelBounds d m)

private def column (u : CarrierVariable n) : ComplexOutputL2 n :=
  (h.memLp_kernel_output u).toLp (fun x ↦ maskedCarrierKernel d m x u)

private theorem measurable_column : StronglyMeasurable (column h) :=
  stronglyMeasurable_toL2 (μ := (volume : Measure (Torus n)))
    (fun u x ↦ maskedCarrierKernel d m x u)
    (h.stronglyMeasurable.comp_measurable measurable_swap)
    h.memLp_kernel_output

private theorem norm_column_le (z : CarrierParameter) (η : Euclidean (n - 1)) :
    ‖column h (z, η)‖ ≤ h.sliceEnvelope η := by
  have hn : 0 ≤ h.sliceEnvelope η := (norm_nonneg _).trans (h.norm_kernel_le_sliceEnvelope 0 z η)
  have hb : ∀ᵐ x ∂volume, ‖(column h (z, η)) x‖ ≤ h.sliceEnvelope η := by
    filter_upwards [(h.memLp_kernel_output (z, η)).coeFn_toLp] with x hx
    exact hx ▸ h.norm_kernel_le_sliceEnvelope x z η
  simpa [measureUnivNNReal, measure_univ] using Lp.norm_le_of_ae_bound hn hb

private theorem memLp_column (z : CarrierParameter) :
    MemLp (fun η ↦ column h (z, η)) 2 volume :=
  h.memLp_sliceEnvelope.mono'
    ((measurable_column h).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_column_le h z))

private def sectionColumn (z : CarrierParameter) :
    Lp (ComplexOutputL2 n) 2 (volume : Measure (Euclidean (n - 1))) :=
  (memLp_column h z).toLp (fun η ↦ column h (z, η))

private theorem measurable_sectionColumn : StronglyMeasurable (sectionColumn h) := by
  have : TopologicalSpace.SeparableSpace (ComplexOutputL2 n) := inferInstance
  exact stronglyMeasurable_toL2 (fun z η ↦ column h (z, η)) (measurable_column h) (memLp_column h)

private def synthesisL2 (k : Lp (ComplexOutputL2 n) 2 (volume : Measure (Euclidean (n - 1)))) :
    CarrierSliceL2 n →L[ℂ] ComplexOutputL2 n := kernelSynthesis (Lp.memLp k)

private theorem continuous_synthesisL2 : Continuous (synthesisL2 (n := n)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro k l
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply (norm_kernelSynthesis_sub_sq_le (Lp.memLp k) (Lp.memLp l)).trans_eq
  rw [l2_vector_norm_sq_eq_integral (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub k l] with η hη
  simp only [hη, Pi.sub_apply]

variable (S : CarrierParameter → CarrierSliceL2 n →L[ℂ] ComplexOutputL2 n)
variable (hS : ∀ z f, (S z f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
  regularizedCarrierSliceIntegral d m z f)

include hS in
private theorem slice_eq_synthesis (z : CarrierParameter) :
    S z = synthesisL2 (sectionColumn h z) := by
  apply ContinuousLinearMap.adjoint.injective
  ext1 w
  apply Lp.ext
  have ha := carrierSlice_adjoint_ae_eq_integral d m h z (S z) (hS z) w
  have hb := kernelSynthesis_hasAdjointKernel (Lp.memLp (sectionColumn h z)) w
  have hc := (memLp_column h z).coeFn_toLp
  filter_upwards [ha, hb, hc] with η hη hη' hcη
  change _ = ((kernelSynthesis (Lp.memLp (sectionColumn h z))).adjoint w) η
  change (sectionColumn h z : Euclidean (n - 1) → ComplexOutputL2 n) η = _ at hcη
  rw [hη, hη', hcη, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h.memLp_kernel_output (z, η)).coeFn_toLp] with x hx
  change ((column h (z, η)) : Torus n → EuclideanSpace ℂ (Fin n)) x = _ at hx
  rw [hx]

include h hS in
/-- Strong measurability in operator norm of the actual slices in
`app:ch_background:eq:bg-T`, needed for the Bochner normal integral in
`app:ch_waves:eq:sampling-prefix-normal`. -/
theorem stronglyMeasurable_carrierSlice : StronglyMeasurable S := by
  have heq : S = fun z ↦ synthesisL2 (sectionColumn h z) := funext (slice_eq_synthesis h S hS)
  rw [heq]
  exact continuous_synthesisL2.comp_stronglyMeasurable (measurable_sectionColumn h)

include h hS in
/-- The actual slice vanishes outside the compact carrier support, as required by
`app:ch_waves:eq:sampling-prefix-normal`. -/
theorem carrierSlice_eq_zero_off_support (z : CarrierParameter) (hz : z ∉ h.carrierSupport) :
    S z = 0 := by
  ext1 f
  apply Lp.ext
  filter_upwards [hS z f, Lp.coeFn_zero (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Torus n))]
    with x hx hzero
  simpa [regularizedCarrierSliceIntegral, h.eq_zero x z _ (Or.inl hz), hzero] using hx

include h hS in
/-- Uniform operator bound from the compact transverse envelope in
`app:ch_background:eq:bg-T`. -/
theorem norm_carrierSlice_le_sliceEnvelope (z : CarrierParameter) :
    ‖S z‖ ≤ ‖h.memLp_sliceEnvelope.toLp h.sliceEnvelope‖ := by
  rw [slice_eq_synthesis h S hS z]
  have hb : ‖synthesisL2 (sectionColumn h z)‖ ≤ ‖sectionColumn h z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact (norm_kernelSynthesis_sq_le (Lp.memLp (sectionColumn h z))).trans_eq
      (l2_vector_norm_sq_eq_integral (𝕜 := ℂ) (sectionColumn h z)).symm
  apply hb.trans
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(memLp_column h z).coeFn_toLp, h.memLp_sliceEnvelope.coeFn_toLp] with η hη heη
  change ‖(sectionColumn h z : Euclidean (n - 1) → ComplexOutputL2 n) η‖ ≤ _
  change (sectionColumn h z : Euclidean (n - 1) → ComplexOutputL2 n) η = _ at hη
  rw [hη, heη]
  exact (norm_column_le h z η).trans (le_abs_self _)

include h hS in
/-- Strong measurability in operator norm of the actual slice normals in
`app:ch_waves:eq:sampling-prefix-normal`. -/
theorem stronglyMeasurable_carrierSlice_normal :
    StronglyMeasurable (fun z ↦ S z ∘L (S z).adjoint) := by
  have hm := stronglyMeasurable_carrierSlice h S hS
  exact (continuous_id.clm_comp (ContinuousLinearMap.adjoint.continuous)).comp_stronglyMeasurable hm

include h hS in
/-- Operator-norm Bochner integrability of the actual finite-band slice normals
in `app:ch_waves:eq:sampling-prefix-normal`. This supplies the `hA` input of
`carrier_normal_eq_integral_of_integrable` from the forward kernel formula alone. -/
theorem integrable_carrierSlice_normal :
    Integrable (fun z ↦ S z ∘L (S z).adjoint) (volume.prod volume) := by
  have hc : HasCompactSupport (fun z ↦ S z ∘L (S z).adjoint) := by
    apply HasCompactSupport.intro h.isCompact_carrierSupport
    intro z hz
    simp [carrierSlice_eq_zero_off_support h S hS z hz]
  apply memLp_one_iff_integrable.mp
  apply hc.memLp_of_bound (stronglyMeasurable_carrierSlice_normal h S hS).aestronglyMeasurable
    (‖h.memLp_sliceEnvelope.toLp h.sliceEnvelope‖ ^ 2)
  apply Filter.Eventually.of_forall
  intro z
  calc
    ‖S z ∘L (S z).adjoint‖ ≤ ‖S z‖ * ‖(S z).adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖S z‖ ^ 2 := by rw [ContinuousLinearMap.adjoint.norm_map]; ring
    _ ≤ ‖h.memLp_sliceEnvelope.toLp h.sliceEnvelope‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_carrierSlice_le_sliceEnvelope h S hS z)

end JanetCartan.ContinuumRow
