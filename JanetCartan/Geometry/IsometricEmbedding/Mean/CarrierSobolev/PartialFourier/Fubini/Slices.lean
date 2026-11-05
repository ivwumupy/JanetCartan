module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Iterated
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# L² sections of carrier functions

The Fubini identification used by the partial Fourier transform in
`app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`.
The slice is zero at exceptional parameters where it does not belong to L².
-/

@[expose] public noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal Topology
namespace JanetCartan.CarrierSobolev
open ContinuumRow
namespace Fubini

/-- Squared L² norm, used in the carrier Fubini norm identity
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Almost every transverse section is L²; consumed by the carrier Fubini
representative formula (`app:ch_background:prop:bg-adjoint`). -/
theorem memLp_slice_ae {n : ℕ} {f : CarrierVariable n → ℂ}
    (hf : MemLp f 2 (carrierMeasure n)) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      MemLp (fun η => f (z, η)) 2 volume := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hi.prod_right_ae] with z hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

/-- L² class of a transverse slice, extended by zero on exceptional parameters;
used to construct the Fubini map in `app:ch_background:prop:bg-adjoint`. -/
def slice {n : ℕ} (f : CarrierVariable n → ℂ) (z : CarrierParameter) : TransverseL2 n := by
  classical
  exact if h : MemLp (fun η => f (z, η)) 2 volume then h.toLp _ else 0

/-- The slice construction agrees with the original section whenever that
section is L² (`app:ch_background:prop:bg-adjoint`). -/
theorem slice_coeFn {n : ℕ} {f : CarrierVariable n → ℂ} {z : CarrierParameter}
    (h : MemLp (fun η => f (z, η)) 2 volume) :
    slice f z =ᵐ[volume] fun η => f (z, η) := by
  rw [slice, dite_eq_left h]
  exact h.coeFn_toLp

/-- The good-section set is measurable for a strongly measurable product
representative (`app:ch_background:prop:bg-adjoint`). -/
theorem measurableSet_memLp_slice {n : ℕ} {f : CarrierVariable n → ℂ}
    (hf : StronglyMeasurable f) :
    MeasurableSet {z : CarrierParameter | MemLp (fun η => f (z, η)) 2 volume} := by
  have he : {z : CarrierParameter | MemLp (fun η => f (z, η)) 2 volume} =
      {z | Integrable (fun η => ‖f (z, η)‖ ^ 2) volume} := by
    ext z
    exact memLp_two_iff_integrable_sq_norm
      ((hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable)
  rw [he]
  exact measurableSet_integrable (hf.norm.pow 2)

private theorem measurable_of_dist {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (h : ∀ c, Measurable (fun x => dist (f x) c)) : Measurable f := by
  have hb : IsTopologicalBasis {s : Set E | ∃ c r, s = Metric.ball c r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨c, r, rfl⟩
      exact Metric.isOpen_ball
    · intro x u hx hu
      obtain ⟨r, hr, hru⟩ := Metric.isOpen_iff.mp hu x hx
      exact ⟨Metric.ball x r, ⟨x, r, rfl⟩, Metric.mem_ball_self hr, hru⟩
  rw [BorelSpace.measurable_eq (α := E), hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨c, r, rfl⟩
  exact measurableSet_lt (h c) measurable_const

/-- Strong measurability of L²-valued carrier sections. This is the measurable
input to `carrierFubiniEquiv`, not a joint-evaluation assertion about arbitrary
iterated representatives (`app:ch_background:prop:bg-adjoint`). -/
theorem stronglyMeasurable_slice {n : ℕ} {f : CarrierVariable n → ℂ}
    (hf : StronglyMeasurable f) : StronglyMeasurable (slice f) := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  borelize ↥(TransverseL2 n)
  apply Measurable.stronglyMeasurable
  apply measurable_of_dist
  intro c
  have hm : Measurable (fun z => Real.sqrt (∫ η, ‖f (z, η) - c η‖ ^ 2 ∂volume)) :=
    ((hf.sub ((Lp.stronglyMeasurable c).comp_measurable measurable_snd)).norm.pow 2
      |>.integral_prod_right').measurable.sqrt
  have he : (fun z => dist (slice f z) c) =
      fun z => if MemLp (fun η => f (z, η)) 2 volume then
        Real.sqrt (∫ η, ‖f (z, η) - c η‖ ^ 2 ∂volume) else ‖c‖ := by
    funext z
    by_cases hz : MemLp (fun η => f (z, η)) 2 volume
    · rw [ite_eq_left hz, dist_eq_norm]
      have hs : ‖slice f z - c‖ ^ 2 = ∫ η, ‖f (z, η) - c η‖ ^ 2 ∂volume := by
        rw [norm_sq]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (slice f z) c, slice_coeFn hz] with η hη hη'
        simp only [hη, Pi.sub_apply, hη']
      rw [← hs, Real.sqrt_sq (norm_nonneg _)]
    · simp [slice, hz]
  rw [he]
  exact Measurable.ite (measurableSet_memLp_slice hf) hm measurable_const

/-- Pointwise squared norm of a good slice, used by the norm identity and
surjectivity of the carrier Fubini map (`app:ch_background:prop:bg-adjoint`). -/
theorem slice_norm_sq {n : ℕ} {f : CarrierVariable n → ℂ} {z : CarrierParameter}
    (hz : MemLp (fun η => f (z, η)) 2 volume) :
    ‖slice f z‖ ^ 2 = ∫ η, ‖f (z, η)‖ ^ 2 ∂volume := by
  rw [norm_sq]
  exact integral_congr_ae ((slice_coeFn hz).fun_comp (fun x => ‖x‖ ^ 2))

/-- The L²-valued section map is itself L² on the carrier parameter space
(`app:ch_background:prop:bg-adjoint`). -/
theorem memLp_slice {n : ℕ} {f : CarrierVariable n → ℂ}
    (hm : StronglyMeasurable f) (hf : MemLp f 2 (carrierMeasure n)) :
    MemLp (slice f) 2 (volume.prod volume) := by
  apply (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_slice hm).aestronglyMeasurable).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  apply hi.integral_prod_left.congr
  filter_upwards [memLp_slice_ae hf] with z hz
  exact (slice_norm_sq hz).symm

/-- Every transverse section of a compact continuous product-space test is
L², including in dimension `n - 1 = 0`. The compact smooth tests used in the
partial Fourier integral formula satisfy these hypotheses
(`app:ch_background:prop:bg-adjoint`). -/
theorem memLp_slice_of_continuous_hasCompactSupport {n : ℕ}
    {f : CarrierVariable n → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (z : CarrierParameter) : MemLp (fun η => f (z, η)) 2 volume := by
  apply (hf.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro η hη
  exact ⟨(z, η), subset_tsupport f hη, rfl⟩

end Fubini
end JanetCartan.CarrierSobolev
