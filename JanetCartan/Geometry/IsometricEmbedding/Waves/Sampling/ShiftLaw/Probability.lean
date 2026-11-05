module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AtomicBlocks
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Independent uniform block shifts

The finite probability law in `app:ch_waves:thm:sampling` (paper.tex,
lines 5782–5788). Each enumerated block receives normalized Lebesgue measure
on `[0,h)^3`; all other shifts are zero. The law is constructed before any
concentration or successful-event argument.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace JanetCartan.Sampling
open SeparatedSampling

/-- The half-open shift cube of `app:ch_waves:thm:sampling`. -/
def shiftCube (h : ℝ) : Set Point := Set.univ.pi fun _ ↦ Set.Ico 0 h

/-- The shift cube is Borel measurable (`app:ch_waves:thm:sampling`). -/
theorem measurableSet_shiftCube (h : ℝ) : MeasurableSet (shiftCube h) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

/-- Membership in the literal half-open cube (`app:ch_waves:thm:sampling`). -/
theorem mem_shiftCube {h : ℝ} {u : Point} :
    u ∈ shiftCube h ↔ ∀ i, 0 ≤ u i ∧ u i < h := by
  simp [shiftCube, Set.mem_pi]

/-- The volume normalization in `app:ch_waves:thm:sampling` is exactly `h³`. -/
theorem volume_shiftCube (h : ℝ) : volume (shiftCube h) = ENNReal.ofReal h ^ 3 := by
  simp [shiftCube, Real.volume_pi_Ico]

/-- Uniform Lebesgue probability on the shift cube of `app:ch_waves:thm:sampling`.
For `h > 0` its normalization is proved below. -/
def uniformShift (h : ℝ) : Measure Point := ProbabilityTheory.cond volume (shiftCube h)

/-- Normalization of the uniform shift law (`app:ch_waves:thm:sampling`). -/
theorem isProbabilityMeasure_uniformShift {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (uniformShift h) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [volume_shiftCube]
    exact pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hh))
  · rw [volume_shiftCube]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

instance {h : ℝ} [Fact (0 < h)] : IsProbabilityMeasure (uniformShift h) :=
  isProbabilityMeasure_uniformShift Fact.out

/-- Every uniform shift is almost surely admissible (`app:ch_waves:thm:sampling`). -/
theorem ae_mem_shiftCube (h : ℝ) : ∀ᵐ u ∂uniformShift h, u ∈ shiftCube h := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_shiftCube h)) _

/-- The finite block index set from `app:ch_waves:thm:sampling`. -/
abbrev ShiftIndex (p : ℕ) (B h : ℝ) := ↥(integerCube (blockCutoff p B h))

/-- The finite product sample space in `app:ch_waves:thm:sampling`. -/
abbrev ShiftSpace (p : ℕ) (B h : ℝ) := ShiftIndex p B h → Point

/-- Independent uniform shifts on all enumerated blocks
(`app:ch_waves:thm:sampling`). -/
def shiftLaw (p : ℕ) (B h : ℝ) : Measure (ShiftSpace p B h) :=
  Measure.pi fun _ ↦ uniformShift h

/-- The product shift law has total mass one (`app:ch_waves:thm:sampling`). -/
theorem isProbabilityMeasure_shiftLaw (p : ℕ) (B : ℝ) {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (shiftLaw p B h) := by
  let := isProbabilityMeasure_uniformShift hh
  unfold shiftLaw
  infer_instance

instance (p : ℕ) (B h : ℝ) [Fact (0 < h)] : IsProbabilityMeasure (shiftLaw p B h) :=
  isProbabilityMeasure_shiftLaw p B Fact.out

/-- Extend the independently chosen shifts by zero outside the finite enumeration
in `app:ch_waves:thm:sampling`. -/
def extendedShift {p : ℕ} {B h : ℝ} (ω : ShiftSpace p B h) (q : Lattice) : Point :=
  if hq : q ∈ integerCube (blockCutoff p B h) then ω ⟨q, hq⟩ else 0

/-- Extension preserves every enumerated shift (`app:ch_waves:thm:sampling`). -/
@[simp] theorem extendedShift_coe {p : ℕ} {B h : ℝ}
    (ω : ShiftSpace p B h) (q : ShiftIndex p B h) : extendedShift ω q = ω q := by
  simp [extendedShift, q.property]

/-- Unenumerated shifts are zero (`app:ch_waves:thm:sampling`). -/
theorem extendedShift_of_not_mem {p : ℕ} {B h : ℝ} (ω : ShiftSpace p B h)
    {q : Lattice} (hq : q ∉ integerCube (blockCutoff p B h)) :
    extendedShift ω q = 0 := by simp [extendedShift, hq]

/-- Each extended shift is a measurable random variable
(`app:ch_waves:thm:sampling`). -/
theorem measurable_extendedShift {p : ℕ} {B h : ℝ} (q : Lattice) :
    Measurable (fun ω : ShiftSpace p B h ↦ extendedShift ω q) := by
  unfold extendedShift
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- Every enumerated shift has exactly the uniform marginal law
(`app:ch_waves:thm:sampling`). -/
theorem measurePreserving_shift {p : ℕ} {B h : ℝ} (hh : 0 < h)
    (q : ShiftIndex p B h) :
    MeasurePreserving (fun ω : ShiftSpace p B h ↦ extendedShift ω q)
      (shiftLaw p B h) (uniformShift h) := by
  let := isProbabilityMeasure_uniformShift hh
  simpa only [extendedShift_coe, shiftLaw, id_eq] using measurePreserving_eval (fun _ ↦ uniformShift h) q

/-- Independence of the uniform block shifts (`app:ch_waves:thm:sampling`). -/
theorem iIndepFun_shift {p : ℕ} {B h : ℝ} (hh : 0 < h) :
    iIndepFun (fun q : ShiftIndex p B h ↦ fun ω : ShiftSpace p B h ↦ extendedShift ω q)
      (shiftLaw p B h) := by
  let := isProbabilityMeasure_uniformShift hh
  simpa only [extendedShift_coe, shiftLaw, id_eq] using
    (iIndepFun_pi (μ := fun _ : ShiftIndex p B h ↦ uniformShift h)
      (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id))

/-- All shifts, including those extended by zero, simultaneously satisfy the
admissibility bounds in `app:ch_waves:thm:sampling` almost surely. -/
theorem ae_admissible_extendedShift {p : ℕ} {B h : ℝ} (hh : 0 < h) :
    ∀ᵐ ω ∂shiftLaw p B h, ∀ q i, 0 ≤ extendedShift ω q i ∧ extendedShift ω q i < h := by
  apply ae_all_iff.mpr
  intro q
  by_cases hq : q ∈ integerCube (blockCutoff p B h)
  · have ha := (measurePreserving_shift hh ⟨q, hq⟩).quasiMeasurePreserving.ae
      (ae_mem_shiftCube h)
    exact ha.mono fun ω hω ↦ mem_shiftCube.mp hω
  · exact Filter.Eventually.of_forall fun ω i ↦ by
      simp [extendedShift_of_not_mem ω hq, hh]

/-- Integrating one block coordinate reduces exactly to the uniform marginal
(`app:ch_waves:thm:sampling`). -/
theorem integral_extendedShift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℕ} {B h : ℝ} (hh : 0 < h) (q : ShiftIndex p B h) (f : Point → F)
    (hf : AEStronglyMeasurable f (uniformShift h)) :
    ∫ ω, f (extendedShift ω q) ∂shiftLaw p B h = ∫ u, f u ∂uniformShift h := by
  let := isProbabilityMeasure_uniformShift hh
  simpa only [extendedShift_coe, shiftLaw, id_eq] using integral_comp_eval (i := q) hf

/-- The uniform shift integral is the normalized cube integral, with the literal
factor `h⁻³` from `app:ch_waves:thm:sampling`. -/
theorem integral_uniformShift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ} (hh : 0 < h) (f : Point → F) :
    ∫ u, f u ∂uniformShift h = (h ^ 3)⁻¹ • ∫ u in shiftCube h, f u := by
  simp [uniformShift, ProbabilityTheory.cond, integral_smul_measure,
    volume_shiftCube, ENNReal.toReal_ofReal hh.le]

end JanetCartan.Sampling
