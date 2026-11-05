module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ShiftLaw.Expectation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Probability

/-! # Literal finite chart families

For `app:ch_waves:eq:sampling-prefix-normal`, each chart has its own literal
`shiftLaw`; their finite product is used before selecting any prefix. The common
radius is any fixed bound for the finitely many chart supports. The output space
is the full complex Hilbert space, with no finite dimensional compression.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace JanetCartan.Sampling.Realization
open SeparatedSampling

variable {J E H : Type*} [Fintype J]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The product of the literal independent chart shift laws in
`app:ch_waves:thm:sampling`. -/
def familyShiftLaw (J : Type*) [Fintype J] (p : ℕ) (B h : ℝ) :
    Measure (J → ShiftSpace p B h) := Measure.pi fun _ ↦ shiftLaw p B h

/-- The finite chart product is a probability law at every positive mesh
(`app:ch_waves:thm:sampling`). -/
theorem isProbabilityMeasure_familyShiftLaw (p : ℕ) (B : ℝ) {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (familyShiftLaw J p B h) := by
  let := isProbabilityMeasure_shiftLaw p B hh
  unfold familyShiftLaw
  infer_instance

/-- All charts have admissible shifts on one common almost-sure event
(`app:ch_waves:thm:sampling`). -/
theorem ae_admissible_familyShift {p : ℕ} {B h : ℝ} (hh : 0 < h) :
    ∀ᵐ ω ∂familyShiftLaw J p B h,
      ∀ j q i, 0 ≤ extendedShift (ω j) q i ∧ extendedShift (ω j) q i < h := by
  let := isProbabilityMeasure_shiftLaw p B hh
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval (fun _ : J ↦ shiftLaw p B h) j).quasiMeasurePreserving.ae
    (ae_admissible_extendedShift hh)

/-- The literal nonzero sample normal of one chart
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def patchSampleNormal (p : ℕ) (B : ℝ) (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H) (U : Lattice → Point) :
    H →L[ℂ] H :=
  ∑ a ∈ samples p B ψ w h U,
    weight ψ w h U a • atomNormal (T (color p a.1) (node h U a))

/-- The exact continuum block integral, using Euclidean Lebesgue measure,
for `app:ch_waves:eq:sampling-prefix-normal`. -/
def patchMeanNormal (p : ℕ) (B : ℝ) (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H) : H →L[ℂ] H :=
  ∑ q ∈ integerCube (blockCutoff p B h),
    ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z)

/-- The exact full-output deviation of the finite chart family, with the same
nodes and weights at every prefix (`app:ch_waves:eq:sampling-all-prefixes`). -/
def familyDeviation (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (ω : J → ShiftSpace p B h) : H →L[ℂ] H :=
  ∑ j, (patchSampleNormal p B (ψ j) w h (T j) (extendedShift (ω j)) -
    patchMeanNormal p B (ψ j) w h (T j))

/-- Identification with the centered literal `atomicBlock` family, so a
Bernstein producer can supply exactly the concentration premise used below
(`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem patchDeviation_eq_sum_centered {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (ω : ShiftSpace p B h) :
    patchSampleNormal p B ψ w h T (extendedShift ω) - patchMeanNormal p B ψ w h T =
      ∑ q ∈ integerCube (blockCutoff p B h),
        (atomicBlock p ψ w h T q (extendedShift ω q) -
          ∫ ω', atomicBlock p ψ w h T q (extendedShift ω' q) ∂shiftLaw p B h) := by
  rw [Finset.sum_sub_distrib, sum_atomicBlock_eq_sample_normal]
  congr 1
  symm
  apply Finset.sum_congr rfl
  intro q hq
  exact integral_atomicBlock_shiftLaw hw hψ hψc hwc hh T hT ⟨q, hq⟩

/-- The continuum normal is the expectation under the literal shift law
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_patchSampleNormal {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    (∫ ω, patchSampleNormal p B ψ w h T (extendedShift ω) ∂shiftLaw p B h) =
      patchMeanNormal p B ψ w h T :=
  integral_sampleNormal_shiftLaw hw hψ hψc hwc hh T hT

/-- Measurability of the actual operator deviation follows from continuity of
the finite block sums, without assuming a measurable successful event or
separability of the full operator space (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem stronglyMeasurable_familyDeviation {p : ℕ} (B h : ℝ)
    {ψ : J → Point → ℝ} {w : ℝ → ℝ}
    (hψ : ∀ j, Continuous (ψ j)) (hw : Continuous w)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ j c, Continuous (T j c)) :
    StronglyMeasurable (familyDeviation p B ψ w h T) := by
  unfold familyDeviation
  apply Finset.stronglyMeasurable_fun_sum
  intro j _
  apply StronglyMeasurable.sub _ stronglyMeasurable_const
  have he : (fun ω : J → ShiftSpace p B h ↦
      patchSampleNormal p B (ψ j) w h (T j) (extendedShift (ω j))) =
      fun ω ↦ ∑ q ∈ integerCube (blockCutoff p B h),
        atomicBlock p (ψ j) w h (T j) q (extendedShift (ω j) q) := by
    funext ω
    exact (sum_atomicBlock_eq_sample_normal B (ψ j) w h (T j) _).symm
  rw [he]
  apply Finset.stronglyMeasurable_fun_sum
  intro q _
  exact (continuous_atomicBlock (hψ j) hw h (T j) (hT j) q).stronglyMeasurable.comp_measurable
    ((measurable_extendedShift q).comp (measurable_pi_apply j))

/-- The all-prefix event is measurable for every fixed finite family of actual
continuous rows (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem measurableSet_familyGood {ι : Type*} {p : ℕ} (B h : ℝ)
    {ψ : J → Point → ℝ} {w : ℝ → ℝ}
    (hψ : ∀ j, Continuous (ψ j)) (hw : Continuous w)
    (s : Finset ι) (T : ι → J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ k j c, Continuous (T k j c)) (t : ℝ) :
    MeasurableSet (allPrefixesGood s (fun k ↦ familyDeviation p B ψ w h (T k)) t) := by
  have he : allPrefixesGood s (fun k ↦ familyDeviation p B ψ w h (T k)) t =
      ⋂ k ∈ s, {ω | ‖familyDeviation p B ψ w h (T k) ω‖ ≤ t} := by
    ext ω
    simp [allPrefixesGood]
  rw [he]
  apply s.measurableSet_biInter
  intro k _
  exact measurableSet_le (stronglyMeasurable_familyDeviation B h hψ hw (T k) (hT k)).norm.measurable
    measurable_const

end JanetCartan.Sampling.Realization
