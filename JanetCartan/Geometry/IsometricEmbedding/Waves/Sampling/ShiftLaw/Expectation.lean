module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ShiftLaw.Translation

/-!
# Exact expectations of the independent atomic blocks

The uniform-shift expectation and independence in `app:ch_waves:thm:sampling`,
with the literal nodes, weights, colors and finite enumeration. The conclusions
require continuity and the existing elementary support bounds; no expectation
identity or successful event is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace JanetCartan.Sampling
open SeparatedSampling

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuity of the tensor window in `app:ch_waves:thm:sampling`. -/
theorem continuous_blockWeight {w : ℝ → ℝ} (hw : Continuous w) (h : ℝ) (q : Lattice) :
    Continuous (blockWeight w h q) := by
  apply continuous_finsetProd
  intro i _
  exact hw.comp (((continuous_apply i : Continuous (fun z : Point ↦ z i)).div_const h).sub
    (continuous_const (y := (q i : ℝ))))

/-- Continuity of the block integral density in
`app:ch_waves:eq:sampling-prefix-normal`. -/
theorem continuous_blockIntegrand {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    (hψ : Continuous ψ) (hw : Continuous w) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (q : Lattice) :
    Continuous (fun z ↦ (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z)) :=
  (hψ.mul (continuous_blockWeight hw h q)).smul
    ((hT _).clm_comp (ContinuousLinearMap.adjoint.continuous.comp (hT _)))

/-- The patch support makes the block density compactly supported, including for
operator-valued rows (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem hasCompactSupport_blockIntegrand {p : ℕ} {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (w : ℝ → ℝ) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H) (q : Lattice) :
    HasCompactSupport (fun z ↦ (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z)) := by
  apply HasCompactSupport.intro (isCompact_Icc :
    IsCompact (Set.Icc (fun _ : Fin 3 ↦ -B) (fun _ : Fin 3 ↦ B)))
  intro z hz
  have hzero : ψ z = 0 := by
    by_contra hn
    apply hz
    exact ⟨fun i ↦ (abs_le.mp (hψ.support z hn i)).1,
      fun i ↦ (abs_le.mp (hψ.support z hn i)).2⟩
  simp [hzero]

/-- The continuum block integral is a genuine Bochner integral
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_blockIntegrand {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (hψc : Continuous ψ) (hwc : Continuous w) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (q : Lattice) :
    Integrable (fun z ↦ (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z)) :=
  (continuous_blockIntegrand hψc hwc h T hT q).integrable_of_hasCompactSupport
    (hasCompactSupport_blockIntegrand hψ w h T q)

/-- The existing offset enumeration discards only zero terms on admissible shifts
(`app:ch_waves:thm:sampling`). -/
theorem blockIntegrand_eq_zero_of_not_mem {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {W h : ℝ} (hw : WindowBounds p w W) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (q m : Lattice) (hm : m ∉ integerCube (p + 2)) (u : Point) (hu : u ∈ shiftCube h) :
    (ψ (node h (fun _ ↦ u) (q, m)) *
      blockWeight w h q (node h (fun _ ↦ u) (q, m))) •
      atomNormal (T (color p q) (node h (fun _ ↦ u) (q, m))) = 0 := by
  have hz : weight ψ w h (fun _ ↦ u) (q, m) = 0 := by
    by_contra hn
    apply hm
    apply mem_integerCube.mpr
    intro i
    simpa using offset_bound hw hh (fun _ ↦ mem_shiftCube.mp hu) hn i
  have hz' : ψ (node h (fun _ ↦ u) (q, m)) *
      blockWeight w h q (node h (fun _ ↦ u) (q, m)) = 0 := by
    simpa only [weight, mul_assoc, mul_eq_zero, pow_eq_zero_iff (by decide : 3 ≠ 0),
      hh.ne', false_or] using hz
  rw [hz', zero_smul]

/-- Exact single-block expectation from uniform lattice translation
(`app:ch_waves:thm:sampling`, paper.tex, lines 5924–5941). -/
theorem integral_atomicBlock_uniformShift {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (q : Lattice) :
    ∫ u, atomicBlock p ψ w h T q u ∂uniformShift h =
      ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z) := by
  have he := integral_uniformShift_sum hh (fun i ↦ h * (q i : ℝ))
    (fun z ↦ (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z))
    (continuous_blockIntegrand hψc hwc h T hT q)
    (integrable_blockIntegrand hψ hψc hwc h T hT q) (integerCube (p + 2))
    (fun m hm u hu ↦ blockIntegrand_eq_zero_of_not_mem hw hh T q m hm u hu)
  convert he using 1
  congr 1
  funext u
  simp only [atomicBlock, Finset.smul_sum, smul_smul, weight, mul_assoc]
  rfl

/-- Integrability of a random atomic block under the constructed law, requiring
only continuity, without a global operator bound (`app:ch_waves:thm:sampling`). -/
theorem integrable_atomicBlock_shiftLaw {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B h : ℝ} (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (q : ShiftIndex p B h) :
    Integrable (fun ω ↦ atomicBlock p ψ w h T q (extendedShift ω q)) (shiftLaw p B h) := by
  exact ((measurePreserving_shift hh q).integrable_comp
    (continuous_atomicBlock hψc hwc h T hT q).stronglyMeasurable.aestronglyMeasurable).mpr
    (integrable_uniformShift_of_continuous hh (continuous_atomicBlock hψc hwc h T hT q))

/-- The expectation of the literal random block `X_q` is exactly its continuum
integral (`app:ch_waves:thm:sampling`). -/
theorem integral_atomicBlock_shiftLaw {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (q : ShiftIndex p B h) :
    ∫ ω, atomicBlock p ψ w h T q (extendedShift ω q) ∂shiftLaw p B h =
      ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z) := by
  rw [integral_extendedShift hh q _
    (continuous_atomicBlock hψc hwc h T hT q).stronglyMeasurable.aestronglyMeasurable]
  exact integral_atomicBlock_uniformShift hw hψ hψc hwc hh T hT q

/-- The literal blocks are independent with their Borel measurable structure
(`app:ch_waves:thm:sampling`). No separability of the operator space is assumed. -/
theorem iIndepFun_atomicBlock_shiftLaw [MeasurableSpace (H →L[ℂ] H)]
    [BorelSpace (H →L[ℂ] H)] {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B h : ℝ} (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    iIndepFun (fun q : ShiftIndex p B h ↦ fun ω ↦
      atomicBlock p ψ w h T q (extendedShift ω q)) (shiftLaw p B h) :=
  (iIndepFun_shift hh).comp (fun q ↦ atomicBlock p ψ w h T q)
    (fun q ↦ (continuous_atomicBlock hψc hwc h T hT q).measurable)

/-- The total block sum is integrable under the actual product law
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_sum_atomicBlock_shiftLaw {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B h : ℝ} (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    Integrable (fun ω ↦ ∑ q ∈ integerCube (blockCutoff p B h),
      atomicBlock p ψ w h T q (extendedShift ω q)) (shiftLaw p B h) := by
  apply integrable_finsetSum
  intro q hq
  exact integrable_atomicBlock_shiftLaw hψc hwc hh T hT ⟨q, hq⟩

/-- Exact expectation of the full finite block sum
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_sum_atomicBlock_shiftLaw {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    (∫ ω, ∑ q ∈ integerCube (blockCutoff p B h),
      atomicBlock p ψ w h T q (extendedShift ω q) ∂shiftLaw p B h) =
      ∑ q ∈ integerCube (blockCutoff p B h),
        ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    exact integral_atomicBlock_shiftLaw hw hψ hψc hwc hh T hT ⟨q, hq⟩
  · intro q hq
    exact integrable_atomicBlock_shiftLaw hψc hwc hh T hT ⟨q, hq⟩

/-- The normal of the enumerated nonzero samples is Bochner integrable
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_sampleNormal_shiftLaw {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B h : ℝ} (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    Integrable (fun ω ↦ ∑ a ∈ samples p B ψ w h (extendedShift ω),
      weight ψ w h (extendedShift ω) a •
        atomNormal (T (color p a.1) (node h (extendedShift ω) a))) (shiftLaw p B h) := by
  simpa only [sum_atomicBlock_eq_sample_normal] using
    integrable_sum_atomicBlock_shiftLaw (B := B) hψc hwc hh T hT

/-- The total literal sample expectation is the finite sum of continuum block
integrals, exactly as in `app:ch_waves:eq:sampling-prefix-normal`. -/
theorem integral_sampleNormal_shiftLaw {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    (∫ ω, ∑ a ∈ samples p B ψ w h (extendedShift ω),
      weight ψ w h (extendedShift ω) a •
        atomNormal (T (color p a.1) (node h (extendedShift ω) a)) ∂shiftLaw p B h) =
      ∑ q ∈ integerCube (blockCutoff p B h),
        ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z) := by
  simpa only [sum_atomicBlock_eq_sample_normal] using
    integral_sum_atomicBlock_shiftLaw hw hψ hψc hwc hh T hT

/-- Almost surely the enumeration contains every nonzero literal sample.
The small-mesh hypothesis is exactly the one in the existing support enumeration
(`app:ch_waves:thm:sampling`). -/
theorem ae_mem_samples_iff {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ} {B P W h : ℝ}
    (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ∀ᵐ ω ∂shiftLaw p B h, ∀ a,
      a ∈ samples p B ψ w h (extendedShift ω) ↔ weight ψ w h (extendedShift ω) a ≠ 0 := by
  filter_upwards [ae_admissible_extendedShift (p := p) (B := B) hh] with ω hω
  intro a
  exact mem_samples_iff hw hψ hh hh₁ hω

end JanetCartan.Sampling
