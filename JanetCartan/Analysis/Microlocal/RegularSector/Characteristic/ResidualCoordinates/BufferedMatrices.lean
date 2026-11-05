module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.BufferedColumns
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.ComplexColumns
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Regularity

/-!
# Buffered physical matrices in canonical residual coordinates

The literal real columns are assembled with the existing Frobenius injection.
The factor `i` in the correction is retained. The global regularity and lower
source-time buffer come from `buffered_pencil_columns_regular`, rather than
being assumed of new matrix fields. These are local-frequency constructions;
conic continuation remains a separate obligation on the same root and chart.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- Matrix zero extension with the same auxiliary output-time cutoff as its
actual columns. Both physical masks and the right multiplier remain separate.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def bufferedAmplitude (V : Set T) (κ : ℝ → ℝ) (W : TwoTimeAmplitude d (d + 1)) :
    TwoTimeAmplitude d (d + 1) := fun t s y η ↦
  V.indicator (fun p ↦ (κ p.1 : ℂ) • W p.1 p.2.1 p.2.2.1 p.2.2.2) (t, (s, (y, η)))

private theorem buffered_leading_matrix
    (V : Set T) (κ : ℝ → ℝ) (i : Fin (d + 1))
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (r c : Fin (d + 1))
    (σ : RootState (Euclidean d) → ℝ) (p : T) :
    bufferedAmplitude V κ (leading i Q B h Φ C r c σ) p.1 p.2.1 p.2.2.1 p.2.2.2 =
      complexColumnMatrix (fun j ↦ bufferedColumn V κ
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) p) := by
  ext k j
  by_cases hp : p ∈ V <;>
    simp [bufferedAmplitude, bufferedColumn, leading, complexColumnMatrix, hp]

private theorem buffered_correction_matrix
    (V : Set T) (κ : ℝ → ℝ) (i : Fin (d + 1))
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (r c : Fin (d + 1))
    (σ : RootState (Euclidean d) → ℝ) (p : T) :
    bufferedAmplitude V κ (correction i Q B h Φ C r c σ) p.1 p.2.1 p.2.2.1 p.2.2.2 =
      Complex.I • complexColumnMatrix (fun j ↦ bufferedColumn V κ
        (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j) p) := by
  ext k j
  by_cases hp : p ∈ V <;>
    simp [bufferedAmplitude, bufferedColumn, correction, complexColumnMatrix, hp, mul_left_comm]

/-- The consumer's global smoothness of both actual matrices follows from
the supported column construction on the same chart. All norms are the
original Frobenius norms. The column regularity is the precise output of
`exists_pencil_leading_amplitude`, and the source product box is the input
already used by `twoTimeRowTransport_spec`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_buffered_pencil_matrices
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hU : IsOpen U) (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκI : tsupport κ ⊆ I) (hcσ : HasCompactSupport σ) (hσI : tsupport σ ⊆ I ×ˢ U)
    (hcols : ∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))) ∧
      ContDiffOn ℝ ∞ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
        (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U)))) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      bufferedAmplitude V κ (leading i Q B h Φ C r c σ) p.1.1 p.1.2 p.2.1 p.2.2) ∧
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      bufferedAmplitude V κ (correction i Q B h Φ C r c σ) p.1.1 p.1.2 p.2.1 p.2.2) := by
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hc j := buffered_pencil_columns_regular (coordinateSplit i) Q B h Φ C hC r c σ
    hI hU hbox κ hκ hcκ hκI hcσ hσI j (hcols j).1 (hcols j).2
  have hu : ContDiff ℝ ∞ (fun p ↦ complexColumnMatrix (fun j ↦
      bufferedColumn V κ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) p)) :=
    contDiffOn_univ.mp (contDiffOn_complexColumnMatrix (fun j ↦ (hc j).1.1.contDiffOn))
  have hv : ContDiff ℝ ∞ (fun p ↦ Complex.I • complexColumnMatrix (fun j ↦
      bufferedColumn V κ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j) p)) :=
    (contDiffOn_univ.mp (contDiffOn_complexColumnMatrix (fun j ↦ (hc j).2.1.contDiffOn))).const_smul _
  have ht : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      (p.1.1, (p.1.2, (p.2.1, p.2.2)))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd))
  constructor
  · simpa only [← buffered_leading_matrix, Function.comp_def, V] using hu.comp ht
  · simpa only [← buffered_correction_matrix, Function.comp_def, V] using hv.comp ht

/-- Both global matrices and the full physical derivative of the correction
retain the original lower source-time buffer. This supplies all three lower
buffer obligations of the two retarded amplitudes, including `B` in `P W₁`.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem buffered_pencil_matrices_lower_buffer
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) (a : ℝ)
    (hbuffer : tsupport σ ⊆ {w | a < w.1})
    {V : Set T} (hVC : V ⊆ C.target) (κ : ℝ → ℝ) :
    let W₀ := bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
    let W₁ := bufferedAmplitude V κ (correction i Q B h Φ C r c σ)
    ∀ t s y η, s ≤ a → W₀ t s y η = 0 ∧ W₁ t s y η = 0 ∧
      twoTimePhysicalApply (fun x j ↦ (coefficient i Q x j).map Complex.ofReal)
        (fun x ↦ (zeroth i B x).map Complex.ofReal) W₁ t s y η = 0 := by
  dsimp only
  have hzero t s y η (hs : s ≤ a) :
      bufferedAmplitude V κ (leading i Q B h Φ C r c σ) t s y η = 0 ∧
      bufferedAmplitude V κ (correction i Q B h Φ C r c σ) t s y η = 0 := by
    have hz j := buffered_pencil_columns_eq_zero_of_lower_buffer (coordinateSplit i)
      Q B h Φ C hC r c σ a hbuffer hVC κ (t, (s, (y, η))) hs j
    constructor
    · rw [buffered_leading_matrix V κ i Q B h Φ C r c σ (t, (s, (y, η)))]
      ext k j
      simp [complexColumnMatrix, (hz j).1]
    · rw [buffered_correction_matrix V κ i Q B h Φ C r c σ (t, (s, (y, η)))]
      ext k j
      simp [complexColumnMatrix, (hz j).2]
  intro t s y η hs
  exact ⟨(hzero t s y η hs).1, (hzero t s y η hs).2,
    twoTimePhysicalApply_eq_zero_of_lower_buffer _ _ _ a
      (fun t s y η hs ↦ (hzero t s y η hs).2) t s y η hs⟩

/-- Both buffered matrices have their topological support strictly inside
the original transported chart. This supplies the support input for the
unbounded conic continuation, with no new derivative-support hypothesis.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem buffered_pencil_matrices_support
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hU : IsOpen U) (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκI : tsupport κ ⊆ I) (hcσ : HasCompactSupport σ) (hσI : tsupport σ ⊆ I ×ˢ U)
    (hcols : ∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))) ∧
      ContDiffOn ℝ ∞ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
        (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U)))) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    tsupport (fun p : T ↦ bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2) ⊆ V ∧
    tsupport (fun p : T ↦ bufferedAmplitude V κ (correction i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2) ⊆ V := by
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hc j := buffered_pencil_columns_regular (coordinateSplit i) Q B h Φ C hC r c σ
    hI hU hbox κ hκ hcκ hκI hcσ hσI j (hcols j).1 (hcols j).2
  have hz (p : T) (hp : p ∉ V) :
      (fun q : T ↦ bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
        q.1 q.2.1 q.2.2.1 q.2.2.2) =ᶠ[𝓝 p] 0 ∧
      (fun q : T ↦ bufferedAmplitude V κ (correction i Q B h Φ C r c σ)
        q.1 q.2.1 q.2.2.1 q.2.2.2) =ᶠ[𝓝 p] 0 := by
    have hu : ∀ᶠ q in 𝓝 p, ∀ j, bufferedColumn V κ
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) q = 0 :=
      Filter.eventually_all.mpr fun j ↦ notMem_tsupport_iff_eventuallyEq.mp
        (fun ht ↦ hp ((hc j).1.2.2.2 ht))
    have hv : ∀ᶠ q in 𝓝 p, ∀ j, bufferedColumn V κ
        (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j) q = 0 :=
      Filter.eventually_all.mpr fun j ↦ notMem_tsupport_iff_eventuallyEq.mp
        (fun ht ↦ hp ((hc j).2.2.2.2 ht))
    constructor
    · filter_upwards [hu] with q hq
      rw [buffered_leading_matrix]
      ext k j
      simp [complexColumnMatrix, hq]
    · filter_upwards [hv] with q hq
      rw [buffered_correction_matrix]
      ext k j
      simp [complexColumnMatrix, hq]
  constructor
  · intro p hp
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hz p hn).1) hp
  · intro p hp
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hz p hn).2) hp

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
