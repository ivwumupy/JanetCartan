module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Support
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-!
# Smooth zero extensions of the actual transported columns

The compact carrier is the image under the SAME inverse chart of a compact
output-time interval times the original source support. A time cutoff only
restricts the output variable; it is not commuted through the right Fourier
multiplier. The original physical masks remain outside this construction.
The buffer hypotheses below are the source product box used by
`twoTimeRowTransport_spec`, before its local outputs are assembled in
`exists_pencil_leading_amplitude`.

This is a local chart construction. Conic continuation of the columns still
has to use the same homogeneous root and normalized nullvectors; a compact
source-frequency mask is not an order-zero conic symbol by itself.
Consumer: the amplitude smoothness and lower-buffer inputs of
`CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
variable {n d : ℕ}
local notation "T" => TwoTimePoint (Euclidean d)

/-- Zero extension of a time-buffered actual column from its smooth chart.
The cutoff is differentiated unless a plateau is explicitly used.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def bufferedColumn (V : Set T) (κ : ℝ → ℝ) (u : T → Fin n → ℝ) : T → Fin n → ℝ :=
  V.indicator (fun p ↦ κ p.1 • u p)

private theorem bufferedColumn_eventuallyEq {V : Set T} (hV : IsOpen V)
    (κ : ℝ → ℝ) (u : T → Fin n → ℝ) {p : T} (hp : p ∈ V) :
    bufferedColumn V κ u =ᶠ[𝓝 p] fun q ↦ κ q.1 • u q := by
  filter_upwards [hV.mem_nhds hp] with q hq
  exact indicator_of_mem hq _

private theorem bufferedColumn_regular
    (C : OpenPartialHomeomorph T T)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hU : IsOpen U) (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκI : tsupport κ ⊆ I)
    (σ : RootState (Euclidean d) → ℝ) (hcσ : HasCompactSupport σ)
    (hσI : tsupport σ ⊆ I ×ˢ U)
    (u : T → Fin n → ℝ)
    (hu : ContDiffOn ℝ ∞ u (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))))
    (hz : ∀ p ∈ C.target, (C.symm p).2 ∉ tsupport σ → u p = 0) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    ContDiff ℝ ∞ (bufferedColumn V κ u) ∧
      HasCompactSupport (bufferedColumn V κ u) ∧
      tsupport (bufferedColumn V κ u) ⊆ C '' (tsupport κ ×ˢ tsupport σ) ∧
      tsupport (bufferedColumn V κ u) ⊆ V := by
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hV : IsOpen V := C.symm.continuousOn.isOpen_inter_preimage
    C.open_target (hI.prod (hI.prod hU))
  have hprod : tsupport κ ×ˢ tsupport σ ⊆ C.source :=
    fun _ hp ↦ hbox ⟨hκI hp.1, hσI hp.2⟩
  have hK : IsCompact (C '' (tsupport κ ×ˢ tsupport σ)) :=
    (hcκ.prod hcσ).image_of_continuousOn (C.continuousOn.mono hprod)
  have hKV : C '' (tsupport κ ×ˢ tsupport σ) ⊆ V := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨C.map_source (hprod hq), by
      change C.symm (C q) ∈ I ×ˢ (I ×ˢ U)
      rw [C.left_inv (hprod hq)]
      exact ⟨hκI hq.1, hσI hq.2⟩⟩
  have hs : Function.support (bufferedColumn V κ u) ⊆ C '' (tsupport κ ×ˢ tsupport σ) := by
    intro p hp
    have hpV : p ∈ V := by
      by_contra hn
      exact hp (indicator_of_notMem hn _)
    have hκp : κ p.1 ≠ 0 := by
      intro hzκ
      exact hp (by simp [bufferedColumn, indicator_of_mem hpV, hzκ])
    have hσp : (C.symm p).2 ∈ tsupport σ := by
      by_contra hn
      exact hp (by simp [bufferedColumn, indicator_of_mem hpV, hz p hpV.1 hn])
    refine ⟨C.symm p, ⟨?_, hσp⟩, C.right_inv hpV.1⟩
    rw [(twoTimeChart_inverse_coordinates hC hpV.1).1]
    exact subset_tsupport κ hκp
  have ht : tsupport (bufferedColumn V κ u) ⊆ C '' (tsupport κ ×ˢ tsupport σ) :=
    closure_minimal hs hK.isClosed
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) ht, ht, ht.trans hKV⟩
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hV _ (ht.trans hKV)
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  exact (((hκ.comp contDiff_fst).contDiffAt).smul
    (hu.contDiffAt (hV.mem_nhds hp))).congr_of_eventuallyEq
      (bufferedColumn_eventuallyEq hV κ u hp)

/-- Both actual columns have smooth compact zero extensions on their SAME
transported source carrier. In particular the correction's derivative cannot
create a boundary term outside that carrier. Local smoothness is precisely
the column output of `exists_pencil_leading_amplitude`; the other hypotheses
are the original compact source mask and the chart's source box.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem buffered_pencil_columns_regular
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ)
    {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hU : IsOpen U) (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκI : tsupport κ ⊆ I) (hcσ : HasCompactSupport σ) (hσI : tsupport σ ⊆ I ×ˢ U)
    (j : Fin n)
    (hu : ContDiffOn ℝ ∞ (pencilLeadingColumn e Q B h Φ C r c σ j)
      (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))))
    (hv : ContDiffOn ℝ ∞ (pencilCorrectionColumn e Q B h Φ C r c σ j)
      (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U)))) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    let u := bufferedColumn V κ (pencilLeadingColumn e Q B h Φ C r c σ j)
    let v := bufferedColumn V κ (pencilCorrectionColumn e Q B h Φ C r c σ j)
    (ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      tsupport u ⊆ C '' (tsupport κ ×ˢ tsupport σ) ∧ tsupport u ⊆ V) ∧
    (ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      tsupport v ⊆ C '' (tsupport κ ×ˢ tsupport σ) ∧ tsupport v ⊆ V) := by
  constructor
  · exact bufferedColumn_regular C hC hI hU hbox κ hκ hcκ hκI σ hcσ hσI _ hu
      (fun p hp hn ↦ (columns_eventuallyEq_zero_of_sourceMask e Q B h Φ C hC r c σ hp hn j).1.eq_of_nhds)
  · exact bufferedColumn_regular C hC hI hU hbox κ hκ hcκ hκI σ hcσ hσI _ hv
      (fun p hp hn ↦ (columns_eventuallyEq_zero_of_sourceMask e Q B h Φ C hC r c σ hp hn j).2.eq_of_nhds)

/-- A plateau in the auxiliary output-time cutoff preserves the full column
germ on the original chart. All physical derivatives therefore agree there.
No extension commutator is dropped outside this plateau.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem bufferedColumn_eventuallyEq_on_plateau
    {V : Set T} (hV : IsOpen V) (κ : ℝ → ℝ) (u : T → Fin n → ℝ)
    {p : T} (hp : p ∈ V) (hκ : κ =ᶠ[𝓝 p.1] fun _ ↦ 1) :
    bufferedColumn V κ u =ᶠ[𝓝 p] u := by
  filter_upwards [bufferedColumn_eventuallyEq hV κ u hp,
    hκ.comp_tendsto continuous_fst.continuousAt] with q hq hκq
  change κ q.1 = 1 at hκq
  simpa only [hκq, one_smul] using hq

/-- Zero extension retains the original lower-time buffer for both actual
columns at every output and frequency, including points outside the chart.
This discharges lower-buffer inputs after complex matrix assembly.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem buffered_pencil_columns_eq_zero_of_lower_buffer
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (a : ℝ)
    (hbuffer : tsupport σ ⊆ {w | a < w.1})
    {V : Set T} (hVC : V ⊆ C.target) (κ : ℝ → ℝ)
    (p : T) (hs : p.2.1 ≤ a) (j : Fin n) :
    bufferedColumn V κ (pencilLeadingColumn e Q B h Φ C r c σ j) p = 0 ∧
      bufferedColumn V κ (pencilCorrectionColumn e Q B h Φ C r c σ j) p = 0 := by
  by_cases hp : p ∈ V
  · obtain ⟨hu, hv⟩ := columns_eventuallyEq_zero_of_lower_source_buffer
      e Q B h Φ C hC r c σ a hbuffer (hVC hp) hs j
    simp [bufferedColumn, indicator_of_mem hp, hu.eq_of_nhds, hv.eq_of_nhds]
  · simp [bufferedColumn, indicator_of_notMem hp]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
