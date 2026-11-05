module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CompactSlices
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.SmoothPhase

/-!
# Primitive convergence of the source-normalized Hamilton transport

The transport in `app:ch_background:defn:bg-carriers` is the canonical
covector derivative of the phase in `app:ch_background:eq:bg-Nsigma`.
Its smooth extension is differentiated before evaluating the fixed carrier
patch. This is distinct from the null-transport ODE density footpoint.

Consumer: the original `cNorm L (m + 2) (Yσ - Y₀)` input of the carrier
normal comparison in `paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4'.
The seed phase is an input from the Hamilton construction; convergence is
proved for its literal source normalization. Matching the retained
`PatchQuantitativeFamily.currentChart` for each dilated stress to this seed
normalization is a separate geometric obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open NormalizedBackground NormalizedBackground.SourceGeometry

variable {n : ℕ}

/-- The Hamilton transport of the actual divided phase, extended through zero
by its integral formula. The fixed patch `ζ` includes the carrier coordinate
relabeling. This is not the ODE map used to evaluate the initial density.
Source: `app:ch_background:eq:bg-Nsigma`, `app:ch_background:defn:bg-carriers`. -/
def sourceTransportPosition
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (ζ : (ℝ × Euclidean 2) → Euclidean (n - 1)) (σ : ℝ)
    (p : Euclidean n × (ℝ × Euclidean 2)) : Euclidean (n - 1) :=
  gradient (fun η ↦ sourcePhaseExtension S (σ, (p.1, η))) (ζ p.2)

/-- At zero the same transport is the canonical derivative of the frozen
linear physical phase, with the carrier label unchanged.
Source: `paper-v2.tex`, `new:lem:scaling`. -/
theorem sourceTransportPosition_zero
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (ζ : (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : Euclidean n × (ℝ × Euclidean 2)) :
    sourceTransportPosition S ζ 0 p =
      gradient (fun η ↦ inner ℝ (gradient (fun x ↦ S (x, η)) 0) p.1) (ζ p.2) := by
  simp only [sourceTransportPosition, sourcePhaseExtension_zero]

/-- Identification at every nonzero scale uses the genuine centered seed
phase. The inverse scale is retained in the Hamilton transport.
Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem sourceTransportPosition_eq_scaled
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    (ζ : (ℝ × Euclidean 2) → Euclidean (n - 1))
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V)) (hzero : ∀ η ∈ V, S (0, η) = 0)
    (h0 : (0 : Euclidean n) ∈ U) {σ : ℝ} (hσ : σ ≠ 0)
    {p : Euclidean n × (ℝ × Euclidean 2)} (hp : σ • p.1 ∈ U) (hζ : ζ p.2 ∈ V) :
    sourceTransportPosition S ζ σ p =
      σ⁻¹ • gradient (fun η ↦ S (σ • p.1, η)) (ζ p.2) := by
  unfold sourceTransportPosition gradient
  rw [fderiv_sourcePhaseExtension_parameter hU hc hV hS hzero h0 hσ hp hζ,
    map_smul]

/-- Joint smoothness of the literal source-normalized transport on the
already fixed physical, scale and carrier buffers. Only seed smoothness and
segment containment are used. Source: `app:ch_background:prop:bg-normalized`. -/
theorem contDiffOn_sourceTransportPosition
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {ζ : (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {U B : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    {W : Set (ℝ × Euclidean 2)} {r : ℝ}
    (hU : IsOpen U) (hB : IsOpen B) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V)) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hζV : MapsTo ζ W V)
    (hseg : ∀ σ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2,
      (t * σ) • x ∈ U) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (ℝ × Euclidean 2)) ↦
      sourceTransportPosition S ζ q.1 q.2) (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) := by
  have hIW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hd : ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × Euclidean (n - 1)) ↦
      fderiv ℝ (fun η ↦ sourcePhaseExtension S (q.1, (q.2.1, η))) q.2.2)
      (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V) :=
    contDiffOn_sourcePhaseExtension_parameterFDeriv
    hU hV hB isOpen_Ioo isOpen_Ioo hIW hS
    (fun q hq t ht ↦ ⟨hseg q.1 hq.1 q.2.1 hq.2.1 t ht, hq.2.2⟩)
  have hz : ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (ℝ × Euclidean 2)) ↦
      ζ q.2.2) (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) :=
    hζ.comp contDiffOn_snd.snd (fun _ hq ↦ hq.2.2)
  have harg : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean n × (ℝ × Euclidean 2)) ↦ (q.1, (q.2.1, ζ q.2.2)))
      (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ W) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hz)
  have hcomp := hd.comp harg (fun _ hq ↦ ⟨hq.1, hq.2.1, hζV hq.2.2⟩)
  unfold sourceTransportPosition gradient
  exact (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm.contDiff.comp_contDiffOn hcomp

/-- The primitive transport difference converges in the exact order `m + 2`
needed by the full-amplitude comparison. All domains precede `σ` and `m`;
the same result holds at any fixed scale inside the chosen interval.
Source: `paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4', and
`app:ch_background:prop:bg-frame`. -/
theorem tendsto_sourceTransportPosition_sub_cNorm
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {ζ : (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {U B : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    {W : Set (ℝ × Euclidean 2)} {L : Set (Euclidean n × (ℝ × Euclidean 2))}
    {r σ₀ : ℝ} (hU : IsOpen U) (hB : IsOpen B) (hV : IsOpen V) (hW : IsOpen W)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V)) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hζV : MapsTo ζ W V) (hL : IsCompact L) (hLBW : L ⊆ B ×ˢ W)
    (hσ₀ : σ₀ ∈ Ioo (-2 * r) (2 * r))
    (hseg : ∀ σ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2,
      (t * σ) • x ∈ U) (m : ℕ) :
    Tendsto (fun σ ↦ cNorm L (m + 2)
      (sourceTransportPosition S ζ σ - sourceTransportPosition S ζ σ₀))
      (𝓝 σ₀) (𝓝 0) :=
  tendsto_cNorm_slice_sub isOpen_Ioo (hB.prod hW)
    (contDiffOn_sourceTransportPosition hU hB hV hS hζ hζV hseg) hL hLBW hσ₀ (m + 2)


/-- The normalized transport is the canonical derivative of the SAME explicit
source-dilated Hamilton chart. The centered seed value follows from its actual
zero-section source; no equality with a separately chosen chart is assumed.
Source: `app:ch_background:eq:bg-Nsigma`, `app:ch_background:defn:bg-carriers`. -/
theorem sourceTransportPosition_eq_sourceHamiltonGradient
    {H : HamiltonPhase.HomogeneousSymbol (Euclidean n)}
    {Φ : HamiltonPhase.HamiltonFlow H (Euclidean (n - 1))}
    (C : HamiltonPhase.ProjectionChart Φ)
    (ζ : (ℝ × Euclidean 2) → Euclidean (n - 1))
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ (fun p : Euclidean n × Euclidean (n - 1) ↦
      HamiltonPhase.phase C.coordinates (p.1, (0, p.2))) (U ×ˢ V))
    (hsection : ∀ η ∈ V, (0, (0, (0, η))) ∈ C.source)
    (h0 : (0 : Euclidean n) ∈ U) {σ : ℝ} (hσ : σ ≠ 0)
    {p : Euclidean n × (ℝ × Euclidean 2)} (hp : σ • p.1 ∈ U) (hζ : ζ p.2 ∈ V) :
    sourceTransportPosition
      (fun q ↦ HamiltonPhase.phase C.coordinates (q.1, (0, q.2))) ζ σ p =
      gradient (fun η ↦ HamiltonPhase.phase (sourceCoordinates C.coordinates σ)
        (p.1, (0, η))) (ζ p.2) := by
  unfold sourceTransportPosition
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [hV.mem_nhds hζ] with η hη
  rw [phase_sourceCoordinates]
  have hs : ContDiffOn ℝ 1 (fun x ↦ HamiltonPhase.phase C.coordinates (x, (0, η))) U :=
    (hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ ⟨hx, hη⟩)).of_le (by simp)
  exact (sourcePhase_eq_extension hU hc hs (seedHamiltonPhase_zero C (hsection η hη))
    h0 hp hσ).symm

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
