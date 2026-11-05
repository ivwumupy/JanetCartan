module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BranchTransfer
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-!
# Support and regularity of the actual normalized branches

The consumer is the differentiated use of `exists_wideBandSliceOperator` in
`app:ch_waves:eq:individual-raw-slice`. Global continuity and compact support
are derived from the original masks and their buffered chart, including the
physical time coordinate. No regularity of a differentiated symbol is assumed.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The exact joint branch restricted to the physical output and original
annular variable, after removal of `L^(s-q)`
(`app:ch_waves:eq:individual-raw-slice`). -/
def rawSliceNormalizedBranch (S : X → P → ℝ) (A : X → P → F)
    (χ : X → ℝ) (m : P → ℂ) (ζ : P) (ε : ℝ)
    {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s) (L : ℝ)
    (x : X) (θ : P) : F :=
  normalizedSliceDerivativeAmplitude (rawSlicePhaseExtension S ζ)
    (rawSliceAmplitudeExtension A χ m ζ)
    (fun i ↦ rawSlicePhysicalLift (v i)) b L (ε, x, θ)

/-- All normalized branch supports lie in the product of the ORIGINAL
physical and input-mask supports, before any operator is constructed
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem tsupport_rawSliceNormalizedBranch_subset
    (S : X → P → ℝ) (A : X → P → F) (χ : X → ℝ) (m : P → ℂ)
    (ζ : P) (ε : ℝ) {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s) (L : ℝ) :
    tsupport (Function.uncurry (rawSliceNormalizedBranch S A χ m ζ ε v b L)) ⊆
      tsupport χ ×ˢ tsupport m := by
  have hbase : tsupport (rawSliceAmplitudeExtension A χ m ζ) ⊆
      (fun q : ℝ × X × P ↦ q.2) ⁻¹' (tsupport χ ×ˢ tsupport m) := by
    apply closure_minimal
    · intro q hq
      constructor
      · apply subset_tsupport χ
        intro hz
        apply hq
        simp [rawSliceAmplitudeExtension, hz]
      · apply subset_tsupport m
        intro hz
        apply hq
        simp [rawSliceAmplitudeExtension, hz]
    · exact ((isClosed_tsupport χ).prod (isClosed_tsupport m)).preimage continuous_snd
  apply closure_minimal _ ((isClosed_tsupport χ).prod (isClosed_tsupport m))
  intro q hq
  apply hbase (a := (ε, q))
  apply tsupport_sliceDerivativeAmplitude_subset (rawSlicePhaseExtension S ζ)
    (rawSliceAmplitudeExtension A χ m ζ) (fun i ↦ rawSlicePhysicalLift (v i)) b
  apply subset_tsupport
  intro hz
  apply hq
  change (L ^ (s - b.phaseCount))⁻¹ • _ = 0
  rw [hz, smul_zero]

/-- The original compact masks give compact support for every branch
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem hasCompactSupport_rawSliceNormalizedBranch
    (S : X → P → ℝ) (A : X → P → F) {χ : X → ℝ} {m : P → ℂ}
    (hχ : HasCompactSupport χ) (hm : HasCompactSupport m)
    (ζ : P) (ε : ℝ) {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s) (L : ℝ) :
    HasCompactSupport (Function.uncurry (rawSliceNormalizedBranch S A χ m ζ ε v b L)) :=
  (hχ.prod hm).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_rawSliceNormalizedBranch_subset S A χ m ζ ε v b L)

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ P]

/-- The primitive buffered chart supplies global smoothness after the original
masks; the phase need only be smooth near their support. This discharges the
continuity premise of the branch channel construction
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiff_rawSliceNormalizedBranch
    {U : Set X} {V Ω : Set P} {Q : Set (ℝ × X × P)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    {S : X → P → ℝ} {A : X → P → F} {χ : X → ℝ} {m : P → ℂ} {ζ : P}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ m Ω)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω) {ε : ℝ}
    (hsupp : ∀ x ∈ tsupport χ, ∀ θ ∈ tsupport m, (ε, x, θ) ∈ Q)
    {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s) (L : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (rawSliceNormalizedBranch S A χ m ζ ε v b L)) := by
  let R : Set (X × P) := (fun q ↦ (ε, q)) ⁻¹' Q
  have hR : IsOpen R := hQ.preimage (by fun_prop)
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hR
  · exact (contDiffOn_normalizedSliceDerivativeAmplitude hQ
      (contDiffOn_rawSlicePhaseExtension hU hV hQ hW hIW hS hshift)
      (contDiffOn_rawSliceAmplitudeExtension hA hχ hm
        (hshift 1 (hIW (by simp))) hθ)
      (fun i ↦ rawSlicePhysicalLift (v i)) b L).comp (f := fun q : X × P ↦ (ε, q)) (by fun_prop) (fun _ h ↦ h)
  · intro q hq
    have h := tsupport_rawSliceNormalizedBranch_subset S A χ m ζ ε v b L hq
    exact hsupp q.1 h.1 q.2 h.2

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ P] in
/-- The unchanged phase is continuous near the support of every normalized
branch. The actual quotient is identified separately at nonzero epsilon
(`app:ch_waves:eq:phase-quotient`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem continuousAt_rawSlicePhaseExtension_on_branch
    {Q : Set (ℝ × X × P)} (hQ : IsOpen Q)
    (S : X → P → ℝ) (A : X → P → F) (χ : X → ℝ) (m : P → ℂ) (ζ : P)
    (hφ : ContDiffOn ℝ ∞ (rawSlicePhaseExtension S ζ) Q) {ε : ℝ}
    (hsupp : ∀ x ∈ tsupport χ, ∀ θ ∈ tsupport m, (ε, x, θ) ∈ Q)
    {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s) (L : ℝ)
    {q : X × P}
    (hq : q ∈ tsupport (Function.uncurry (rawSliceNormalizedBranch S A χ m ζ ε v b L))) :
    ContinuousAt (fun p : X × P ↦ rawSlicePhaseExtension S ζ (ε, p)) q := by
  have h := tsupport_rawSliceNormalizedBranch_subset S A χ m ζ ε v b L hq
  exact (hφ.contDiffAt (hQ.mem_nhds (hsupp q.1 h.1 q.2 h.2))).continuousAt.comp
    (by fun_prop)

end JanetCartan.RawPrimary.SliceBounds
