module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Symbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Bounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.PairedCoordinates

/-!
# The exact cycle symbol on a buffered physical output box

Only the output box requires inverse geometry. The local zero extension is
proved equal to the literal cycle symbol used in the compact graph identity.
The consumer is the uniform compact graph estimate in actual-calculus Step 1,
`app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set Function
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The inverse chart restricted to the buffered physical output box, for
`app:ch_regular_base:eq:actual-normal-amplitude`. No phase condition is imposed
at zero covectors or outside this chart. -/
def bufferedNormalDomain (X D : Set E) (S : E → E → ℝ) : Set (NormalVariables n) :=
  {q | q.1 ∈ X ∧ q.2.1 ∈ X ∧ q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D}

/-- Restricting the chart to a physical buffer leaves the literal normal
amplitude unchanged, since both original amplitudes vanish off the box.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem extendedCrossNormalAmplitude_eq_buffered
    (X D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (hA : ∀ x u, x ∉ X → A x u = 0) (hB : ∀ y u, y ∉ X → B y u = 0) :
    extendedCrossNormalAmplitude {q | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D} A B η J =
      extendedCrossNormalAmplitude (bufferedNormalDomain X D S) A B η J := by
  funext q
  by_cases hx : q.1 ∈ X
  · by_cases hy : q.2.1 ∈ X
    · by_cases hξ : q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D
      · have hd : q ∈ {q | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D} := hξ
        have hd' : q ∈ bufferedNormalDomain X D S := ⟨hx, hy, hξ⟩
        simp only [extendedCrossNormalAmplitude, indicator_of_mem hd, indicator_of_mem hd']
      · have hd : q ∉ {q | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D} := hξ
        have hd' : q ∉ bufferedNormalDomain X D S := fun h ↦ hξ h.2.2
        simp only [extendedCrossNormalAmplitude, indicator_of_notMem hd, indicator_of_notMem hd']
    · simp [extendedCrossNormalAmplitude, bufferedNormalDomain, hy, crossNormalAmplitude,
        crossNormalNumerator, hB _ _ hy, Set.indicator]
  · simp [extendedCrossNormalAmplitude, bufferedNormalDomain, hx, crossNormalAmplitude,
      crossNormalNumerator, hA _ _ hx, Set.indicator]

/-- Exact agreement of the cycle symbol with the locally buffered extension,
including the `2π` frequency conversion. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem cycleCrossNormalSymbol_eq_pairedBuffered
    (X D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (hA : ∀ x u, x ∉ X → A x u = 0) (hB : ∀ y u, y ∉ X → B y u = 0)
    (ξ : E) (z : Euclidean (2 * n)) :
    cycleCrossNormalSymbol D S A B η J ξ z =
      pairedNormalAmplitude
        (extendedCrossNormalAmplitude (bufferedNormalDomain X D S) A B η J)
        ((2 * Real.pi) • ξ) z := by
  unfold cycleCrossNormalSymbol cycleCrossNormalAmplitude
  rw [extendedCrossNormalAmplitude_eq_buffered X D S A B η J hA hB]
  rfl

/-- Primitive local geometry and original support used to obtain global
smoothness. Hamilton and compatible geometry supply the open chart, inverse
law and Jacobian gap; inverse coefficients supply the smooth inverse. Original
cutoff supports supply `carrier`, `closed_image` and `buffer`. Every field is
an input still to be instantiated by the parent. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
structure PrimitiveNormalGeometry
    (X D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (W K : Set (NormalVariables n)) : Prop where
  open_domain : IsOpen (bufferedNormalDomain X D S)
  inverse_smooth : ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D S)
  mapsTo : MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D S) W
  input_smooth : ContDiffOn ℝ ∞ (normalInputCoefficients A B J) W
  gap : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0
  rightInverse : ∀ q ∈ bufferedNormalDomain X D S,
    normalForwardCoordinates S (normalInverseCoordinates η q) = q
  carrier : ∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K
  closed_image : IsClosed (normalForwardCoordinates S '' K)
  buffer : normalForwardCoordinates S '' K ⊆ bufferedNormalDomain X D S
  left_output : ∀ x u, x ∉ X → A x u = 0
  right_output : ∀ y u, y ∉ X → B y u = 0

/-- Smoothness follows from the existing buffered extension construction, with
nondegeneracy needed only on the input chart. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem PrimitiveNormalGeometry.contDiff_extension
    {X D : Set E} {S : E → E → ℝ} {A B : E → E → Mat}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {W K : Set (NormalVariables n)}
    (G : PrimitiveNormalGeometry X D S A B η J W K) :
    ContDiff ℝ ∞ (extendedCrossNormalAmplitude (bufferedNormalDomain X D S) A B η J) :=
  extendedCrossNormalAmplitude_contDiff S A B η J G.open_domain G.inverse_smooth.snd.snd
    G.mapsTo G.input_smooth.snd.fst G.input_smooth.snd.snd G.input_smooth.fst G.gap
    G.rightInverse G.carrier G.closed_image G.buffer

/-- Global smoothness of the exact packed cycle symbol, deduced from primitive
local geometry. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem PrimitiveNormalGeometry.contDiff_cycleSymbol
    {X D : Set E} {S : E → E → ℝ} {A B : E → E → Mat}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {W K : Set (NormalVariables n)}
    (G : PrimitiveNormalGeometry X D S A B η J W K) :
    ContDiff ℝ ∞ (Function.uncurry (cycleCrossNormalSymbol D S A B η J)) := by
  have hs := contDiff_pairedNormalAmplitude G.contDiff_extension
  have he : Function.uncurry (cycleCrossNormalSymbol D S A B η J) =
      (fun p : E × Euclidean (2 * n) ↦ pairedNormalAmplitude
        (extendedCrossNormalAmplitude (bufferedNormalDomain X D S) A B η J)
        ((2 * Real.pi) • p.1) p.2) := by
    funext p
    exact cycleCrossNormalSymbol_eq_pairedBuffered X D S A B η J G.left_output G.right_output _ _
  rw [he]
  exact hs.comp ((contDiff_fst.const_smul (2 * Real.pi : ℝ)).prodMk contDiff_snd)

/-- The physical support box comes from the original output cutoffs, without
any hypothesis on a transformed support. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem cycleCrossNormalSymbol_supportedInCenteredBox
    {X D : Set E} {S : E → E → ℝ} {A B : E → E → Mat}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {R : ℝ}
    (hA : ∀ x u, x ∉ X → A x u = 0) (hB : ∀ y u, y ∉ X → B y u = 0)
    (hR : ∀ x ∈ X, ‖x‖ ≤ R) (ξ : E) (i j : Fin r) :
    SupportedInCenteredBox R (fun z ↦ cycleCrossNormalSymbol D S A B η J ξ z i j) := by
  simp_rw [cycleCrossNormalSymbol_eq_pairedBuffered X D S A B η J hA hB]
  apply pairedNormalAmplitude_supportedInCenteredBox hR
  intro q hq
  have hmem : q ∈ bufferedNormalDomain X D S := by
    by_contra hh
    exact hq (by simp [extendedCrossNormalAmplitude, hh])
  exact ⟨hmem.1, hmem.2.1⟩

end JanetCartan.FourierIntegral.LowBounds
