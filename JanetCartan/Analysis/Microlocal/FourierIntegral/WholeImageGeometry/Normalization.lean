module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.SymbolBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.QuadraticJets

/-!
# Source normalization for the whole normal image

These identities connect local phase jets to the literal normalized inverse
and Jacobian used by `NormalAmplitudeShellInputs`. They do not replace the
whole normal image by a common target. Source: actual-calculus Step 1,
`app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Original phase reserve for the low normal bound: one derivative forms the
averaged gradient and one forms its Jacobian. This dimension-only choice precedes
every output Sobolev order (`app:ch_regular_base:thm:actual-calculus`, Step 1).
Its sufficiency is proved by `exists_normalizedWholeImage_jet_bounds` and assembled
in `exists_wholeImage_primitive_inputs`. -/
def wholeImagePhaseReserve (n : ℕ) : ℕ := primitiveNormalReserve n + 2

/-- Degree-one normalization of the original phase, with positions unscaled,
for the finite input jets in actual-calculus Step 1. -/
def normalizedPhase (ρ : ℝ) (S : E → E → ℝ) (x u : E) : ℝ :=
  ρ⁻¹ * S x (ρ • u)

/-- The original source chart in normalized covectors, for the shell input
of `app:ch_regular_base:eq:actual-normal-amplitude`. -/
def normalizedSourceChart (D : Set E) (ρ : ℝ) : Set E :=
  (fun u ↦ ρ • u) ⁻¹' D

/-- A fixed normalized source annulus inside the actual rescaled chart.
The whole-image shell-range proof must supply `a` and `b`, including the fixed
low-frequency shoulder (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def normalizedSourceBand (D : Set E) (ρ a b : ℝ) : Set E :=
  normalizedSourceChart D ρ ∩ {u | a < ‖u‖ ∧ ‖u‖ < b}

/-- The normalized chart is open (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem isOpen_normalizedSourceChart {D : Set E} (hD : IsOpen D) (ρ : ℝ) :
    IsOpen (normalizedSourceChart D ρ) := hD.preimage (continuous_id.const_smul ρ)

/-- The fixed annular restriction is open, as required by the shell input
of `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem isOpen_normalizedSourceBand {D : Set E} (hD : IsOpen D) (ρ a b : ℝ) :
    IsOpen (normalizedSourceBand D ρ a b) :=
  (isOpen_normalizedSourceChart hD ρ).inter
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))

/-- Local phase smoothness survives covector normalization. The auxiliary
global extension is unnecessary for this step of actual-calculus Step 1. -/
theorem normalizedPhase_contDiffOn {S : E → E → ℝ} {X D : Set E}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) (ρ : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (normalizedPhase ρ S))
      (X ×ˢ normalizedSourceChart D ρ) :=
  contDiffOn_const.mul (hS.comp (contDiffOn_fst.prodMk (contDiffOn_snd.const_smul ρ))
    (fun _ hq ↦ hq))

/-- Averaging commutes with the literal degree-one phase normalization.
This identity uses local phase jets, not an assumed homogeneity law, in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem averagedGradient_normalizedPhase {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (ρ : ℝ) {x y u : E} (hx : x ∈ X) (hy : y ∈ X)
    (hu : u ∈ normalizedSourceChart D ρ) :
    averagedGradient (normalizedPhase ρ S) x y u = ρ⁻¹ • averagedGradient S x y (ρ • u) := by
  unfold averagedGradient averagedPhaseDifferential
  rw [← map_smul, ← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hp := hS.contDiffAt (x := (y + t • (x - y), ρ • u)) ((hX.prod hD).mem_nhds
    ⟨hcX.add_smul_sub_mem hy hx (by simpa using ht), hu⟩)
  have hd : DifferentiableAt ℝ (fun z ↦ S z (ρ • u)) (y + t • (x - y)) :=
    (hp.comp _ (f := fun z : E ↦ (z, ρ • u))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact fderiv_const_mul hd ρ⁻¹

/-- The Jacobian of the normalized phase is exactly the normalized original
Jacobian. Thus the determinant gap and phase-derived finite jets refer to the
same coefficient as `NormalAmplitudeShellInputs`, in actual-calculus Step 1. -/
theorem averagedJacobian_normalizedPhase {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {ρ : ℝ} (hρ : ρ ≠ 0) {x y u : E} (hx : x ∈ X) (hy : y ∈ X)
    (hu : u ∈ normalizedSourceChart D ρ) :
    averagedJacobian (normalizedPhase ρ S) x y u =
      normalizedNormalJacobian ρ (averagedJacobian S) x y u := by
  have he : averagedGradient (normalizedPhase ρ S) x y =ᶠ[𝓝 u]
      (fun v ↦ ρ⁻¹ • averagedGradient S x y (ρ • v)) := by
    filter_upwards [(isOpen_normalizedSourceChart hD ρ).mem_nhds hu] with v hv
    exact averagedGradient_normalizedPhase hX hD hcX hS ρ hx hy hv
  have hf := (averagedGradient_contDiffOn hX hD hcX hS).contDiffAt
    (x := (x, (y, ρ • u))) ((hX.prod (hX.prod hD)).mem_nhds ⟨hx, hy, hu⟩)
  have hd : DifferentiableAt ℝ (averagedGradient S x y) (ρ • u) :=
    (hf.comp (ρ • u) (contDiffAt_const.prodMk
      (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hcomp := ((hd.hasFDerivAt.comp u
    ((ρ • ContinuousLinearMap.id ℝ E).hasFDerivAt)).const_smul ρ⁻¹).fderiv
  rw [averagedJacobian, he.fderiv_eq]
  change fderiv ℝ (fun v ↦ ρ⁻¹ • averagedGradient S x y (ρ • v)) u = _ at hcomp
  rw [hcomp]
  ext v
  simp [normalizedNormalJacobian, averagedJacobian, smul_smul, hρ]

/-- Normalizing the constructed inverse amounts to conjugating by the two
frequency dilations. Both physical positions remain fixed, as required by
`NormalAmplitudeShellInputs` in actual-calculus Step 1. -/
theorem normalInverseCoordinates_normalized (ρ : ℝ)
    (η : E → E → E → E) :
    normalInverseCoordinates (normalizedNormalInverse ρ η) =
      normalFrequencyDilation ρ⁻¹ ∘ normalInverseCoordinates η ∘ normalFrequencyDilation ρ := rfl

/-- The normalized actual inverse is smooth on every whole-image dyadic
shell, including the zeroth shell (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem normalizedWholeImageInverse_contDiffOn_shell {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hinj : ∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|)
    (j : ℕ) :
    ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^j) (wholeImageInverse S D)))
      (normalDyadicShell (bufferedNormalDomain X D S) j) := by
  rw [normalInverseCoordinates_normalized]
  exact (normalFrequencyDilation _).contDiff.comp_contDiffOn
    ((wholeImageInverse_contDiffOn hX hD hcX hS hinj hδ hgap).comp
      (normalFrequencyDilation _).contDiff.contDiffOn (fun _ hq ↦ hq.1))

end JanetCartan.FourierIntegral.WholeImageGeometry
