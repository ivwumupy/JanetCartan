module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Jets.InputJacobian

/-!
# Differential identities on the normalized whole image

These identities connect the local inverse-jet induction to the literal
normalized inverse and Jacobian in `app:ch_regular_base:eq:actual-normal-amplitude`.
Their consumer is `exists_normalizedWholeImage_jet_bounds`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Every dyadic shell of an open whole-image domain is open, including the
low-frequency shell, as needed for actual-calculus Step 1. -/
theorem isOpen_normalDyadicShell {Ω : Set (NormalVariables n)} (hΩ : IsOpen Ω) (j : ℕ) :
    IsOpen (normalDyadicShell Ω j) := by
  have hc : Continuous (fun z : NormalVariables n ↦
      Real.sqrt (1 + ‖((2 : ℝ)^j) • z.2.2‖^2)) := by fun_prop
  exact (hΩ.preimage (normalFrequencyDilation _).continuous).inter
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))

/-- The literal normalized inverse solves the normalized phase equation at
 every point of the whole shell. This is the equation differentiated in
 actual-calculus Step 1, with no common target restriction. -/
theorem normalizedWholeImageInverse_right_inverse {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (j : ℕ) {q : NormalVariables n}
    (hq : q ∈ normalDyadicShell (bufferedNormalDomain X D S) j) :
    averagedGradient (normalizedPhase ((2 : ℝ)^j) S) q.1 q.2.1
      (normalizedNormalInverse ((2 : ℝ)^j) (wholeImageInverse S D) q.1 q.2.1 q.2.2) = q.2.2 := by
  have hρ : (2 : ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hu : normalizedNormalInverse ((2 : ℝ)^j) (wholeImageInverse S D)
      q.1 q.2.1 q.2.2 ∈ normalizedSourceChart D ((2 : ℝ)^j) := by
    change (2 : ℝ)^j • ((2 : ℝ)^j)⁻¹ •
      wholeImageInverse S D q.1 q.2.1 ((2 : ℝ)^j • q.2.2) ∈ D
    rw [smul_inv_smul₀ hρ]
    exact wholeImageInverse_mem hq.1.2.2
  have hx : q.1 ∈ X := hq.1.1
  have hy : q.2.1 ∈ X := hq.1.2.1
  rw [averagedGradient_normalizedPhase hX hD hcX hS _ hx hy hu]
  have hξ : (2 : ℝ)^j • q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D := hq.1.2.2
  simp only [normalizedNormalInverse, smul_inv_smul₀ hρ,
    averagedGradient_wholeImageInverse hξ, inv_smul_smul₀ hρ]

/-- The normalized original Jacobian is smooth on its entire source band.
This supplies the Jacobian component of `PrimitiveNormalShellInputs.input_smooth`
in `app:ch_regular_base:eq:actual-normal-amplitude`; original amplitude
smoothness is a separate input. -/
theorem normalizedAveragedJacobian_contDiffOn_band {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) (ρ a b : ℝ) :
    ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦
      normalizedNormalJacobian ρ (averagedJacobian S) q.1 q.2.1 q.2.2)
      (X ×ˢ (X ×ˢ normalizedSourceBand D ρ a b)) := by
  exact (averagedJacobian_contDiffOn hX hD hcX hS).comp
    (normalFrequencyDilation ρ).contDiff.contDiffOn (fun _ hq ↦ ⟨hq.1, hq.2.1, hq.2.2.1⟩)

/-- Jets of the literal normalized Jacobian equal the covector-Jacobian
jets of the normalized phase, so they cost one averaged-gradient derivative.
This identifies the coefficient estimated in actual-calculus Step 1. -/
theorem norm_iteratedFDeriv_normalizedAveragedJacobian_le
    {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {ρ : ℝ} (hρ : ρ ≠ 0) (a b : ℝ)
    {z : NormalVariables n} (hz : z ∈ X ×ˢ (X ×ˢ normalizedSourceBand D ρ a b)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      normalizedNormalJacobian ρ (averagedJacobian S) q.1 q.2.1 q.2.2) z‖ ≤
    ‖iteratedFDeriv ℝ (k + 1) (fun q : NormalVariables n ↦
      averagedGradient (normalizedPhase ρ S) q.1 q.2.1 q.2.2) z‖ := by
  have he : (fun q : NormalVariables n ↦
      normalizedNormalJacobian ρ (averagedJacobian S) q.1 q.2.1 q.2.2) =ᶠ[𝓝 z]
      (fun q ↦ averagedJacobian (normalizedPhase ρ S) q.1 q.2.1 q.2.2) := by
    filter_upwards [(hX.prod (hX.prod (isOpen_normalizedSourceBand hD ρ a b))).mem_nhds hz]
      with q hq
    exact (averagedJacobian_normalizedPhase hX hD hcX hS hρ hq.1 hq.2.1 hq.2.2.1).symm
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact norm_iteratedFDeriv_averagedJacobian_le hX (isOpen_normalizedSourceBand hD ρ a b) hcX
    ((normalizedPhase_contDiffOn hS ρ).mono (fun _ hq ↦ ⟨hq.1, hq.2.1⟩)) hz k

end JanetCartan.FourierIntegral.WholeImageGeometry
