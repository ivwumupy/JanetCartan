module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Jets.Inverse
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Jets.Normalized

/-!
# Uniform jets on every normalized whole-image shell

For `app:ch_regular_base:thm:actual-calculus`, Step 1, and
`app:ch_regular_base:eq:actual-normal-amplitude`, derive the Jacobian and
positive joint inverse-coordinate jets from the original normalized phase jets.
The constants precede the phase, chart, and dyadic index. The input reserve
`N + 2` becomes exactly `wholeImagePhaseReserve n` at `primitiveNormalReserve n`.

The consumer is the parent construction of `LowBounds.PrimitiveNormalShellInputs`.
Its shell-to-source `MapsTo` premise is produced by the independent whole-image
frequency comparison. This theorem proves the implication without assuming
inverse jets or restricting the shell to a common target.

The parent must separately supply smoothness and jets through `N` of both
original normalized amplitudes, composed respectively with `(x,y,u) ↦ (x,u)`
and `(x,y,u) ↦ (y,u)`, on the source band. Those are the `leftJets` and `rightJets`
fields, with their own amplitude bounds. The Jacobian smoothness here combines
with that original amplitude smoothness to give `input_smooth`. No amplitude
hypothesis is hidden in the geometric constants below.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Uniform finite normalized Jacobian jets and positive joint inverse jets
on every whole-image shell, including the fixed low-frequency shoulder.
Only `N+2` original normalized phase derivatives are used, so
`wholeImagePhaseReserve n` suffices for `PrimitiveNormalShellInputs` at
`primitiveNormalReserve n`. The exact shell-to-band mapping is a separate
frequency-comparison obligation of the parent construction; all other inverse
hypotheses are derived here from the original phase data. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`, actual-calculus Step 1. -/
theorem exists_normalizedWholeImage_jet_bounds (N : ℕ) (B b : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M > 0, ∃ L > 0, ∀ (S : E → E → ℝ) (X D : Set E),
      IsOpen X → IsOpen D → Convex ℝ X →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) →
      ∀ a : ℝ, 0 < a → a < b →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ N + 2, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedPhase ((2 : ℝ)^j) S)) z‖ ≤ B) →
      (∀ j : ℕ, MapsTo
        (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^j) (wholeImageInverse S D)))
        (normalDyadicShell (bufferedNormalDomain X D S) j)
        (X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b))) →
      ∀ j : ℕ,
        (∀ z ∈ X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b), ∀ k ≤ N,
          ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
            normalizedNormalJacobian ((2 : ℝ)^j) (averagedJacobian S) q.1 q.2.1 q.2.2) z‖ ≤ M) ∧
        (∀ z ∈ normalDyadicShell (bufferedNormalDomain X D S) j, ∀ k, 1 ≤ k → k ≤ N →
          ‖iteratedFDeriv ℝ k
            (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^j) (wholeImageInverse S D)))
            z‖ ≤ L) := by
  let F := (3 : ℝ)^(N + 1) * |B|
  obtain ⟨L, hL, hbound⟩ := exists_jointInverse_jet_bound (n := n) N F b hδ
  refine ⟨max 1 F, lt_of_lt_of_le zero_lt_one (le_max_left _ _), L, hL, ?_⟩
  intro S X D hX hD hcX hS hinj hgap a _ha _hab hj hmap j
  let ρ := (2 : ℝ)^j
  let Dj := normalizedSourceBand D ρ a b
  let U := normalDyadicShell (bufferedNormalDomain X D S) j
  let g : NormalVariables n → E := fun q ↦
    normalizedNormalInverse ρ (wholeImageInverse S D) q.1 q.2.1 q.2.2
  have hρ : ρ ≠ 0 := pow_ne_zero _ (by norm_num)
  have hDj : IsOpen Dj := isOpen_normalizedSourceBand hD ρ a b
  have hφ : ContDiffOn ℝ ∞ (Function.uncurry (normalizedPhase ρ S)) (X ×ˢ Dj) :=
    (normalizedPhase_contDiffOn hS ρ).mono (fun _ hq ↦ ⟨hq.1, hq.2.1⟩)
  have hfjet : ∀ z ∈ X ×ˢ (X ×ˢ Dj), ∀ k ≤ N + 1, ‖iteratedFDeriv ℝ k
      (fun q : NormalVariables n ↦ averagedGradient (normalizedPhase ρ S) q.1 q.2.1 q.2.2) z‖ ≤ F := by
    intro z hz k hk
    exact averagedGradient_jets_le_of_phase_jets N B hX hDj hcX hφ (hj j) hz hk
  constructor
  · intro z hz k hk
    exact ((norm_iteratedFDeriv_normalizedAveragedJacobian_le hX hD hcX hS hρ a b hz k).trans
      (hfjet z hz (k + 1) (by omega))).trans (le_max_right _ _)
  · apply hbound (normalizedPhase ρ S) X Dj U g hX hDj hcX hφ
    · exact isOpen_normalDyadicShell (isOpen_bufferedNormalDomain hX hD hcX hS hinj hδ hgap) j
    · exact (normalizedWholeImageInverse_contDiffOn_shell hX hD hcX hS hinj hδ hgap j).snd.snd
    · exact hmap j
    · intro q hq
      exact normalizedWholeImageInverse_right_inverse hX hD hcX hS j hq
    · intro q hq
      exact (hmap j hq).2.2.2.2.le
    · intro q hq
      rw [averagedJacobian_normalizedPhase hX hD hcX hS hρ hq.1 hq.2.1 hq.2.2.1]
      exact hgap _ hq.1 _ hq.2.1 _ hq.2.2.1
    · exact hfjet

end JanetCartan.FourierIntegral.WholeImageGeometry
