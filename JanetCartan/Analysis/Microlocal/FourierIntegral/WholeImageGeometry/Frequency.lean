module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Frequency.Comparison
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Frequency.ShellRange

/-!
# Frequency geometry from the original phase

For `app:ch_regular_base:thm:actual-calculus`, Step 1, the original mixed
second-jet bound, positive averaged-Jacobian determinant gap and local
homogeneity give two-sided frequency comparison on the whole source chart.
The original positive source collar then gives a fixed normalized annulus
for every whole-image dyadic shell, including the two low shells.

These results supply `primitiveNormalGeometry_of_frequency_bound` and the
shell-range input to the independent normalized-jet construction. The parent
whole-image geometry construction must instantiate the original mixed bound,
homogeneity, determinant gap and collar from its buffered phase data; no
inverse estimate or smaller common target is an input here.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Whole-image frequency comparison and normalized shell ranges from the
original phase's degree-zero mixed bound, determinant gap and source collar.
All four constants precede the phase and shell index. This discharges the
frequency and range obligations in `app:ch_regular_base:eq:actual-normal-amplitude`;
the separate injectivity hypothesis is needed for inverse smoothness, but is
unnecessary for these estimates on the actual image. -/
theorem exists_wholeImage_frequency_comparison_and_shell_range
    (B : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ F > 0, ∃ C > 0, ∃ a > 0, ∃ b > a,
      ∀ (S : E → E → ℝ) (X D : Set E),
      IsOpen X → IsOpen D → Convex ℝ X →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
        S x (t • u) = t * S x u) →
      (∀ x ∈ X, ∀ u ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) →
      (∀ u ∈ D, ε < ‖u‖) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * ‖u‖ ∧
        ‖u‖ ≤ C * ‖averagedGradient S x y u‖) ∧
      (∀ j : ℕ, MapsTo
        (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^j) (wholeImageInverse S D)))
        (normalDyadicShell (bufferedNormalDomain X D S) j)
        (X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b))) := by
  obtain ⟨F, hF, C, hC, hcompare⟩ :=
    exists_frequency_comparison_of_mixed_bound (n := n) B hδ
  obtain ⟨a, ha, b, hab, hrange⟩ :=
    exists_normalizedWholeImageInverse_shell_range (n := n) hε hF hC
  refine ⟨F, hF, C, hC, a, ha, b, hab, ?_⟩
  intro S X D hX hD hcX hS hhom hb hgap hcollar
  have hf := hcompare S X D hX hD hcX hS hhom hb hgap
  exact ⟨hf, hrange S X D hcollar hf⟩

end JanetCartan.FourierIntegral.WholeImageGeometry
