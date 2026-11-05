module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactNormal

/-!
# Source-frequency control on restricted normal ranges

The consumer is the cutoff jet construction for actual-calculus Step 1,
`app:ch_regular_base:eq:actual-normal-amplitude`. The growth hypothesis concerns
only the original averaged gradient; Hamilton/compatible geometry must supply it.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison
variable {n : ℕ}
local notation "E" => Euclidean n

/-- The open source-frequency restriction used for cutoff jets in
`app:ch_regular_base:eq:actual-normal-amplitude`. It is independent of the cutoff index. -/
def cutoffJetRange (V : Set (NormalVariables n)) (ρ Q : ℝ) : Set (NormalVariables n) :=
  V ∩ {z | ρ < Q * (1 + ‖ρ • z.2.2‖)}

/-- The restriction for actual-calculus Step 1 is open, including cutoff shoulders. -/
theorem isOpen_cutoffJetRange {V : Set (NormalVariables n)} (hV : IsOpen V) (ρ Q : ℝ) :
    IsOpen (cutoffJetRange V ρ Q) :=
  hV.inter (isOpen_lt continuous_const
    (continuous_const.mul (continuous_const.add ((continuous_snd.snd.const_smul ρ).norm))))

/-- Original phase growth and the exact inverse law place every normalized
shell in the restricted source range. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem mapsTo_cutoffJetRange
    {X D : Set E} {S : E → E → ℝ} {η : E → E → E → E}
    {J : E → E → E → E →L[ℝ] E} {δ F : ℝ}
    (chart : AveragedGradientChart S X D η J δ)
    (hgrowth : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖averagedGradient S x y u‖ ≤ F * (1 + ‖u‖))
    (l : ℕ) {V : Set (NormalVariables n)}
    (hmap : MapsTo (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D S) l) V) :
    MapsTo (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D S) l)
      (cutoffJetRange V ((2 : ℝ)^l) (2 * (1 + F))) := by
  intro z hz
  refine ⟨hmap hz, ?_⟩
  obtain ⟨hx, hy, u, hu, he⟩ := hz.1
  simp only [normalFrequencyDilation_apply] at hx hy he
  have hρ : (2 : ℝ)^l ≠ 0 := by positivity
  have hinv : η z.1 z.2.1 (((2 : ℝ)^l) • z.2.2) = u := by
    rw [← he]
    exact chart.leftInverse _ hx _ hy _ hu
  change (2 : ℝ)^l < 2 * (1 + F) *
    (1 + ‖((2 : ℝ)^l) • (((2 : ℝ)^l)⁻¹ • η z.1 z.2.1 (((2 : ℝ)^l) • z.2.2))‖)
  rw [smul_inv_smul₀ hρ, hinv]
  have hg := hgrowth _ hx _ hy _ hu
  change averagedGradient S z.1 z.2.1 u = ((2 : ℝ)^l) • z.2.2 at he
  rw [he] at hg
  have hs : Real.sqrt (1 + ‖((2 : ℝ)^l) • z.2.2‖ ^ 2) ≤
      1 + ‖((2 : ℝ)^l) • z.2.2‖ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [norm_nonneg (((2 : ℝ)^l) • z.2.2)]
  have hlo := hz.2.1
  have hu0 := norm_nonneg u
  nlinarith

end JanetCartan.FourierIntegral.LowBounds
