module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Channels

/-!
# Compact normal calculus under the manuscript mask hypotheses

The completed calculus interface for `app:ch_osc:prop:osc-normal`. The actual
multipliers and channels are constructed from the data; the geometric phase
velocity identity and uniform-in-frequency bounds remain with the consumer.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Under precisely the value and first-derivative mask bounds of
`app:ch_osc:prop:osc-normal`, construct the L∞ multipliers and all bounded full
normal channels, and prove their sum is the actual operator norm derivative.
The phase/amplitude and velocity are smooth extensions; the phase-velocity
identity is imposed only on the original amplitude carrier. -/
theorem exists_compactOscillatoryNormal_maskTransportChannels
    {D : Set E} (hD : IsOpen D) (scale K : ℝ)
    {φ : ℝ → E → E → ℝ} {a : ℝ → E → E → Fin r → ℂ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2))
    (ha : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ a p.1 p.2.1 p.2.2 i))
    {S : Set (E × E)} (hS : IsCompact S) (hSD : Prod.snd '' S ⊆ D)
    (hs : ∀ i s z, z ∉ S → a s z.1 z.2 i = 0)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m D)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hmask : ∀ u ∈ D, 0 ≤ m u ∧ m u ≤ 1)
    (hderiv : ∀ u ∈ D, ‖fderiv ℝ m u‖ ≤ L / h)
    (χ : E → E → ℂ) (hχ : ∀ z ∈ S, χ z.1 z.2 = 1)
    (s₀ : ℝ) (w : (E × E) → E → E)
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hv : ∀ x y u, u ∈ D → (x, u) ∈ S → (y, u) ∈ S →
      deriv (fun s ↦ φ s x u - φ s y u) s₀ =
        fderiv ℝ (fun v ↦ φ s₀ x v - φ s₀ y v) u (w (x, y) u)) :
    ∃ g : Option (Fin n) → Lp ℂ ∞ (volume.restrict D),
      (∀ k, g k =ᵐ[volume.restrict D] compactTransportMask m k) ∧
      ‖g none‖ ≤ 1 ∧ (∀ j, ‖g (some j)‖ ≤ L / h) ∧
    let A := fun i j s (z : E × E) u ↦ a s z.1 u i * star (a s z.2 u j)
    let c := fun k u z i j ↦ compactTransportEntry (A i j) w s₀ k
      (splitPhysicalPositions z) u
    ∃ N : Option (Fin n) → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      (∀ k f i, (N k f) i =ᵐ[volume] fun x ↦ ∑ j,
        fullNormalAmplitudeKernel (μ := volume.restrict D)
          (normalizedOscillatoryKernel scale K (φ s₀) χ)
          (fun u z ↦ c k u z i j) (g k) (f j) x) ∧
      HasDerivAt
        (fun s ↦ compactOscillatoryNormalOperator D scale K
          (φ := φ s) (a := a s)
          (hφ.continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ (ha i).continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s) (g none))
        (N none + ∑ k, N (some k)) s₀ := by
  obtain ⟨g₀, g₁, hg₀, hb₀, hg₁, hb₁⟩ := exists_mask_derivative_symbols hD m
    (hm.of_le (by simp)) hh hL hmask hderiv
  let g : Option (Fin n) → Lp ℂ ∞ (volume.restrict D) := fun k ↦
    match k with
    | none => g₀
    | some j => g₁ j
  have hg (k) : g k =ᵐ[volume.restrict D] compactTransportMask m k := by
    cases k with
    | none => exact hg₀
    | some j => exact hg₁ j
  exact ⟨g, hg, hb₀, hb₁,
    exists_compactOscillatoryNormal_transportChannels hD scale K hφ ha hS hSD hs
      hm g hg χ hχ s₀ w hw hv⟩
end JanetCartan.NormalComparison
