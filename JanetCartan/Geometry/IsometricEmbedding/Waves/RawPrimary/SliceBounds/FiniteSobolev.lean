module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.PrimitiveSobolev

/-!
# Prescribed finite-order raw Sobolev estimate for every cutoff scale

The `L=1` specialization in the proof of `app:ch_waves:thm:individual`
requires bounded coefficient jets only through the explicitly displayed fixed
shift of the requested order. No scale-dependent lower cutoff is imposed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceBounds
open NormalComparison RawInputPartition SingleChannel ActualCarriers.FrozenPhaseReference

variable {d m : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "E" => Euclidean (d + 1)
local notation "Qₚ" => ℝ × X × Y
local notation "Mat" => Matrix (Fin m) (Fin (d + 1)) ℂ

/-- At each prescribed finite order, ordinary bounded original coefficient
jets through `s + rawSliceJetOrder (d+1) + 1` give the SAME physical integral's
`H^s` estimate for all `K≥1`. This is an actual specialization of the primitive
constructor with `L=1`; there is no differentiated estimate or Sobolev premise
(`app:ch_waves:eq:individual-raw-slice`, `app:ch_waves:thm:individual`). -/
theorem exists_rawPhysicalSliceSobolev_finiteJets
    {ξ : E} (sec : AdaptedSection ξ)
    (G : UniformNormalGeometry d (m * (d + 1))) (C : ℕ → ℝ)
    {U : Set E} {V Ω : Set Y} {Q H : Set Qₚ} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hH : IsCompact H) (hHQ : H ⊆ Q)
    (hband : wideBand (d + 1) 0 ⊆ Ω) (ζ : Y) (hζ : ζ ∈ V)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q
      ((adaptedPhysicalCoordinates sec ⁻¹' U) ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p bmask : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hbmask : ∀ j, 0 ≤ bmask j) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) :
    ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
      ∀ (K τ : ℝ), 1 ≤ K → τ ≠ 0 →
      ∀ (χ : E → ℝ) (mask : Y → ℂ) (S : E → Y → ℝ) (A : E → Y → Mat),
      ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      (∀ q, χ (adaptedPhysicalCoordinates sec q) ≠ 0 → q.2 ∈ G.X₀) →
      (∀ x ∈ tsupport χ, ((adaptedPhysicalCoordinates sec).symm x).1 ∈ Ioo t₀ t₁) →
      Measurable mask → ∀ M : ℝ, (∀ η, ‖mask η‖ ≤ M) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      let U₀ := adaptedPhysicalCoordinates sec ⁻¹' U
      let S₀ := fun q η ↦ S (adaptedPhysicalCoordinates sec q) η
      let A₀ := fun q η i ↦ matrixChannelEquiv m (d + 1) (A (adaptedPhysicalCoordinates sec q) η) i
      let χ₀ := fun q ↦ χ (adaptedPhysicalCoordinates sec q)
      let mask₀ := fun (j : Fin (cutoffCount K)) (θ : Y) ↦
        (Real.sqrt ‖θ‖ : ℂ) * weightedRadialBand (n := d + 1) mask j.val ((2 : ℝ) ^ j.val • θ)
      (∀ j, ContDiffOn ℝ ∞ (mask₀ j) Ω) →
      (∀ j, Function.support (mask₀ j) ⊆ G.D₀) →
      (∀ j, tsupport (mask₀ j) ⊆ Ω) →
      ∀ s : ℕ,
      (∀ j, ∀ q ∈ H, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun z : Qₚ ↦ (χ₀ z.2.1 : ℂ) * mask₀ j z.2.2) q‖ ≤ bmask k) →
      (∀ z ∈ U₀ ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (Function.uncurry A₀) z‖ ≤
          a k) →
      (∀ z ∈ U₀ ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun w : X × Y ↦ fderiv ℝ (S₀ w.1) w.2) z‖ ≤
          p k) →
      (∀ j : Fin (cutoffCount K), τ * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) →
      (∀ j : Fin (cutoffCount K), ∀ x ∈ U₀, ∀ θ ∈ Ω,
        (τ * (2 : ℝ) ^ j.val, x, θ) ∈ Q) →
      (∀ j : Fin (cutoffCount K), ∀ θ ∈ Ω, ζ + (τ * (2 : ℝ) ^ j.val) • θ ∈ V) →
      (∀ η ∈ Metric.closedBall 0 (4 * K), ζ + τ • η ∈ V) →
      ∀ (F : (j : Fin (cutoffCount K)) → (t : ℝ) → t ∈ Ioo t₀ t₁ → UniformNormalData G C),
      (∀ j t (ht' : t ∈ Ioo t₀ t₁), ∀ q ∈ (F j t ht').parameterDomain ×ˢ (F j t ht').extensionDomain,
        (q.1, (t, q.2.1), q.2.2) ∈ Q) →
      (∀ t ∈ Ioo t₀ t₁, ∀ ε' ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D,
        (ε', (t, z.1), z.2) ∈ H) →
      (∀ j t (ht' : t ∈ Ioo t₀ t₁) ε' y u,
        (F j t ht').phase ε' y u = rawSlicePhaseExtension S₀ ζ (ε', (t, y), u)) →
      ∀ (v : WideInput (d + 1) (cutoffCount K)) (R : Set E),
      let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
        (weightedWideDensity (n := d + 1) mask v) x
      let J := rawSliceIntegralJet χ S A ζ τ volume (weightedWideDensity (n := d + 1) mask v)
      ∃ u : LocalSobolev.LocalL2 R Mat, g =ᵐ[volume.restrict R] u ∧
        ∃ e : LocalSobolev.SobolevExtension R s u, e.toFun = g ∧ e.jet = J ∧
          e.jetNorm ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
          LocalSobolev.cartesianJetNorm univ s J ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
          LocalSobolev.restrictionSobolevNorm R s u ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ := by
  obtain ⟨B, hB, hconstruct⟩ := exists_rawPhysicalSliceSobolev sec G C
    hU hV hΩ hQ hW hIW hH hHQ hband ζ hζ hshift hθ a p bmask ha hp hbmask t₀ t₁ ht
  refine ⟨B, hB, ?_⟩
  intro K τ hK hτ χ mask S A hχ hχc hχU hχsp htime hmask M hmb hS hA
    U₀ S₀ A₀ χ₀ mask₀ hm hmsp hmΩ s hmaskjet hAj hDj hε hstrip hshiftBand hshift4
    F hchart hpoints hphase v R
  apply hconstruct K 1 τ hK le_rfl hK hτ χ mask S A hχ hχc hχU hχsp htime
    hmask M hmb hS hA hm hmsp hmΩ 0 s hmaskjet _ _ hε hstrip hshiftBand hshift4
    F hchart hpoints hphase v R
  · simpa only [one_pow, mul_one] using hAj
  · simpa only [one_pow, mul_one] using hDj

end JanetCartan.RawPrimary.SliceBounds
