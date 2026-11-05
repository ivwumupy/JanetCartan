module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedSum

/-!
# Sharp differentiated operator for the same raw integral

This assembles primitive original-chart jets, the actual SingleChannel
construction, exact differentiated integrals and the count-independent dyadic
sum. The output is full Lebesgue L² in the retained adapted coordinates.
The physical/Frobenius Sobolev conversion remains the consumer of this result.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open NormalComparison RawInputPartition SingleChannel

variable {d r : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "Qₚ" => ℝ × X × Y
local notation "Vₒ" => EuclideanSpace ℂ (Fin r)

/-- Sharp directional derivative operators for the SAME measured raw field,
constructed from primitive buffered phase charts and ORIGINAL joint grades.
The bound is `C_s K^(s+1/2)` on the actual original `WideInput`, with no band
or sample count. Constants precede `K`, `L`, history, order directions, masks
and datum. The finite quantitative input ends at
`s + rawSliceJetOrder (d+1) + 1`, with the fixed reserve
`rawSlicePrimitiveReserve (d+1) Dpr`. Thus `L=1` yields the prescribed finite
order estimate for every `K≥1` from bounded jets at exactly those orders.

Both real quadratures and all physical directions, including time, are
retained. The actual WKB/current-family parent must instantiate the displayed
original phase/amplitude grades, masks and buffered chart. No differentiated
operator, weak-jet estimate or successful raw-family bound is a premise
(`app:ch_waves:eq:individual-raw-slice`, `app:ch_waves:thm:individual`). -/
theorem exists_rawSliceDifferentiatedOperator
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    {U : Set X} {V Ω : Set Y} {Q H : Set Qₚ} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hH : IsCompact H) (hHQ : H ⊆ Q)
    (hband : wideBand (d + 1) 0 ⊆ Ω) (ζ : Y) (hζ : ζ ∈ V)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p bmask : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hbmask : ∀ j, 0 ≤ bmask j) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) :
    ∃ D : ℕ → ℝ, (∀ s, 0 < D s) ∧
      ∀ (K L τ : ℝ), 1 ≤ K → 1 ≤ L → L ≤ K → τ ≠ 0 →
      ∀ (χ : X → ℝ) (mask : Y → ℂ) (S : X → Y → ℝ) (A : X → Y → Fin r → ℂ),
      ContDiffOn ℝ ∞ χ U → HasCompactSupport χ → tsupport χ ⊆ U →
      (∀ x, χ x ≠ 0 → x.2 ∈ G.X₀) → (∀ x ∈ tsupport χ, x.1 ∈ Ioo t₀ t₁) →
      Measurable mask → ∀ M : ℝ, (∀ η, ‖mask η‖ ≤ M) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      let m := fun (j : Fin (cutoffCount K)) (θ : Y) ↦
        (Real.sqrt ‖θ‖ : ℂ) * weightedRadialBand (n := d + 1) mask j.val ((2 : ℝ) ^ j.val • θ)
      (∀ j, ContDiffOn ℝ ∞ (m j) Ω) →
      (∀ j, Function.support (m j) ⊆ G.D₀) →
      (∀ j, tsupport (m j) ⊆ Ω) →
      ∀ (Dpr s : ℕ),
      (∀ j, ∀ q ∈ H, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun z : Qₚ ↦ (χ z.2.1 : ℂ) * m j z.2.2) q‖ ≤ bmask k) →
      (∀ z ∈ U ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (Function.uncurry A) z‖ ≤
          a k * L ^ (k + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr)) →
      (∀ z ∈ U ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun w : X × Y ↦ fderiv ℝ (S w.1) w.2) z‖ ≤
          p k * L ^ (k - 1 + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr)) →
      (∀ j : Fin (cutoffCount K), τ * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) →
      (∀ j : Fin (cutoffCount K), ∀ x ∈ U, ∀ θ ∈ Ω,
        (τ * (2 : ℝ) ^ j.val, x, θ) ∈ Q) →
      (∀ j : Fin (cutoffCount K), ∀ θ ∈ Ω, ζ + (τ * (2 : ℝ) ^ j.val) • θ ∈ V) →
      (∀ j : Fin (cutoffCount K), ∀ (η : Y), η ∈ wideBand (d + 1) j.val → ζ + τ • η ∈ V) →
      ∀ (F : (j : Fin (cutoffCount K)) → (t : ℝ) → t ∈ Ioo t₀ t₁ → UniformNormalData G C),
      (∀ j t (ht' : t ∈ Ioo t₀ t₁), ∀ q ∈ (F j t ht').parameterDomain ×ˢ (F j t ht').extensionDomain,
        (q.1, (t, q.2.1), q.2.2) ∈ Q) →
      (∀ t ∈ Ioo t₀ t₁, ∀ ε' ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D,
        (ε', (t, z.1), z.2) ∈ H) →
      (∀ j t (ht' : t ∈ Ioo t₀ t₁) ε' y u,
        (F j t ht').phase ε' y u = rawSlicePhaseExtension S ζ (ε', (t, y), u)) →
      ∀ (v : Fin s → X), (∀ i, ‖v i‖ ≤ 1) →
      ∃ T : WideInput (d + 1) (cutoffCount K) →L[ℂ] Lp Vₒ 2 (volume : Measure X),
        (∀ f, T f =ᵐ[volume] fun x ↦
          iteratedFDeriv ℝ s (fun y ↦ (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
            ((χ y : ℂ) • rawPrimaryDemodulatedIntegral S (fun z η ↦ WithLp.toLp 2 (A z η))
              ζ τ volume (weightedWideDensity (n := d + 1) mask f) y)) x v) ∧
        ‖T‖ ≤ D s * K ^ ((s : ℝ) + 1 / 2) ∧
        ‖realQuadratureChannel T‖ ^ 2 ≤ 4 * (D s * K ^ ((s : ℝ) + 1 / 2)) ^ 2 ∧
        (∀ f, ‖T f‖ ≤ D s * K ^ ((s : ℝ) + 1 / 2) * ‖f‖) := by
  obtain ⟨B, hB, hconstruct⟩ := exists_rawSliceNormalizedBranchOperators G C
    hU hV hQ hW hIW hH hHQ ζ hshift hθ a p bmask ha hp hbmask t₀ t₁ ht
  let D : ℕ → ℝ := fun s ↦ 1 + 2 * (4 : ℝ) ^ s * ∑ b : SliceDerivativeBranch s, Real.sqrt (B s b)
  have hD (s : ℕ) : 0 < D s := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro K L τ hK hL hLK hτ χ mask S A hχ hχc hχU hχsp htime hmask M hmb hS hA m
    hm hmsp hmΩ Dpr s hmaskjet hAj hDj hε hstrip hshiftBand hshiftOriginal F hchart hpoints hphase v hv
  have hb (j : Fin (cutoffCount K)) := hconstruct χ (m j) S A hχ (hm j) hχc
    hχsp (hmsp j) htime hS hA Dpr s L hL (hmaskjet j) hAj hDj v hv j.val _ (hε j)
    (fun x hx θ hθ' ↦ hstrip j x (hχU hx) θ (hmΩ j hθ')) (F j) (hchart j) hpoints (hphase j)
  choose T hT hnorm hreal using hb
  let T' := fun b j ↦ T j b
  have hbound := norm_gradedWideBandOperatorSum_rounded_le hK hL hLK T' (B s)
    (fun b ↦ (hB s b).le) (fun b j ↦ hnorm j b)
  have hbound' : ‖gradedWideBandOperatorSum T' L‖ ≤ D s * K ^ ((s : ℝ) + 1 / 2) := by
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    dsimp [D]
    linarith
  refine ⟨gradedWideBandOperatorSum T' L, ?_, hbound', ?_, ?_⟩
  · intro f
    have hAv : ContDiffOn ℝ ∞
        (Function.uncurry (fun x η ↦ WithLp.toLp 2 (A x η))) (U ×ˢ V) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.contDiff.comp_contDiffOn hA
    apply gradedWideBandOperatorSum_coeFn_rawSliceDerivative hU hV hΩ hQ hW hIW hband
      hS hAv
      hχ hχU hζ hτ (by linarith) hmask hmb hm hshift hθ hstrip hshiftBand hshiftOriginal v T'
      (fun b j g ↦ hT j b g) f
  · exact (realQuadratureChannel_norm_sq_le _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hbound' 2) (by norm_num))
  · intro f
    exact ((gradedWideBandOperatorSum T' L).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hbound' (norm_nonneg f))

end JanetCartan.RawPrimary.SliceBounds
