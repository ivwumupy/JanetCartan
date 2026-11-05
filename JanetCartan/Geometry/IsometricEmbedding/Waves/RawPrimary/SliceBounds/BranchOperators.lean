module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BranchRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandOperator

/-!
# Actual normalized derivative branch operators

For `app:ch_waves:eq:individual-raw-slice`, instantiate the completed
SingleChannel producer with the primitive input constructed from original
phase and amplitude jets. Continuity, compact support and time support of the
branches are proved from the original masks. No differentiated channel bound
or differentiated-symbol seminorm is an input.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open NormalComparison RawInputPartition SingleChannel

variable {d r : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "Qₚ" => ℝ × X × Y
local notation "Vₒ" => EuclideanSpace ℂ (Fin r)

/-- Actual normalized branch channels, uniformly in band, physical order,
unit directions and original data. The constants depend only on the displayed
primitive profiles and buffered chart. The fixed additional reserve is
`Dpr + (20 * ((d+1)+1) + 3) + 2`; the required original amplitude and covector
jets stop at `s + 20 * ((d+1)+1) + 1`.

The parent raw-family construction must supply these original jets and chart
geometry for its canonical derivative amplitude. This theorem constructs the
operators and their bounds by `exists_wideBandSliceOperator`, and retains
full Lebesgue output, the actual wide-band unitary, and both quadratures
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_rawSliceNormalizedBranchOperators
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    {U : Set X} {V Ω : Set Y} {Q H : Set Qₚ} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hH : IsCompact H) (hHQ : H ⊆ Q)
    (ζ : Y)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p bmask : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hbmask : ∀ j, 0 ≤ bmask j) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) :
    ∃ B : (s : ℕ) → SliceDerivativeBranch s → ℝ,
      (∀ s b, 0 < B s b) ∧
      ∀ (χ : X → ℝ) (m : Y → ℂ) (S : X → Y → ℝ) (A : X → Y → Fin r → ℂ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ m Ω → HasCompactSupport χ →
      (∀ x, χ x ≠ 0 → x.2 ∈ G.X₀) → (Function.support m ⊆ G.D₀) →
      (∀ x ∈ tsupport χ, x.1 ∈ Ioo t₀ t₁) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      ∀ (Dpr s : ℕ) (L : ℝ), 1 ≤ L →
      (∀ q ∈ H, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun z : Qₚ ↦ (χ z.2.1 : ℂ) * m z.2.2) q‖ ≤ bmask k) →
      (∀ z ∈ U ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (Function.uncurry A) z‖ ≤
          a k * L ^ (k + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr)) →
      (∀ z ∈ U ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun w : X × Y ↦ fderiv ℝ (S w.1) w.2) z‖ ≤
          p k * L ^ (k - 1 + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr)) →
      ∀ (v : Fin s → X), (∀ i, ‖v i‖ ≤ 1) →
      ∀ (j : ℕ) (ε : ℝ), ε ∈ Icc 0 G.ε₀ →
      (∀ x ∈ tsupport χ, ∀ θ ∈ tsupport m, (ε, x, θ) ∈ Q) →
      ∀ (F : (t : ℝ) → t ∈ Ioo t₀ t₁ → UniformNormalData G C),
      (∀ t (ht' : t ∈ Ioo t₀ t₁), ∀ q ∈ (F t ht').parameterDomain ×ˢ (F t ht').extensionDomain,
        (q.1, (t, q.2.1), q.2.2) ∈ Q) →
      (∀ t ∈ Ioo t₀ t₁, ∀ ε' ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D,
        (ε', (t, z.1), z.2) ∈ H) →
      (∀ t (ht' : t ∈ Ioo t₀ t₁) ε' y u,
        (F t ht').phase ε' y u = rawSlicePhaseExtension S ζ (ε', (t, y), u)) →
      ∃ T : SliceDerivativeBranch s → WideBandL2 (d + 1) j →L[ℂ] Lp Vₒ 2 (volume : Measure X),
        (∀ b f, T b f =ᵐ[volume] fun x ↦
          normalOperatorScale (d + 1) ((2 : ℝ) ^ j) •
            ∫ θ in wideBand (d + 1) 0,
              (oscillatoryFactor ((2 : ℝ) ^ j) (rawSlicePhaseExtension S ζ (ε, x, θ)) *
                wideBandDilation (d + 1) j f θ) •
                  rawSliceNormalizedBranch S (fun y u ↦ WithLp.toLp 2 (A y u)) χ m ζ ε v b L x θ) ∧
        (∀ b, ‖T b‖ ^ 2 ≤ B s b * (2 : ℝ) ^ j) ∧
        (∀ b, ‖realQuadratureChannel (T b)‖ ^ 2 ≤ 4 * (B s b * (2 : ℝ) ^ j)) := by
  obtain ⟨a', p', ha', hp', hnormal⟩ := exists_rawSlicePrimitiveBranchNormalData
    G C hU hV hQ hW hIW hH hHQ ζ hshift hθ a p bmask ha hp hbmask
  have hc (s : ℕ) (b : SliceDerivativeBranch s) :=
    exists_wideBandSliceOperator G (sliceBranchInputConstant C a' p' b) t₀ t₁ ht
  choose B hB hchannel using hc
  refine ⟨B, hB, ?_⟩
  intro χ m S A hχ hm hχc hχsp hmsp htime hS hA Dpr s L hL hmask hAj hDj v hv
    j ε hε hsupp F hchart hpoints hphase
  let Av : X → Y → Vₒ := fun y u ↦ WithLp.toLp 2 (A y u)
  have hAv : ContDiffOn ℝ ∞ (Function.uncurry Av) (U ×ˢ V) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.contDiff.comp_contDiffOn hA
  have hmc : HasCompactSupport m := G.compact_D₀.of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal hmsp G.compact_D₀.isClosed)
  have hφ := contDiffOn_rawSlicePhaseExtension hU hV hQ hW hIW hS hshift
  have hb (b : SliceDerivativeBranch s) := by
    have hf (t : ℝ) (ht' : t ∈ Ioo t₀ t₁) := hnormal χ m S A hχ hm hχsp hmsp hS hA
      Dpr s L hL hmask hAj hDj v hv b t (F t ht')
      (hchart t ht') (hpoints t ht') (hphase t ht')
    choose Hn hsame hphase' hamp using hf
    apply hchannel s b j Hn ε hε
      (fun x θ ↦ rawSlicePhaseExtension S ζ (ε, x, θ))
      (rawSliceNormalizedBranch S Av χ m ζ ε v b L)
    · exact (contDiff_rawSliceNormalizedBranch hU hV hQ hW hIW hS hAv hχ hm
        hshift hθ hsupp v b L).continuous
    · exact hasCompactSupport_rawSliceNormalizedBranch S Av hχc hmc ζ ε v b L
    · intro q hq
      exact continuousAt_rawSlicePhaseExtension_on_branch hQ S Av χ m ζ hφ hsupp v b L hq
    · intro t ht' y u
      change Function.uncurry (rawSliceNormalizedBranch S Av χ m ζ ε v b L) ((t, y), u) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact ht' (htime (t, y)
        (tsupport_rawSliceNormalizedBranch_subset S Av χ m ζ ε v b L h).1)
    · intro t ht' y u
      rw [hphase' t ht']
    · intro t ht' y u i
      rw [hamp t ht']
      change normalizedSliceDerivativeAmplitude _
        (fun q ↦ WithLp.toLp 2 (rawSliceAmplitudeExtension A χ m ζ q)) _ b L _ i = _
      rw [normalizedSliceDerivativeAmplitude_toLp]
  choose T hT hnorm hreal using hb
  exact ⟨T, hT, hnorm, hreal⟩

end JanetCartan.RawPrimary.SliceBounds
