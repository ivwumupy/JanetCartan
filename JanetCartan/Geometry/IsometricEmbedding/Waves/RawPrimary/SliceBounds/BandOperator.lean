module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandIntegral
public import JanetCartan.Analysis.Microlocal.SingleChannel

/-!
# Construction of the actual one-band slice operator

The estimate in `app:ch_waves:eq:individual-raw-slice` is deduced from the
primitive buffered phase and amplitude data of the completed single-channel
producer. We do not assume a bounded raw operator or its integral realization.
The source is the original complex wide-band Hilbert space, and the output
uses full Lebesgue measure on the retained time and slice coordinates.

The actual raw-family parent must instantiate `UniformNormalData` for the
literal quotient and `rawSliceBandAmplitude`; those primitive hypotheses are
not produced by this deduction.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition NormalComparison SingleChannel

variable {d r : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Euclidean d
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- Primitive support and the time cutoff imply support in the original
buffered input chart (`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceAmplitude_eq_zero_off_chart
    {G : UniformNormalGeometry d r} {C : ℕ → ℝ} {a b ε : ℝ}
    (F : (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C)
    (hε : ε ∈ Icc 0 G.ε₀) (amp : X → Y → V)
    (htime : ∀ t ∉ Ioo a b, ∀ y u, amp (t, y) u = 0)
    (hamp : ∀ t (ht : t ∈ Ioo a b) y u i,
      amp (t, y) u i = (F t ht).amplitude ε y u i)
    (x : X) (u : Y) (hu : u ∉ G.D) : amp x u = 0 := by
  rcases x with ⟨t, y⟩
  by_cases ht : t ∈ Ioo a b
  · have hz : (F t ht).amplitude ε y u = 0 := by
      by_contra hn
      have hs := (F t ht).amplitude_support ε hε
        (show (y, u) ∈ Function.support (Function.uncurry ((F t ht).amplitude ε)) from hn)
      exact hu (G.D₀_subset hs.2)
    apply PiLp.ext
    intro i
    rw [hamp t ht, hz]
    rfl
  · exact htime t ht y u

/-- The single-channel construction on the SAME original wide-band datum,
for an arbitrary primitive slice amplitude. This variant is consumed by the
normalized derivative branches produced by
`exists_rawSlicePrimitiveBranchNormalData`, as well as the order-zero band.
No branch operator or its bound is assumed; the source map is the actual
`wideBandDilation` followed by chart restriction. The full product-Lebesgue
output and both real quadratures are retained
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_wideBandSliceOperator
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ B > 0, ∀ (j : ℕ)
      (F : (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C),
      ∀ ε ∈ Icc 0 G.ε₀, ∀ (φ : X → Y → ℝ) (amp : X → Y → V),
      Continuous (Function.uncurry amp) → HasCompactSupport (Function.uncurry amp) →
      (∀ p ∈ tsupport (Function.uncurry amp), ContinuousAt (Function.uncurry φ) p) →
      (∀ t ∉ Ioo a b, ∀ y u, amp (t, y) u = 0) →
      (∀ t (ht : t ∈ Ioo a b) y u, φ (t, y) u = (F t ht).phase ε y u) →
      (∀ t (ht : t ∈ Ioo a b) y u i, amp (t, y) u i = (F t ht).amplitude ε y u i) →
      ∃ T : WideBandL2 (d + 1) j →L[ℂ] Lp V 2 (volume : Measure X),
        (∀ f, T f =ᵐ[volume] fun x ↦
          normalOperatorScale (d + 1) ((2 : ℝ) ^ j) •
            ∫ θ in wideBand (d + 1) 0,
              (oscillatoryFactor ((2 : ℝ) ^ j) (φ x θ) *
                wideBandDilation (d + 1) j f θ) • amp x θ) ∧
        ‖T‖ ^ 2 ≤ B * (2 : ℝ) ^ j ∧
        ‖realQuadratureChannel T‖ ^ 2 ≤ 4 * (B * (2 : ℝ) ^ j) := by
  obtain ⟨B, hB, hchannel⟩ := exists_oscillatorySingleChannelOperator G C a b hab
  refine ⟨B, hB, ?_⟩
  intro j F ε hε φ amp ha hs hφ htime hphase hamp
  obtain ⟨L, hL, hbound, _⟩ := hchannel F ε hε ((2 : ℝ) ^ j)
    (one_le_pow₀ (by norm_num)) φ amp ha hs hφ htime hphase hamp
  let T := L.comp (wideBandChartInput (d + 1) j G.D)
  have hnorm : ‖T‖ ≤ ‖L‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_wideBandChartInput_le (n := d + 1) j G.D) (norm_nonneg L)
  have hT : ‖T‖ ^ 2 ≤ B * (2 : ℝ) ^ j :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hbound
  refine ⟨T, ?_, hT, (realQuadratureChannel_norm_sq_le T).trans
    (mul_le_mul_of_nonneg_left hT (by norm_num))⟩
  intro f
  refine (hL (wideBandChartInput (d + 1) j G.D f)).trans ?_
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  have hi := integral_wideBandChartInput (n := d + 1) j
    (fun θ ↦ oscillatoryFactor ((2 : ℝ) ^ j) (φ x θ) • amp x θ)
    (fun θ hθ ↦ by rw [sliceAmplitude_eq_zero_off_chart F hε _ htime hamp x θ hθ, smul_zero]) f
  convert hi using 1 <;> apply integral_congr_ae <;> filter_upwards [] with θ
    <;> rw [mul_smul, smul_comm]

/-- The actual normalized raw one-band operator, constructed from primitive
buffered slice charts by `SingleChannel.exists_oscillatorySingleChannelOperator`.
The constant precedes the band, inverse frequency, carrier, phase and amplitude.
Both real quadratures and time integration are retained, and the realization
is the SAME integral for every original wide-band Hilbert datum
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_rawSliceBandOperator
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ B > 0, ∀ (j : ℕ) (τ : ℝ), τ ≠ 0 →
      ∀ (F : (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C),
        τ * (2 : ℝ) ^ j ∈ Icc 0 G.ε₀ →
      ∀ (S : X → Y → ℝ) (A : X → Y → V) (χ : X → ℝ) (ζ : Y)
        (β : Y → ℂ),
        (∀ η ∉ wideBand (d + 1) j, β η = 0) →
        Continuous (Function.uncurry (rawSliceBandAmplitude (n := d + 1) A χ ζ τ β j)) →
        HasCompactSupport (Function.uncurry (rawSliceBandAmplitude (n := d + 1) A χ ζ τ β j)) →
        (∀ p ∈ tsupport (Function.uncurry (rawSliceBandAmplitude (n := d + 1) A χ ζ τ β j)),
          ContinuousAt (Function.uncurry
            (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j))) p) →
        (∀ t ∉ Ioo a b, ∀ y u, rawSliceBandAmplitude (n := d + 1) A χ ζ τ β j (t, y) u = 0) →
        (∀ t (ht : t ∈ Ioo a b) y u,
          rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) (t, y) u =
            (F t ht).phase (τ * (2 : ℝ) ^ j) y u) →
        (∀ t (ht : t ∈ Ioo a b) y u i,
          rawSliceBandAmplitude (n := d + 1) A χ ζ τ β j (t, y) u i =
            (F t ht).amplitude (τ * (2 : ℝ) ^ j) y u i) →
        ∃ T : WideBandL2 (d + 1) j →L[ℂ] Lp V 2 (volume : Measure X),
          (∀ f, T f =ᵐ[volume] fun x ↦
            (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
              rawSliceBandIntegral (n := d + 1) S A χ ζ τ β j f x) ∧
          ‖T‖ ^ 2 ≤ B * (2 : ℝ) ^ j ∧
          ‖realQuadratureChannel T‖ ^ 2 ≤ 4 * (B * (2 : ℝ) ^ j) := by
  obtain ⟨B, hB, hchannel⟩ := exists_wideBandSliceOperator G C a b hab
  refine ⟨B, hB, ?_⟩
  intro j τ hτ F hε S A χ ζ β hβ ha hs hφ htime hphase hamp
  obtain ⟨T, hT, hbound, hreal⟩ := hchannel j F _ hε _ _ ha hs hφ htime hphase hamp
  refine ⟨T, ?_, hbound, hreal⟩
  intro f
  refine (hT f).trans (Filter.Eventually.of_forall (fun x ↦ ?_))
  exact (normalized_rawSliceBandIntegral (n := d + 1) (by omega)
    S A χ ζ hτ β j hβ f x).symm

end JanetCartan.RawPrimary.SliceBounds
