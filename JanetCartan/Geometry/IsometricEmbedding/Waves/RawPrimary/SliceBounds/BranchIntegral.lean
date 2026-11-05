module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BranchOperators

/-!
# Exact normalized branch integrals of the measured raw field

The branch operators constructed from original primitive jets represent these
literal integrals. Restoring `κ^q L^(s-q)` gives the physical derivatives of
the SAME raw band field, with the original Fourier normalization and cutoff
(`app:ch_waves:eq:individual-raw-slice`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open NormalComparison RawInputPartition

variable {n : ℕ} {X F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The integral represented by the actual normalized branch operator. It
keeps the full product-Lebesgue output and the original wide-band datum
(`app:ch_waves:eq:individual-raw-slice`). -/
def rawSliceNormalizedBranchIntegral
    (S : X → Euclidean (n - 1) → ℝ) (A : X → Euclidean (n - 1) → F)
    (χ : X → ℝ) (m : Euclidean (n - 1) → ℂ) (ζ : Euclidean (n - 1)) (ε : ℝ)
    (j : ℕ) {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s) (L : ℝ)
    (f : WideBandL2 n j) (x : X) : F :=
  normalOperatorScale n ((2 : ℝ) ^ j) •
    ∫ θ in wideBand n 0,
      (oscillatoryFactor ((2 : ℝ) ^ j) (rawSlicePhaseExtension S ζ (ε, x, θ)) *
        wideBandDilation n j f θ) • rawSliceNormalizedBranch S A χ m ζ ε v b L x θ

variable [FiniteDimensional ℝ X] [CompleteSpace F]

/-- Restore every exact branch grade to obtain all physical derivatives of
the literal raw band integral, at EVERY physical output point. The proof
uses the original buffered chart on the mask support and vanishing outside
the physical cutoff. No derivative-interchange or realization identity is
assumed (`app:ch_waves:eq:individual-raw-slice`). -/
theorem iteratedFDeriv_normalized_rawSliceBandIntegral_eq_normalizedBranches
    (hn : 1 ≤ n) {U : Set X} {V Ω : Set (Euclidean (n - 1))}
    {Q : Set (ℝ × X × Euclidean (n - 1))} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hband : wideBand n 0 ⊆ Ω)
    {S : X → Euclidean (n - 1) → ℝ} {A : X → Euclidean (n - 1) → F}
    {χ : X → ℝ} {ζ : Euclidean (n - 1)} {τ : ℝ}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U) (hχU : tsupport χ ⊆ U) (hζ : ζ ∈ V) (hτ : τ ≠ 0)
    (β : Euclidean (n - 1) → ℂ) (j : ℕ)
    (hβ : ∀ η ∉ wideBand n j, β η = 0)
    (hmask : ContDiffOn ℝ ∞
      (fun θ ↦ (Real.sqrt ‖θ‖ : ℂ) * β ((2 : ℝ) ^ j • θ)) Ω)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (hstrip : ∀ x ∈ U, ∀ θ ∈ Ω, (τ * (2 : ℝ) ^ j, x, θ) ∈ Q)
    (f : WideBandL2 n j) (s : ℕ) (x : X) (v : Fin s → X) {L : ℝ} (hL : 0 < L) :
    iteratedFDeriv ℝ s (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      rawSliceBandIntegral S A χ ζ τ β j f y) x v =
      ∑ b : SliceDerivativeBranch s,
        (((2 : ℝ) ^ j) ^ b.phaseCount * L ^ (s - b.phaseCount)) •
          rawSliceNormalizedBranchIntegral S A χ
            (fun θ ↦ (Real.sqrt ‖θ‖ : ℂ) * β ((2 : ℝ) ^ j • θ))
            ζ (τ * (2 : ℝ) ^ j) j v b L f x := by
  let m : Euclidean (n - 1) → ℂ := fun θ ↦
    (Real.sqrt ‖θ‖ : ℂ) * β ((2 : ℝ) ^ j • θ)
  by_cases hx : x ∈ U
  · rw [iteratedFDeriv_normalized_rawSliceBandIntegral_eq_branches hn hU hΩ hband
      hS hA hχ hζ hτ β j hβ hmask
      (fun θ hθ' ↦ by
        simpa only [rawSliceShift, one_mul] using
          (hshift 1 (hIW (by simp)) (hstrip x hx θ hθ')).2) f s hx v,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hi : (∫ θ in wideBand n 0,
        (oscillatoryFactor ((2 : ℝ) ^ j)
          (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) x θ) * wideBandDilation n j f θ) •
          rawSliceBandDerivativeAmplitude S A χ ζ τ β j v b x θ) =
        L ^ (s - b.phaseCount) • ∫ θ in wideBand n 0,
          (oscillatoryFactor ((2 : ℝ) ^ j)
            (rawSlicePhaseExtension S ζ (τ * (2 : ℝ) ^ j, x, θ)) * wideBandDilation n j f θ) •
              rawSliceNormalizedBranch S A χ m ζ (τ * (2 : ℝ) ^ j) v b L x θ := by
      rw [← integral_smul]
      apply integral_congr_ae
      have hcompact : IsCompact (wideBand n 0) :=
        (isCompact_closedBall _ _).diff Metric.isOpen_ball
      filter_upwards [ae_restrict_mem hcompact.measurableSet] with θ hθ'
      have hq := hstrip x hx θ (hband hθ')
      rw [← rawSlicePhaseExtension_eq_rawPrimaryPhaseDifference hV hS hx
        (mul_ne_zero hτ (pow_ne_zero _ (by norm_num)))
        (fun t ht ↦ (hshift t (hIW ht) hq).2)]
      rw [rawSliceBandDerivativeAmplitude_eq_jointBranch hU hV hQ hW hIW hτ β j
        hS hA hχ hmask hshift hθ v b hq]
      change _ = L ^ (s - b.phaseCount) • (_ • normalizedSliceDerivativeAmplitude _ _ _ b L _)
      rw [smul_comm (L ^ (s - b.phaseCount)), scale_normalizedSliceDerivativeAmplitude _ b hL]
    rw [hi, ← Complex.ofReal_pow, Complex.coe_smul]
    change _ = _ • (normalOperatorScale n ((2 : ℝ) ^ j) • _)
    rw [mul_smul, smul_comm (normalOperatorScale n ((2 : ℝ) ^ j)),
      smul_comm (normalOperatorScale n ((2 : ℝ) ^ j)) (L ^ (s - b.phaseCount))]
  · have hxχ : x ∉ tsupport χ := fun h ↦ hx (hχU h)
    have hz : iteratedFDeriv ℝ s (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        rawSliceBandIntegral S A χ ζ τ β j f y) x = 0 := by
      apply Function.notMem_support.mp
      intro hs
      apply hxχ
      apply tsupport_comp_subset (g := fun a : ℝ ↦ (a : ℂ)) (by simp) χ
      apply tsupport_smul_subset_left (fun y ↦ (χ y : ℂ))
        (fun y ↦ rawPrimaryDemodulatedIntegral S A ζ τ volume
          (fun η ↦ (Real.sqrt ‖η‖ : ℂ) * β η * f η) y)
      apply tsupport_smul_subset_right
        (fun _ : X ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2))
        (fun y ↦ rawSliceBandIntegral S A χ ζ τ β j f y)
      exact support_iteratedFDeriv_subset s hs
    rw [hz, zero_apply]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hb (θ : Euclidean (n - 1)) :
        rawSliceNormalizedBranch S A χ m ζ (τ * (2 : ℝ) ^ j) v b L x θ = 0 := by
      change Function.uncurry (rawSliceNormalizedBranch S A χ m ζ (τ * (2 : ℝ) ^ j) v b L)
        (x, θ) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hxχ (tsupport_rawSliceNormalizedBranch_subset S A χ m ζ _ v b L h).1
    change _ • rawSliceNormalizedBranchIntegral S A χ m ζ _ j v b L f x = 0
    simp [rawSliceNormalizedBranchIntegral, hb]

end JanetCartan.RawPrimary.SliceBounds
