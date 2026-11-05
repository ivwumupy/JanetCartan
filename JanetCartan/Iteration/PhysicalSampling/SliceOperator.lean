module

public import JanetCartan.Iteration.PhysicalSampling.SliceAmplitude

/-!
# The actual scalar one-band operator on retained canonical slices

This invokes the proved full-space single-channel theorem with the original
canonical phase quotient and the scalar cutoff amplitude. It constructs, rather
than assumes, the `C * 2^j` bound, from the SAME current immersion phase data.
The remaining physical kernel identification retains the original wide input
and its two sharp Hilbert refinements (`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSampling

open NormalComparison ActualCarriers.FrozenPhaseReference ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary RawPrimary.SliceBounds RawPrimary.SliceGeometry RawPrimary.MaskProfiles RawInputPartition
open FullPhaseCharts.ActualPhase

variable {n : ℕ}

/-- Same scalar amplitude in the product coordinates of SingleChannel. -/
def scalarSliceChannelAmplitude {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (hn : 1 ≤ n) (j : ℕ) (q : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (scalarSliceAmplitude sec χ angular H hn j (q.1.1, q.1.2, q.2))

/-- Literal closed support bound for the scalar amplitude; no phase hypothesis. -/
theorem scalarSliceChannelAmplitude_support {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (hn : 1 ≤ n) {a : ℝ}
    (hχ : tsupport (χ : Euclidean n → ℝ) ⊆ closedBall 0 (a / 4)) (j : ℕ) :
    tsupport (scalarSliceChannelAmplitude sec χ angular H hn j) ⊆
      closedBall (0 : ℝ × Euclidean (n - 1)) (a / 4) ×ˢ closedBall 0 2 := by
  apply closure_minimal _ (isClosed_closedBall.prod isClosed_closedBall)
  intro q hq
  have hm : normalizedMask (n := n) angular H j q.2 ≠ 0 := by
    intro hz
    apply hq
    ext i
    simp only [scalarSliceChannelAmplitude, scalarSliceAmplitude, PiLp.toLp_apply,
      hz, zero_mul, PiLp.zero_apply]
  have hx : χ (adaptedPhysicalCoordinates sec q.1) ≠ 0 := by
    intro hz
    apply hq
    ext i
    simp only [scalarSliceChannelAmplitude, scalarSliceAmplitude, PiLp.toLp_apply,
      hz, Complex.ofReal_zero, mul_zero, zero_mul, PiLp.zero_apply]
  refine ⟨?_, support_normalizedMask_subset angular H j hm⟩
  have hh : ‖adaptedPhysicalCoordinates sec q.1‖ ≤ a / 4 := by
    simpa using hχ (subset_tsupport _ hx)
  have hc := norm_adaptedPhysicalCoordinates_symm_le sec (adaptedPhysicalCoordinates sec q.1)
  rw [MeasurableEquiv.symm_apply_apply] at hc
  simpa only [mem_closedBall, dist_zero_right] using hc.trans hh

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- A sharp one-band bound from the same actual canonical phase family.
`exists_scalarSliceNormalData` constructs the amplitude fields, and the original
before-bounds slice constructor produces the phase fields from the current map.
There is no operator-norm premise in this result. -/
theorem exists_scalarSliceBandOperator (hn : 1 ≤ n)
    (G : UniformNormalGeometry (n - 1) n) (C : ℕ → ℝ)
    {a e b : ℝ} (ha : 0 < a) (haR : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b) (hGe : G.ε₀ = e) :
    ∃ B > 0,
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n //
        ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (z : Euclidean 3),
      (ball (T.reference.spatialPatch z) b ⊆
        ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) →
      ∀ (χ : ContDiffBump (0 : Euclidean n))
      (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ),
      (∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) → ContDiff ℝ ∞ H →
      tsupport (χ : Euclidean n → ℝ) ⊆ closedBall 0 (a / 4) →
      ∀ j (ε : ℝ), ε ∈ Icc 0 G.ε₀ →
      ∀ (N : (t : ℝ) → t ∈ Ioo (-a) a → UniformNormalData G C),
      (∀ t (ht : t ∈ Ioo (-a) a), (N t ht).phase = fun ε y η ↦
        rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)
          (ε, (t, y), η)) →
      (∀ t (ht : t ∈ Ioo (-a) a), (N t ht).amplitude = fun _ y η ↦
        scalarSliceAmplitude T.data.adapted χ angular H hn j (t, y, η)) →
      ∃ L : WideBandL2 n j →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (ℝ × Euclidean (n - 1))),
        (∀ f, L f =ᵐ[volume] fun x ↦
          normalOperatorScale n ((2 : ℝ) ^ j) •
            ∫ θ in wideBand n 0,
              (oscillatoryFactor ((2 : ℝ) ^ j)
                (rawSlicePhaseExtension (canonicalBasePhase T Q)
                  (T.reference.spatialPatch z) (ε, x, θ)) *
                wideBandDilation n j f θ) •
                scalarSliceChannelAmplitude T.data.adapted χ angular H hn j (x, θ)) ∧
        ‖L‖ ^ 2 ≤ B * (2 : ℝ) ^ j := by
  obtain ⟨B, hB, hconstruct⟩ := exists_wideBandSliceOperator G C (-a) a (by linarith)
  refine ⟨B, hB, ?_⟩
  intro Q z hb χ angular H hang hH hχ j ε hε N hNphase hNamp
  let amp := scalarSliceChannelAmplitude T.data.adapted χ angular H hn j
  let φ := fun x θ ↦ rawSlicePhaseExtension (canonicalBasePhase T Q)
    (T.reference.spatialPatch z) (ε, x, θ)
  have hnsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simp only [hnsucc] at hconstruct
  have hamp : Continuous amp :=
    (PiLp.continuous_toLp 2 _).comp
      ((contDiff_scalarSliceAmplitude T.data.adapted χ angular H hang hH hn j).continuous.comp
        (by fun_prop))
  have hsupport := scalarSliceChannelAmplitude_support T.data.adapted χ angular H hn hχ j
  have hcompact : HasCompactSupport amp :=
    (isCompact_closedBall (0 : ℝ × Euclidean (n - 1)) (a / 4)).prod
      (isCompact_closedBall 0 2) |>.of_isClosed_subset isClosed_closure hsupport
  have htime : ∀ t ∉ Ioo (-a) a, ∀ y u, amp ((t, y), u) = 0 := by
    intro t ht y u
    by_contra hh
    have hs := hsupport (subset_tsupport _ hh)
    have ht' := (norm_fst_le (t, y)).trans (mem_closedBall_zero_iff.mp hs.1)
    rw [Real.norm_eq_abs] at ht'
    exact ht (abs_lt.mp (ht'.trans_lt (by linarith : a / 4 < a)))
  have hφ : ∀ q ∈ tsupport amp, ContinuousAt (Function.uncurry φ) q := by
    intro q hq
    have hsup := hsupport hq
    have hnorm : ‖q.1‖ ≤ a / 4 := mem_closedBall_zero_iff.mp hsup.1
    have htime' : q.1.1 ∈ Ioo (-a) a := by
      have hh := (norm_fst_le q.1).trans hnorm
      rw [Real.norm_eq_abs] at hh
      exact abs_lt.mp (hh.trans_lt (by linarith : a / 4 < a))
    have hy : q.1.2 ∈ ball (0 : Euclidean (n - 1)) (2 * a) := by
      exact mem_ball_zero_iff.mpr ((norm_snd_le q.1).trans hnorm |>.trans_lt (by linarith))
    have hθ : q.2 ∈ sliceInputExtension n :=
      closedBall_subset_ball (by norm_num : (2 : ℝ) < 4) hsup.2
    have hε' : ε ∈ sliceParameterDomain e := by
      rw [hGe] at hε
      exact ⟨by linarith [hε.1], by linarith [hε.2]⟩
    have hmem : (ε, q.1.2, q.2) ∈
        sliceParameterDomain e ×ˢ sliceExtensionDomain n a := ⟨hε', hy, hθ⟩
    have hm := sliceExtensionDomain_mapsTo_shiftDomain T ha htime' hmem
    change (ε, q.1, q.2) ∈ sliceShiftDomain T a e at hm
    exact ((canonicalSlicePhase_smooth_on_shiftDomain T Q z haR he heb hb).continuousOn.continuousAt
      ((isOpen_sliceShiftDomain T a e).mem_nhds hm)).comp (by fun_prop)
  obtain ⟨L, hL, hnorm, _⟩ := hconstruct j N ε hε φ (fun x θ ↦ amp (x, θ))
    hamp hcompact hφ htime
    (fun t ht y u ↦ congrFun (congrFun (congrFun (hNphase t ht) ε) y) u |>.symm)
    (fun t ht y u i ↦ by
      rw [hNamp t ht]
      rfl)
  exact ⟨L, hL, hnorm⟩

end JanetCartan.PhysicalSampling
