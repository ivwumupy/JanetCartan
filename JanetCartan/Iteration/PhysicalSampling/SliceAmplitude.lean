module

public import JanetCartan.Iteration.PhysicalSampling.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.SliceGeometryBeforeBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceLocalization
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandOperator

/-!
# Scalar amplitudes on the original transverse slice geometry

Only the finite output-coordinate count changes from the raw tensor channel to
the scalar embedding. Every geometric set, phase, inverse chart, buffer and gap
is retained literally. The scalar cutoff and three original normalized masks
supply all amplitude jets uniformly before the current phase and frequency.
Consumer: the sharp scalar single-band bound in `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalSampling

open NormalComparison ActualCarriers.FrozenPhaseReference RawPrimary
open RawPrimary.SliceBounds RawPrimary.SliceGeometry RawPrimary.MaskProfiles

variable {n : ℕ}

/-- The same transverse geometry with only the scalar-row output rank. -/
def scalarSliceGeometry (hn : 1 ≤ n)
    (G : UniformNormalGeometry (n - 1) (embeddingDimension n * n)) :
    UniformNormalGeometry (n - 1) n := { G with rank_pos := hn }

/-- The literal normalized scalar slice amplitude. -/
def scalarSliceAmplitude {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (hn : 1 ≤ n) (j : ℕ) (q : ℝ × (Euclidean (n - 1) × Euclidean (n - 1))) :
    Fin n → ℂ :=
  fun i ↦ (normalizedMask angular H j q.2.2 *
    (χ (adaptedPhysicalCoordinates sec (q.1, q.2.1)) : ℂ)) *
      (PiLp.single 2 ⟨0, hn⟩ (1 : ℂ) : EuclideanSpace ℂ (Fin n)) i

/-- Joint smoothness of the original fixed scalar slice amplitude. -/
theorem contDiff_scalarSliceAmplitude {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) (hH : ContDiff ℝ ∞ H)
    (hn : 1 ≤ n) (j : ℕ) :
    ContDiff ℝ ∞ (scalarSliceAmplitude sec χ angular H hn j) := by
  apply contDiff_pi.mpr
  intro i
  unfold scalarSliceAmplitude
  apply ContDiff.mul _ contDiff_const
  exact ((contDiff_normalizedMask angular H ha hH j).comp (by fun_prop)).mul
    (Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp (by
      simp only [adaptedPhysicalCoordinates_apply]
      fun_prop)))

/-- Fixed scalar amplitude budgets, before all phase data and band ceilings. -/
theorem exists_scalarSliceAmplitude_budgets {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) (hn : 1 ≤ n)
    {K : Set (ℝ × (Euclidean (n - 1) × Euclidean (n - 1)))} (hK : IsCompact K) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧ ∀ j, ∀ q ∈ K, ∀ k,
      ‖iteratedFDeriv ℝ k (scalarSliceAmplitude sec χ angular H hn j) q‖ ≤ B k := by
  let A (j k : ℕ) := cNorm K k (scalarSliceAmplitude sec χ angular H hn j)
  let B (k : ℕ) := 1 + A 0 k + A 1 k + A 2 k
  have hA (j k : ℕ) : 0 ≤ A j k := cNorm_nonneg _ _ _
  refine ⟨B, fun k ↦ by dsimp [B]; linarith [hA 0 k, hA 1 k, hA 2 k], ?_⟩
  intro j q hq k
  have heq : scalarSliceAmplitude sec χ angular H hn j =
      scalarSliceAmplitude sec χ angular H hn (min j 2) := by
    funext q i
    simp only [scalarSliceAmplitude, normalizedMask_eq_min angular H hah hH₁ j]
  rw [heq]
  apply (norm_iteratedFDeriv_le_cNorm hK
    ((contDiff_scalarSliceAmplitude sec χ angular H ha hH hn (min j 2)).of_le
      (by simp : (k : ℕ∞ω) ≤ ∞)) hq le_rfl).trans
  have hj : min j 2 ≤ 2 := min_le_right _ _
  interval_cases h : min j 2 <;> change A _ k ≤ B k <;>
    dsimp [B] <;> linarith [hA 0 k, hA 1 k, hA 2 k]

/-- The scalar cutoff inside the already chosen slice core gives its actual
spatial support. The original source cap will be chosen inside this cutoff's
plateau, so the measured row is never changed afterwards. -/
theorem scalarSliceAmplitude_support {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a)
    (hχ : tsupport (χ : Euclidean n → ℝ) ⊆ closedBall 0 (a / 4))
    (j : ℕ) (t : ℝ) :
    Function.support (fun w : Euclidean (n - 1) × Euclidean (n - 1) ↦
      scalarSliceAmplitude sec χ angular H hn j (t, w)) ⊆
        sliceSpatialCore n a ×ˢ sliceInputCore n := by
  intro w hw
  have hm : normalizedMask (n := n) angular H j w.2 ≠ 0 := by
    intro hz
    apply hw
    ext i
    simp only [scalarSliceAmplitude, hz, zero_mul, Pi.zero_apply]
  have hx : χ (adaptedPhysicalCoordinates sec (t, w.1)) ≠ 0 := by
    intro hz
    apply hw
    ext i
    simp only [scalarSliceAmplitude, hz, Complex.ofReal_zero, mul_zero, zero_mul, Pi.zero_apply]
  refine ⟨?_, support_normalizedMask_subset angular H j hm⟩
  have hphysical := hχ (subset_tsupport _ hx)
  have hnorm : ‖adaptedPhysicalCoordinates sec (t, w.1)‖ ≤ a / 4 := by simpa using hphysical
  have hc := norm_adaptedPhysicalCoordinates_symm_le sec (adaptedPhysicalCoordinates sec (t, w.1))
  rw [MeasurableEquiv.symm_apply_apply] at hc
  have hy := (norm_snd_le (t, w.1)).trans (hc.trans hnorm)
  change dist w.1 0 ≤ a / 2
  rw [dist_zero_right]
  linarith

/-- All scalar slice normal-data amplitude fields are constructed on the
same supplied canonical phase geometry. The scalar coefficient is independent
of epsilon, so its epsilon jets vanish exactly. -/
theorem exists_scalarSliceNormalData {ξ : Euclidean n} (sec : AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) (hn : 1 ≤ n)
    (G : UniformNormalGeometry (n - 1) (embeddingDimension n * n)) (C : ℕ → ℝ)
    {a : ℝ} (ha₀ : 0 < a) (hX : G.X₀ = sliceSpatialCore n a) (hD : G.D₀ = sliceInputCore n)
    (hχ : tsupport (χ : Euclidean n → ℝ) ⊆ closedBall 0 (a / 4)) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧ ∀ (t : ℝ), t ∈ Ioo (-a) a →
      ∀ j (N₀ : UniformNormalData G C),
      ∃ N : UniformNormalData (scalarSliceGeometry hn G) (fun k ↦ C k + B k),
        N.phase = N₀.phase ∧ N.parameterDomain = N₀.parameterDomain ∧
        N.extensionDomain = N₀.extensionDomain ∧
        N.amplitude = (fun _ y u ↦ scalarSliceAmplitude sec χ angular H hn j (t, y, u)) := by
  let K := Icc (-a) a ×ˢ (closure G.X ×ˢ closure G.D)
  have hK : IsCompact K := isCompact_Icc.prod
    (G.bounded_X.isCompact_closure.prod G.bounded_D.isCompact_closure)
  obtain ⟨B, hB, hb⟩ := exists_scalarSliceAmplitude_budgets sec χ angular H ha hah hH hH₁ hn hK
  refine ⟨B, hB, ?_⟩
  intro t ht j N₀
  let amp := fun y u ↦ scalarSliceAmplitude sec χ angular H hn j (t, y, u)
  have hs := contDiff_scalarSliceAmplitude sec χ angular H ha hH hn j
  have hamp (ε : ℝ) (w : Euclidean (n - 1) × Euclidean (n - 1)) (hw : w ∈ G.X ×ˢ G.D)
      (k : ℕ) :
      ‖iteratedFDeriv ℝ k (Function.uncurry amp) w‖ +
        ‖deriv (fun _ : ℝ ↦ iteratedFDeriv ℝ k (Function.uncurry amp) w) ε‖ ≤ B k := by
    simp only [deriv_const, norm_zero, add_zero]
    have hh := norm_iteratedFDeriv_slice_le_joint isOpen_univ isOpen_univ hs.contDiffOn
      (mem_univ t) (mem_univ w) k
    exact hh.trans (hb j (t, w) ⟨⟨ht.1.le, ht.2.le⟩, subset_closure hw.1, subset_closure hw.2⟩ k)
  let N : UniformNormalData (scalarSliceGeometry hn G) (fun k ↦ C k + B k) := {
    N₀ with
    amplitude := fun _ ↦ amp
    amplitude_smooth := (hs.comp (by fun_prop)).contDiffOn
    amplitude_support := by
      intro ε _
      change Function.support (Function.uncurry amp) ⊆ G.X₀ ×ˢ G.D₀
      rw [hX, hD]
      exact scalarSliceAmplitude_support sec χ angular H hn ha₀ hχ j t
    input_jets := by
      intro ε hε w hw k hk
      have hp := N₀.input_jets ε hε w hw k hk
      have ha := hamp ε w hw k
      have hz₁ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (N₀.amplitude ε)) w)
      have hz₂ := norm_nonneg (deriv (fun t ↦ iteratedFDeriv ℝ k
        (Function.uncurry (N₀.amplitude t)) w) ε)
      simp only [Function.uncurry_def] at hp ha hz₁ hz₂ ⊢
      linarith }
  exact ⟨N, rfl, rfl, rfl, rfl⟩

end JanetCartan.PhysicalSampling
