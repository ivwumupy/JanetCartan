module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Bounds

/-!
# Compact output Sobolev conversion from coordinate bounds

The final compact-output step in `app:ch_response:thm:response-literal-transfer`.
`LowEnvelope.IntegratedJets` supplies integrated pointwise jet estimates; its
consumer must identify those jets with the output's coordinate derivatives and
supply smoothness and compact support. This module then constructs actual L²
coordinate derivatives and obtains integer Fourier Sobolev membership and a
norm bound. All measures are literal Euclidean Lebesgue measures, and the
Fourier Sobolev normalization is the existing pseudodifferential one.

The constant `2^s (n+1)^s` is chosen independently of the function, its compact
support and the derivative bound. Finite vector outputs are handled in the
existing scalar spaces, one component at a time.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.ResponseTransfer.LowEnvelope

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Build the actual derivative family consumed by the integer Sobolev norm
comparison in `app:ch_response:thm:response-literal-transfer`. The aggregate
bound uses the specified compact support at every derivative order. -/
private theorem compact_derivative_family (s : ℕ) {K : Set E} (hK : IsCompact K)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ K)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ α : List (Fin n), α.length ≤ s → ∀ x,
      ‖euclideanCoordinateDerivList α u x‖ ≤ B) :
    ∃ v : EuclideanL2DerivativeFamily n s,
      HasEuclideanL2Derivatives s
        ((hu.continuous.memLp_of_hasCompactSupport
          (hK.of_isClosed_subset (isClosed_tsupport u) hs)).toLp u) v ∧
      euclideanL2DerivativeNormSum v ≤
        ((n : ℝ) + 1) ^ s * (B * Real.sqrt (volume.real K)) := by
  induction s generalizing u with
  | zero =>
    have hus : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hs
    let u₂ : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    have hroot : ‖u₂‖ ≤ B * Real.sqrt (volume.real K) :=
      FiniteChain.Retarded.KernelSobolev.norm_toLp_le_of_support_bound
        (hu.continuous.memLp_of_hasCompactSupport hus) hK.measurableSet hK.measure_ne_top
        hB (hb [] (by simp))
        (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)))
    exact ⟨fun _ ↦ u₂, rfl, by simpa [euclideanL2DerivativeNormSum] using hroot⟩
  | succ s ih =>
    have hus : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hs
    let u₂ : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    have hroot : ‖u₂‖ ≤ B * Real.sqrt (volume.real K) :=
      FiniteChain.Retarded.KernelSobolev.norm_toLp_le_of_support_bound
        (hu.continuous.memLp_of_hasCompactSupport hus) hK.measurableSet hK.measure_ne_top
        hB (hb [] (by simp))
        (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)))
    let D (i : Fin n) := euclideanCoordinateDerivList [i] u
    have hd (i : Fin n) : ContDiff ℝ ∞ (D i) := contDiff_euclideanCoordinateDerivList hu [i]
    have hds (i : Fin n) : tsupport (D i) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hs
    have hdb (i : Fin n) (α : List (Fin n)) (hα : α.length ≤ s) (x : E) :
        ‖euclideanCoordinateDerivList α (D i) x‖ ≤ B := by
      rw [← euclideanCoordinateDerivList_append]
      exact hb (α ++ [i]) (by simpa using Nat.succ_le_succ hα) x
    choose w hw hwbound using fun i ↦ ih (D i) (hd i) (hds i) (hdb i)
    let v : EuclideanL2DerivativeFamily n (s + 1) := fun a ↦
      match a with
      | none => u₂
      | some (i, a) => w i a
    have hv : HasEuclideanL2Derivatives (s + 1) u₂ v := by
      refine ⟨rfl, fun i ↦ ?_⟩
      change HasEuclideanL2CoordinateDerivative i u₂ (w i (.empty n s)) ∧
        HasEuclideanL2Derivatives s (w i (.empty n s)) (w i)
      rw [(hw i).root]
      exact ⟨hasEuclideanL2CoordinateDerivative_toLp u hu hus i, hw i⟩
    refine ⟨v, hv, ?_⟩
    have hpow : 1 ≤ ((n : ℝ) + 1) ^ s :=
      one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hR : 0 ≤ B * Real.sqrt (volume.real K) := mul_nonneg hB (Real.sqrt_nonneg _)
    calc
      euclideanL2DerivativeNormSum v = ‖u₂‖ + ∑ i : Fin n, euclideanL2DerivativeNormSum (w i) := rfl
      _ ≤ ((n : ℝ) + 1) ^ s * (B * Real.sqrt (volume.real K)) +
          ∑ _i : Fin n, ((n : ℝ) + 1) ^ s * (B * Real.sqrt (volume.real K)) :=
        add_le_add (hroot.trans (le_mul_of_one_le_left hR hpow))
          (Finset.sum_le_sum fun i _ ↦ hwbound i)
      _ = ((n : ℝ) + 1) ^ (s + 1) * (B * Real.sqrt (volume.real K)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
        ring

/-- Dimension/order constant for the compact output conversion in
`app:ch_response:thm:response-literal-transfer`. -/
def compactCoordinateSobolevConstant (n s : ℕ) : ℝ :=
  (2 : ℝ) ^ s * ((n : ℝ) + 1) ^ s

/-- The constant for `app:ch_response:thm:response-literal-transfer` is positive,
including at order zero and in dimension zero. -/
theorem compactCoordinateSobolevConstant_pos (n s : ℕ) :
    0 < compactCoordinateSobolevConstant n s := by
  unfold compactCoordinateSobolevConstant
  positivity

/-- Compact output conversion for `app:ch_response:thm:response-literal-transfer`.
The input consists only of smoothness, compact support, and pointwise bounds for
ordered coordinate derivatives. Both actual L² realization and integer Fourier
Sobolev membership are conclusions. The constant is fixed before `u`, `K`, `B`.
The consumer identifies the integrated jets with these derivatives. -/
theorem exists_compactCoordinateSobolev (s : ℕ) (u : E → ℂ)
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (hs : Function.support u ⊆ K) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ α : List (Fin n), α.length ≤ s → ∀ x,
      ‖euclideanCoordinateDerivList α u x‖ ≤ B) :
    ∃ hu₂ : MemLp u 2 volume,
      MemFourierSobolev (s : ℝ) (hu₂.toLp u) ∧
      fourierSobolevNorm (s : ℝ) (hu₂.toLp u) ≤
        compactCoordinateSobolevConstant n s * Real.sqrt (volume.real K) * B := by
  have hts : tsupport u ⊆ K := closure_minimal hs hK.isClosed
  have hus : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hts
  obtain ⟨v, hv, hvbound⟩ := compact_derivative_family s hK u hu hts hB hb
  refine ⟨hu.continuous.memLp_of_hasCompactSupport hus, hv.memFourierSobolev, ?_⟩
  calc
    _ ≤ (2 : ℝ) ^ s * euclideanL2DerivativeNormSum v := hv.fourierSobolevNorm_le
    _ ≤ (2 : ℝ) ^ s * (((n : ℝ) + 1) ^ s * (B * Real.sqrt (volume.real K))) :=
      mul_le_mul_of_nonneg_left hvbound (by positivity)
    _ = _ := by unfold compactCoordinateSobolevConstant; ring

/-- The finite-vector version of the compact output conversion in
`app:ch_response:thm:response-literal-transfer`, expressed in the existing scalar
Fourier Sobolev spaces. There is also an actual vector L² realization; no vector
Sobolev model is introduced. -/
theorem exists_compactCoordinateSobolev_components {r : ℕ} (s : ℕ)
    (u : E → EuclideanSpace ℂ (Fin r)) (hu : ContDiff ℝ ∞ u)
    {K : Set E} (hK : IsCompact K) (hs : Function.support u ⊆ K)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i : Fin r, ∀ α : List (Fin n), α.length ≤ s → ∀ x,
      ‖euclideanCoordinateDerivList α (fun y ↦ u y i) x‖ ≤ B) :
    MemLp u 2 volume ∧
    ∃ hc : ∀ i : Fin r, MemLp (fun x ↦ u x i) 2 volume,
      (∀ i, MemFourierSobolev (s : ℝ) ((hc i).toLp (fun x ↦ u x i))) ∧
      (∀ i, fourierSobolevNorm (s : ℝ) ((hc i).toLp (fun x ↦ u x i)) ≤
        compactCoordinateSobolevConstant n s * Real.sqrt (volume.real K) * B) ∧
      (∑ i, fourierSobolevNorm (s : ℝ) ((hc i).toLp (fun x ↦ u x i))) ≤
        (r : ℝ) * compactCoordinateSobolevConstant n s * Real.sqrt (volume.real K) * B := by
  have hus : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u)
    (closure_minimal hs hK.isClosed)
  refine ⟨hu.continuous.memLp_of_hasCompactSupport hus, ?_⟩
  have hcomp (i : Fin r) : ContDiff ℝ ∞ (fun x ↦ u x i) :=
    ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin r) →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hu
  have hcs (i : Fin r) : Function.support (fun x ↦ u x i) ⊆ K := by
    intro x hx
    apply hs
    intro hz
    exact hx (by simp [hz])
  choose hc hmem hnorm using fun i ↦ exists_compactCoordinateSobolev s
    (fun x ↦ u x i) (hcomp i) hK (hcs i) hB (hb i)
  refine ⟨hc, hmem, hnorm, ?_⟩
  calc
    _ ≤ ∑ _i : Fin r, compactCoordinateSobolevConstant n s * Real.sqrt (volume.real K) * B :=
      Finset.sum_le_sum fun i _ ↦ hnorm i
    _ = _ := by simp [mul_assoc]

end JanetCartan.ResponseTransfer.LowEnvelope
