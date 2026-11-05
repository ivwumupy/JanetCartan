module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Periodic
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.FiniteRows

/-!
# Finite matrices of periodic chart commutators

For `app:ch_background:eq:bg-commutator`, assemble actual periodic weak
identities on the shared finite Hilbert sums. The input Hⁿ quantity is still
the finite Hilbert sum of the compact extensions' Euclidean Hⁿ norms.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Ordered periodic weak differentiation commutes with finite row sums
(`app:ch_background:eq:bg-commutator`). -/
theorem periodicWeakDerivativeList_sum {J : Type*} [Fintype J]
    (is : List (Fin d)) (f g : J → PeriodicL2 d ℂ)
    (h : ∀ j, HasPeriodicWeakDerivativeList is (f j) (g j)) :
    HasPeriodicWeakDerivativeList is (∑ j, f j) (∑ j, g j) := by
  intro φ hφ
  rw [← inner_periodicL2_ofSmooth _ 0 φ hφ,
    ← inner_periodicL2_ofSmooth _ 0 _ (hφ.coordinateDerivList is.reverse)]
  simp only [sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [inner_periodicL2_ofSmooth] using h j φ hφ

/-- The actual finite matrix of unit-torus operators satisfies the ordered
weak commutator identity. Its additive constant depends on the finite row
counts and low budget, independently of the high budget. The remaining local
Sobolev comparison concerns only the fixed input extensions
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_matrixTorusL2Operator_smooth_commutator_bound
    (I J : Type*) [Fintype I] [Fintype J]
    (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : I → J → E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (b i j)))
        (hs : ∀ i j ξ, SupportedInCenteredBox r (b i j ξ)) (H : ℝ)
        (hM : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + is.length) H)
        (χ : SourceCutoff d r) (u : J → Torus d → ℂ)
        (hu : ∀ j, IsSmoothPeriodic (u j)) (hm : ∀ j, MemLp (u j) 2),
        let f : PiLp 2 (fun _ : J ↦ PeriodicL2 d ℂ) :=
          WithLp.toLp 2 (fun j ↦ (hm j).toLp (u j))
        let df : PiLp 2 (fun _ : J ↦ PeriodicL2 d ℂ) := WithLp.toLp 2 (fun j ↦
          (((hu j).coordinateDerivList is).1.memLp_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).toLp (periodicCoordinateDerivList is (u j)))
        let T := matrixOperator (fun i j ↦ torusL2Operator hd r (b i j) (hb i j)
          (hs i j) M (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _)))
        ∃ w : PiLp 2 (fun _ : I ↦ PeriodicL2 d ℂ),
          (∀ i, HasPeriodicWeakDerivativeList is ((T f) i) ((T df) i + w i)) ∧
          ‖w‖ ≤ C * (‖WithLp.toLp 2 (fun j ↦
            fourierSobolevNorm (n : ℝ) (χ.extendL2 (hu j)))‖ + max 1 H * ‖f‖) := by
  classical
  obtain ⟨C, hC, he⟩ := exists_torusL2Operator_smooth_commutator_bound hd r hr n M
  refine ⟨(Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C, by positivity, ?_⟩
  intro b hb hs H hM is hlen hH χ u hu hm
  dsimp only
  let f : PiLp 2 (fun _ : J ↦ PeriodicL2 d ℂ) :=
    WithLp.toLp 2 (fun j ↦ (hm j).toLp (u j))
  let df : PiLp 2 (fun _ : J ↦ PeriodicL2 d ℂ) := WithLp.toLp 2 (fun j ↦
    (((hu j).coordinateDerivList is).1.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).toLp (periodicCoordinateDerivList is (u j)))
  let T := fun i j ↦ torusL2Operator hd r (b i j) (hb i j) (hs i j) M
    (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _))
  choose w hw hnorm using fun i j ↦
    he (b i j) (hb i j) (hs i j) H (hM i j) is hlen (hH i j) χ (u j) (hu j) (hm j)
  let W : PiLp 2 (fun _ : I ↦ PeriodicL2 d ℂ) := ∑ i, ∑ j, coordinateInjection i (w i j)
  have hW (i : I) : W i = ∑ j, w i j := by
    simp [W, coordinateInjection, Pi.single_apply]
  refine ⟨W, ?_, ?_⟩
  · intro i
    change HasPeriodicWeakDerivativeList is ((matrixOperator T f) i)
      ((matrixOperator T df) i + W i)
    rw [matrixOperator_apply, matrixOperator_apply, hW, ← Finset.sum_add_distrib]
    exact periodicWeakDerivativeList_sum is _ _ (hw i)
  · let N : PiLp 2 (fun _ : J ↦ ℝ) := WithLp.toLp 2
      (fun j ↦ fourierSobolevNorm (n : ℝ) (χ.extendL2 (hu j)))
    have hentry (i : I) (j : J) : ‖w i j‖ ≤ C * (‖N‖ + max 1 H * ‖f‖) := by
      apply (hnorm i j).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add
      · have h := PiLp.norm_apply_le N j
        simpa only [N, PiLp.toLp_apply, Real.norm_eq_abs,
          abs_of_nonneg (fourierSobolevNorm_nonneg _ _)] using h
      · exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le f j) (by positivity)
    calc
      ‖W‖ ≤ ∑ i, ∑ j, ‖w i j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
            (coordinateInjection i).norm_map _ |>.le))
      _ ≤ ∑ _i : I, ∑ _j : J, C * (‖N‖ + max 1 H * ‖f‖) :=
        Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hentry i j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end JanetCartan.Pseudodifferential.DifferentialChart
