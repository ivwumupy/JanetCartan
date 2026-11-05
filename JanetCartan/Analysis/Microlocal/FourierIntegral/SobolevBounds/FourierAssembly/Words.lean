module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Coordinates

/-!
# Sobolev reconstruction from finite weak words

The finite expansion in `app:ch_regular_base:eq:graph-derivative-transfer`
provides L² representatives of all words. This module deduces membership and a
norm estimate, without assuming that the output already belongs to Hˢ.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv JanetCartan.Pseudodifferential
open scoped SchwartzMap
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private theorem scalar_distribution_injective {u v : L²}
    (h : (u : 𝓢'(E, ℂ)) = (v : 𝓢'(E, ℂ))) : u = v := by
  apply Lp.ext
  have he : TemperedDistribution.smulLeftCLM ℂ (fun _ : E ↦ 1)
      (u : 𝓢'(E, ℂ)) = (v : 𝓢'(E, ℂ)) := by
    simpa only [TemperedDistribution.smulLeftCLM_const, one_smul] using h
  simpa using ae_eq_pointwise_smul_of_toTemperedDistribution_eq _ (by fun_prop) u v he

private theorem ordered_action_append {B : Type*} (D : Fin n → B → B)
    (is js : List (Fin n)) (u : B) :
    orderedTransferAction D (is ++ js) u =
      orderedTransferAction D is (orderedTransferAction D js u) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, orderedTransferAction, ih]

/-- Scalar coordinates preserve the exact order of weak graph derivatives.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphL2_coordinate_word (u : H) (a : Fin r) (is : List (Fin n))
    (φ : 𝓢(E, ℂ)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        ((finiteL2CoordinateIsometry volume u a : L²) : 𝓢'(E, ℂ)) φ =
      (orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (u : 𝓢'(E, V)) φ) a := by
  induction is generalizing φ with
  | nil => exact graphL2_coordinate_distribution u a φ
  | cons i is ih => exact ih (-lineDerivOp (EuclideanSpace.single i (1 : ℝ)) φ)

/-- Uniform L² bounds on the actual scalar weak words give integer Sobolev
membership and a dimension/order constant, including order zero.
Source: `app:ch_regular_base:eq:fio-input`. -/
theorem graph_scalar_sobolev_of_weak_words (s : ℕ) (u : L²)
    (v : List (Fin n) → L²) (M : ℝ)
    (hw : ∀ is, is.length ≤ s →
      orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (u : 𝓢'(E, ℂ)) = (v is : 𝓢'(E, ℂ)))
    (hb : ∀ is, is.length ≤ s → ‖v is‖ ≤ M) :
    MemFourierSobolev (s : ℝ) u ∧
      fourierSobolevNorm (s : ℝ) u ≤ (n + 1 : ℝ) ^ s * M := by
  induction s generalizing u v with
  | zero =>
    have he : u = v [] := scalar_distribution_injective (hw [] (by simp))
    simp only [Nat.cast_zero]
    exact ⟨memFourierSobolev_zero u, by simpa [he] using hb [] (by simp)⟩
  | succ s ih =>
    have hbase := ih u v (fun is hi ↦ hw is (hi.trans (Nat.le_succ s)))
      (fun is hi ↦ hb is (hi.trans (Nat.le_succ s)))
    have hd (i : Fin n) : HasEuclideanL2CoordinateDerivative i u (v [i]) := by
      simpa only [HasEuclideanL2CoordinateDerivative, euclideanCoordinateDerivative,
        EuclideanSpace.basisFun_apply, orderedTransferAction] using hw [i] (by simp)
    have hbranch (i : Fin n) := ih (v [i]) (fun is ↦ v (is ++ [i]))
      (fun is hi ↦ by
        have he := hw (is ++ [i]) (by simpa using Nat.add_le_add_right hi 1)
        rw [ordered_action_append, hw [i] (by simp)] at he
        exact he)
      (fun is hi ↦ hb (is ++ [i]) (by simpa using Nat.add_le_add_right hi 1))
    constructor
    · simpa only [Nat.cast_add, Nat.cast_one] using
        hbase.1.of_coordinateDerivatives (by positivity) (fun i ↦ (hbranch i).1) hd
    · calc
        _ ≤ fourierSobolevNorm (s : ℝ) u +
            ∑ i, fourierSobolevNorm (s : ℝ) (v [i]) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            fourierSobolevNorm_le_coordinateDerivatives (by positivity) hbase.1
              (fun i ↦ (hbranch i).1) hd
        _ ≤ (n + 1 : ℝ) ^ s * M + ∑ _i : Fin n, (n + 1 : ℝ) ^ s * M :=
          add_le_add hbase.2 (Finset.sum_le_sum (fun i _ ↦ (hbranch i).2))
        _ = _ := by simp [pow_succ]; ring

/-- Finite vector weak derivatives reconstruct the actual Euclidean Fourier
Sobolev output. The constant is independent of `M` and the datum; zero order
and zero-dimensional fibers are included.
Source: `app:ch_regular_base:eq:graph-derivative-transfer` to
`app:ch_regular_base:eq:fio-input`. -/
theorem graph_vector_sobolev_of_weak_words (s : ℕ) (u : H)
    (v : List (Fin n) → H) (M : ℝ)
    (hw : ∀ is, is.length ≤ s →
      orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (u : 𝓢'(E, V)) = (v is : 𝓢'(E, V)))
    (hb : ∀ is, is.length ≤ s → ‖v is‖ ≤ M) :
    MemVectorFourierSobolev (s : ℝ) u ∧
      vectorFourierSobolevNorm (s : ℝ) u ≤ ((r : ℝ) * (n + 1 : ℝ) ^ s) * M := by
  have hc (a : Fin r) := graph_scalar_sobolev_of_weak_words s
    (finiteL2CoordinateIsometry volume u a)
    (fun is ↦ finiteL2CoordinateIsometry volume (v is) a) M
    (fun is hi ↦ by
      ext φ
      rw [graphL2_coordinate_word, graphL2_coordinate_distribution, hw is hi])
    (fun is hi ↦ by
      have hn : ‖finiteL2CoordinateIsometry volume (v is) a‖ ≤ ‖v is‖ := by
        simpa using PiLp.norm_apply_le (finiteL2CoordinateIsometry volume (v is)) a
      exact hn.trans (hb is hi))
  refine ⟨fun a ↦ (hc a).1, ?_⟩
  calc
    _ ≤ ∑ a, fourierSobolevNorm (s : ℝ) (finiteL2CoordinateIsometry volume u a) :=
      matrixFourierSobolevNorm_le_sum _ _
    _ ≤ ∑ _a : Fin r, (n + 1 : ℝ) ^ s * M :=
      Finset.sum_le_sum (fun a _ ↦ (hc a).2)
    _ = _ := by simp [mul_assoc]

end JanetCartan.FourierIntegral
