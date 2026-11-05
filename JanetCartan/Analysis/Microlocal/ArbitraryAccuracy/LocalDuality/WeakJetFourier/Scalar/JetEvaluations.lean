module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Scalar.Distribution
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives

/-!
# Coordinate derivatives constructed from weak jets

For `app:ch_regular_base:eq:negative-duality` and
`app:ch_regular:eq:inverse-remainder`, evaluate each genuine multilinear weak jet
on unit vectors. The resulting L² classes satisfy the actual distributional
coordinate identities. Recursion constructs all ordered derivatives with a
uniform finite norm bound for the scalar Fourier comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped SchwartzMap LineDeriv Topology ContDiff

namespace JanetCartan.LocalSobolev.SobolevExtension

open Pseudodifferential

variable {d N : ℕ} {W : Set (EuclideanSpace ℝ (Fin d))} {v : LocalL2 W ℂ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Evaluation of a genuine L² jet is L², for the coordinate derivative
construction in `app:ch_regular_base:eq:negative-duality`. -/
theorem memLp_evaluatedJet (e : SobolevExtension W N v) (j : ℕ) (hj : j ≤ N)
    (w : Fin j → E) : MemLp (fun x ↦ e.jet j x w) 2 volume :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ E) ℂ w).comp_memLp'
    (e.memLp_jet j hj)

/-- The actual L² class obtained by evaluating a weak jet, for
`app:ch_regular_base:eq:negative-duality`. -/
def evaluatedJetL2 (e : SobolevExtension W N v) (j : ℕ) (hj : j ≤ N)
    (w : Fin j → E) : Lp (α := E) ℂ 2 :=
  (e.memLp_evaluatedJet j hj w).toLp (fun x ↦ e.jet j x w)

/-- The evaluated L² jet retains its prescribed representative a.e., as
needed for the weak-to-distribution bridge in `app:ch_regular_base:eq:negative-duality`. -/
theorem evaluatedJetL2_coeFn (e : SobolevExtension W N v) (j : ℕ) (hj : j ≤ N)
    (w : Fin j → E) : e.evaluatedJetL2 j hj w =ᵐ[volume] fun x ↦ e.jet j x w :=
  MemLp.coeFn_toLp _

/-- Unit-vector evaluation is bounded by the total genuine jet norm,
for the scalar comparison in `app:ch_regular:eq:inverse-remainder`. -/
theorem norm_evaluatedJetL2_le (e : SobolevExtension W N v) (j : ℕ) (hj : j ≤ N)
    (w : Fin j → E) (hw : ∀ i, ‖w i‖ ≤ 1) :
    ‖e.evaluatedJetL2 j hj w‖ ≤ e.jetNorm := by
  rw [evaluatedJetL2, Lp.norm_toLp]
  have hb : eLpNorm (fun x ↦ e.jet j x w) 2 volume ≤ eLpNorm (e.jet j) 2 volume :=
    eLpNorm_mono (e.memLp_evaluatedJet j hj w).aestronglyMeasurable
      (fun x ↦ (e.jet j x).unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr hw))
  exact (ENNReal.toReal_mono (e.memLp_jet j hj).eLpNorm_ne_top hb).trans
    (Finset.single_le_sum (f := fun k ↦ (eLpNorm (e.jet k) 2 volume).toReal)
      (fun _ _ ↦ ENNReal.toReal_nonneg) (Finset.mem_range.mpr (by omega)))

/-- The next evaluated jet is the actual distributional coordinate
derivative, with the Fourier convention inherited from the derivative API, for
`app:ch_regular_base:eq:negative-duality`. -/
theorem evaluatedJetL2_hasCoordinateDerivative (e : SobolevExtension W N v)
    (j : ℕ) (hj : j < N) (w : Fin j → E) (i : Fin d) :
    HasEuclideanL2CoordinateDerivative i (e.evaluatedJetL2 j hj.le w)
      (e.evaluatedJetL2 (j + 1) (by omega)
        (Fin.cons (EuclideanSpace.basisFun (Fin d) ℝ i) w)) := by
  exact (e.weakJet.2 j hj).comp_clm_univ
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ E) ℂ w)
    |>.toTemperedDistribution (e.evaluatedJetL2 j hj.le w)
      (e.evaluatedJetL2 (j + 1) (by omega)
        (Fin.cons (EuclideanSpace.basisFun (Fin d) ℝ i) w))
      (EuclideanSpace.basisFun (Fin d) ℝ i)
      (e.evaluatedJetL2_coeFn j hj.le w)
      (e.evaluatedJetL2_coeFn (j + 1) (by omega) _)

/-- Construct the finite family of genuine coordinate derivatives from
the remaining weak jet. The norm bound supplies the scalar Fourier comparison
for `app:ch_regular:eq:inverse-remainder`, including dimension and order zero. -/
theorem evaluatedJetL2_exists_integerDerivatives (e : SobolevExtension W N v)
    (m j : ℕ) (hjm : j + m ≤ N) (w : Fin j → E) (hw : ∀ i, ‖w i‖ ≤ 1) :
    ∃ f : EuclideanL2DerivativeFamily d m,
      HasEuclideanL2Derivatives m (e.evaluatedJetL2 j (by omega) w) f ∧
      euclideanL2DerivativeNormSum f ≤ ((d : ℝ) + 1) ^ m * e.jetNorm := by
  induction m generalizing j with
  | zero =>
    refine ⟨fun _ ↦ e.evaluatedJetL2 j (by omega) w, rfl, ?_⟩
    simpa only [euclideanL2DerivativeNormSum, pow_zero, one_mul] using
      e.norm_evaluatedJetL2_le j (by omega) w hw
  | succ m ih =>
    have hw' (i : Fin d) :
        ∀ k : Fin (j + 1),
          ‖(Fin.cons (EuclideanSpace.basisFun (Fin d) ℝ i) w : Fin (j + 1) → E) k‖ ≤ 1 := by
      intro k
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · simp
      · exact hw k
    choose f hf hnorm using fun i : Fin d ↦
      ih (j + 1) (by omega) (Fin.cons (EuclideanSpace.basisFun (Fin d) ℝ i) w) (hw' i)
    let g : EuclideanL2DerivativeFamily d (m + 1) := fun x ↦
      match x with
      | none => e.evaluatedJetL2 j (by omega) w
      | some (i, z) => f i z
    refine ⟨g, ⟨rfl, fun i ↦ ?_⟩, ?_⟩
    · change HasEuclideanL2CoordinateDerivative i _ (f i (.empty d m)) ∧
        HasEuclideanL2Derivatives m (f i (.empty d m)) (f i)
      rw [(hf i).root]
      exact ⟨e.evaluatedJetL2_hasCoordinateDerivative j (by omega) w i, hf i⟩
    · change ‖e.evaluatedJetL2 j (by omega) w‖ +
          ∑ i : Fin d, euclideanL2DerivativeNormSum (f i) ≤ _
      have hpow : 1 ≤ ((d : ℝ) + 1) ^ m :=
        one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) d])
      calc
        _ ≤ ((d : ℝ) + 1) ^ m * e.jetNorm +
            ∑ _i : Fin d, ((d : ℝ) + 1) ^ m * e.jetNorm :=
          add_le_add ((e.norm_evaluatedJetL2_le j (by omega) w hw).trans
            (le_mul_of_one_le_left e.jetNorm_nonneg hpow))
            (Finset.sum_le_sum (fun i _ ↦ hnorm i))
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, pow_succ]; ring

/-- Order-zero evaluation is exactly the whole-space extension class,
for the final assembly of `app:ch_regular_base:eq:negative-duality`. -/
theorem evaluatedJetL2_zero (e : SobolevExtension W N v) (w : Fin 0 → E) :
    e.evaluatedJetL2 0 (Nat.zero_le _) w = e.toL2 := by
  apply Lp.ext
  filter_upwards [e.evaluatedJetL2_coeFn 0 (Nat.zero_le _) w, e.toL2_coeFn] with x hx he
  rw [hx, he, e.weakJet.1, iteratedFDeriv_zero_apply]

end JanetCartan.LocalSobolev.SobolevExtension
