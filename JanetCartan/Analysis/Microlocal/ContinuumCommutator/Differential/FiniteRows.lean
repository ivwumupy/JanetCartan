module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Compact
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Finite matrix rows of full-amplitude commutators

For `app:ch_background:eq:bg-commutator`, assemble the proved scalar kernel
identity and additive bound on the existing finite Hilbert sums. The Sobolev
quantity is the ℓ² norm of the scalar Fourier Sobolev norms. The parent may
flatten its finite normal-row and chart indices into the matrix index.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- `app:ch_background:eq:bg-commutator`: distributional differentiation
commutes with the finite normal-row sums. -/
theorem orderedTransferAction_distribution_sum {J : Type*} [Fintype J]
    (is : List (Fin d)) (v : J → 𝓢'(E, ℂ)) :
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i 1 : E)) is (∑ j, v j) =
      ∑ j, orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i 1 : E)) is (v j) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [orderedTransferAction, ih, lineDerivOp_sum]

private theorem distribution_coe_sum {J : Type*} [Fintype J] (v : J → L²) :
    ((∑ j, v j : L²) : 𝓢'(E, ℂ)) = ∑ j, (v j : 𝓢'(E, ℂ)) :=
  map_sum (Lp.toTemperedDistributionCLM ℂ volume 2) v Finset.univ

/-- `app:ch_background:eq:bg-commutator`: exact compact-test commutator and
one-high bound for an actual finite matrix of two-position PDOs. All scalar
entry estimates and identities are instantiated from primitive bounds. The
input and output use the shared finite Hilbert sums, with their ℓ² norms. -/
theorem exists_matrixTwoPositionL2Operator_compact_commutator_bound
    (I J : Type*) [Fintype I] [Fintype J]
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : I → J → E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (b i j)))
        (hs : ∀ i j ξ, SupportedInCenteredBox R (b i j ξ)) (H : ℝ)
        (hM : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + is.length) H)
        (u : J → E → ℂ) (hu : ∀ j, ContDiff ℝ ∞ (u j))
        (hus : ∀ j, HasCompactSupport (u j)),
        let f : PiLp 2 (fun _ : J => L²) := WithLp.toLp 2 (fun j =>
          ((hu j).continuous.memLp_of_hasCompactSupport (hus j)).toLp (u j))
        let df : PiLp 2 (fun _ : J => L²) := WithLp.toLp 2 (fun j =>
          ((contDiff_euclideanCoordinateDerivList (hu j) is).continuous.memLp_of_hasCompactSupport
            (hasCompactSupport_euclideanCoordinateDerivList (hus j) is)).toLp
              (euclideanCoordinateDerivList is (u j)))
        let T := matrixOperator (fun i j => twoPositionL2Operator hd R (b i j) (hb i j)
          (hs i j) M (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _)))
        ∃ w : PiLp 2 (fun _ : I => L²),
          (∀ i, orderedTransferAction (fun a => lineDerivOp (EuclideanSpace.single a 1 : E)) is
            ((T f) i : 𝓢'(E, ℂ)) - ((T df) i : 𝓢'(E, ℂ)) = (w i : 𝓢'(E, ℂ))) ∧
          ‖w‖ ≤ C * (‖WithLp.toLp 2 (fun j => fourierSobolevNorm (n : ℝ) (f j))‖ +
            max 1 H * ‖f‖) := by
  classical
  obtain ⟨C, hC, he⟩ := exists_twoPositionL2Operator_compact_commutator_bound hd R n M
  refine ⟨(Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C, by positivity, ?_⟩
  intro b hb hs H hM is hlen hH u hu hus
  dsimp only
  let f : PiLp 2 (fun _ : J => L²) := WithLp.toLp 2 (fun j =>
    ((hu j).continuous.memLp_of_hasCompactSupport (hus j)).toLp (u j))
  let df : PiLp 2 (fun _ : J => L²) := WithLp.toLp 2 (fun j =>
    ((contDiff_euclideanCoordinateDerivList (hu j) is).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordinateDerivList (hus j) is)).toLp
        (euclideanCoordinateDerivList is (u j)))
  let T := fun i j => twoPositionL2Operator hd R (b i j) (hb i j) (hs i j) M
    (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _))
  choose w hw hnorm using fun i j =>
    he (b i j) (hb i j) (hs i j) H (hM i j) is hlen (hH i j) (u j) (hu j) (hus j)
  let W : PiLp 2 (fun _ : I => L²) := ∑ i, ∑ j, coordinateInjection i (w i j)
  have hW (i : I) : W i = ∑ j, w i j := by
    simp [W, coordinateInjection, Pi.single_apply]
  refine ⟨W, ?_, ?_⟩
  · intro i
    change orderedTransferAction (fun a => lineDerivOp (EuclideanSpace.single a 1 : E)) is
      ((matrixOperator T f) i : 𝓢'(E, ℂ)) - ((matrixOperator T df) i : 𝓢'(E, ℂ)) = _
    rw [matrixOperator_apply, matrixOperator_apply, hW]
    simp only [distribution_coe_sum, orderedTransferAction_distribution_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => hw i j)
  · let N : PiLp 2 (fun _ : J => ℝ) := WithLp.toLp 2
      (fun j => fourierSobolevNorm (n : ℝ) (f j))
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
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
            (coordinateInjection i).norm_map _ |>.le))
      _ ≤ ∑ _i : I, ∑ _j : J, C * (‖N‖ + max 1 H * ‖f‖) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end JanetCartan.Pseudodifferential
