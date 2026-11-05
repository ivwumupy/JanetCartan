module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior

/-!
# Smooth normal commutators including the exterior multiplier

For `app:ch_background:eq:bg-commutator`, combine the literal finite matrix
chart operator with a fixed smooth exterior multiplier. The additive bound
has one high amplitude budget and no high coefficient multiplying the Hⁿ norm.
The actual normal-reduction producer must supply the amplitude bounds and the
identification with its normal. The all-data chart extension is separate.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
open JanetCartan.AmplitudeBound
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.Pseudodifferential.DifferentialChart
open PeriodicSobolevSpace
open JanetCartan.ContinuumCommutator
variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => PeriodicL2 d ℂ
local notation "Rows" => PiLp 2 (fun _ : I ↦ L²)

/-- The actual matrix operator plus the fixed diagonal exterior multiplier
on the shared finite Hilbert sum (`app:ch_background:prop:bg-inverse`). -/
def matrixWithExteriorOperator (T : Rows →L[ℂ] Rows)
    (q : Torus d → ℝ) (hq : Continuous q) : Rows →L[ℝ] Rows :=
  T.restrictScalars ℝ + ∑ i,
    ((coordinateInjection i).toContinuousLinearMap.restrictScalars ℝ).comp
      ((Exterior.multiplication q hq).comp (PiLp.proj 2 (fun _ : I ↦ L²) i))

/-- The exterior normal acts by literal multiplication on each row
(`app:ch_background:eq:bg-commutator`). -/
theorem matrixWithExteriorOperator_apply (T : Rows →L[ℂ] Rows)
    (q : Torus d → ℝ) (hq : Continuous q) (f : Rows) (i : I) :
    matrixWithExteriorOperator T q hq f i = T f i + Exterior.multiplication q hq (f i) := by
  classical
  simp [matrixWithExteriorOperator, coordinateInjection, Pi.single_apply]

private theorem weakDerivativeList_add (is : List (Fin d)) (f g v w : L²)
    (hf : HasPeriodicWeakDerivativeList is f v)
    (hg : HasPeriodicWeakDerivativeList is g w) :
    HasPeriodicWeakDerivativeList is (f + g) (v + w) := by
  intro φ hφ
  rw [← inner_periodicL2_ofSmooth _ 0 φ hφ,
    ← inner_periodicL2_ofSmooth _ 0 _ (hφ.coordinateDerivList is.reverse)]
  simp only [inner_add_left, mul_add]
  rw [inner_periodicL2_ofSmooth, inner_periodicL2_ofSmooth,
    inner_periodicL2_ofSmooth, inner_periodicL2_ofSmooth, hf φ hφ, hg φ hφ]

private theorem exterior_weakDerivativeList (q : Torus d → ℝ) (hq : IsSmoothPeriodic q)
    (is : List (Fin d)) (u : Torus d → ℂ) (hu : IsSmoothPeriodic u) :
    HasPeriodicWeakDerivativeList is
      (Exterior.multiplication q hq.1 (toL2 0 (ofSmooth 0 u hu)))
      (Exterior.multiplication q hq.1 (toL2 0 (ofSmooth 0
        (periodicCoordinateDerivList is u) (hu.coordinateDerivList is))) +
        Exterior.commutator q hq is (ofSmooth (is.length - 1) u hu)) := by
  rw [Exterior.commutator_ofSmooth, ← add_sub_assoc, add_sub_cancel_left,
    Exterior.multiplication_ofSmooth hq hu 0 0]
  exact (Exterior.smooth_smul hq hu).hasPeriodicWeakDerivativeList is 0 0

/-- `app:ch_background:eq:bg-commutator` on smooth periodic data for the
finite matrix normal plus a fixed smooth exterior multiplier. All entry
estimates, chart comparisons, and multiplier estimates are proved from the
primitive bounds; the constant is selected before the amplitude and high budget.
Taking `q = (1 - χ)^2` uses `Exterior.smooth_exteriorCoefficient`. -/
theorem exists_matrixWithExterior_periodic_commutator_bound
    (I : Type*) [Fintype I] (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2)
    (n : ℕ) (M : ℝ) (q : Torus d → ℝ) (hq : IsSmoothPeriodic q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : I → I → E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (b i j)))
        (hs : ∀ i j ξ, SupportedInCenteredBox r (b i j ξ)) (H : ℝ)
        (hM : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + is.length) H)
        (u : I → Torus d → ℂ) (hu : ∀ i, IsSmoothPeriodic (u i)),
        let f : PiLp 2 (fun _ : I ↦ L²) :=
          WithLp.toLp 2 (fun i ↦ toL2 0 (ofSmooth 0 (u i) (hu i)))
        let df : PiLp 2 (fun _ : I ↦ L²) := WithLp.toLp 2 (fun i ↦ toL2 0
          (ofSmooth 0 (periodicCoordinateDerivList is (u i)) ((hu i).coordinateDerivList is)))
        let T := matrixWithExteriorOperator (matrixOperator (fun i j ↦
          torusL2Operator hd r (b i j) (hb i j) (hs i j) M
            (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _)))) q hq.1
        ∃ w : PiLp 2 (fun _ : I ↦ L²),
          (∀ i, HasPeriodicWeakDerivativeList is (T f i) (T df i + w i)) ∧
          ‖w‖ ≤ C * (‖WithLp.toLp 2 (fun i ↦ periodicSobolevNorm n (u i))‖ +
            max 1 H * ‖f‖) := by
  classical
  obtain ⟨C, hC, he⟩ := exists_matrixTorusL2Operator_periodic_commutator_bound I I hd r hr n M
  let Q := Exterior.commutatorConstant (F := ℂ) q hq (n + 1)
  have hQ : 0 ≤ Q := (Exterior.commutatorConstant_pos q hq (n + 1)).le
  refine ⟨C + (Fintype.card I : ℝ) * Q, by positivity, ?_⟩
  intro b hb hs H hM is hlen hH u hu
  dsimp only
  let f : PiLp 2 (fun _ : I ↦ L²) :=
    WithLp.toLp 2 (fun i ↦ toL2 0 (ofSmooth 0 (u i) (hu i)))
  let df : PiLp 2 (fun _ : I ↦ L²) := WithLp.toLp 2 (fun i ↦ toL2 0
    (ofSmooth 0 (periodicCoordinateDerivList is (u i)) ((hu i).coordinateDerivList is)))
  let T := matrixOperator (fun i j ↦ torusL2Operator hd r (b i j) (hb i j) (hs i j) M
    (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _)))
  obtain ⟨v, hv, hn⟩ := he b hb hs H hM is hlen hH u hu
    (fun i ↦ (hu i).1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  let e : I → L² := fun i ↦ Exterior.commutator q hq is (ofSmooth (is.length - 1) (u i) (hu i))
  let W : PiLp 2 (fun _ : I ↦ L²) := ∑ i, coordinateInjection i (e i)
  have hW (i : I) : W i = e i := by simp [W, coordinateInjection, Pi.single_apply]
  refine ⟨v + W, ?_, ?_⟩
  · intro i
    change HasPeriodicWeakDerivativeList is
      (matrixWithExteriorOperator T q hq.1 f i)
      (matrixWithExteriorOperator T q hq.1 df i + (v + W) i)
    rw [matrixWithExteriorOperator_apply, matrixWithExteriorOperator_apply, PiLp.add_apply, hW]
    have hvi : HasPeriodicWeakDerivativeList is (T f i) (T df i + v i) := hv i
    have hqi : HasPeriodicWeakDerivativeList is (Exterior.multiplication q hq.1 (f i))
        (Exterior.multiplication q hq.1 (df i) + e i) :=
      exterior_weakDerivativeList q hq is (u i) (hu i)
    convert weakDerivativeList_add is _ _ _ _ hvi hqi using 1
    abel
  · let N : PiLp 2 (fun _ : I ↦ ℝ) := WithLp.toLp 2 (fun i ↦ periodicSobolevNorm n (u i))
    have heach (i : I) : ‖e i‖ ≤ Q * ‖N‖ := by
      have hi : periodicSobolevNorm n (u i) ≤ ‖N‖ := by
        exact (le_abs_self _).trans (PiLp.norm_apply_le N i)
      apply (Exterior.norm_commutator_le q hq is (ofSmooth (is.length - 1) (u i) (hu i))).trans
      rw [hlen, Nat.add_sub_cancel]
      apply mul_le_mul_of_nonneg_left _ hQ
      rw [PeriodicSobolevSpace.norm_eq]
      simpa only [periodicSobolevNorm,
        periodicFourierCoeff_congr_ae (toL2_ofSmooth_ae n (u i) (hu i))] using hi
    have hWn : ‖W‖ ≤ (Fintype.card I : ℝ) * Q * ‖N‖ := by
      calc
        ‖W‖ ≤ ∑ i, ‖e i‖ := (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun i _ ↦ (coordinateInjection i).norm_map _ |>.le)
        _ ≤ ∑ _i : I, Q * ‖N‖ := Finset.sum_le_sum fun i _ ↦ heach i
        _ = _ := by simp [mul_assoc]
    calc
      ‖v + W‖ ≤ ‖v‖ + ‖W‖ := norm_add_le _ _
      _ ≤ C * (‖N‖ + max 1 H * ‖f‖) + (Fintype.card I : ℝ) * Q * ‖N‖ :=
        add_le_add hn hWn
      _ ≤ (C + (Fintype.card I : ℝ) * Q) * (‖N‖ + max 1 H * ‖f‖) := by
        have : 0 ≤ (Fintype.card I : ℝ) * Q * (max 1 H * ‖f‖) := by positivity
        nlinarith

end JanetCartan.Pseudodifferential.DifferentialChart
