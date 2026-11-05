module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PencilContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.Roots
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Stability
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Literal current and frozen incidence equations

The equations used in Step 3 of `app:ch_seed:prop:seed-actual-menu`.
The current equation evaluates the actual determinant differential at the
physical gradient of the supplied phase. The frozen determinant equation is
distinct from `FrozenMenu.incidence`, which uses the reciprocal normal.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ActualCarriers

/-- Vary the first parameter, fixing both spectator coordinates
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def incidenceParameter (z : Euclidean 3) (t : ℝ) : Euclidean 3 :=
  z + t • EuclideanSpace.single 0 1

/-- The spectators stay fixed during incidence continuation
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem incidenceParameter_spectators (z : Euclidean 3) (t : ℝ) :
    incidenceParameter z t 1 = z 1 ∧ incidenceParameter z t 2 = z 2 := by
  simp [incidenceParameter]

/-- Scalar root displacement equals the Euclidean displacement of the full
parameter vector, since the spectators are fixed
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem norm_incidenceParameter_sub (z : Euclidean 3) (s t : ℝ) :
    ‖incidenceParameter z s - incidenceParameter z t‖ = |s - t| := by
  simp only [incidenceParameter, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
    Real.norm_eq_abs]
  simp [EuclideanSpace.single, PiLp.norm_single]

/-- A parameter with zero spectators lies on the distinguished scalar line
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem eq_single_of_zero_spectators {z : Euclidean 3} (h₁ : z 1 = 0) (h₂ : z 2 = 0) :
    z = z 0 • EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [h₁, h₂]

/-- The literal equation `k · d_ξ p_F(x,d_x Θ(x,z))`, with only the first
patch parameter varying (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def currentIncidence {n : ℕ} (Q : Euclidean n → Fin n → MetricTensor n)
    (Θ : Euclidean n → Euclidean 3 → ℝ) (z : Euclidean 3)
    (p : (Euclidean n × Euclidean n) × ℝ) : ℝ :=
  fderiv ℝ (determinant (Q p.1.1))
    (gradient (fun x ↦ Θ x (incidenceParameter z p.2)) p.1.1) p.1.2

/-- The scalar derivative used by continuation is precisely the
first-parameter derivative of the literal incidence equation, with physical
point, covector and spectators held fixed
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem scalarDerivative_currentIncidence_eq {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n)
    (Θ : Euclidean n → Euclidean 3 → ℝ) (z : Euclidean 3)
    (p : (Euclidean n × Euclidean n) × ℝ)
    (hf : DifferentiableAt ℝ (currentIncidence Q Θ z) p)
    (hz : DifferentiableAt ℝ (fun w ↦ fderiv ℝ (determinant (Q p.1.1))
      (gradient (fun x ↦ Θ x w) p.1.1) p.1.2) (incidenceParameter z p.2)) :
    CharacteristicRoot.scalarDerivative (currentIncidence Q Θ z) p =
      fderiv ℝ (fun w ↦ fderiv ℝ (determinant (Q p.1.1))
        (gradient (fun x ↦ Θ x w) p.1.1) p.1.2)
        (incidenceParameter z p.2) (EuclideanSpace.single 0 1) := by
  have hline : HasDerivAt (incidenceParameter z) (EuclideanSpace.single 0 1) p.2 := by
    change HasDerivAt (fun t : ℝ ↦ z + t • EuclideanSpace.single 0 1) _ p.2
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id p.2).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).const_add z
  exact (CharacteristicRoot.hasDerivAt_scalarSlice hf).unique
    (hz.hasFDerivAt.comp_hasDerivAt p.2 hline)

/-- The literal frozen determinant incidence, before inserting the constant
physical variable (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def frozenDeterminantIncidence {n : ℕ} (P : FrozenMenu.Patch n) (z : Euclidean 3)
    (p : Euclidean n × ℝ) : ℝ :=
  fderiv ℝ (determinant (cubeStress n)) (P.toFun (incidenceParameter z p.2)) p.1

/-- The current incidence at the reference frame and reference phase gradient
is exactly the frozen determinant incidence
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem currentIncidence_eq_frozen {n : ℕ} (P : FrozenMenu.Patch n)
    (Θ : Euclidean n → Euclidean 3 → ℝ) (z : Euclidean 3)
    (p : (Euclidean n × Euclidean n) × ℝ)
    (hΘ : gradient (fun x ↦ Θ x (incidenceParameter z p.2)) p.1.1 =
      P.toFun (incidenceParameter z p.2)) :
    currentIncidence (fun _ ↦ cubeStress n) Θ z p =
      frozenDeterminantIncidence P z (p.1.2, p.2) := by
  simp only [currentIncidence, frozenDeterminantIncidence, hΘ]

/-- On the characteristic cube the frozen determinant incidence is the
explicit nonzero normal multiplier times `FrozenMenu.incidence`
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem frozenDeterminantIncidence_eq_mul {n : ℕ} {P : FrozenMenu.Patch n}
    {c C : ℝ} (hP : P.IsValid c C) (z : Euclidean 3) (p : Euclidean n × ℝ)
    (hp : incidenceParameter z p.2 ∈ FrozenMenu.parameterCube P.radius) :
    frozenDeterminantIncidence P z p =
      ((∏ i, P.toFun (incidenceParameter z p.2) i) * cubeCoefficient n *
        (∑ i, P.toFun (incidenceParameter z p.2) i)) *
      FrozenMenu.incidence p.1 (P.toFun (incidenceParameter z p.2)) := by
  have hdet : determinant (cubeStress n) = cubeDeterminant := funext determinant_cubeStress
  simpa only [frozenDeterminantIncidence, hdet,
    FrozenMenu.incidence, FrozenMenu.normal] using
    CubeCarrier.determinant_differential (hP.2.2.2.2.1 _ hp).1
      (hP.2.2.2.2.1 _ hp).2.1 p.1

end JanetCartan.ActualCarriers
