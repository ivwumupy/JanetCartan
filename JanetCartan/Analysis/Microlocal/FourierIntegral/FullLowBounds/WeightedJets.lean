module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.JointJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.OrderedJets

/-!
# The Sobolev weighted jets supply the full source-symbol budget

The actual ordered derivatives in `SobolevBounds.IntegerBounds` are identified
with the source/output/covector derivatives used by the source Fourier series.
This closes the low-reserve input for every complete modified amplitude in
`app:ch_regular_base:eq:graph-derivative-transfer`, with no derivative loss.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion AmplitudeBound FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

private def parameterCoordinate : Fin n ⊕ Fin n → Coordinate n
  | .inl i => (.left, i)
  | .inr i => (.covector, i)

private theorem smooth_jet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Field n F} (hA : ContDiff ℝ ∞ (uncurry A)) (w : List (Coordinate n)) :
    ContDiff ℝ ∞ (uncurry (jet w A)) :=
  contDiff_iff_contDiffAt.mpr fun _p ↦ contDiffAt_jet hA.contDiffAt w

private theorem scalarParameterJet_eq {A : Field n ℂ}
    (hA : ContDiff ℝ ∞ (uncurry A)) (is : List (Fin n ⊕ Fin n)) (x y η : E) :
    scalarCoefficientJet is (fun p ↦ A p.1 y p.2) (x, η) =
      jet (is.map parameterCoordinate) A x y η := by
  induction is generalizing x y η with
  | nil => rfl
  | cons i is ih =>
    simp only [scalarCoefficientJet, List.map_cons, jet_cons]
    have he : (fun p : E × E ↦ scalarCoefficientJet is (fun q ↦ A q.1 y q.2) p) =
        fun p ↦ jet (is.map parameterCoordinate) A p.1 y p.2 :=
      funext fun p ↦ ih p.1 y p.2
    change scalarCoefficientJet is (fun q ↦ A q.1 y q.2) = _ at he
    rw [he]
    have hd : Differentiable ℝ (fun p : E × E ↦
        jet (is.map parameterCoordinate) A p.1 y p.2) :=
      ((smooth_jet hA (is.map parameterCoordinate)).comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)).differentiable (by simp)
    cases i with
    | inl i =>
      have hh := (hd (x, η)).hasFDerivAt.comp (f := fun z : E ↦ (z, η)) x
        ((hasFDerivAt_id x).prodMk (hasFDerivAt_const η x))
      exact (congrArg (fun D : E →L[ℝ] ℂ ↦ D (EuclideanSpace.single i 1)) hh.fderiv).symm
    | inr i =>
      have hh := (hd (x, η)).hasFDerivAt.comp (f := fun z : E ↦ (x, z)) η
        ((hasFDerivAt_const x η).prodMk (hasFDerivAt_id η))
      exact (congrArg (fun D : E →L[ℝ] ℂ ↦ D (EuclideanSpace.single i 1)) hh.fderiv).symm

private theorem jet_entry {A : FullAmplitude n r}
    (hA : ContDiff ℝ ∞ (uncurry A)) (w : List (Coordinate n)) (i j : Fin r) :
    jet w (fun x y η ↦ A x y η i j) = fun x y η ↦ jet w A x y η i j := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [jet_cons, ih]
    funext x y η
    have hd := sliceDifferentiableAt_of_contDiffAt
      (smooth_jet hA w).contDiffAt (p := ((x,y),η)) c.1
    have hh := (matrixEntryEvaluation i j).hasFDerivAt.comp
      (anchor c.1 x y η) hd.hasFDerivAt
    have he := congrArg (fun D : E →L[ℝ] ℂ ↦ D (EuclideanSpace.single c.2 1)) hh.fderiv
    cases c with
    | mk s a => cases s <;> exact he

private theorem jet_append' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u v : List (Coordinate n)) (A : Field n F) : jet (u ++ v) A = jet u (jet v A) := by
  induction u with
  | nil => rfl
  | cons c u ih => simp only [List.cons_append, jet_cons, ih]

private theorem sourceJet_eq (js : List (Fin n)) (A : Field n ℂ) (x y η : E) :
    euclideanCoordinateDerivList js (fun z ↦ A x z η) y =
      jet (js.map (fun j ↦ (Slot.right, j))) A x y η := by
  induction js generalizing y with
  | nil => rfl
  | cons j js ih =>
    simp only [euclideanCoordinateDerivList, List.map_cons, jet_cons]
    rw [funext ih]
    rfl

/-- The mixed source and output/covector words are the actual joint ordered
jets used in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
private theorem fullSourceSymbolJet_eq_jointJet {A : FullAmplitude n r}
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (is : List (Fin n ⊕ Fin n)) (js : List (Fin n)) (x y η : E) :
    matrixAmplitudeCoordinateDerivList js (fun z ↦ fullAmplitudeParameterJet is A x z η) y =
      jet (js.map (fun j ↦ (Slot.right, j)) ++ is.map parameterCoordinate) A x y η := by
  have ha : ContDiff ℝ ∞ (uncurry A) :=
    hA.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  ext i j
  change euclideanCoordinateDerivList js
    (fun z ↦ scalarCoefficientJet is (fun p ↦ A p.1 z p.2 i j) (x,η)) y = _
  have hh : ContDiff ℝ ∞ (uncurry (fun x y η ↦ A x y η i j)) :=
    (matrixEntryEvaluation i j).contDiff.comp ha
  rw [show (fun z ↦ scalarCoefficientJet is (fun p ↦ A p.1 z p.2 i j) (x,η)) =
    fun z ↦ jet (is.map parameterCoordinate) (fun x y η ↦ A x y η i j) x z η from
      funext fun z ↦ scalarParameterJet_eq hh is x z η]
  rw [sourceJet_eq, ← jet_append', jet_entry ha]

private theorem frequencyOrder_source_parameter (is : List (Fin n ⊕ Fin n)) (js : List (Fin n)) :
    frequencyOrder (js.map (fun j ↦ (Slot.right, j)) ++ is.map parameterCoordinate) =
      (is.filter Sum.isRight).length := by
  simp only [frequencyOrder, List.countP_append]
  have hjs : (js.map (fun j ↦ (Slot.right, j))).countP
      (fun c ↦ c.1 == Slot.covector) = 0 := by simp
  rw [hjs, zero_add]
  induction is with
  | nil => rfl
  | cons i is ih => cases i <;> simp [parameterCoordinate, ih, List.filter_cons, Sum.isRight]

/-- The weighted joint-jet premise of `SobolevBounds.IntegerBounds` supplies
exactly the original source-symbol budget, at the same derivative order.
The factor permits any bracket with `1 + ‖η‖ ≤ c * ρ η`. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem hasFullSourceSymbolBound_of_weighted_jets {A : FullAmplitude n r}
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (N : ℕ) (ρ : E → ℝ) {c B : ℝ} (hc : 1 ≤ c) (hB : 0 ≤ B)
    (hweight : ∀ η, 1 + ‖η‖ ≤ c * ρ η)
    (hb : ∀ w : List (Coordinate n), w.length ≤ N → ∀ x y η,
      (ρ η) ^ frequencyOrder w * ‖jet w A x y η‖ ≤ B) :
    HasFullSourceSymbolBound A N (c ^ N * B) := by
  intro is js hij x y η
  rw [fullSourceSymbolJet_eq_jointJet hA]
  let w := js.map (fun j ↦ (Slot.right, j)) ++ is.map parameterCoordinate
  have hw : w.length ≤ N := by simp only [w, List.length_append, List.length_map]; omega
  have hf : frequencyOrder w = (is.filter Sum.isRight).length :=
    frequencyOrder_source_parameter is js
  have hfN : (is.filter Sum.isRight).length ≤ N :=
    (List.length_filter_le _ _).trans (by omega)
  have hh := hb w hw x y η
  rw [hf] at hh
  calc
    _ ≤ (c * ρ η) ^ (is.filter Sum.isRight).length * ‖jet w A x y η‖ := by
      unfold coefficientCovectorWeight
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (hweight η) _) (norm_nonneg _)
    _ = c ^ (is.filter Sum.isRight).length *
        ((ρ η) ^ (is.filter Sum.isRight).length * ‖jet w A x y η‖) := by rw [mul_pow]; ring
    _ ≤ c ^ (is.filter Sum.isRight).length * B :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg (zero_le_one.trans hc) _)
    _ ≤ c ^ N * B := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc hfN) hB
end JanetCartan.FourierIntegral.FullLowBounds
