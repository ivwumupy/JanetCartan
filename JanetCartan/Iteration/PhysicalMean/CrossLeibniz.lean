module

public import JanetCartan.Iteration.PhysicalMean.QuadraticRow
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Matrix
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.NormComparison.Coordinates

/-!
# Exact differentiated Hermitian source terms

The physical derivative word is distributed among the actual measurement
coefficient and the two actual full individual fields. The finite branch
sum counts only derivative assignments, not samples or bands. Symmetry
allows the lower-order field to be placed in the amplitude while the
higher-order field remains inside the aggregate row
(`new:eq:Q-derivative-term`, `app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean BallExtension

/-- The three physical derivative subwords in a genuine Leibniz term. -/
def crossDerivativeBranches {n : ℕ} : List (Fin n) →
    List (List (Fin n) × List (Fin n) × List (Fin n))
  | [] => [([], [], [])]
  | i :: ds => (crossDerivativeBranches ds).flatMap fun q ↦
      [(i :: q.1, q.2.1, q.2.2), (q.1, i :: q.2.1, q.2.2), (q.1, q.2.1, i :: q.2.2)]

/-- Every exact Leibniz branch spends precisely the original physical order. -/
theorem crossDerivativeBranches_grade {n : ℕ} (ds : List (Fin n))
    (q : List (Fin n) × List (Fin n) × List (Fin n)) (hq : q ∈ crossDerivativeBranches ds) :
    q.1.length + q.2.1.length + q.2.2.length = ds.length := by
  induction ds generalizing q with
  | nil =>
    have hq' : q = ([], [], []) := by simpa only [crossDerivativeBranches, List.mem_singleton] using hq
    subst q
    rfl
  | cons i ds ih =>
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
    have hg := ih p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [List.length_cons] <;> omega

private theorem smooth_cartesianWord {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean n → F} (hf : ContDiff ℝ ∞ f) (ds : List (Fin n)) :
    ContDiff ℝ ∞ (cartesianCoordinateDerivList ds f) :=
  contDiffOn_univ.mp (contDiffOn_cartesianCoordinateDerivList isOpen_univ hf.contDiffOn ds)

private theorem smooth_measuredHermitian {n N : ℕ}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (U V : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x ↦ C x (hermitianContinuousBilinear (U x) (V x))) :=
  hC.clm_apply (((hermitianContinuousBilinear (m := Fin N) (n := Fin n)).contDiff.comp hU).clm_apply hV)

private theorem measuredHermitian_oneDeriv {n N : ℕ}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (U V : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (i : Fin n) (x : Euclidean n) :
    fderiv ℝ (fun y ↦ C y (hermitianContinuousBilinear (U y) (V y))) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      cartesianCoordinateDerivList [i] C x (hermitianContinuousBilinear (U x) (V x)) +
      C x (hermitianContinuousBilinear (cartesianCoordinateDerivList [i] U x) (V x)) +
      C x (hermitianContinuousBilinear (U x) (cartesianCoordinateDerivList [i] V x)) := by
  let HB := hermitianContinuousBilinear (m := Fin N) (n := Fin n)
  have hU' := (hU.differentiable (by simp) x).hasFDerivAt
  have hV' := (hV.differentiable (by simp) x).hasFDerivAt
  have hh := ((hC.differentiable (by simp) x).hasFDerivAt.clm_apply
    (HB.hasFDerivAt_of_bilinear hU' hV')).fderiv
  rw [hh]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply, map_add, cartesianCoordinateDerivList, HB]
  abel

/-- A literal physical derivative term before any operator norm is taken.
The two full fields are still distinct; no larger individual-field norm
has replaced the high factor. -/
def measuredHermitianDerivativeTerm {n N : ℕ}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (U V : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (q : List (Fin n) × List (Fin n) × List (Fin n)) (x : Euclidean n) : Euclidean n :=
  cartesianCoordinateDerivList q.1 C x
    (hermitianContinuousBilinear (cartesianCoordinateDerivList q.2.1 U x)
      (cartesianCoordinateDerivList q.2.2 V x))

private theorem smooth_measuredHermitianDerivativeTerm {n N : ℕ}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (U V : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (q : List (Fin n) × List (Fin n) × List (Fin n)) :
    ContDiff ℝ ∞ (measuredHermitianDerivativeTerm C U V q) :=
  smooth_measuredHermitian _ _ _ (smooth_cartesianWord hC q.1)
    (smooth_cartesianWord hU q.2.1) (smooth_cartesianWord hV q.2.2)

private theorem fderiv_listSum_apply {n : ℕ} {F ι : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (l : List ι)
    (f : ι → Euclidean n → F) (hf : ∀ i ∈ l, ContDiff ℝ ∞ (f i))
    (x v : Euclidean n) :
    fderiv ℝ (fun y ↦ (l.map (fun i ↦ f i y)).sum) x v =
      (l.map (fun i ↦ fderiv ℝ (f i) x v)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi := hf i (by simp)
    have hl : ∀ j ∈ l, ContDiff ℝ ∞ (f j) := fun j hj ↦ hf j (by simp [hj])
    have hs : ContDiff ℝ ∞ (fun y ↦ (l.map (fun j ↦ f j y)).sum) := by
      clear ih hf hi
      induction l with
      | nil => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Euclidean n ↦ (0 : F)))
      | cons j l ih =>
        simpa using (hl j (by simp)).add (ih (fun k hk ↦ hl k (by simp [hk])))
    simp only [List.map_cons, List.sum_cons]
    rw [fderiv_fun_add (hi.differentiable (by simp) x) (hs.differentiable (by simp) x),
      add_apply, ih hl]

private theorem sum_flatMap {ι F : Type*} [AddMonoid F] (l : List ι) (f : ι → List F) :
    (l.flatMap f).sum = (l.map (fun i ↦ (f i).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- Exact three-factor Leibniz expansion of the actual measured Hermitian
source. Every summand carries the original derivative subwords, so the
higher factor can subsequently be expanded INSIDE the aggregate row. -/
theorem measuredHermitian_coordinate_eq_branchSum {n N : ℕ}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (U V : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (ds : List (Fin n)) (x : Euclidean n) :
    cartesianCoordinateDerivList ds (fun y ↦ C y (hermitianContinuousBilinear (U y) (V y))) x =
      ((crossDerivativeBranches ds).map (fun q ↦ measuredHermitianDerivativeTerm C U V q x)).sum := by
  induction ds generalizing x with
  | nil => simp [crossDerivativeBranches, measuredHermitianDerivativeTerm, cartesianCoordinateDerivList]
  | cons i ds ih =>
    rw [cartesianCoordinateDerivList, show cartesianCoordinateDerivList ds
        (fun y ↦ C y (hermitianContinuousBilinear (U y) (V y))) =
        (fun y ↦ ((crossDerivativeBranches ds).map (fun q ↦ measuredHermitianDerivativeTerm C U V q y)).sum)
      from funext ih]
    dsimp only
    rw [fderiv_listSum_apply _ _ (fun q _ ↦ smooth_measuredHermitianDerivativeTerm C U V hC hU hV q)]
    simp only [crossDerivativeBranches, List.map_flatMap, sum_flatMap]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    have heq : measuredHermitianDerivativeTerm C U V q =
        (fun y ↦ cartesianCoordinateDerivList q.1 C y
          (hermitianContinuousBilinear (cartesianCoordinateDerivList q.2.1 U y)
            (cartesianCoordinateDerivList q.2.2 V y))) := rfl
    rw [heq]
    dsimp only [measuredHermitianDerivativeTerm]
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      cartesianCoordinateDerivList, add_assoc] using
      measuredHermitian_oneDeriv (cartesianCoordinateDerivList q.1 C)
        (cartesianCoordinateDerivList q.2.1 U) (cartesianCoordinateDerivList q.2.2 V)
        (smooth_cartesianWord hC q.1) (smooth_cartesianWord hU q.2.1) (smooth_cartesianWord hV q.2.2) i x

/-- Exact Hermitian symmetry reorients each differentiated term. Therefore
only the smaller derivative word is placed in the modified amplitude. -/
theorem measuredHermitianDerivativeTerm_swap {n N : ℕ}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (U V : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (c r t : List (Fin n)) (x : Euclidean n) :
    measuredHermitianDerivativeTerm C U V (c,r,t) x =
      measuredHermitianDerivativeTerm C V U (c,t,r) x := by
  simp only [measuredHermitianDerivativeTerm, hermitianContinuousBilinear_apply,
    mixedHermitianTensor_comm]

/-- The smaller differentiated field uses at most half the total order,
exactly as required by the already checked revised exponent inequality. -/
theorem crossDerivativeBranches_smaller_grade {n : ℕ} (ds : List (Fin n))
    (q : List (Fin n) × List (Fin n) × List (Fin n)) (hq : q ∈ crossDerivativeBranches ds) :
    q.1.length + max q.2.1.length q.2.2.length + min q.2.1.length q.2.2.length = ds.length ∧
      2 * min q.2.1.length q.2.2.length ≤ ds.length := by
  have h := crossDerivativeBranches_grade ds q hq
  omega

/-- Cartesian words commute with a finite smooth physical sum. In the full
quadratic source this gathers each sample's refined shells BEFORE Hermitian
pairing (`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem cartesianWord_finsetSum {n : ℕ} {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ι → Euclidean n → F) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (ds : List (Fin n)) :
    cartesianCoordinateDerivList ds (fun x ↦ ∑ i, f i x) =
      fun x ↦ ∑ i, cartesianCoordinateDerivList ds (f i) x := by
  induction ds with
  | nil => rfl
  | cons j ds ih =>
    funext x
    simp only [cartesianCoordinateDerivList, ih]
    rw [fderiv_fun_sum (fun i _ ↦ (smooth_cartesianWord (hf i) ds).differentiable (by simp) x)]
    simp only [sum_apply]

private theorem cartesianWord_const_smul {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Euclidean n → F) (hf : ContDiff ℝ ∞ f) (c : ℝ) (ds : List (Fin n)) :
    cartesianCoordinateDerivList ds (fun x ↦ c • f x) =
      fun x ↦ c • cartesianCoordinateDerivList ds f x := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    funext x
    simp only [cartesianCoordinateDerivList, ih]
    rw [fderiv_fun_const_smul ((smooth_cartesianWord hf ds).differentiable (by simp) x) c]
    simp only [smul_apply]

private theorem weighted_sum_list_sum {ι κ F : Type*} [Fintype ι]
    [AddCommGroup F] [Module ℝ F] (μ : ι → ℝ) (l : List κ) (f : κ → ι → F) :
    (∑ i, μ i • (l.map (fun q ↦ f q i)).sum) =
      (l.map (fun q ↦ ∑ i, μ i • f q i)).sum := by
  induction l with
  | nil => simp
  | cons q l ih => simp [smul_add, Finset.sum_add_distrib, ih]

/-- Exact differentiated source identity with the SAME original weighted
sample sum still inside every Leibniz branch. There is NO samplewise norm
estimate or division by a weight. This is the aggregate form consumed by
the full high-factor matrix branch expansion and modified cross-row bound. -/
theorem weightedHermitian_coordinate_eq_branchSum {n N : ℕ} {ι : Type*} [Fintype ι]
    (μ : ι → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (U V : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (ds : List (Fin n)) (x : Euclidean n) :
    cartesianCoordinateDerivList ds
      (fun y ↦ C y (∑ i, μ i • hermitianContinuousBilinear (U i y) (V i y))) x =
      ((crossDerivativeBranches ds).map
        (fun q ↦ ∑ i, μ i • measuredHermitianDerivativeTerm C (U i) (V i) q x)).sum := by
  have he : (fun y ↦ C y (∑ i, μ i • hermitianContinuousBilinear (U i y) (V i y))) =
      (fun y ↦ ∑ i, μ i • C y (hermitianContinuousBilinear (U i y) (V i y))) := by
    funext y
    simp only [map_sum, map_smul]
  rw [he, cartesianWord_finsetSum _ (fun i ↦
    (smooth_measuredHermitian C (U i) (V i) hC (hU i) (hV i)).const_smul (μ i)) ds]
  simp only [cartesianWord_const_smul _ (smooth_measuredHermitian C _ _ hC (hU _) (hV _)),
    measuredHermitian_coordinate_eq_branchSum C _ _ hC (hU _) (hV _)]
  exact weighted_sum_list_sum μ (crossDerivativeBranches ds)
    (fun q i ↦ measuredHermitianDerivativeTerm C (U i) (V i) q x)

end JanetCartan.PhysicalMean
