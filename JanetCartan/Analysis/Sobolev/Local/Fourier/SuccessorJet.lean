module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.FirstJet
public import JanetCartan.Analysis.Sobolev.Local.Scale.WeakJet
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Assembling higher weak jets from jets of coordinate derivatives

The induction for the natural-order Fourier comparison in `app:not:fourier`
adjoins the original function to genuine jets of its first coordinate
derivatives. A coordinate is appended at the last multilinear slot, so that
the weak derivative in the first slot commutes with this bounded linear
operation. No symmetry or smooth representative is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function Filter

namespace JanetCartan.Mollification

variable {n : ℕ} {F I : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Finite sums preserve whole-space weak derivative identities, for the
coordinate reconstruction in `app:not:fourier`. -/
theorem HasWeakFDerivOn.sum_univ (S : Finset I)
    {f : I → E → F} {D : I → E → E →L[ℝ] F}
    (h : ∀ i ∈ S, HasWeakFDerivOn volume (f i) (D i) univ) :
    HasWeakFDerivOn volume (fun x ↦ ∑ i ∈ S, f i x) (fun x ↦ ∑ i ∈ S, D i x) univ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    convert hasWeakFDerivOn_of_contDiff volume
      (contDiff_const : ContDiff ℝ 1 (fun _ : E ↦ (0 : F))) univ using 1 <;> simp; rfl
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self _ _)).add_univ
        (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

end JanetCartan.Mollification

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Append one real coordinate to a multilinear tensor. The consuming
construction is the successor weak jet for `app:not:fourier`. -/
def appendCoordinate (i : Fin n) (j : ℕ) : (E [×j]→L[ℝ] F) →L[ℝ] (E [×(j + 1)]→L[ℝ] F) :=
  ((continuousMultilinearCurryRightEquiv' ℝ j E F).symm
    |>.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ E) F
        (E →L[ℝ] F)) (ContinuousLinearMap.smulRightL ℝ E F
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)))

/-- Evaluation of the appended tensor, for the weak-jet induction in
`app:not:fourier`. -/
theorem appendCoordinate_apply (i : Fin n) (j : ℕ) (T : E [×j]→L[ℝ] F)
    (z : Fin (j + 1) → E) :
    appendCoordinate i j T z = z (Fin.last j) i • T (Fin.init z) := rfl

set_option maxHeartbeats 800000 in
/-- Appending a unit real coordinate does not increase tensor operator norms
(`app:not:fourier`). -/
theorem norm_appendCoordinate_le_one (i : Fin n) (j : ℕ) :
    ‖appendCoordinate (F := F) i j‖ ≤ 1 := by
  let L := ContinuousLinearMap.smulRightL ℝ E F
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).smulRight z‖ ≤ 1 * ‖z‖
    rw [ContinuousLinearMap.norm_smulRight_apply, one_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa using PiLp.norm_apply_le x i
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  change ‖(continuousMultilinearCurryRightEquiv' ℝ j E F).symm
    (L.compContinuousMultilinearMap T)‖ ≤ 1 * ‖T‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  exact (L.norm_compContinuousMultilinearMap_le T).trans
    (mul_le_of_le_one_left (norm_nonneg T) hL)

/-- Adjoin a value to the jets of all first coordinate derivatives, for
the natural-order comparison in `app:not:fourier`. -/
def successorWeakJet (f : E → F) (K : Fin n → (j : ℕ) → E → E [×j]→L[ℝ] F) :
    (j : ℕ) → E → E [×j]→L[ℝ] F
  | 0 => iteratedFDeriv ℝ 0 f
  | j + 1 => fun x ↦ ∑ i, appendCoordinate i j (K i j x)

variable [CompleteSpace F]

/-- Genuine jets of actual first derivatives assemble to the next-order
genuine weak jet, for the natural-order norm comparison in `app:not:fourier`. -/
theorem hasWeakJetOn_successorWeakJet {s : ℕ} {f : E → F} {v : Fin n → E → F}
    {K : Fin n → (j : ℕ) → E → E [×j]→L[ℝ] F}
    (hD : Mollification.HasWeakFDerivOn volume f (coordinateFDeriv v) univ)
    (hK : ∀ i, Mollification.HasWeakJetOn volume (v i) (K i) univ s) :
    Mollification.HasWeakJetOn volume f (successorWeakJet f K) univ (s + 1) := by
  refine ⟨rfl, fun j hj ↦ ?_⟩
  cases j with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap
    convert hD.comp_clm_univ L using 1
    · rfl
    · ext x z w
      simp [successorWeakJet, appendCoordinate_apply, (hK _).1,
        coordinateFDeriv_apply, L, iteratedFDeriv_zero_apply]
  | succ j =>
    have h (i : Fin n) := ((hK i).2 j (by omega)).comp_clm_univ (appendCoordinate i j)
    convert Mollification.HasWeakFDerivOn.sum_univ Finset.univ (fun i _ ↦ h i) using 1
    · rfl
    · ext x z w
      simp only [successorWeakJet, comp_apply, sum_apply,
        ContinuousLinearMap.comp_apply,
        continuousMultilinearCurryLeftEquiv_apply, appendCoordinate_apply,
        Fin.cons_last]
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      funext a
      refine Fin.cases ?_ (fun a ↦ ?_) a <;> rfl

set_option maxHeartbeats 800000 in
omit [CompleteSpace F] in
/-- Every assembled successor-jet component is genuinely L², for
`app:not:fourier`. -/
theorem memLp_successorWeakJet {s : ℕ} {f : E → F}
    {K : Fin n → (j : ℕ) → E → E [×j]→L[ℝ] F}
    (hf : MemLp f 2 volume) (hK : ∀ i j, j ≤ s → MemLp (K i j) 2 volume)
    (j : ℕ) (hj : j ≤ s + 1) : MemLp (successorWeakJet f K j) 2 volume := by
  cases j with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hf
  | succ j =>
    exact memLp_finsetSum Finset.univ
      (f := fun i x ↦ appendCoordinate (F := F) i j (K i j x))
      (fun i _ ↦ (appendCoordinate (F := F) i j).comp_memLp' (hK i j (by omega)))

set_option maxHeartbeats 800000 in
omit [CompleteSpace F] in
/-- The entire successor jet is controlled by the value plus the sum of
the lower-order derivative jets, using actual Fréchet operator norms
(`app:not:fourier`). -/
theorem successorWeakJet_normSum_le {s : ℕ} {f : E → F}
    {K : Fin n → (j : ℕ) → E → E [×j]→L[ℝ] F}
    (hf : MemLp f 2 volume) (hK : ∀ i j, j ≤ s → MemLp (K i j) 2 volume) :
    (∑ j ∈ Finset.range (s + 2), (eLpNorm (successorWeakJet f K j) 2 volume).toReal) ≤
      (eLpNorm f 2 volume).toReal +
        ∑ i, ∑ j ∈ Finset.range (s + 1), (eLpNorm (K i j) 2 volume).toReal := by
  have hzero : eLpNorm (successorWeakJet f K 0) 2 volume = eLpNorm f 2 volume := by
    apply eLpNorm_congr_norm_ae
      (memLp_successorWeakJet hf hK 0 (by omega)).aestronglyMeasurable hf.aestronglyMeasurable
    exact Eventually.of_forall fun x ↦ norm_iteratedFDeriv_zero
  have hcomp (i : Fin n) (j : ℕ) (hj : j ≤ s) :
      (eLpNorm (fun x ↦ appendCoordinate i j (K i j x)) 2 volume).toReal ≤
        (eLpNorm (K i j) 2 volume).toReal := by
    let L := appendCoordinate (F := F) i j
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (L.comp_memLp' (hK i j hj)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ L.le_opNorm (K i j x)) 2
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hK i j hj).eLpNorm_ne_top) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at ht
    exact ht.trans (mul_le_of_le_one_left ENNReal.toReal_nonneg
      (norm_appendCoordinate_le_one i j))
  have hsucc (j : ℕ) (hj : j ≤ s) :
      (eLpNorm (successorWeakJet f K (j + 1)) 2 volume).toReal ≤
        ∑ i, (eLpNorm (K i j) 2 volume).toReal := by
    have hsum := lpNorm_sum_le (p := 2) (μ := (volume : Measure E))
      (s := Finset.univ) (f := fun i x ↦ appendCoordinate (F := F) i j (K i j x))
      (fun i _ ↦ (appendCoordinate (F := F) i j).comp_memLp' (hK i j hj)) (by norm_num)
    have heq : (∑ i, fun x ↦ appendCoordinate i j (K i j x)) =
        successorWeakJet f K (j + 1) := by funext x; simp [successorWeakJet]
    rw [heq] at hsum
    exact hsum.trans (Finset.sum_le_sum fun i _ ↦ hcomp i j hj)
  rw [Finset.sum_range_succ', hzero, add_comm]
  refine add_le_add (le_refl _) ?_
  calc
    _ ≤ ∑ j ∈ Finset.range (s + 1), ∑ i, (eLpNorm (K i j) 2 volume).toReal :=
      Finset.sum_le_sum fun j hj ↦ hsucc j (by simpa using Finset.mem_range.mp hj)
    _ = _ := Finset.sum_comm

end JanetCartan.LocalSobolev
