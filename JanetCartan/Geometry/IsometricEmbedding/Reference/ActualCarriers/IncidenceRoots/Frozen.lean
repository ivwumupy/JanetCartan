module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Basic

/-!
# Simple frozen determinant incidence roots

Step 3 of `app:ch_seed:prop:seed-actual-menu`: transfer transversality
from the published frozen incidence sections to the literal determinant.
Differentiating the normal multiplier contributes zero at incidence.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

open FrozenMenu CharacteristicRoot

/-- Smoothness of the literal frozen determinant incidence on the interior
of the original cube (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem contDiffAt_frozenDeterminantIncidence {n : ℕ} {P : Patch n} {c C : ℝ}
    (hP : P.IsValid c C) (z : Euclidean 3) (p : Euclidean n × ℝ)
    (hp : incidenceParameter z p.2 ∈ parameterCube P.radius) :
    ContDiffAt ℝ ∞ (frozenDeterminantIncidence P z) p := by
  have hline : ContDiff ℝ ∞ (fun q : Euclidean n × ℝ ↦ incidenceParameter z q.2) :=
    contDiff_const.add (contDiff_snd.smul contDiff_const)
  have hpatch := (hP.2.2.2.1.contDiffAt ((isOpen_parameterInterior _).mem_nhds
    (parameterCube_subset_doubledInterior hP.1 hp))).comp p hline.contDiffAt
  exact (((contDiff_fderiv_determinant (n := n)).contDiffAt).comp p
    (contDiffAt_const.prodMk hpatch)).clm_apply contDiffAt_fst

/-- A frozen reciprocal-normal root is a simple root of the literal
determinant equation. No determinant transversality is assumed
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem frozenDeterminantIncidence_simple {n : ℕ} {P : Patch n} {c C : ℝ}
    (hP : P.IsValid c C) {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hzero : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    frozenDeterminantIncidence P z (k, 0) = 0 ∧
      scalarDerivative (frozenDeterminantIncidence P z) (k, 0) ≠ 0 := by
  have hzC : z ∈ parameterCube P.radius := fun i ↦ (hz i).le
  have hline0 : incidenceParameter z 0 = z := by simp [incidenceParameter]
  have h0 : incidenceParameter z (0 : ℝ) ∈ parameterCube P.radius := by
    simpa only [hline0] using hzC
  constructor
  · rw [frozenDeterminantIncidence_eq_mul hP z (k, 0) h0, hline0, hzero, mul_zero]
  let m : ℝ → ℝ := fun t ↦
    (∏ i, P.toFun (incidenceParameter z t) i) * cubeCoefficient n *
      (∑ i, P.toFun (incidenceParameter z t) i)
  let I : ℝ → ℝ := fun t ↦ incidence k (P.toFun (incidenceParameter z t))
  have hline : HasDerivAt (incidenceParameter z) (EuclideanSpace.single 0 1) 0 := by
    change HasDerivAt (fun t : ℝ ↦ z + t • EuclideanSpace.single 0 1) _ 0
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).const_add z
  have hpatch : ContDiffAt ℝ ∞ P.toFun z :=
    hP.2.2.2.1.contDiffAt ((isOpen_parameterInterior _).mem_nhds
      (parameterCube_subset_doubledInterior hP.1 hzC))
  have hcoord (i : Fin n) : DifferentiableAt ℝ
      (fun t ↦ P.toFun (incidenceParameter z t) i) 0 := by
    have hp : DifferentiableAt ℝ P.toFun (incidenceParameter z 0) := by
      simpa only [hline0] using hpatch.differentiableAt (by simp)
    exact ((contDiff_piLp_apply 2 (𝕜 := ℝ) (i := i) (n := ∞)).differentiable (by simp) _).comp 0
      (hp.comp 0 hline.differentiableAt)
  have hm : DifferentiableAt ℝ m 0 := by
    exact (((DifferentiableAt.fun_finsetProd (fun i _ ↦ hcoord i)).mul_const _).mul
      (DifferentiableAt.fun_sum (fun i _ ↦ hcoord i)))
  have hinc : DifferentiableAt ℝ (fun w ↦ incidence k (P.toFun w)) z := by
    exact ((Patch.contDiffAt_joint_incidence hP k hzC).comp z
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hI : HasDerivAt I
      (fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)) 0 := by
    have hi : HasFDerivAt (fun w ↦ incidence k (P.toFun w))
        (fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z) (incidenceParameter z 0) := by
      simpa only [hline0] using hinc.hasFDerivAt
    exact hi.comp_hasDerivAt 0 hline
  have heq : (fun t ↦ frozenDeterminantIncidence P z (k, t)) =ᶠ[𝓝 0]
      (fun t ↦ m t * I t) := by
    have hev : ∀ᶠ t in 𝓝 0, incidenceParameter z t ∈ parameterInterior P.radius := by
      apply hline.continuousAt.preimage_mem_nhds
      simpa only [hline0] using (isOpen_parameterInterior _).mem_nhds hz
    filter_upwards [hev] with t ht
    exact frozenDeterminantIncidence_eq_mul hP z (k, t) (fun i ↦ (ht i).le)
  have hder := (hm.hasDerivAt.mul hI).congr_of_eventuallyEq heq
  have hscalar := hasDerivAt_scalarSlice
    ((contDiffAt_frozenDeterminantIncidence hP z (k, 0) h0).differentiableAt (by simp))
  rw [hscalar.unique hder]
  have hI0 : I 0 = 0 := by simpa only [I, hline0] using hzero
  rw [hI0, mul_zero, zero_add]
  exact mul_ne_zero (by
    simpa only [m, hline0] using CubeCarrier.determinant_normal_multiplier_ne_zero
      (hP.2.2.2.2.1 z hzC).1 (hP.2.2.2.2.1 z hzC).2.1) hd

/-- Construct a buffered fixed cylinder, endpoint margins and a transverse
gap from one frozen incidence root. All choices precede the actual frame,
phase, higher norms and accuracy (`app:ch_seed:prop:seed-actual-menu`, Step 3).
The entire closed scalar interval stays inside the original parameter cube. -/
theorem exists_frozen_incidence_cylinder {n : ℕ} {P : Patch n} {c₀ C₀ : ℝ}
    (hP : P.IsValid c₀ C₀) {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hzero : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    ∃ r a c e : ℝ, 0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < e ∧
      (∀ t ∈ Icc (-a) a, incidenceParameter z t ∈ parameterInterior P.radius) ∧
      (∀ q ∈ Metric.closedBall k (2 * r), ∀ t ∈ Icc (-a) a,
        2 * c ≤ |scalarDerivative (frozenDeterminantIncidence P z) (q, t)|) ∧
      (∀ q ∈ Metric.closedBall k (2 * r),
        (frozenDeterminantIncidence P z (q, -a) ≤ -e ∧
          e ≤ frozenDeterminantIncidence P z (q, a)) ∨
        (frozenDeterminantIncidence P z (q, a) ≤ -e ∧
          e ≤ frozenDeterminantIncidence P z (q, -a))) := by
  let D : Set (Euclidean n × ℝ) :=
    {p | incidenceParameter z p.2 ∈ parameterInterior P.radius}
  have hD : IsOpen D := (isOpen_parameterInterior _).preimage
    (continuous_const.add (continuous_snd.smul continuous_const))
  have hf : ContDiffOn ℝ ∞ (frozenDeterminantIncidence P z) D := by
    intro p hp
    exact (contDiffAt_frozenDeterminantIncidence hP z p (fun i ↦ (hp i).le)).contDiffWithinAt
  have hmem : (k, 0) ∈ D := by simpa [D, incidenceParameter] using hz
  have hs := frozenDeterminantIncidence_simple hP hz hzero hd
  obtain ⟨r, a, c, e, hr, ha, hc, he, hKD, hgap, hend⟩ :=
    exists_simple_root_cylinder hD hf hmem hs.1 hs.2
  simp only [zero_sub, zero_add] at hKD hgap hend
  refine ⟨r, a, c, e, hr, ha, hc, he, ?_, ?_, hend⟩
  · intro t ht
    exact hKD (show (k, t) ∈ Metric.closedBall k (2 * r) ×ˢ Icc (-a) a from
      ⟨Metric.mem_closedBall_self (by positivity), ht⟩)
  · intro q hq t ht
    exact hgap (q, t) ⟨hq, ht⟩

/-- The existing frozen incidence sections supply every hypothesis for the
literal determinant cylinder construction; actual roots are not inputs
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem exists_frozen_incidence_cylinder_of_section {n : ℕ} {P : Patch n}
    {c₀ C₀ d : ℝ} (hP : P.IsValid c₀ C₀) {V : Set (Euclidean n)}
    {z₀ : Euclidean n → Euclidean 3} (hsec : P.IsIncidenceSection V z₀ d)
    (hd : 0 < d) {k : Euclidean n} (hk : k ∈ V) :
    ∃ r a c e : ℝ, 0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < e ∧
      (∀ t ∈ Icc (-a) a, incidenceParameter (z₀ k) t ∈ parameterInterior P.radius) ∧
      (∀ q ∈ Metric.closedBall k (2 * r), ∀ t ∈ Icc (-a) a,
        2 * c ≤ |scalarDerivative (frozenDeterminantIncidence P (z₀ k)) (q, t)|) ∧
      (∀ q ∈ Metric.closedBall k (2 * r),
        (frozenDeterminantIncidence P (z₀ k) (q, -a) ≤ -e ∧
          e ≤ frozenDeterminantIncidence P (z₀ k) (q, a)) ∨
        (frozenDeterminantIncidence P (z₀ k) (q, a) ≤ -e ∧
          e ≤ frozenDeterminantIncidence P (z₀ k) (q, -a))) := by
  have hz := hsec.2.1 k hk
  exact exists_frozen_incidence_cylinder hP hz.1 hz.2.2.2
    (abs_pos.mp (hd.trans_le (hsec.2.2 k hk _ (fun i ↦ (hz.1 i).le))))

/-- Uniqueness of the original frozen section among all incident parameters
with its fixed zero spectators, on the entire cube. This identifies the
reference branch used in the continuation estimate with the input to
`RootDetection` (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem eq_frozen_section_of_incidence {n : ℕ} {P : Patch n} {c₀ C₀ d : ℝ}
    (hP : P.IsValid c₀ C₀) {V : Set (Euclidean n)}
    {z₀ : Euclidean n → Euclidean 3} (hsec : P.IsIncidenceSection V z₀ d)
    (hd : 0 < d) {k : Euclidean n} (hk : k ∈ V) {w : Euclidean 3}
    (hw : w ∈ parameterCube P.radius) (hw₁ : w 1 = 0) (hw₂ : w 2 = 0)
    (hinc : incidence k (P.toFun w) = 0) : w = z₀ k := by
  have hz := hsec.2.1 k hk
  have hwline := eq_single_of_zero_spectators hw₁ hw₂
  have hzline := eq_single_of_zero_spectators hz.2.1 hz.2.2.1
  let f : Euclidean n × ℝ → ℝ := fun p ↦
    incidence p.1 (P.toFun (p.2 • EuclideanSpace.single 0 1))
  have hline (t : ℝ) (ht : t ∈ Icc (-P.radius) P.radius) :
      t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ∈ parameterCube P.radius := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa using abs_le.mpr ht
    · simp [hi, hP.1.le]
  have he : w 0 = z₀ k 0 := by
    apply scalar_root_unique_of_gap (f := f) hd
      (fun t ht ↦ (Patch.contDiffAt_scalar_incidence hP k (hline t ht)).differentiableAt
        (by simp))
      (fun t ht ↦ ?_) (abs_le.mp (hw 0)) (abs_le.mp (hz.1 0).le)
    · simpa only [f, ← hwline] using hinc
    · simpa only [f, ← hzline] using hz.2.2.2
    · dsimp only [f]
      rw [Patch.scalarDerivative_incidence_eq hP k (hline t ht)]
      exact hsec.2.2 k hk _ (hline t ht)
  rw [hwline, hzline, he]

/-- Any interior frozen determinant root on the continued line is the
published frozen incidence section. This discharges the reference-branch
identification required for detector stability
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem incidenceParameter_eq_frozen_section {n : ℕ} {P : Patch n} {c₀ C₀ d : ℝ}
    (hP : P.IsValid c₀ C₀) {V : Set (Euclidean n)}
    {z₀ : Euclidean n → Euclidean 3} (hsec : P.IsIncidenceSection V z₀ d)
    (hd : 0 < d) {k q : Euclidean n} (hk : k ∈ V) (hq : q ∈ V) {t : ℝ}
    (ht : incidenceParameter (z₀ k) t ∈ parameterCube P.radius)
    (hzero : frozenDeterminantIncidence P (z₀ k) (q, t) = 0) :
    incidenceParameter (z₀ k) t = z₀ q := by
  apply eq_frozen_section_of_incidence hP hsec hd hq ht
  · rw [(incidenceParameter_spectators _ _).1]
    exact (hsec.2.1 k hk).2.1
  · rw [(incidenceParameter_spectators _ _).2]
    exact (hsec.2.1 k hk).2.2.1
  · rw [frozenDeterminantIncidence_eq_mul hP _ (q, t) ht] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left
      (CubeCarrier.determinant_normal_multiplier_ne_zero
        (hP.2.2.2.2.1 _ ht).1 (hP.2.2.2.2.1 _ ht).2.1)

end JanetCartan.ActualCarriers
