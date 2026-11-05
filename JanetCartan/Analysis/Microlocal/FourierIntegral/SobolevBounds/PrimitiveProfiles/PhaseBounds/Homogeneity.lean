module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.Profiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Homogeneity

/-!
# Local normalized phase primitives

The degree-one phase on an open position chart and an open positive cone
produces the degree-zero matrix and scalar primitives of Step 3 in
`app:ch_regular_base:thm:actual-calculus`. The second position is retained.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {X D : Set (Euclidean n)}

/-- Phase smoothness and degree-one homogeneity on an open conic chart imply
actual mixed-matrix degree zero. Source: Step 3 of
`app:ch_regular_base:thm:actual-calculus`. -/
theorem mixedPhaseMatrix_dilation_eq_on (hX : IsOpen X) (hD : IsOpen D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hh : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    {R : ℝ} (hR : 0 < R) {x η : Euclidean n} (hx : x ∈ X) (hη : η ∈ D) :
    mixedPhaseMatrix S x (R • η) = mixedPhaseMatrix S x η := by
  have hs (ξ) (hξ : ξ ∈ D) := hS.contDiffAt ((hX.prod hD).mem_nhds (x := (x, ξ)) ⟨hx, hξ⟩)
  have hd (ξ) (hξ : ξ ∈ D) (i : Fin n) : ContDiffAt ℝ ∞
      (fun η ↦ partialDeriv (fun z ↦ S z η) x i) ξ := by
    have ht := (hs ξ hξ).comp (ξ, x) (contDiffAt_snd.prodMk contDiffAt_fst)
    exact (ht.fderiv contDiffAt_const (by simp)).clm_apply contDiffAt_const
  exact ResponseTransfer.mixedPhaseMatrix_smul_covector hX hD hx hη hR.ne'
    (hh R hR)
    (fun ξ hξ ↦ ((hs ξ hξ).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
    (fun i ↦ (hd η hη i).differentiableAt (by simp))
    (fun i ↦ (hd (R • η) (hcone R hR η hη) i).differentiableAt (by simp))

/-- All actual scalar primitives, including inverse entries, have degree zero
on the buffered chart. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem scalarPrimitive_dilation_eq_on (hX : IsOpen X) (hD : IsOpen D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hh : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    {U : Set (Point n)} (hchart : ∀ p ∈ U, p.1.1 ∈ X ∧ p.2 ∈ D)
    (a : ScalarIndex n) {R : ℝ} (hR : 0 < R) :
    Set.EqOn (normalizedField R (uncurry (scalarPrimitive S a)))
      (uncurry (scalarPrimitive S a)) U := by
  intro p hp
  have he := mixedPhaseMatrix_dilation_eq_on hX hD hcone hS hh hR
    (hchart p hp).1 (hchart p hp).2
  simp only [normalizedField, uncurry, scalarPrimitive, he]

/-- Smoothness of the actual mixed matrix with the dummy position retained,
from the ordinary phase on its open chart. Source: Step 3 of
`app:ch_regular_base:thm:actual-calculus`. -/
theorem contDiffOn_joint_mixedPhaseMatrix (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {U : Set (Point n)} (hchart : ∀ p ∈ U, p.1.1 ∈ X ∧ p.2 ∈ D) :
    ContDiffOn ℝ ∞ (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2) U := by
  intro p hp
  exact ((contDiffAt_mixedPhaseMatrix_of_phase S (p.1.1, p.2)
    (hS.contDiffAt ((hX.prod hD).mem_nhds (hchart p hp)))).comp p
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).contDiffWithinAt

/-- Scalar smoothness follows from the actual phase and determinant gap,
without assuming any inverse jets. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem contDiffOn_joint_scalarPrimitive (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {U : Set (Point n)} (hchart : ∀ p ∈ U, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hu : ∀ p ∈ U, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) (a : ScalarIndex n) :
    ContDiffOn ℝ ∞ (uncurry (scalarPrimitive S a)) U := by
  intro p hp
  let ev : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) a.2.2).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) a.2.1))
  have hs := hS.contDiffAt ((hX.prod hD).mem_nhds (x := (p.1.1, p.2)) (hchart p hp))
  have hm : ContDiffAt ℝ ∞ (fun q : Point n ↦
      if a.1 then (mixedPhaseMatrix S q.1.1 q.2)⁻¹ else mixedPhaseMatrix S q.1.1 q.2) p := by
    cases ha : a.1 with
    | false =>
      simpa only [ha, Bool.false_eq_true, ↓reduceIte, Function.comp_def, Function.uncurry_def] using
        (contDiffAt_mixedPhaseMatrix_of_phase S (p.1.1, p.2) hs).comp p
          (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    | true =>
      simpa only [ha, ↓reduceIte, Function.comp_def] using
        (contDiffAt_mixedPhaseMatrix_inverse_of_phase S (p.1.1, p.2) hs (hu p hp)).comp p
          (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp p (ev.contDiff.contDiffAt.comp p hm)
  apply ContDiffAt.contDiffWithinAt
  convert hc using 1
  funext q
  cases ha : a.1 <;> simp [uncurry, scalarPrimitive, ha, ev] <;> rfl

/-- Normalized scalar smoothness and seminorm finiteness are consequences of
phase geometry. This supplies the scalar hypotheses of
`exists_primitiveProfile_interpolation` in Step 3 of the actual-calculus theorem. -/
theorem normalized_scalarPrimitive_regular (hX : IsOpen X) (hD : IsOpen D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hh : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    {K U : Set (Point n)} (hU : IsOpen U) (hKU : K ⊆ U)
    (hchart : ∀ p ∈ U, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hu : ∀ p ∈ U, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det)
    (a : ScalarIndex n) (k : ℕ) :
    (∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ ∞
      (normalizedField R (uncurry (scalarPrimitive S a))) U) ∧
    BoundedNormalizedSeminorm K k (uncurry (scalarPrimitive S a)) ∧
    normalizedSeminorm K k (uncurry (scalarPrimitive S a)) =
      cNorm K k (uncurry (scalarPrimitive S a)) := by
  have hi (R : ℝ) (hR : 1 ≤ R) := scalarPrimitive_dilation_eq_on hX hD hcone hS hh
    hchart a (lt_of_lt_of_le zero_lt_one hR)
  refine ⟨?_, normalizedSeminorm_eq_cNorm_of_invariant hU hKU _ hi k⟩
  intro R hR
  exact (contDiffOn_joint_scalarPrimitive hX hD hS hchart hu a).congr (hi R hR)

end JanetCartan.FourierIntegral.PrimitiveProfiles
