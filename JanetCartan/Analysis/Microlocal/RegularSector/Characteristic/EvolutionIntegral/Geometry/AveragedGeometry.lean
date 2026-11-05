module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.MixedBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Basic
public import JanetCartan.Analysis.Calculus.BufferedInverse
/-!
# Averaged geometry of the elapsed-time phase

The whole-image inputs of `exists_fullGraphFamily_of_wholeImage_phase` for
`app:ch_regular_base:lem:retarded-kernel` follow from the original spatial
mixed near-identity estimate. The spatial mixed block is averaged along the
full spacetime segment, with both output positions retained. Its determinant
is exactly the spacetime averaged-Jacobian determinant. Convexity of the outer
spatial covector chart gives injectivity; closure buffers transfer the result
to inner conic domains with low-frequency collars.

The phase regularity and near-identity estimate are the primitive hypotheses
of the retarded-kernel lemma, supplied by the parent's spatial phase. No
averaged invertibility or injectivity is assumed. Temporal mixed-row bounds
are needed only for the inverse-norm estimates in `Geometry.MixedBounds`.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral NormalComparison WholeImageGeometry
variable {n : ℕ}
private def coordinateMatrix : (Euclidean n →L[ℝ] Euclidean n) →L[ℝ]
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L ↦ LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis L.toLinearMap
      map_add' := by intros; simp
      map_smul' := by intros; simp }
private theorem coordinateMatrix_apply (L : Euclidean n →L[ℝ] Euclidean n) (i j : Fin n) :
    coordinateMatrix L i j = L (EuclideanSpace.single j 1) i := by
  simp [coordinateMatrix, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply]
private theorem norm_le_coordinateMatrix (L : Euclidean n →L[ℝ] Euclidean n) :
    ‖L‖ ≤ ‖coordinateMatrix L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have he : (coordinateMatrix L).toEuclideanLin = L.toLinearMap := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.toLin_toMatrix _ _ _
  have ha := congrArg (fun f : Euclidean n →ₗ[ℝ] Euclidean n ↦ f v) he
  rw [Matrix.toLpLin_apply] at ha
  calc
    ‖L v‖ = ‖Matrix.replicateCol Unit ((coordinateMatrix L).mulVec v.ofLp)‖ := by
      rw [Matrix.frobenius_norm_replicateCol, ha]
      rfl
    _ ≤ ‖coordinateMatrix L‖ * ‖Matrix.replicateCol Unit v.ofLp‖ := by
      rw [Matrix.replicateCol_mulVec]
      exact Matrix.frobenius_norm_mul _ _
    _ = ‖coordinateMatrix L‖ * ‖v‖ := by rw [Matrix.frobenius_norm_replicateCol]

private theorem contDiffAt_outputGradient (S : Euclidean n → Euclidean n → ℝ)
    {z : Euclidean n × Euclidean n}
    (h : ContDiffAt ℝ ∞ (Function.uncurry S) z) :
    ContDiffAt ℝ ∞ (fun q : Euclidean n × Euclidean n ↦ gradient (fun x ↦ S x q.2) q.1) z := by
  have hh : ContDiffAt ℝ ∞
      (Function.uncurry (fun q : Euclidean n × Euclidean n ↦ fun x ↦ S x q.2)) (z, z.1) :=
    h.comp (z, z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (InnerProductSpace.toDual ℝ (Euclidean n)).symm.contDiff.contDiffAt.comp z
    (hh.fderiv (m := ∞) contDiffAt_fst (by simp))

private theorem coordinateMatrix_mixedGradient (S : Euclidean n → Euclidean n → ℝ)
    (x u : Euclidean n)
    (h : DifferentiableAt ℝ (fun η ↦ gradient (fun z ↦ S z η) x) u) :
    coordinateMatrix (fderiv ℝ (fun η ↦ gradient (fun z ↦ S z η) x) u) =
      mixedPhaseMatrix S x u := by
  have hg (f : Euclidean n → ℝ) (v : Euclidean n) (i : Fin n) :
      gradient f v i = partialDeriv f v i := by
    have hh : inner ℝ (EuclideanSpace.single i 1) (gradient f v) = partialDeriv f v i := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using hh
  ext i j
  rw [coordinateMatrix_apply]
  have hi : (fun η ↦ partialDeriv (fun z ↦ S z η) x i) =
      fun η ↦ gradient (fun z ↦ S z η) x i := funext fun η ↦ (hg _ _ _).symm
  change _ = (fderiv ℝ _ u) (EuclideanSpace.single j 1)
  have hd := ((EuclideanSpace.proj i).hasFDerivAt.comp u h.hasFDerivAt).fderiv
  simp only [EuclideanSpace.coe_proj, Function.comp_def] at hd
  rw [hi, hd]
  rfl

private theorem segmentGradient_contDiffAt {S : Euclidean n → Euclidean n → ℝ}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x y : Euclidean n} (hx : x ∈ X) (hy : y ∈ X)
    {q : ℝ × Euclidean n} (hq : q ∈ uIcc (0 : ℝ) 1 ×ˢ D) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Euclidean n ↦
      gradient (fun z ↦ S z p.2) (y + p.1 • (x - y))) q := by
  have hm : (y + q.1 • (x - y), q.2) ∈ X ×ˢ D :=
    ⟨hcX.add_smul_sub_mem hy hx (by simpa using hq.1), hq.2⟩
  exact (contDiffAt_outputGradient S (hs.contDiffAt ((hX.prod hD).mem_nhds hm))).comp q
    (f := fun p : ℝ × Euclidean n ↦ (y + p.1 • (x - y), p.2)) ((contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk contDiffAt_snd)

private theorem segmentDifferential_integrable {S : Euclidean n → Euclidean n → ℝ}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x y u : Euclidean n} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D) :
    IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ (fun z ↦ S z u)
      (y + t • (x - y))) volume 0 1 := by
  have hc : ContinuousOn (fun t : ℝ ↦ gradient (fun z ↦ S z u)
      (y + t • (x - y))) (uIcc 0 1) := by
    intro t ht
    exact ((segmentGradient_contDiffAt hX hD hcX hs hx hy ⟨ht, hu⟩).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have he : (fun t : ℝ ↦ fderiv ℝ (fun z ↦ S z u) (y + t • (x - y))) =
      fun t ↦ (InnerProductSpace.toDual ℝ (Euclidean n))
        (gradient (fun z ↦ S z u) (y + t • (x - y))) := by
    funext t
    simp [gradient]
  rw [he]
  exact ((InnerProductSpace.toDual ℝ (Euclidean n)).continuous.comp_continuousOn hc).intervalIntegrable

private theorem hasFDerivAt_segmentAverage {S : Euclidean n → Euclidean n → ℝ}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x y u : Euclidean n} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D) :
    HasFDerivAt (averagedGradient S x y)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun η ↦ gradient (fun z ↦ S z η)
        (y + t • (x - y))) u) u := by
  have hh := hasFDerivAt_fixedIntervalIntegral hD
    (fun q hq ↦ segmentGradient_contDiffAt hX hD hcX hs hx hy hq) hu
  have he : (∫ t in (0 : ℝ)..1,
      (fderiv ℝ (fun p : ℝ × Euclidean n ↦ gradient (fun z ↦ S z p.2)
        (y + p.1 • (x - y))) (t, u)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n))) =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun η ↦ gradient (fun z ↦ S z η)
        (y + t • (x - y))) u := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact (((segmentGradient_contDiffAt hX hD hcX hs hx hy ⟨ht, hu⟩).differentiableAt
      (by simp)).hasFDerivAt.comp u (hasFDerivAt_prodMk_right t u)).fderiv.symm
  rw [he] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds hu] with v hv
  exact averagedGradient_eq_integral_gradient S x y v
    (segmentDifferential_integrable hX hD hcX hs hx hy hv)

private theorem segmentMixed_continuousOn {S : Euclidean n → Euclidean n → ℝ}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x y u : Euclidean n} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D) :
    ContinuousOn (fun t : ℝ ↦ fderiv ℝ (fun η ↦ gradient (fun z ↦ S z η)
      (y + t • (x - y))) u) (uIcc 0 1) := by
  intro t ht
  exact (((segmentGradient_contDiffAt hX hD hcX hs hx hy ⟨ht, hu⟩).fderiv
    (m := ∞) contDiffAt_const (by simp)).continuousAt).continuousWithinAt

private theorem coordinateMatrix_averagedJacobian {S : Euclidean n → Euclidean n → ℝ}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x y u : Euclidean n} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D) :
    coordinateMatrix (averagedJacobian S x y u) =
      ∫ t in (0 : ℝ)..1, mixedPhaseMatrix S (y + t • (x - y)) u := by
  rw [averagedJacobian, (hasFDerivAt_segmentAverage hX hD hcX hs hx hy hu).fderiv]
  trans ∫ t in (0 : ℝ)..1, coordinateMatrix
    (fderiv ℝ (fun η ↦ gradient (fun z ↦ S z η) (y + t • (x-y))) u)
  · exact (ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) coordinateMatrix
      (segmentMixed_continuousOn hX hD hcX hs hx hy hu).intervalIntegrable).symm
  apply intervalIntegral.integral_congr
  intro t ht
  apply coordinateMatrix_mixedGradient
  exact ((segmentGradient_contDiffAt hX hD hcX hs hx hy ⟨ht, hu⟩).comp u
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)

private theorem segmentMixedMatrix_continuousOn {S : Euclidean n → Euclidean n → ℝ}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x y u : Euclidean n} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D) :
    ContinuousOn (fun t : ℝ ↦ mixedPhaseMatrix S (y + t • (x-y)) u) (uIcc 0 1) := by
  apply (coordinateMatrix.continuous.comp_continuousOn
    (segmentMixed_continuousOn hX hD hcX hs hx hy hu)).congr
  intro t ht
  exact (coordinateMatrix_mixedGradient _ _ _
    (((segmentGradient_contDiffAt hX hD hcX hs hx hy (q := (t, u)) ⟨ht, hu⟩).comp u
      (f := fun η ↦ (t, η)) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
        (by simp))).symm

variable {d : ℕ}
private def spatialMatrixBlock : Matrix (Fin (d+1)) (Fin (d+1)) ℝ →L[ℝ]
    Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A.submatrix Fin.succ Fin.succ
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
private def matrixEntry (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Spatial mixed block averaged along the full spacetime segment in
`app:ch_regular_base:eq:fixed-time-representation`. Its determinant is the
whole-image Jacobian determinant, with both output positions retained. -/
def elapsedAveragedSpatialMixed (Ψ : TwoTimePhase d) (r : ℝ)
    (x y : Euclidean (d+1)) (η : Euclidean d) : Matrix (Fin d) (Fin d) ℝ :=
  ∫ t in (0 : ℝ)..1, mixedPhaseMatrix
    (Ψ ((y + t • (x-y)) 0) ((y + t • (x-y)) 0 - r))
    (spatialPart (y + t • (x-y))) η

private theorem averagedJacobian_elapsed_blocks (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d+1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    {x y ξ : Euclidean (d+1)} (hx : x ∈ X) (hy : y ∈ X) (hξ : spatialPart ξ ∈ D) :
    (∀ i, coordinateMatrix (averagedJacobian (elapsedPhase Ψ r) x y ξ) i 0 =
      Fin.cases 1 (fun _ ↦ 0) i) ∧
    spatialMatrixBlock (coordinateMatrix (averagedJacobian (elapsedPhase Ψ r) x y ξ)) =
      elapsedAveragedSpatialMixed Ψ r x y (spatialPart ξ) := by
  have ho := hD.preimage spatialPartCLM.continuous
  have hS := elapsedPhase_contDiffOn Ψ r hs
  have hM := segmentMixedMatrix_continuousOn hX ho hcX hS hx hy hξ
  have hm (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :=
    mixedPhaseMatrix_elapsedPhase_of_contDiff Ψ r (y+t • (x-y)) ξ hD hξ
      (fun η hη ↦ contDiffAt_elapsedSpatialPhase Ψ r
        (hs _ (hcX.add_smul_sub_mem hy hx (by simpa using ht)) η hη))
  rw [coordinateMatrix_averagedJacobian hX ho hcX hS hx hy hξ]
  constructor
  · intro i
    change matrixEntry i 0 (∫ t in (0 : ℝ)..1,
      mixedPhaseMatrix (elapsedPhase Ψ r) (y+t • (x-y)) ξ) = _
    trans ∫ t in (0 : ℝ)..1, matrixEntry i 0
      (mixedPhaseMatrix (elapsedPhase Ψ r) (y+t • (x-y)) ξ)
    · exact (ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
        (matrixEntry i 0) hM.intervalIntegrable).symm
    calc
      _ = ∫ _t in (0 : ℝ)..1, Fin.cases (1 : ℝ) (fun _ ↦ 0) i := by
        apply intervalIntegral.integral_congr
        intro t ht
        change mixedPhaseMatrix _ _ _ i 0 = _
        rw [hm t ht]
        induction i using Fin.cases <;> rfl
      _ = _ := by simp
  · trans ∫ t in (0 : ℝ)..1, spatialMatrixBlock
      (mixedPhaseMatrix (elapsedPhase Ψ r) (y+t • (x-y)) ξ)
    · exact (ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
        spatialMatrixBlock hM.intervalIntegrable).symm
    apply intervalIntegral.integral_congr
    intro t ht
    ext i j
    change mixedPhaseMatrix _ _ _ i.succ j.succ = _
    rw [hm t ht]
    rfl

/-- The whole-image averaged Jacobian has the spatial averaged determinant.
The average follows the full spacetime segment, including its time coordinate.
Consumer: `exists_fullGraphFamily_of_wholeImage_phase` for
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem det_averagedJacobian_elapsedPhase (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d+1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    {x y ξ : Euclidean (d+1)} (hx : x ∈ X) (hy : y ∈ X) (hξ : spatialPart ξ ∈ D) :
    (averagedJacobian (elapsedPhase Ψ r) x y ξ).det =
      (elapsedAveragedSpatialMixed Ψ r x y (spatialPart ξ)).det := by
  obtain ⟨hcol, hblock⟩ := averagedJacobian_elapsed_blocks Ψ r hX hD hcX hs hx hy hξ
  change (averagedJacobian _ _ _ _).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (d+1)) ℝ).toBasis]
  change (coordinateMatrix (averagedJacobian _ _ _ _)).det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hcol, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, mul_one, one_mul,
    Fin.succAbove_zero]
  exact congrArg Matrix.det hblock

private def spatialLiftCLM : Euclidean d →L[ℝ] Euclidean (d+1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun η ↦ WithLp.toLp 2 (Fin.cases 0 η.ofLp)
      map_add' := by intros; ext i; induction i using Fin.cases <;> simp
      map_smul' := by intros; ext i; induction i using Fin.cases <;> simp }
private theorem spatialPart_lift (η : Euclidean d) : spatialPart (spatialLiftCLM η) = η := by
  ext i
  rfl
private theorem spatialLift_single (i : Fin d) :
    spatialLiftCLM (EuclideanSpace.single i (1 : ℝ)) = EuclideanSpace.single i.succ 1 := by
  ext j
  induction j using Fin.cases <;> simp [spatialLiftCLM, EuclideanSpace.single, Pi.single_apply]

/-- Spatial near-identity control survives averaging over the **spacetime**
segment. This supplies the uniform whole-image determinant gap and injectivity
in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_elapsedAveragedSpatialMixed_sub_one_le (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d+1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    (hnear : ∀ x ∈ X, ∀ η ∈ D,
      ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2)
    {x y : Euclidean (d+1)} {η : Euclidean d} (hx : x ∈ X) (hy : y ∈ X) (hη : η ∈ D) :
    ‖elapsedAveragedSpatialMixed Ψ r x y η - 1‖ ≤ 1/2 := by
  let ξ := spatialLiftCLM η
  have hξ : spatialPart ξ = η := spatialPart_lift η
  have hc := segmentMixedMatrix_continuousOn hX (hD.preimage spatialPartCLM.continuous)
    hcX (elapsedPhase_contDiffOn Ψ r hs) hx hy (show spatialPart ξ ∈ D from hξ ▸ hη)
  have hA : ContinuousOn (fun t : ℝ ↦ mixedPhaseMatrix
      (Ψ ((y+t • (x-y)) 0) ((y+t • (x-y)) 0-r)) (spatialPart (y+t • (x-y))) η)
      (uIcc 0 1) := by
    apply (spatialMatrixBlock.continuous.comp_continuousOn hc).congr
    intro t ht
    have hm := mixedPhaseMatrix_elapsedPhase_of_contDiff Ψ r (y+t • (x-y)) ξ hD
      (hξ ▸ hη) (fun ζ hζ ↦ contDiffAt_elapsedSpatialPhase Ψ r
        (hs _ (hcX.add_smul_sub_mem hy hx (by simpa using ht)) ζ hζ))
    ext i j
    change _ = mixedPhaseMatrix _ _ _ i.succ j.succ
    rw [hm]
    simp only [Fin.cases_succ, hξ]
  have he : elapsedAveragedSpatialMixed Ψ r x y η - 1 =
      ∫ t in (0 : ℝ)..1, mixedPhaseMatrix
        (Ψ ((y+t • (x-y)) 0) ((y+t • (x-y)) 0-r)) (spatialPart (y+t • (x-y))) η - 1 := by
    rw [intervalIntegral.integral_sub hA.intervalIntegrable intervalIntegrable_const]
    simp [elapsedAveragedSpatialMixed]
  rw [he]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := (1/2 : ℝ))
    (fun t ht ↦ hnear _ (hcX.add_smul_sub_mem hy hx (by simpa using uIoc_subset_uIcc ht)) η hη)

private theorem spatialAverage_hasFDerivAt (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d+1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    {x y : Euclidean (d+1)} {η : Euclidean d} (hx : x ∈ X) (hy : y ∈ X) (hη : η ∈ D) :
    HasFDerivAt (fun η ↦ spatialPart (averagedGradient (elapsedPhase Ψ r) x y (spatialLiftCLM η)))
      (spatialPartCLM.comp ((averagedJacobian (elapsedPhase Ψ r) x y (spatialLiftCLM η)).comp
        spatialLiftCLM)) η := by
  have hd := (hasFDerivAt_segmentAverage hX (hD.preimage spatialPartCLM.continuous)
    hcX (elapsedPhase_contDiffOn Ψ r hs) hx hy
    (show spatialPart (spatialLiftCLM η) ∈ D by rw [spatialPart_lift]; exact hη)).differentiableAt.hasFDerivAt
  exact spatialPartCLM.hasFDerivAt.comp η (hd.comp η spatialLiftCLM.hasFDerivAt)

private theorem spatialAverage_coordinateMatrix (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d+1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    {x y : Euclidean (d+1)} {η : Euclidean d} (hx : x ∈ X) (hy : y ∈ X) (hη : η ∈ D) :
    coordinateMatrix (fderiv ℝ (fun η ↦ spatialPart
      (averagedGradient (elapsedPhase Ψ r) x y (spatialLiftCLM η))) η) =
        elapsedAveragedSpatialMixed Ψ r x y η := by
  have hb := (averagedJacobian_elapsed_blocks Ψ r hX hD hcX hs hx hy
    (show spatialPart (spatialLiftCLM η) ∈ D by rw [spatialPart_lift]; exact hη)).2
  rw [spatialPart_lift] at hb
  rw [← hb, (spatialAverage_hasFDerivAt Ψ r hX hD hcX hs hx hy hη).fderiv]
  ext i j
  rw [coordinateMatrix_apply]
  change _ = coordinateMatrix _ i.succ j.succ
  rw [coordinateMatrix_apply]
  simp only [ContinuousLinearMap.comp_apply, spatialLift_single, spatialPartCLM_apply]
  rfl

private theorem elapsed_time_integrable (Ψ : TwoTimePhase d) (r : ℝ)
    (x y ξ : Euclidean (d+1))
    (h : ∀ θ ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ
      (fun p ↦ elapsedSpatialPhase Ψ r p (spatialPart ξ))
      ((y + θ • (x-y)) 0, spatialPart (y + θ • (x-y))))
    (hi : IntervalIntegrable (fun θ : ℝ ↦ fderiv ℝ (fun z ↦ elapsedPhase Ψ r z ξ)
      (y + θ • (x-y))) volume 0 1) :
    IntervalIntegrable (fun θ : ℝ ↦ elapsedTimeDerivative Ψ r
      ((y + θ • (x-y)) 0, spatialPart (y + θ • (x-y))) (spatialPart ξ)) volume 0 1 := by
  let L := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (0 : Fin (d+1)) (1 : ℝ))
  have he : IntervalIntegrable (fun θ : ℝ ↦ partialDeriv (fun z ↦ elapsedPhase Ψ r z ξ)
      (y + θ • (x-y)) 0) volume 0 1 :=
    ⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩
  apply (he.sub (intervalIntegrable_const (c := ξ 0))).congr
  intro θ hθ
  dsimp only
  rw [elapsedPhase_output_zero Ψ r _ ξ (h θ (uIoc_subset_uIcc hθ))]
  ring

private theorem averagedGradient_elapsed_same_spatial (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d+1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    {x y ξ ζ : Euclidean (d+1)} (hx : x ∈ X) (hy : y ∈ X)
    (hξ : spatialPart ξ ∈ D) (he : spatialPart ξ = spatialPart ζ) :
    spatialPart (averagedGradient (elapsedPhase Ψ r) x y ξ) =
      spatialPart (averagedGradient (elapsedPhase Ψ r) x y ζ) ∧
    averagedGradient (elapsedPhase Ψ r) x y ξ 0 - ξ 0 =
      averagedGradient (elapsedPhase Ψ r) x y ζ 0 - ζ 0 := by
  have hd (v : Euclidean (d+1)) (hv : spatialPart v ∈ D) (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      DifferentiableAt ℝ (fun p ↦ elapsedSpatialPhase Ψ r p (spatialPart v))
        ((y+t • (x-y)) 0, spatialPart (y+t • (x-y))) := by
    exact ((contDiffAt_elapsedSpatialPhase Ψ r
      (hs _ (hcX.add_smul_sub_mem hy hx (by simpa using ht)) _ hv)).comp _
        (f := fun p : ℝ × Euclidean d ↦ (p, spatialPart v))
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hi (v : Euclidean (d+1)) (hv : spatialPart v ∈ D) :=
    segmentDifferential_integrable hX (hD.preimage spatialPartCLM.continuous) hcX
      (elapsedPhase_contDiffOn Ψ r hs) hx hy hv
  have hζ : spatialPart ζ ∈ D := he ▸ hξ
  constructor
  · ext i
    change averagedGradient _ _ _ ξ i.succ = averagedGradient _ _ _ ζ i.succ
    rw [averagedGradient_elapsedPhase_spatial Ψ r x y ξ i (hd ξ hξ) (hi ξ hξ),
      averagedGradient_elapsedPhase_spatial Ψ r x y ζ i (hd ζ hζ) (hi ζ hζ), he]
  · rw [averagedGradient_elapsedPhase_time Ψ r x y ξ (hd ξ hξ) (hi ξ hξ)
        (elapsed_time_integrable Ψ r x y ξ (hd ξ hξ) (hi ξ hξ)),
      averagedGradient_elapsedPhase_time Ψ r x y ζ (hd ζ hζ) (hi ζ hζ)
        (elapsed_time_integrable Ψ r x y ζ (hd ζ hζ) (hi ζ hζ)), he]
    ring

/-- Convexity of the spatial covector chart and primitive spatial mixed
near-identity control imply injectivity of the full averaged gradient.
The temporal shear need not be small. The result holds on any subset of the
lifted chart, including a buffered conic frequency domain with a low collar.
Consumer: `exists_fullGraphFamily_of_wholeImage_phase` in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem injOn_averagedGradient_elapsedPhase (Ψ : TwoTimePhase d) (r : ℝ)
    {X : Set (Euclidean (d+1))} {D : Set (Euclidean d)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X) (hcD : Convex ℝ D)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    (hnear : ∀ x ∈ X, ∀ η ∈ D,
      ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2)
    {x y : Euclidean (d+1)} (hx : x ∈ X) (hy : y ∈ X) :
    InjOn (averagedGradient (elapsedPhase Ψ r) x y) (spatialPart ⁻¹' D) := by
  let f := fun η ↦ spatialPart (averagedGradient (elapsedPhase Ψ r) x y (spatialLiftCLM η))
  have hd (η) (hη : η ∈ D) := spatialAverage_hasFDerivAt Ψ r hX hD hcX hs hx hy hη
  have hg (η) (hη : η ∈ D) : ‖fderiv ℝ f η - ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤ 1/2 := by
    apply (norm_le_coordinateMatrix _).trans
    rw [map_sub]
    have hid : coordinateMatrix (ContinuousLinearMap.id ℝ (Euclidean d)) = 1 :=
      LinearMap.toMatrix_id _
    rw [hid, spatialAverage_coordinateMatrix Ψ r hX hD hcX hs hx hy hη]
    exact norm_elapsedAveragedSpatialMixed_sub_one_le Ψ r hX hD hcX hs hnear hx hy hη
  have hinj : InjOn f D := injOn_of_normalized_derivative_gap hcD
    (ContinuousLinearEquiv.refl ℝ (Euclidean d)) (fun η hη ↦ (hd η hη).differentiableAt)
    (by simpa using hg)
  intro ξ hξ ζ hζ heq
  have hξf := (averagedGradient_elapsed_same_spatial Ψ r hX hD hcX hs hx hy hξ
    (spatialPart_lift (spatialPart ξ)).symm).1
  have hζf := (averagedGradient_elapsed_same_spatial Ψ r hX hD hcX hs hx hy hζ
    (spatialPart_lift (spatialPart ζ)).symm).1
  have hsp : spatialPart ξ = spatialPart ζ := hinj hξ hζ
    (hξf.symm.trans ((congrArg spatialPart heq).trans hζf))
  have ht := (averagedGradient_elapsed_same_spatial Ψ r hX hD hcX hs hx hy hξ hsp).2
  rw [heq] at ht
  ext i
  induction i using Fin.cases with
  | zero => linarith
  | succ i => exact congrArg (fun v : Euclidean d ↦ v i) hsp

/-- A common positive determinant gap and averaged-gradient injectivity,
uniform for every `r ∈ [0, Δ]`, follow from the original spatial mixed
near-identity estimate. These are the exact whole-image geometry inputs of
`exists_fullGraphFamily_of_wholeImage_phase`. Restricting the lifted spatial
chart to a smaller buffered cone or positive frequency collar preserves them.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_elapsedPhase_averaged_geometry (d : ℕ) :
    ∃ δ > 0, ∀ (Ψ : TwoTimePhase d) (Δ : ℝ)
      (X : Set (Euclidean (d+1))) (D : Set (Euclidean d)),
      IsOpen X → IsOpen D → Convex ℝ X → Convex ℝ D →
      (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
        (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
        ((x 0, x 0-r), (spatialPart x, η))) →
      (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ D,
        ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2) →
      ∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ y ∈ X,
        InjOn (averagedGradient (elapsedPhase Ψ r) x y) (spatialPart ⁻¹' D) ∧
        ∀ ξ : Euclidean (d+1), spatialPart ξ ∈ D →
          δ ≤ |(averagedJacobian (elapsedPhase Ψ r) x y ξ).det| := by
  obtain ⟨δ, hδ, _, _, hbound⟩ := exists_spatialMixed_half_gap_constants d
  refine ⟨δ, hδ, ?_⟩
  intro Ψ Δ X D hX hD hcX hcD hs hn r hr x hx y hy
  refine ⟨injOn_averagedGradient_elapsedPhase Ψ r hX hD hcX hcD (hs r hr) (hn r hr) hx hy, ?_⟩
  intro ξ hξ
  rw [det_averagedJacobian_elapsedPhase Ψ r hX hD hcX (hs r hr) hx hy hξ]
  exact (hbound _ (norm_elapsedAveragedSpatialMixed_sub_one_le Ψ r hX hD hcX
    (hs r hr) (hn r hr) hx hy hξ)).2.1

/-- Transfer the elapsed-time geometry to fixed inner physical and frequency
charts with closure buffers in common open convex outer charts. The inner
frequency chart can be a conic sector with a positive low-frequency collar;
it need not itself be convex. The open neighborhood, local phase smoothness,
injectivity and determinant gap are the corresponding exact inputs of
`exists_fullGraphFamily_of_wholeImage_phase`. Primitive homogeneity and finite
jet budgets remain with their original producers. Source:
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_elapsedPhase_buffered_geometry (d : ℕ) :
    ∃ δ > 0, ∀ (Ψ : TwoTimePhase d) (Δ : ℝ)
      (Xouter : Set (Euclidean (d+1))) (Douter : Set (Euclidean d)),
      IsOpen Xouter → IsOpen Douter → Convex ℝ Xouter → Convex ℝ Douter →
      (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter, ContDiffAt ℝ ∞
        (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
        ((x 0, x 0-r), (spatialPart x, η))) →
      (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter,
        ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2) →
      ∀ (X F : Set (Euclidean (d+1))), closure X ⊆ Xouter →
        closure F ⊆ spatialPart ⁻¹' Douter →
        IsOpen (Xouter ×ˢ (spatialPart ⁻¹' Douter)) ∧
        closure (X ×ˢ F) ⊆ Xouter ×ˢ (spatialPart ⁻¹' Douter) ∧
        ∀ r ∈ Icc 0 Δ,
          ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r))
            (Xouter ×ˢ (spatialPart ⁻¹' Douter)) ∧
          ∀ x ∈ X, ∀ y ∈ X,
            InjOn (averagedGradient (elapsedPhase Ψ r) x y) F ∧
            ∀ ξ ∈ F, δ ≤ |(averagedJacobian (elapsedPhase Ψ r) x y ξ).det| := by
  obtain ⟨δ, hδ, hgeom⟩ := exists_elapsedPhase_averaged_geometry d
  refine ⟨δ, hδ, ?_⟩
  intro Ψ Δ Xouter Douter hX hD hcX hcD hs hn X F hXX hFD
  refine ⟨hX.prod (hD.preimage spatialPartCLM.continuous), ?_, ?_⟩
  · rw [closure_prod_eq]
    exact Set.prod_mono hXX hFD
  · intro r hr
    refine ⟨elapsedPhase_contDiffOn Ψ r (hs r hr), ?_⟩
    intro x hx y hy
    have hg := hgeom Ψ Δ Xouter Douter hX hD hcX hcD hs hn r hr
      x (hXX (subset_closure hx)) y (hXX (subset_closure hy))
    exact ⟨hg.1.mono (subset_closure.trans hFD), fun ξ hξ ↦ hg.2 ξ (hFD (subset_closure hξ))⟩
end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
