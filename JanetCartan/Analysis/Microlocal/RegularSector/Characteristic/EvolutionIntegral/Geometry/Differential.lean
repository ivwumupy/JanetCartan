module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Basic
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChangeOfVariables

/-!
# Triangular differential geometry of the elapsed phase

The literal phase of `app:ch_regular_base:eq:fixed-time-representation`
has a triangular mixed matrix. Both output positions, including their
different times, remain in the averaged-gradient identities. These are
inputs to the whole-image graph construction in the retarded-kernel lemma.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral NormalComparison
variable {d : ℕ}
/-- Continuous spatial projection used to differentiate the phase in
`app:ch_regular_base:eq:fixed-time-representation`. -/
def spatialPartCLM : Euclidean (d + 1) →L[ℝ] Euclidean d :=
  LinearMap.toContinuousLinearMap
    { toFun := spatialPart
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
/-- The continuous projection is the spatial coordinate map of the fixed-time representation. -/
@[simp] theorem spatialPartCLM_apply (x : Euclidean (d + 1)) :
    spatialPartCLM x = spatialPart x := rfl
/-- The time basis vector has no spatial part in the fixed-time representation. -/
@[simp] theorem spatialPart_single_zero :
    spatialPart (EuclideanSpace.single (0 : Fin (d + 1)) (1 : ℝ)) = 0 := by
  ext i
  simp [spatialPart, EuclideanSpace.single]
/-- Spatial basis vectors are preserved by the fixed-time spatial projection. -/
@[simp] theorem spatialPart_single_succ (i : Fin d) :
    spatialPart (EuclideanSpace.single i.succ (1 : ℝ)) = EuclideanSpace.single i 1 := by
  ext j
  simp [spatialPart, EuclideanSpace.single]
/-- The original two-time phase restricted to `s = t-r`. This is the spatial
term in `app:ch_regular_base:eq:fixed-time-representation`. -/
def elapsedSpatialPhase (Ψ : TwoTimePhase d) (r : ℝ) (p : ℝ × Euclidean d)
    (η : Euclidean d) : ℝ := Ψ p.1 (p.1 - r) p.2 η
/-- The derivative along simultaneous motion of both times, namely
`(∂t + ∂s) Ψ(t,t-r,y,η)`, in the fixed-time representation. -/
def elapsedTimeDerivative (Ψ : TwoTimePhase d) (r : ℝ)
    (p : ℝ × Euclidean d) (η : Euclidean d) : ℝ :=
  fderiv ℝ (fun q ↦ elapsedSpatialPhase Ψ r q η) p (1, 0)

/-- The time derivative of the literal elapsed phase, with both original
times differentiated. Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedPhase_output_zero (Ψ : TwoTimePhase d) (r : ℝ)
    (x ξ : Euclidean (d + 1))
    (h : DifferentiableAt ℝ (fun p ↦ elapsedSpatialPhase Ψ r p (spatialPart ξ))
      (x 0, spatialPart x)) :
    partialDeriv (fun z ↦ elapsedPhase Ψ r z ξ) x 0 =
      ξ 0 + elapsedTimeDerivative Ψ r (x 0, spatialPart x) (spatialPart ξ) := by
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt.prodMk
    spatialPartCLM.hasFDerivAt (x := x)
  have ht := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt (x := x)).sub_const r).mul_const (ξ 0)
  have hd := ht.fun_add (h.hasFDerivAt.comp x hc)
  simp only [EuclideanSpace.coe_proj, spatialPartCLM_apply, Function.comp_def] at hd
  change (fderiv ℝ (fun z ↦ (z 0 - r) * ξ 0 +
    elapsedSpatialPhase Ψ r (z 0, spatialPart z) (spatialPart ξ)) x)
    (EuclideanSpace.single 0 1) = _
  rw [hd.fderiv]
  simp [elapsedTimeDerivative, EuclideanSpace.single]

/-- The spatial output derivatives of the literal elapsed phase.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedPhase_output_succ (Ψ : TwoTimePhase d) (r : ℝ)
    (x ξ : Euclidean (d + 1)) (i : Fin d)
    (h : DifferentiableAt ℝ (fun p ↦ elapsedSpatialPhase Ψ r p (spatialPart ξ))
      (x 0, spatialPart x)) :
    partialDeriv (fun z ↦ elapsedPhase Ψ r z ξ) x i.succ =
      partialDeriv (fun y ↦ Ψ (x 0) (x 0 - r) y (spatialPart ξ)) (spatialPart x) i := by
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt.prodMk
    spatialPartCLM.hasFDerivAt (x := x)
  have ht := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt (x := x)).sub_const r).mul_const (ξ 0)
  have hd := ht.fun_add (h.hasFDerivAt.comp x hc)
  simp only [EuclideanSpace.coe_proj, spatialPartCLM_apply, Function.comp_def] at hd
  have hs := (h.hasFDerivAt.comp (spatialPart x)
    (hasFDerivAt_prodMk_right (x 0) (spatialPart x))).fderiv
  change (fderiv ℝ (fun z ↦ (z 0 - r) * ξ 0 +
    elapsedSpatialPhase Ψ r (z 0, spatialPart z) (spatialPart ξ)) x)
    (EuclideanSpace.single i.succ 1) = _
  rw [hd.fderiv]
  change _ = (fderiv ℝ (fun y ↦ elapsedSpatialPhase Ψ r (x 0, y) (spatialPart ξ))
    (spatialPart x)) (EuclideanSpace.single i 1)
  simp only [Function.comp_def] at hs
  rw [hs]
  simp [EuclideanSpace.single]

/-- The full triangular spacetime mixed matrix from the original spatial
phase. Only local differentiability in spatial frequency is used; the
upper-right row may be large. Consumer: the graph geometry in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem mixedPhaseMatrix_elapsedPhase (Ψ : TwoTimePhase d) (r : ℝ)
    (x ξ : Euclidean (d + 1)) {D : Set (Euclidean d)}
    (hD : IsOpen D) (hξ : spatialPart ξ ∈ D)
    (hx : ∀ η ∈ D, DifferentiableAt ℝ (fun p ↦ elapsedSpatialPhase Ψ r p η)
      (x 0, spatialPart x))
    (ht : DifferentiableAt ℝ (elapsedTimeDerivative Ψ r (x 0, spatialPart x))
      (spatialPart ξ))
    (hy : ∀ i : Fin d, DifferentiableAt ℝ
      (fun η ↦ partialDeriv (fun y ↦ Ψ (x 0) (x 0 - r) y η) (spatialPart x) i)
      (spatialPart ξ)) :
    mixedPhaseMatrix (elapsedPhase Ψ r) x ξ =
      fun i j ↦ Fin.cases
        (Fin.cases 1 (fun j ↦ partialDeriv
          (elapsedTimeDerivative Ψ r (x 0, spatialPart x)) (spatialPart ξ) j) j)
        (fun i ↦ Fin.cases 0
          (fun j ↦ mixedPhaseMatrix (Ψ (x 0) (x 0 - r)) (spatialPart x) (spatialPart ξ) i j) j) i := by
  have hn : ∀ᶠ ζ in 𝓝 ξ, spatialPart ζ ∈ D :=
    spatialPartCLM.continuous.continuousAt.eventually (hD.mem_nhds hξ)
  have he₀ : (fun ζ ↦ partialDeriv (fun z ↦ elapsedPhase Ψ r z ζ) x 0) =ᶠ[𝓝 ξ]
      (fun ζ ↦ ζ 0 + elapsedTimeDerivative Ψ r (x 0, spatialPart x) (spatialPart ζ)) := by
    filter_upwards [hn] with ζ hζ
    exact elapsedPhase_output_zero Ψ r x ζ (hx _ hζ)
  have he₁ (i : Fin d) :
      (fun ζ ↦ partialDeriv (fun z ↦ elapsedPhase Ψ r z ζ) x i.succ) =ᶠ[𝓝 ξ]
      (fun ζ ↦ partialDeriv (fun y ↦ Ψ (x 0) (x 0 - r) y (spatialPart ζ)) (spatialPart x) i) := by
    filter_upwards [hn] with ζ hζ
    exact elapsedPhase_output_succ Ψ r x ζ i (hx _ hζ)
  have ht' := ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt (x := ξ)).fun_add
    (ht.hasFDerivAt.comp ξ spatialPartCLM.hasFDerivAt)
  simp only [EuclideanSpace.coe_proj, Function.comp_def] at ht'
  have hy' (i : Fin d) := (hy i).hasFDerivAt.comp ξ spatialPartCLM.hasFDerivAt
  simp only [Function.comp_def] at hy'
  ext i j
  induction i using Fin.cases with
  | zero =>
      change (fderiv ℝ _ ξ) (EuclideanSpace.single j 1) = _
      rw [he₀.fderiv_eq, ht'.fderiv]
      induction j using Fin.cases <;>
        simp [partialDeriv, EuclideanSpace.single]
  | succ i =>
      change (fderiv ℝ _ ξ) (EuclideanSpace.single j 1) = _
      rw [(he₁ i).fderiv_eq, (hy' i).fderiv]
      induction j using Fin.cases <;>
        simp [mixedPhaseMatrix, partialDeriv, EuclideanSpace.single]

/-- Primitive joint regularity of the original two-time phase gives
regularity after restricting to `s = t-r`, without adding regularity at
spatial frequency zero. Source: the fixed-time representation. -/
theorem contDiffAt_elapsedSpatialPhase (Ψ : TwoTimePhase d) (r : ℝ)
    {p : (ℝ × Euclidean d) × Euclidean d} {k : ℕ∞ω}
    (h : ContDiffAt ℝ k (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ q.1.1 q.1.2 q.2.1 q.2.2) ((p.1.1, p.1.1-r), (p.1.2, p.2))) :
    ContDiffAt ℝ k (Function.uncurry (elapsedSpatialPhase Ψ r)) p := by
  exact h.comp p ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.fst.sub contDiffAt_const)).prodMk
    (contDiffAt_fst.snd.prodMk contDiffAt_snd))

/-- Local spatial-frequency regularity suffices for the elapsed spacetime
phase. Consumer: the supported integer Sobolev API for the retarded kernel. -/
theorem contDiffAt_elapsedPhase (Ψ : TwoTimePhase d) (r : ℝ)
    {x ξ : Euclidean (d + 1)} {k : ℕ∞ω}
    (h : ContDiffAt ℝ k (Function.uncurry (elapsedSpatialPhase Ψ r))
      ((x 0, spatialPart x), spatialPart ξ)) :
    ContDiffAt ℝ k (Function.uncurry (elapsedPhase Ψ r)) (x, ξ) := by
  have hc : ContDiff ℝ k (fun z : Euclidean (d + 1) ↦ z 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff
  exact ((hc.contDiffAt.comp _ contDiffAt_fst).sub contDiffAt_const |>.mul
    (hc.contDiffAt.comp _ contDiffAt_snd)).add
      (h.comp (x, ξ) (f := fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦ ((p.1 0, spatialPart p.1), spatialPart p.2)) (((hc.contDiffAt.comp _ contDiffAt_fst).prodMk
        (spatialPartCLM.contDiff.contDiffAt.comp _ contDiffAt_fst)).prodMk
        (spatialPartCLM.contDiff.contDiffAt.comp _ contDiffAt_snd)))

/-- Joint regularity discharges every differentiability input of the
triangular mixed formula. Consumer: mixed invertibility in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem mixedPhaseMatrix_elapsedPhase_of_contDiff (Ψ : TwoTimePhase d) (r : ℝ)
    (x ξ : Euclidean (d + 1)) {D : Set (Euclidean d)}
    (hD : IsOpen D) (hξ : spatialPart ξ ∈ D)
    (h : ∀ η ∈ D, ContDiffAt ℝ ∞ (Function.uncurry (elapsedSpatialPhase Ψ r))
      ((x 0, spatialPart x), η)) :
    mixedPhaseMatrix (elapsedPhase Ψ r) x ξ =
      fun i j ↦ Fin.cases
        (Fin.cases 1 (fun j ↦ partialDeriv
          (elapsedTimeDerivative Ψ r (x 0, spatialPart x)) (spatialPart ξ) j) j)
        (fun i ↦ Fin.cases 0
          (fun j ↦ mixedPhaseMatrix (Ψ (x 0) (x 0 - r)) (spatialPart x) (spatialPart ξ) i j) j) i := by
  apply mixedPhaseMatrix_elapsedPhase Ψ r x ξ hD hξ
  · intro η hη
    exact ((h η hη).comp (x 0, spatialPart x) (f := fun p : ℝ × Euclidean d ↦ (p, η)) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  · have hs : ContDiffAt ℝ ∞
        (Function.uncurry (fun η p ↦ elapsedSpatialPhase Ψ r p η))
        (spatialPart ξ, (x 0, spatialPart x)) :=
      (h _ hξ).comp (spatialPart ξ, (x 0, spatialPart x)) (f := Prod.swap) (contDiffAt_snd.prodMk contDiffAt_fst)
    exact ((hs.fderiv (m := ∞) contDiffAt_const (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  · intro i
    have hs : ContDiffAt ℝ ∞
        (Function.uncurry (fun η y ↦ Ψ (x 0) (x 0 - r) y η))
        (spatialPart ξ, spatialPart x) :=
      (h _ hξ).comp (spatialPart ξ, spatialPart x) (f := fun p : Euclidean d × Euclidean d ↦ ((x 0, p.2), p.1)) ((contDiffAt_const.prodMk contDiffAt_snd).prodMk contDiffAt_fst)
    exact ((hs.fderiv (m := ∞) contDiffAt_const (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)

/-- The spacetime determinant is exactly the spatial mixed determinant,
independently of the temporal shear. Consumer: the mixed determinant gap
in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem det_mixedPhaseMatrix_elapsedPhase (Ψ : TwoTimePhase d) (r : ℝ)
    (x ξ : Euclidean (d + 1)) {D : Set (Euclidean d)}
    (hD : IsOpen D) (hξ : spatialPart ξ ∈ D)
    (h : ∀ η ∈ D, ContDiffAt ℝ ∞ (Function.uncurry (elapsedSpatialPhase Ψ r))
      ((x 0, spatialPart x), η)) :
    (mixedPhaseMatrix (elapsedPhase Ψ r) x ξ).det =
      (mixedPhaseMatrix (Ψ (x 0) (x 0 - r)) (spatialPart x) (spatialPart ξ)).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [mixedPhaseMatrix_elapsedPhase_of_contDiff Ψ r x ξ hD hξ h, Matrix.submatrix]
  rfl

private theorem averagedGradient_apply_eq (S : Euclidean (d + 1) → Euclidean (d + 1) → ℝ)
    (x y ξ : Euclidean (d + 1)) (i : Fin (d + 1))
    (hi : IntervalIntegrable (fun θ : ℝ ↦ fderiv ℝ (fun z ↦ S z ξ)
      (y + θ • (x - y))) volume 0 1) :
    averagedGradient S x y ξ i =
      ∫ θ in (0 : ℝ)..1, partialDeriv (fun z ↦ S z ξ) (y + θ • (x - y)) i := by
  have he : inner ℝ (EuclideanSpace.single i 1) (averagedGradient S x y ξ) =
      averagedPhaseDifferential S x y ξ (EuclideanSpace.single i 1) := by
    rw [real_inner_comm, averagedGradient, InnerProductSpace.toDual_symm_apply]
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul,
    averagedPhaseDifferential, ContinuousLinearMap.intervalIntegral_apply hi, partialDeriv] using he

/-- The time coordinate of the averaged gradient is the original temporal
covector plus the average of the two-time derivative along the **full
spacetime** segment. Consumer: whole-image geometry in the retarded kernel. -/
theorem averagedGradient_elapsedPhase_time (Ψ : TwoTimePhase d) (r : ℝ)
    (x y ξ : Euclidean (d + 1))
    (h : ∀ θ ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ
      (fun p ↦ elapsedSpatialPhase Ψ r p (spatialPart ξ))
      ((y + θ • (x - y)) 0, spatialPart (y + θ • (x - y))))
    (hi : IntervalIntegrable (fun θ : ℝ ↦ fderiv ℝ (fun z ↦ elapsedPhase Ψ r z ξ)
      (y + θ • (x - y))) volume 0 1)
    (ht : IntervalIntegrable (fun θ : ℝ ↦ elapsedTimeDerivative Ψ r
      ((y + θ • (x - y)) 0, spatialPart (y + θ • (x - y))) (spatialPart ξ)) volume 0 1) :
    averagedGradient (elapsedPhase Ψ r) x y ξ 0 = ξ 0 +
      ∫ θ in (0 : ℝ)..1, elapsedTimeDerivative Ψ r
        ((y + θ • (x - y)) 0, spatialPart (y + θ • (x - y))) (spatialPart ξ) := by
  rw [averagedGradient_apply_eq _ _ _ _ _ hi]
  calc
    _ = ∫ θ in (0 : ℝ)..1, ξ 0 + elapsedTimeDerivative Ψ r
        ((y + θ • (x - y)) 0, spatialPart (y + θ • (x - y))) (spatialPart ξ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact elapsedPhase_output_zero Ψ r _ ξ (h θ hθ)
    _ = _ := by rw [intervalIntegral.integral_add intervalIntegrable_const ht]; simp

/-- The spatial averaged gradient follows both time and space along the
full spacetime segment. It is not a fixed-time spatial average. Consumer:
whole-image injectivity in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem averagedGradient_elapsedPhase_spatial (Ψ : TwoTimePhase d) (r : ℝ)
    (x y ξ : Euclidean (d + 1)) (i : Fin d)
    (h : ∀ θ ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ
      (fun p ↦ elapsedSpatialPhase Ψ r p (spatialPart ξ))
      ((y + θ • (x - y)) 0, spatialPart (y + θ • (x - y))))
    (hi : IntervalIntegrable (fun θ : ℝ ↦ fderiv ℝ (fun z ↦ elapsedPhase Ψ r z ξ)
      (y + θ • (x - y))) volume 0 1) :
    averagedGradient (elapsedPhase Ψ r) x y ξ i.succ =
      ∫ θ in (0 : ℝ)..1, partialDeriv
        (fun v ↦ Ψ ((y + θ • (x - y)) 0) ((y + θ • (x - y)) 0 - r) v (spatialPart ξ))
        (spatialPart (y + θ • (x - y))) i := by
  rw [averagedGradient_apply_eq _ _ _ _ _ hi]
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact elapsedPhase_output_succ Ψ r _ ξ i (h θ hθ)
end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
