module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Composition

/-! The explicit finite circular-bending construction. -/

@[expose] public noncomputable section

namespace JanetCartan.ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: The standard inclusion into one more Euclidean
coordinate. -/
def coordinateInclusion (m : ℕ) : Euclidean m →L[ℝ] Euclidean (m + 1) :=
  (appendIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.comp bendingInclusion

/-- Proposition `app:ch_seed:prop:seed-analytic`: The standard inclusion preserves the inner
product. -/
theorem coordinateInclusion_inner (m : ℕ) (u w : Euclidean m) :
    inner ℝ (coordinateInclusion m u) (coordinateInclusion m w) = inner ℝ u w := by
  change inner ℝ (appendIsometry m (bendingInclusion u))
    (appendIsometry m (bendingInclusion w)) = _
  rw [(appendIsometry m).inner_map_map]
  simp [WithLp.prod_inner_apply]

/-- Proposition `app:ch_seed:prop:seed-analytic`: Include the original tangent space after a finite
number of bendings. -/
def initialInclusion (n : ℕ) : (k : ℕ) → Euclidean n →L[ℝ] Euclidean (n + k)
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (coordinateInclusion (n + k)).comp (initialInclusion n k)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The original tangent inclusion preserves inner
products. -/
theorem initialInclusion_inner (n k : ℕ) (u w : Euclidean n) :
    inner ℝ (initialInclusion n k u) (initialInclusion n k w) = inner ℝ u w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change inner ℝ (coordinateInclusion (n + k) (initialInclusion n k u))
      (coordinateInclusion (n + k) (initialInclusion n k w)) = _
    rw [coordinateInclusion_inner, ih]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The original tangent inclusion preserves unit
directions. -/
theorem initialInclusion_norm (n k : ℕ) (u : Euclidean n) :
    ‖initialInclusion n k u‖ = ‖u‖ :=
  ((initialInclusion n k).toLinearMap.isometryOfInner (initialInclusion_inner n k)).norm_map u

/-- Proposition `app:ch_seed:prop:seed-analytic`: The explicit circular bending in Euclidean
coordinates. -/
def coordinateBending {m : ℕ} (v : Euclidean m) (ν : ℝ) :
    Euclidean m → Euclidean (m + 1) := appendIsometry m ∘ circularBending v ν

/-- Proposition `app:ch_seed:prop:seed-analytic`: The coordinate bending is globally analytic. -/
theorem coordinateBending_analyticOnNhd {m : ℕ} (v : Euclidean m) (ν : ℝ) :
    AnalyticOnNhd ℝ (coordinateBending v ν) Set.univ := by
  intro y _
  exact ((appendIsometry m).toContinuousLinearEquiv.analyticAt _).comp
    (circularBending_analyticAt v ν y)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The coordinate bending is smooth to every order.
-/
theorem coordinateBending_contDiff {m : ℕ} (v : Euclidean m) (ν : ℝ)
    (r : WithTop ℕ∞) : ContDiff ℝ r (coordinateBending v ν) :=
  (coordinateBending_analyticOnNhd v ν).contDiff

/-- Proposition `app:ch_seed:prop:seed-analytic`: Each coordinate bending fixes the center. -/
@[simp] theorem coordinateBending_zero {m : ℕ} (v : Euclidean m) (ν : ℝ) :
    coordinateBending v ν 0 = 0 := by simp [coordinateBending]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The differential of the coordinate bending. -/
theorem coordinateBending_fderiv {m : ℕ} (v : Euclidean m) {ν : ℝ} (hν : ν ≠ 0)
    (y : Euclidean m) : fderiv ℝ (coordinateBending v ν) y =
      (appendIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (circularBending v ν) y) := by
  exact ((appendIsometry m).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp y
    (circularBending_hasFDerivAt v hν y)).fderiv.trans (by rw [circularBending_fderiv v hν])

/-- Proposition `app:ch_seed:prop:seed-analytic`: The coordinate bending has isometric differential.
-/
theorem coordinateBending_fderiv_inner {m : ℕ} (v : Euclidean m) (hv : ‖v‖ = 1)
    {ν : ℝ} (hν : ν ≠ 0) (y u w : Euclidean m) :
    inner ℝ (fderiv ℝ (coordinateBending v ν) y u)
      (fderiv ℝ (coordinateBending v ν) y w) = inner ℝ u w := by
  rw [coordinateBending_fderiv v hν]
  change inner ℝ (appendIsometry m (fderiv ℝ (circularBending v ν) y u))
    (appendIsometry m (fderiv ℝ (circularBending v ν) y w)) = _
  rw [(appendIsometry m).inner_map_map, circularBending_fderiv_inner v hv hν]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The first center jet is the standard inclusion. -/
theorem coordinateBending_fderiv_zero {m : ℕ} (v : Euclidean m) {ν : ℝ} (hν : ν ≠ 0) :
    fderiv ℝ (coordinateBending v ν) 0 = coordinateInclusion m := by
  rw [coordinateBending_fderiv v hν, circularBending_fderiv_zero v hν]
  rfl

/-- Proposition `app:ch_seed:prop:seed-analytic`: The explicit finite composition, with directions
lifted from the original tangent space. -/
def iteratedBending {n : ℕ} (v : ℕ → Euclidean n) (ν : ℝ) (k : ℕ) :
    Euclidean n → Euclidean (n + k) :=
  successiveComposition (fun j ↦ n + j)
    (fun j ↦ coordinateBending (initialInclusion n j (v j)) ν) k

/-- Proposition `app:ch_seed:prop:seed-analytic`: The explicit composition fixes the center. -/
@[simp] theorem iteratedBending_zero {n : ℕ} (v : ℕ → Euclidean n) (ν : ℝ) (k : ℕ) :
    iteratedBending v ν k 0 = 0 :=
  successiveComposition_zero k (fun _ _ ↦ coordinateBending_zero _ _)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The explicit composition is globally analytic. -/
theorem iteratedBending_analyticOnNhd {n : ℕ} (v : ℕ → Euclidean n) (ν : ℝ) (k : ℕ) :
    AnalyticOnNhd ℝ (iteratedBending v ν k) Set.univ :=
  analyticOnNhd_successiveComposition k (fun _ _ ↦ coordinateBending_analyticOnNhd _ _)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The explicit composition is smooth to every order.
-/
theorem iteratedBending_contDiff {n : ℕ} (v : ℕ → Euclidean n) (ν : ℝ) (k : ℕ)
    (r : WithTop ℕ∞) : ContDiff ℝ r (iteratedBending v ν k) :=
  (iteratedBending_analyticOnNhd v ν k).contDiff

/-- Proposition `app:ch_seed:prop:seed-analytic`: The first center jet of the composition is the
original tangent inclusion. -/
theorem iteratedBending_fderiv_zero {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) :
    fderiv ℝ (iteratedBending v ν k) 0 = initialInclusion n k := by
  induction k with
  | zero => simp [iteratedBending, successiveComposition, initialInclusion]
  | succ k ih =>
    change fderiv ℝ (coordinateBending (initialInclusion n k (v k)) ν ∘ iteratedBending v ν k) 0 = _
    rw [fderiv_comp 0 ((coordinateBending_contDiff _ _ 1).differentiable one_ne_zero _)
      ((iteratedBending_contDiff _ _ _ 1).differentiable one_ne_zero _),
      iteratedBending_zero, coordinateBending_fderiv_zero _ hν, ih]
    rfl

/-- Proposition `app:ch_seed:prop:seed-analytic`: Unit bending directions give exactly the flat
metric everywhere. -/
theorem iteratedBending_inducedMetric {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) (hv : ∀ j < k, ‖v j‖ = 1) (x : Euclidean n) :
    inducedMetric (iteratedBending v ν k) x = 1 := by
  apply inducedMetric_successiveComposition (d := fun j ↦ n + j)
    (step := fun j ↦ coordinateBending (initialInclusion n j (v j)) ν) k
    (fun j _ ↦ (coordinateBending_contDiff _ _ 1).differentiable one_ne_zero)
  intro j hj y u w
  exact coordinateBending_fderiv_inner _ ((initialInclusion_norm n j _).trans (hv j hj)) hν y u w
end JanetCartan.ReferenceConstruction
