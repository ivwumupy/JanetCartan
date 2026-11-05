module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Iteration
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Jets

/-! The actual center second fundamental forms of the explicit bending composition. -/

@[expose] public noncomputable section

namespace JanetCartan.ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: The new unit normal in Euclidean coordinates. -/
def newNormal (m : ℕ) : Euclidean (m + 1) := appendIsometry m bendingNormal

/-- Proposition `app:ch_seed:prop:seed-analytic`: The new normal is orthogonal to all preceding
coordinates. -/
theorem inner_coordinateInclusion_newNormal (m : ℕ) (u : Euclidean m) :
    inner ℝ (coordinateInclusion m u) (newNormal m) = 0 := by
  change inner ℝ (appendIsometry m (bendingInclusion u))
    (appendIsometry m bendingNormal) = 0
  rw [(appendIsometry m).inner_map_map]
  simp [bendingNormal, WithLp.prod_inner_apply]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The prescribed center second jet, retaining old
forms and adding one rank-one form at each step. -/
def centerSecondJet {n : ℕ} (v : ℕ → Euclidean n) (ν : ℝ) :
    (k : ℕ) → Euclidean n → Euclidean n → Euclidean (n + k)
  | 0, _, _ => 0
  | k + 1, u, w => coordinateInclusion (n + k) (centerSecondJet v ν k u w) +
      (ν * inner ℝ (v k) u * inner ℝ (v k) w) • newNormal (n + k)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The second jet of the explicit composition
satisfies the bending recurrence. -/
theorem iteratedBending_secondFDeriv_succ {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) (u w : Euclidean n) :
    fderiv ℝ (fderiv ℝ (iteratedBending v ν (k + 1))) 0 u w =
      coordinateInclusion (n + k) (fderiv ℝ (fderiv ℝ (iteratedBending v ν k)) 0 u w) +
        (ν * inner ℝ (v k) u * inner ℝ (v k) w) • newNormal (n + k) := by
  change fderiv ℝ (fderiv ℝ
    ((appendIsometry (n + k)).toContinuousLinearEquiv.toContinuousLinearMap ∘
      (circularBending (initialInclusion n k (v k)) ν ∘ iteratedBending v ν k))) 0 u w = _
  rw [secondFDeriv_linear_comp_apply
    ((circularBending_contDiff _ _ 2).comp (iteratedBending_contDiff _ _ _ 2)),
    secondFDeriv_circularBending_comp_zero (iteratedBending_contDiff _ _ _ 2)
      (iteratedBending_zero v ν k) _ hν,
    iteratedBending_fderiv_zero v hν k, initialInclusion_inner, initialInclusion_inner]
  simp only [map_add, map_smul]
  rfl

/-- Proposition `app:ch_seed:prop:seed-analytic`: The second derivative of the explicit composition
equals its prescribed center jet. -/
theorem iteratedBending_secondFDeriv_zero {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) (u w : Euclidean n) :
    fderiv ℝ (fderiv ℝ (iteratedBending v ν k)) 0 u w = centerSecondJet v ν k u w := by
  induction k with
  | zero =>
    have h : fderiv ℝ (iteratedBending v ν 0) = fun _ ↦ ContinuousLinearMap.id ℝ _ := by
      ext x z i
      simp [iteratedBending, successiveComposition]
    rw [h]
    simp [centerSecondJet]
  | succ k ih => rw [iteratedBending_secondFDeriv_succ v hν, ih]; rfl

/-- Proposition `app:ch_seed:prop:seed-analytic`: The prescribed second jet is orthogonal to the
original tangent space. -/
theorem inner_initialInclusion_centerSecondJet {n : ℕ} (v : ℕ → Euclidean n)
    (ν : ℝ) (k : ℕ) (t u w : Euclidean n) :
    inner ℝ (initialInclusion n k t) (centerSecondJet v ν k u w) = 0 := by
  induction k with
  | zero => simp [centerSecondJet]
  | succ k ih =>
    change inner ℝ (coordinateInclusion (n + k) (initialInclusion n k t))
      (coordinateInclusion (n + k) (centerSecondJet v ν k u w) +
        (ν * inner ℝ (v k) u * inner ℝ (v k) w) • newNormal (n + k)) = 0
    rw [inner_add_right, real_inner_smul_right, coordinateInclusion_inner,
      inner_coordinateInclusion_newNormal, ih, mul_zero, add_zero]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The prescribed center jet is in the actual normal
space. -/
theorem centerSecondJet_mem_normalSpace {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) (u w : Euclidean n) :
    centerSecondJet v ν k u w ∈ normalSpace (iteratedBending v ν k) 0 := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  change inner ℝ (fderiv ℝ (iteratedBending v ν k) 0 t) _ = 0
  rw [iteratedBending_fderiv_zero v hν]
  exact inner_initialInclusion_centerSecondJet v ν k t u w

/-- Proposition `app:ch_seed:prop:seed-analytic`: The actual second fundamental form equals the
prescribed center jet. -/
theorem iteratedBending_secondFundamentalForm_zero {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) (i j : Fin n) :
    secondFundamentalForm (iteratedBending v ν k) 0 i j =
      centerSecondJet v ν k (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hd : Differentiable ℝ (fderiv ℝ (iteratedBending v ν k)) :=
    ((iteratedBending_contDiff v ν k 2).fderiv_right
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable one_ne_zero
  have h := (hd 0).hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single j 1) 0)
  unfold secondFundamentalForm partialDeriv
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
  rw [iteratedBending_secondFDeriv_zero v hν]
  exact Submodule.starProjection_eq_self_iff.mpr (centerSecondJet_mem_normalSpace v hν k _ _)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The ordered normal directions, carried through the
later standard inclusions. -/
def centerNormal (n : ℕ) : (k : ℕ) → Fin k → Euclidean (n + k)
  | 0 => Fin.elim0
  | k + 1 => Fin.lastCases (newNormal (n + k))
      (fun a ↦ coordinateInclusion (n + k) (centerNormal n k a))

/-- Proposition `app:ch_seed:prop:seed-analytic`: Each new normal has unit length. -/
theorem inner_newNormal_self (m : ℕ) : inner ℝ (newNormal m) (newNormal m) = 1 := by
  unfold newNormal
  rw [(appendIsometry m).inner_map_map]
  simp [bendingNormal]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The component of the center second jet in each
normal direction is its prescribed rank-one form. -/
theorem inner_centerNormal_centerSecondJet {n : ℕ} (v : ℕ → Euclidean n)
    (ν : ℝ) (k : ℕ) (a : Fin k) (u w : Euclidean n) :
    inner ℝ (centerNormal n k a) (centerSecondJet v ν k u w) =
      ν * inner ℝ (v a) u * inner ℝ (v a) w := by
  induction k with
  | zero => exact Fin.elim0 a
  | succ k ih =>
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · simp only [centerNormal, Fin.lastCases_last, centerSecondJet, inner_add_right,
        real_inner_smul_right, inner_newNormal_self, mul_one, Fin.val_last]
      rw [real_inner_comm, inner_coordinateInclusion_newNormal, zero_add]
    · simp only [centerNormal, Fin.lastCases_castSucc, centerSecondJet, inner_add_right,
        real_inner_smul_right, coordinateInclusion_inner, inner_coordinateInclusion_newNormal,
        mul_zero, add_zero, Fin.val_castSucc]
      exact ih b

/-- Proposition `app:ch_seed:prop:seed-analytic`: The center normal directions are orthonormal. -/
theorem centerNormal_orthonormal (n k : ℕ) : Orthonormal ℝ (centerNormal n k) := by
  rw [orthonormal_iff_ite]
  intro a b
  induction k with
  | zero => exact Fin.elim0 a
  | succ k ih =>
    refine Fin.lastCases ?_ (fun a' ↦ ?_) a
    · refine Fin.lastCases ?_ (fun b' ↦ ?_) b
      · simp only [centerNormal, Fin.lastCases_last, ite_true]
        exact inner_newNormal_self _
      · simp only [centerNormal, Fin.lastCases_last, Fin.lastCases_castSucc,
          (Fin.castSucc_ne_last b').symm, ite_false]
        rw [real_inner_comm, inner_coordinateInclusion_newNormal]
    · refine Fin.lastCases ?_ (fun b' ↦ ?_) b
      · simp [centerNormal, inner_coordinateInclusion_newNormal]
      · simpa [centerNormal, coordinateInclusion_inner] using ih a' b'

/-- Proposition `app:ch_seed:prop:seed-analytic`: Every center normal is orthogonal to the original
tangent space. -/
theorem inner_initialInclusion_centerNormal (n k : ℕ) (t : Euclidean n) (a : Fin k) :
    inner ℝ (initialInclusion n k t) (centerNormal n k a) = 0 := by
  induction k with
  | zero => exact Fin.elim0 a
  | succ k ih =>
    refine Fin.lastCases ?_ (fun a' ↦ ?_) a
    · simp [centerNormal, initialInclusion, inner_coordinateInclusion_newNormal]
    · simpa [centerNormal, initialInclusion, coordinateInclusion_inner] using ih a'

/-- Proposition `app:ch_seed:prop:seed-analytic`: Each center normal belongs to the actual normal
space. -/
theorem centerNormal_mem_normalSpace {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) (a : Fin k) :
    centerNormal n k a ∈ normalSpace (iteratedBending v ν k) 0 := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  change inner ℝ (fderiv ℝ (iteratedBending v ν k) 0 t) _ = 0
  rw [iteratedBending_fderiv_zero v hν]
  exact inner_initialInclusion_centerNormal n k t a

/-- Proposition `app:ch_seed:prop:seed-analytic`: The center normal directions span the entire
actual normal space. -/
theorem normalSpace_iteratedBending_zero {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) :
    normalSpace (iteratedBending v ν k) 0 =
      Submodule.span ℝ (Set.range (centerNormal n k)) := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact centerNormal_mem_normalSpace v hν k a
  · rw [finrank_span_eq_card (centerNormal_orthonormal n k).linearIndependent, Fintype.card_fin]
    unfold normalSpace
    rw [iteratedBending_fderiv_zero v hν]
    symm
    apply Submodule.finrank_add_finrank_orthogonal'
    have hinj : Function.Injective (initialInclusion n k).toLinearMap :=
      ((initialInclusion n k).toLinearMap.isometryOfInner (initialInclusion_inner n k)).injective
    rw [LinearMap.finrank_range_of_inj hinj]
    simp

/-- Proposition `app:ch_seed:prop:seed-analytic`: Normal vectors are determined by their components
in the center normal frame. -/
theorem eq_of_inner_centerNormal_eq {n : ℕ} (v : ℕ → Euclidean n)
    {ν : ℝ} (hν : ν ≠ 0) (k : ℕ) {z w : Euclidean (n + k)}
    (hz : z ∈ normalSpace (iteratedBending v ν k) 0)
    (hw : w ∈ normalSpace (iteratedBending v ν k) 0)
    (heq : ∀ a, inner ℝ (centerNormal n k a) z = inner ℝ (centerNormal n k a) w) : z = w := by
  have hmem := (normalSpace (iteratedBending v ν k) 0).sub_mem hz hw
  rw [normalSpace_iteratedBending_zero v hν k] at hmem
  have horth : ∀ t ∈ Submodule.span ℝ (Set.range (centerNormal n k)),
      inner ℝ t (z - w) = 0 := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, rfl⟩ := ht
      rw [inner_sub_right, heq a, sub_self]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [real_inner_smul_left, ha, mul_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (horth _ hmem))

end JanetCartan.ReferenceConstruction
