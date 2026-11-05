module
public import JanetCartan.Analysis.Matrix.InverseBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Basic
/-!
# Smooth complement inverses on a common interval

For `app:ch_regular_base:eq:complement-inverse`, the rank-one completion is
smooth in the original matrices, nullvectors and spectral displacement. Its
nonsingularity at the root gives a common interval and a positive determinant
gap on every compact family. These results construct the inverse; they do not
assume an inverse or its norm. The quantitative coefficient-family bounds are
separate from this compact-family existence argument.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι] {s : Set E} {m : ℕ∞ω}

omit [DecidableEq ι] in
private theorem matrix_contDiffOn_of_entries {f : E → Matrix ι ι ℝ}
    (hf : ∀ i j, ContDiffOn ℝ m (fun x ↦ f x i j) s) : ContDiffOn ℝ m f s :=
by
  let L : (ι × ι → ℝ) ≃ₗ[ℝ] Matrix ι ι ℝ :=
    { toFun := fun g i j ↦ g (i, j)
      invFun := fun B ij ↦ B ij.1 ij.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact L.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr fun ij ↦ hf ij.1 ij.2)

omit [DecidableEq ι] in
/-- Primitive entrywise smoothness gives Frobenius smoothness of the completion
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem contDiffOn_pencilCompletion {H A : E → Matrix ι ι ℝ} {k l : E → ι → ℝ}
    {e : E → ℝ} (hH : ∀ i j, ContDiffOn ℝ m (fun x ↦ H x i j) s)
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s)
    (hk : ContDiffOn ℝ m k s) (hl : ContDiffOn ℝ m l s) (he : ContDiffOn ℝ m e s) :
    ContDiffOn ℝ m (fun x ↦ pencilCompletion (H x) (A x) (k x) (l x) (e x)) s := by
  apply matrix_contDiffOn_of_entries
  intro i j
  simp only [pencilCompletion, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, mulVec, vecMul, dotProduct]
  exact ((hH i j).add (he.mul (hA i j))).add
    ((contDiffOn_const.sub he).mul
      ((ContDiffOn.sum (fun a _ ↦ (hA i a).mul (contDiffOn_pi.mp hk a))).mul
        (ContDiffOn.sum (fun a _ ↦ (contDiffOn_pi.mp hl a).mul (hA a j)))))

/-- Smooth dependence of the original oblique projection
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem contDiffOn_complementProjection {A : E → Matrix ι ι ℝ} {k l : E → ι → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s)
    (hk : ContDiffOn ℝ m k s) (hl : ContDiffOn ℝ m l s) :
    ContDiffOn ℝ m (fun x ↦ complementProjection (A x) (k x) (l x)) s := by
  apply matrix_contDiffOn_of_entries
  intro i j
  simp only [complementProjection, Matrix.sub_apply, vecMulVec_apply, mulVec, dotProduct]
  exact contDiffOn_const.sub
    ((ContDiffOn.sum (fun a _ ↦ (hA i a).mul (contDiffOn_pi.mp hk a))).mul
      (contDiffOn_pi.mp hl j))

/-- Joint smoothness of the constructed complement inverse wherever its
completion is nonsingular (`app:ch_regular_base:eq:complement-inverse`). -/
theorem contDiffOn_complementInverse {H A : E → Matrix ι ι ℝ} {k l : E → ι → ℝ}
    {e : E → ℝ} (hH : ∀ i j, ContDiffOn ℝ m (fun x ↦ H x i j) s)
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s)
    (hk : ContDiffOn ℝ m k s) (hl : ContDiffOn ℝ m l s) (he : ContDiffOn ℝ m e s)
    (hd : ∀ x ∈ s, (pencilCompletion (H x) (A x) (k x) (l x) (e x)).det ≠ 0) :
    ContDiffOn ℝ m (fun x ↦ complementInverse (H x) (A x) (k x) (l x) (e x)) s :=
  (contDiffOn_matrix_inv (contDiffOn_pencilCompletion hH hA hk hl he)
    (fun x hx ↦ (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (hd x hx)))).mul (contDiffOn_complementProjection hA hk hl)

section Compact
variable {X : Type*} [TopologicalSpace X]

/-- The original algebraic inputs on a compact family produce a common closed
spectral interval and a positive completion determinant gap
(`app:ch_regular_base:lem:characteristic-kernel`). No gap for the completion
is assumed. -/
theorem exists_uniform_completion_gap (H A : X → Matrix ι ι ℝ) (k l : X → ι → ℝ)
    (hH : Continuous H) (hA : Continuous A) (hk : Continuous k) (hl : Continuous l)
    {K : Set X} (hK : IsCompact K)
    (hleft : ∀ x ∈ K, l x ᵥ* H x = 0)
    (hnorm : ∀ x ∈ K, l x ⬝ᵥ (A x *ᵥ k x) = 1)
    (hker : ∀ x ∈ K, ∀ v, H x *ᵥ v = 0 → ∃ c : ℝ, v = c • k x) :
    ∃ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ e : ℝ, |e| ≤ ε →
      δ ≤ |(pencilCompletion (H x) (A x) (k x) (l x) e).det| := by
  have hc : Continuous (fun p : X × ℝ ↦ pencilCompletion (H p.1) (A p.1)
      (k p.1) (l p.1) p.2) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [pencilCompletion, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      vecMulVec_apply, mulVec, vecMul, dotProduct]
    fun_prop
  let U : Set (X × ℝ) := {p | (pencilCompletion (H p.1) (A p.1) (k p.1) (l p.1) p.2).det ≠ 0}
  have hopen : IsOpen U := (isClosed_eq hc.matrix_det continuous_const).isOpen_compl
  have hsub : K ×ˢ {0} ⊆ U := by
    rintro ⟨x, e⟩ ⟨hx, he⟩
    have he0 : e = 0 := he
    subst e
    exact pencilCompletion_det_ne_zero (hleft x hx) (hnorm x hx) (hker x hx)
  obtain ⟨u, v, _, hv, huK, hv0, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hopen hsub
  obtain ⟨R, hR, hRv⟩ := Metric.isOpen_iff.mp hv 0 (hv0 rfl)
  have hnonzero : ∀ p ∈ K ×ˢ Metric.closedBall (0 : ℝ) (R / 2),
      (pencilCompletion (H p.1) (A p.1) (k p.1) (l p.1) p.2).det ≠ 0 := by
    intro p hp
    apply huv
    refine ⟨huK hp.1, hRv ?_⟩
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hp.2).trans_lt (by linarith)
  obtain ⟨δ, hδ, hbound⟩ := (hK.prod (isCompact_closedBall (0 : ℝ) (R / 2))).exists_forall_le'
    hc.matrix_det.abs.continuousOn (fun p hp ↦ abs_pos.mpr (hnonzero p hp))
  refine ⟨R / 2, half_pos hR, δ, hδ, ?_⟩
  intro x hx e he
  exact hbound (x, e) ⟨hx, by simpa [Metric.mem_closedBall, Real.dist_eq] using he⟩
end Compact
end JanetCartan.RegularSector.Characteristic
