module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.Profiles
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.InverseBounds

/-!
# Extracting the actual mixed matrix from phase jets

Step 3 of `app:ch_regular_base:thm:actual-calculus`: the endpoint comparison
uses the second joint derivative of the phase with the dummy position retained.
The consumer is `exists_normalizedSeminorm_scalarPrimitive_le_phase`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Filter
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {n : ℕ}

/-- Fixed linear extraction of `S_{xη}` from the second joint derivative,
for `app:ch_regular_base:eq:fio-input`. -/
def mixedPhaseJetExtraction :
    (Point n →L[ℝ] Point n →L[ℝ] ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := Point n →L[ℝ] Point n →L[ℝ] ℝ) (F' := Matrix (Fin n) (Fin n) ℝ) {
    toFun := fun D i j ↦ D (coordinateDirection (.covector, j))
      (coordinateDirection (.left, i))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The actual mixed matrix is a fixed linear image of the second phase jet,
locally on the buffered chart (`app:ch_regular_base:eq:fio-input`). -/
theorem mixedPhaseMatrix_eq_secondJet_on {S : Euclidean n → Euclidean n → ℝ}
    {U : Set (Point n)} (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (fun p : Point n ↦ S p.1.1 p.2) U) :
    Set.EqOn (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2)
      (fun p ↦ mixedPhaseJetExtraction (fderiv ℝ (fderiv ℝ
        (fun p : Point n ↦ S p.1.1 p.2)) p)) U := by
  intro p hp
  let f : Field n ℝ := fun x _ η ↦ S x η
  have hs : ContDiffAt ℝ ∞ (uncurry f) p := hS.contDiffAt (hU.mem_nhds hp)
  ext i j
  have he : uncurry (derivative (.left, i) f) =ᶠ[nhds p]
      (fun q ↦ fderiv ℝ (uncurry f) q (coordinateDirection (.left, i))) := by
    apply eventuallyEq_of_mem (hU.mem_nhds hp)
    intro q hq
    exact derivative_eq_fderiv
      ((hS.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)) _
  have hd := (ContinuousLinearMap.apply ℝ ℝ (coordinateDirection (.left, i))).hasFDerivAt.comp p
    ((hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hd' : fderiv ℝ (uncurry (derivative (.left, i) f)) p =
      (ContinuousLinearMap.apply ℝ ℝ (coordinateDirection (.left, i))).comp
        (fderiv ℝ (fderiv ℝ (uncurry f)) p) := by
    rw [he.fderiv_eq]
    exact hd.fderiv
  have hv := derivative_eq_fderiv
    ((contDiffAt_derivative hs (.left, i)).differentiableAt (by simp)) (.covector, j)
  rw [hd'] at hv
  exact hv

private theorem cNorm_linear_image_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {K : Set E} (hK : IsCompact K) (k : ℕ)
    {f : E → F} (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) :
    cNorm K k (L ∘ f) ≤ (k + 1 : ℝ) * ‖L‖ * cNorm K k f := by
  have hb := cNorm_le_sum_of_bounds (s := K) (r := k)
    (C := fun _ ↦ ‖L‖ * cNorm K k f)
    (fun _ _ ↦ mul_nonneg (norm_nonneg L) (cNorm_nonneg K k f)) (by
      intro j hj x hx
      rw [L.iteratedFDeriv_comp_left (hf x hx) (by simp : (j : ℕ∞ω) ≤ ∞)]
      exact (L.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
            (fun y hy ↦ (hf y hy).of_le (by simp)) hx hj) (norm_nonneg L)))
  simpa [Finset.sum_const, mul_assoc] using hb

private theorem exists_cNorm_linear_image_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Set E), IsCompact K → ∀ f : E → F,
      (∀ x ∈ K, ContDiffAt ℝ ∞ f x) →
      cNorm K k (L ∘ f) ≤ C * cNorm K k f := by
  refine ⟨(k + 1 : ℝ) * ‖L‖ + 1, by positivity, ?_⟩
  intro K hK f hf
  exact (cNorm_linear_image_le L hK k hf).trans
    (mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _))

private theorem exists_cNorm_secondJet_linear_image_le
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] G) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Set E), IsCompact K → ∀ f : E → ℝ,
      (∀ x ∈ K, ContDiffAt ℝ ∞ f x) →
      cNorm K k (L ∘ fderiv ℝ (fderiv ℝ f)) ≤ C * cNorm K (k + 2) f := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_linear_image_le
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (G := G) L k
  refine ⟨C, hC, ?_⟩
  intro K hK f hf
  have hdd (p) (hp : p ∈ K) : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) p :=
    ((hf p hp).fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hshift : cNorm K k (fderiv ℝ (fderiv ℝ f)) ≤ cNorm K (k + 2) f := by
    unfold cNorm
    simp_rw [norm_iteratedFDeriv_fderiv]
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
    linarith [sSup_norm_iteratedFDeriv_nonneg K 0 f,
      sSup_norm_iteratedFDeriv_nonneg K 1 f]
  exact (hb K hK _ hdd).trans (mul_le_mul_of_nonneg_left hshift hC.le)

set_option backward.isDefEq.respectTransparency false in
/-- A fixed shift of two bounds the actual mixed matrix, with a constant
independent of the phase and its high seminorms. Source:
Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem exists_cNorm_mixedPhaseMatrix_le_phase (n k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K U : Set (Point n)), IsCompact K → IsOpen U → K ⊆ U →
      ∀ S : Euclidean n → Euclidean n → ℝ,
      ContDiffOn ℝ ∞ (fun p : Point n ↦ S p.1.1 p.2) U →
      cNorm K k (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2) ≤
        C * cNorm K (k + 2) (fun p : Point n ↦ S p.1.1 p.2) := by
  let L : (Point n →L[ℝ] Point n →L[ℝ] ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    mixedPhaseJetExtraction
  obtain ⟨C, hC, hb⟩ := exists_cNorm_secondJet_linear_image_le
    (E := Point n) (G := Matrix (Fin n) (Fin n) ℝ) L k
  refine ⟨C, hC, ?_⟩
  intro K U hK hU hKU S hS
  let P := fun p : Point n ↦ S p.1.1 p.2
  have he := mixedPhaseMatrix_eq_secondJet_on hU hS
  have hc : cNorm K k (fun p : Point n ↦ mixedPhaseMatrix S p.1.1 p.2) =
      cNorm K k (L ∘ fderiv ℝ (fderiv ℝ P)) := by
    unfold cNorm
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Set.image_congr
    intro p hp
    rw [((eventuallyEq_of_mem (hU.mem_nhds (hKU hp)) he).iteratedFDeriv
      (𝕜 := ℝ) j).self_of_nhds]
    rfl
  rw [hc]
  exact hb K hK P (fun p hp ↦ hS.contDiffAt (hU.mem_nhds (hKU hp)))

/-- Fixed real matrix-entry extraction followed by complexification, for the
scalar primitive endpoints in `app:ch_regular_base:eq:fio-input`. -/
def phaseMatrixEntry (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap
    (𝕜 := ℝ) (E := Matrix (Fin n) (Fin n) ℝ) (F' := ℝ)
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i)))

set_option backward.isDefEq.respectTransparency false in
/-- One constant bounds every complexified matrix entry, uniformly in the
matrix field. Used for both the actual mixed matrix and its inverse in Step 3
of `app:ch_regular_base:thm:actual-calculus`. -/
theorem exists_cNorm_phaseMatrixEntry_le (n k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Set (Point n)), IsCompact K →
      ∀ f : Point n → Matrix (Fin n) (Fin n) ℝ,
      (∀ p ∈ K, ContDiffAt ℝ ∞ f p) → ∀ i j,
      cNorm K k (fun p ↦ (f p i j : ℂ)) ≤ C * cNorm K k f := by
  let C := fun i j : Fin n ↦ (k + 1 : ℝ) * ‖phaseMatrixEntry i j‖
  refine ⟨1 + ∑ i, ∑ j, C i j, by positivity, ?_⟩
  intro K hK f hf i j
  have hi : C i j ≤ ∑ i, ∑ j, C i j :=
    (Finset.single_le_sum (fun a _ ↦ by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ by positivity))
        (Finset.mem_univ i))
  exact (cNorm_linear_image_le (phaseMatrixEntry i j) hK k hf).trans
    (mul_le_mul_of_nonneg_right (by dsimp [C] at hi ⊢; linarith) (cNorm_nonneg _ _ _))

end JanetCartan.FourierIntegral.PrimitiveProfiles
