module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FrameExtension

/-!
# The fixed Seeley operator in joint coordinates

The phase and transport domains in `app:eq:uniform-high-coeff` use product
norms. Conjugating the actual ball extension by a fixed continuous linear
equivalence retains those norms, with explicit coordinate costs and no loss of
derivatives. The agreement domain is the image of the closed extension ball;
it is not silently identified with a ball for a different norm.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions

variable {E V F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The SAME Seeley operator, expressed in the original joint coordinates,
for `main:prop:current-scale`. Both `L` and `p` precede every input and order. -/
def coordinateSeeley (L : V ≃L[ℝ] E) (p : BallExtension.Parameters V)
    (f : E → F) : E → F :=
  p.seeleyExtension (f ∘ L) ∘ L.symm

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
/-- Agreement on the precise closed ellipsoid in the original product norm
(`app:eq:uniform-high-coeff`). -/
theorem coordinateSeeley_eqOn (L : V ≃L[ℝ] E) (p : BallExtension.Parameters V)
    (f : E → F) :
    EqOn (coordinateSeeley L p f) f (L '' closedBall p.center p.radius) := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [coordinateSeeley, Function.comp_apply, L.symm_apply_apply]
  exact p.seeleyExtension_eq_on_closedBall (f ∘ L) hx

omit [FiniteDimensional ℝ F] in
/-- The fixed compact support of the joint extension
(`app:eq:uniform-high-coeff`). -/
theorem tsupport_coordinateSeeley_subset (L : V ≃L[ℝ] E)
    (p : BallExtension.Parameters V) (f : E → F) :
    tsupport (coordinateSeeley L p f) ⊆
      L '' closedBall p.center (p.radius + p.width / 2) := by
  apply closure_minimal
  · intro x hx
    refine ⟨L.symm x, ?_, L.apply_symm_apply x⟩
    exact p.tsupport_seeleyExtension_subset (f ∘ L) (subset_closure hx)
  · exact ((isCompact_closedBall _ _).image L.continuous).isClosed

/-- Smoothness of the actual joint extension from smoothness on its original
closed domain (`app:eq:uniform-high-coeff`). -/
theorem contDiff_coordinateSeeley (L : V ≃L[ℝ] E)
    (p : BallExtension.Parameters V) {f : E → F}
    (hf : ∀ x ∈ L '' closedBall p.center p.radius, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (coordinateSeeley L p f) := by
  apply (p.contDiff_seeleyExtension ?_).comp L.symm.contDiff
  intro x hx
  exact ((hf (L x) (mem_image_of_mem L hx)).comp x L.contDiff.contDiffAt).contDiffWithinAt

private theorem cNorm_precomp_equiv_le {A B G : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A ≃L[ℝ] B) {J : Set A} {K : Set B} {f : B → G} (m : ℕ)
    (hmap : MapsTo L J K)
    (hb : ∀ i ≤ m, BddAbove ((fun y ↦ ‖iteratedFDeriv ℝ i f y‖) '' K)) :
    cNorm J m (f ∘ L) ≤
      ((m + 1 : ℝ) * (max 1 ‖(L : A →L[ℝ] B)‖) ^ m) * cNorm K m f := by
  have hjet (i : ℕ) (hi : i ≤ m) (x : A) (hx : x ∈ J) :
      ‖iteratedFDeriv ℝ i (f ∘ L) x‖ ≤
        (max 1 ‖(L : A →L[ℝ] B)‖) ^ m * cNorm K m f := by
    have he := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (L x)) i
    simp only [preimage_univ, iteratedFDerivWithin_univ] at he
    rw [he]
    apply ((iteratedFDeriv ℝ i f (L x)).norm_compContinuousLinearMap_le
      (fun _ ↦ (L : A →L[ℝ] B))).trans
    simp only [Finset.prod_const, Finset.card_fin]
    rw [mul_comm]
    apply mul_le_mul
    · exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ (le_max_left _ _) hi)
    · exact norm_iteratedFDeriv_le_cNorm_of_bddAbove (hb i hi) (hmap hx) hi
    · exact norm_nonneg _
    · positivity
  have hh := cNorm_le_sum_of_bounds
    (fun _ _ ↦ mul_nonneg (pow_nonneg (by positivity) _) (cNorm_nonneg _ _ _)) hjet
  simpa [mul_assoc] using hh

/-- No derivative is lost in the fixed coordinate change and Seeley
extension. The input norm is the literal norm on `K`; containment of the
extension ball is an explicit geometric premise. This is the extension step
used by the actual joint families in `app:eq:uniform-high-coeff`. -/
theorem exists_cNorm_coordinateSeeley_le (L : V ≃L[ℝ] E)
    (p : BallExtension.Parameters V) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (K : Set E), IsCompact K →
      MapsTo L (closedBall p.center p.radius) K →
      ∀ (f : E → F), (∀ x ∈ K, ContDiffAt ℝ ∞ f x) →
        cNorm univ m (coordinateSeeley L p f) ≤ C * cNorm K m f := by
  obtain ⟨A, hA, hbound⟩ := ProtectedFlow.exists_cNorm_vector_seeleyExtension_le (F := F) p m
  let d := (m + 1 : ℝ) * (max 1 ‖(L : V →L[ℝ] E)‖) ^ m
  let e := (m + 1 : ℝ) * (max 1 ‖(L.symm : E →L[ℝ] V)‖) ^ m
  have hd : 0 < d := by dsimp [d]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  refine ⟨e * A * d, mul_pos (mul_pos he hA) hd, ?_⟩
  intro K hK hmap f hf
  have hlocal : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ (f ∘ L) x :=
    fun x hx ↦ (hf (L x) (hmap hx)).comp x L.contDiff.contDiffAt
  have hb := hbound (f ∘ L) hlocal
  have hi : cNorm (closedBall p.center p.radius) m (f ∘ L) ≤ d * cNorm K m f := by
    apply cNorm_precomp_equiv_le L m hmap
    intro i hi
    exact hK.bddAbove_image (fun x hx ↦
      ((hf x hx).continuousAt_iteratedFDeriv (by simp)).norm.continuousWithinAt)
  have hs : ContDiff ℝ ∞ (p.seeleyExtension (f ∘ L)) :=
    p.contDiff_seeleyExtension (fun x hx ↦ (hlocal x hx).contDiffWithinAt)
  obtain ⟨B, _, hB⟩ := (p.hasCompactSupport_seeleyExtension (f ∘ L)).exists_bound_iteratedFDeriv hs m
  have ho : cNorm univ m (coordinateSeeley L p f) ≤
      e * cNorm univ m (p.seeleyExtension (f ∘ L)) := by
    apply cNorm_precomp_equiv_le L.symm m (mapsTo_univ _ _)
    intro i hi
    exact ⟨B, by rintro _ ⟨x, _, rfl⟩; exact hB i hi x⟩
  calc
    _ ≤ e * (A * (d * cNorm K m f)) :=
      ho.trans (mul_le_mul_of_nonneg_left
        (hb.trans (mul_le_mul_of_nonneg_left hi hA.le)) he.le)
    _ = _ := by ring

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
/-- A fixed inner-product ball whose coordinate image fits in the original
norm ball. The norm factor is retained explicitly for the joint phase and
transport consumers of `app:eq:uniform-high-coeff`. -/
def coordinateBallParameters (L : V ≃L[ℝ] E) (c : E) {R : ℝ} (hR : 0 < R) :
    BallExtension.Parameters V where
  center := L.symm c
  radius := R / (1 + ‖(L : V →L[ℝ] E)‖)
  radius_pos := div_pos hR (by positivity)
  width := (R / (1 + ‖(L : V →L[ℝ] E)‖)) / 4
  width_pos := by positivity
  width_lt := by have := div_pos hR (show 0 < 1 + ‖(L : V →L[ℝ] E)‖ by positivity); linarith

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
/-- The smaller working radius in the ORIGINAL norm, before histories or
orders, used in `app:eq:uniform-high-coeff`. -/
def coordinateWorkingRadius (L : V ≃L[ℝ] E) (c : E) {R : ℝ} (hR : 0 < R) : ℝ :=
  (coordinateBallParameters L c hR).radius / (1 + ‖(L.symm : E →L[ℝ] V)‖)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
/-- The joint working domain has positive radius
(`app:eq:uniform-high-coeff`). -/
theorem coordinateWorkingRadius_pos (L : V ≃L[ℝ] E) (c : E) {R : ℝ} (hR : 0 < R) :
    0 < coordinateWorkingRadius L c hR :=
  div_pos (coordinateBallParameters L c hR).radius_pos (by positivity)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
/-- The input ball is contained in the domain of the original joint profile;
no replacement of the product norm by a Hilbert norm is made
(`app:eq:uniform-high-coeff`). -/
theorem coordinateBallParameters_mapsTo (L : V ≃L[ℝ] E) (c : E) {R : ℝ} (hR : 0 < R) :
    MapsTo L (closedBall (coordinateBallParameters L c hR).center
      (coordinateBallParameters L c hR).radius) (closedBall c R) := by
  intro x hx
  let p := coordinateBallParameters L c hR
  have hd : dist (L x) c ≤ ‖(L : V →L[ℝ] E)‖ * dist x (L.symm c) := by
    simpa only [dist_eq_norm, map_sub, ContinuousLinearEquiv.coe_coe, L.apply_symm_apply] using
      (L : V →L[ℝ] E).le_opNorm (x - L.symm c)
  have hr : (1 + ‖(L : V →L[ℝ] E)‖) * p.radius = R :=
    mul_div_cancel₀ _ (by positivity)
  exact (hd.trans (mul_le_mul_of_nonneg_left (mem_closedBall.mp hx) (norm_nonneg _))).trans
    (by linarith [p.radius_pos])

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
/-- The entire smaller ball in the original norm is an agreement domain of
the Seeley extension (`app:eq:uniform-high-coeff`). -/
theorem coordinateWorkingBall_subset (L : V ≃L[ℝ] E) (c : E) {R : ℝ} (hR : 0 < R) :
    closedBall c (coordinateWorkingRadius L c hR) ⊆
      L '' closedBall (coordinateBallParameters L c hR).center
        (coordinateBallParameters L c hR).radius := by
  intro x hx
  refine ⟨L.symm x, ?_, L.apply_symm_apply x⟩
  let p := coordinateBallParameters L c hR
  have hd : dist (L.symm x) (L.symm c) ≤ ‖(L.symm : E →L[ℝ] V)‖ * dist x c := by
    simpa only [dist_eq_norm, map_sub, ContinuousLinearEquiv.coe_coe] using
      (L.symm : E →L[ℝ] V).le_opNorm (x - c)
  have hr : (1 + ‖(L.symm : E →L[ℝ] V)‖) * coordinateWorkingRadius L c hR = p.radius :=
    mul_div_cancel₀ _ (by positivity)
  exact (hd.trans (mul_le_mul_of_nonneg_left (mem_closedBall.mp hx) (norm_nonneg _))).trans
    (by linarith [coordinateWorkingRadius_pos L c hR])

end JanetCartan.CurrentCoefficientProfiles.JointExtensions
