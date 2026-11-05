module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Bounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates

/-!
# The scalar freezing amplitude and its primitive budget

For `app:ch_background:prop:bg-frame`, Step 3, retain both fixed physical
cutoffs in the actual amplitude. This leaf supplies the amplitude input to
`freezingTaylorL2Operator`; all quantitative assumptions concern primitive jets.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff NNReal
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))

/-- Output projection for the paired positions in `app:ch_background:prop:bg-frame`. -/
def freezingOutputProjection : P →L[ℝ] E :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z ↦ WithLp.toLp 2 (fun i : Fin d ↦ z ⟨i.val, by omega⟩)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- Source projection for the paired positions in `app:ch_background:prop:bg-frame`. -/
def freezingSourceProjection : P →L[ℝ] E :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z ↦ WithLp.toLp 2 (fun i : Fin d ↦ z ⟨d + i.val, by omega⟩)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The output coordinate in `app:ch_background:prop:bg-frame` is recovered exactly. -/
@[simp] theorem freezingOutputProjection_pairedPosition (x y : E) :
    freezingOutputProjection (pairedPosition x y) = x := by
  ext i
  simp [freezingOutputProjection, pairedPosition]

/-- The source coordinate in `app:ch_background:prop:bg-frame` is recovered exactly. -/
@[simp] theorem freezingSourceProjection_pairedPosition (x y : E) :
    freezingSourceProjection (pairedPosition x y) = y := by
  ext i
  simp [freezingSourceProjection, pairedPosition]

/-- The literal two-position Taylor amplitude of `app:ch_background:prop:bg-frame`,
Step 3. The output cutoff is inside the extended Taylor symbol. -/
def freezingTaylorAmplitude (a : E → E → ℂ) (β γ : E → ℝ) (i : Fin d)
    (ξ : E) (z : P) : ℂ :=
  γ (freezingSourceProjection z) •
    extendedFreezingTaylorCoefficient a β i (freezingOutputProjection z) ξ

/-- The paired amplitude retains both cutoffs (`app:ch_background:prop:bg-frame`). -/
@[simp] theorem freezingTaylorAmplitude_pairedPosition (a : E → E → ℂ)
    (β γ : E → ℝ) (i : Fin d) (x y ξ : E) :
    freezingTaylorAmplitude a β γ i ξ (pairedPosition x y) =
      γ y • extendedFreezingTaylorCoefficient a β i x ξ := by
  simp [freezingTaylorAmplitude]

/-- Joint smoothness of the actual amplitude (`app:ch_background:prop:bg-frame`). -/
theorem contDiff_freezingTaylorAmplitude (a : E → E → ℂ) (β γ : E → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hβ : ContDiff ℝ ∞ β)
    (hγ : ContDiff ℝ ∞ γ) (i : Fin d) :
    ContDiff ℝ ∞ (Function.uncurry (freezingTaylorAmplitude a β γ i)) :=
  (hγ.comp (freezingSourceProjection.contDiff.comp contDiff_snd)).smul
    ((contDiff_extendedFreezingTaylorCoefficient a β ha hβ i).comp
      ((freezingOutputProjection.contDiff.comp contDiff_snd).prodMk contDiff_fst))

/-- Both fixed support boxes survive in `app:ch_background:prop:bg-frame`, Step 3. -/
theorem supportedInCenteredBox_freezingTaylorAmplitude (a : E → E → ℂ)
    (β γ : E → ℝ) (R : ℝ)
    (hβ : ∀ x, β x ≠ 0 → ∀ j, |x j| ≤ R)
    (hγ : ∀ y, γ y ≠ 0 → ∀ j, |y j| ≤ R) (i : Fin d) (ξ : E) :
    SupportedInCenteredBox R (freezingTaylorAmplitude a β γ i ξ) := by
  intro z hz j
  have hb : β (freezingOutputProjection z) ≠ 0 := by
    intro h
    simp [freezingTaylorAmplitude, extendedFreezingTaylorCoefficient, h] at hz
  have hg : γ (freezingSourceProjection z) ≠ 0 := by
    intro h
    simp [freezingTaylorAmplitude, h] at hz
  by_cases hj : j.val < d
  · exact hβ _ hb ⟨j.val, hj⟩
  · simpa [freezingSourceProjection, show d + (j.val - d) = j.val by omega] using
      hγ _ hg ⟨j.val - d, by omega⟩

/-- Output inclusion for the Taylor jet budget in `app:ch_background:prop:bg-frame`. -/
def freezingOutputInclusion : P →L[ℝ] E × E :=
  freezingOutputProjection.prod 0

/-- The explicit fixed Leibniz budget for `app:ch_background:prop:bg-frame`.
`B`, `G`, and `M` bound the primitive cutoff and symbol jets, respectively.
There is no eventual support radius in this constant. -/
def freezingAmplitudeJetBudget (B G M : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
    ((G : ℝ) * ‖freezingSourceProjection (d := d)‖ ^ k) *
    ((∑ l ∈ Finset.range (n - k + 1), ((n - k).choose l : ℝ) * B * M) *
      ‖freezingOutputInclusion (d := d)‖ ^ (n - k))

/-- A single amplitude budget through order `N`, for the L² realization in
`app:ch_background:prop:bg-frame`, Step 3. -/
def freezingAmplitudeBudget (B G M : ℝ≥0) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), freezingAmplitudeJetBudget (d := d) B G M n

/-- Primitive jets through `N+1` give all physical amplitude jets through `N`
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem norm_iteratedFDeriv_freezingTaylorAmplitude_le
    (a : E → E → ℂ) (β γ : E → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hβ : ContDiff ℝ ∞ β)
    (hγ : ContDiff ℝ ∞ γ) (B G M : ℝ≥0) (N : ℕ)
    (hb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k β x‖ ≤ B)
    (hg : ∀ k ≤ N, ∀ y, ‖iteratedFDeriv ℝ k γ y‖ ≤ G)
    (hm : ∀ k ≤ N + 1, ∀ p, ‖iteratedFDeriv ℝ k (Function.uncurry a) p‖ ≤ M)
    (i : Fin d) (ξ : E) (n : ℕ) (hn : n ≤ N) (z : P) :
    ‖iteratedFDeriv ℝ n (freezingTaylorAmplitude a β γ i ξ) z‖ ≤
      freezingAmplitudeJetBudget (d := d) B G M n := by
  let f := Function.uncurry (extendedFreezingTaylorCoefficient a β i)
  have hf : ContDiff ℝ ∞ f := contDiff_extendedFreezingTaylorCoefficient a β ha hβ i
  have hleft (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun z : P ↦ f (freezingOutputProjection z, ξ)) z‖ ≤
        (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * B * M) *
          ‖freezingOutputInclusion (d := d)‖ ^ j := by
    have h := norm_iteratedFDeriv_comp_linear_le freezingOutputInclusion
      (fun p ↦ f ((0, ξ) + p)) (hf.comp (contDiff_const.add contDiff_id)) j z
    simp only [iteratedFDeriv_comp_add_left'] at h
    apply (show ‖iteratedFDeriv ℝ j (fun z : P ↦ f (freezingOutputProjection z, ξ)) z‖ ≤
      ‖iteratedFDeriv ℝ j f (freezingOutputProjection z, ξ)‖ *
        ‖freezingOutputInclusion (d := d)‖ ^ j from by
          simpa [Function.comp_def, freezingOutputInclusion] using h).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply (norm_iteratedFDeriv_extendedFreezingTaylorCoefficient_le a β ha hβ i
      (freezingOutputProjection z, ξ) j (fun _ ↦ (M : ℝ))
      (fun k hk t _ ↦ hm (k + 1) (by omega) _)).trans
    apply Finset.sum_le_sum
    intro l hl
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hb l (by have := Finset.mem_range.mp hl; omega) _)
        (by positivity)) M.coe_nonneg
  apply (norm_iteratedFDeriv_smul_le
    (hγ.comp freezingSourceProjection.contDiff)
    (hf.comp (freezingOutputProjection.contDiff.prodMk contDiff_const)) z (by simp)).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
  have hright : ‖iteratedFDeriv ℝ k (γ ∘ freezingSourceProjection) z‖ ≤
      (G : ℝ) * ‖freezingSourceProjection (d := d)‖ ^ k :=
    (norm_iteratedFDeriv_comp_linear_le freezingSourceProjection γ hγ k z).trans
      (mul_le_mul_of_nonneg_right (hg k hkN _) (by positivity))
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hright (by positivity)) (hleft (n - k) (by omega))
    (norm_nonneg _) (by positivity)

/-- The exact amplitude hypothesis required by `twoPositionL2Operator` is
derived from primitive jets (`app:ch_background:prop:bg-frame`, Step 3). -/
theorem hasAmplitudeDerivativeBound_freezingTaylorAmplitude
    (a : E → E → ℂ) (β γ : E → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hβ : ContDiff ℝ ∞ β)
    (hγ : ContDiff ℝ ∞ γ) (B G M : ℝ≥0) (N : ℕ)
    (hb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k β x‖ ≤ B)
    (hg : ∀ k ≤ N, ∀ y, ‖iteratedFDeriv ℝ k γ y‖ ≤ G)
    (hm : ∀ k ≤ N + 1, ∀ p, ‖iteratedFDeriv ℝ k (Function.uncurry a) p‖ ≤ M)
    (i : Fin d) :
    HasAmplitudeDerivativeBound (freezingTaylorAmplitude a β γ i) N
      (freezingAmplitudeBudget (d := d) B G M N) := by
  intro ξ is hi z
  apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv
    ((contDiff_freezingTaylorAmplitude a β γ ha hβ hγ i).comp
      (contDiff_const.prodMk contDiff_id)) is z).trans
  apply (norm_iteratedFDeriv_freezingTaylorAmplitude_le a β γ ha hβ hγ B G M N
    hb hg hm i ξ is.length hi z).trans
  exact Finset.single_le_sum (fun n _ ↦ by unfold freezingAmplitudeJetBudget; positivity)
    (show is.length ∈ Finset.range (N + 1) by simp; omega)

end JanetCartan.ContinuumNormal
