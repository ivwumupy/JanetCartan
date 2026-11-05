module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.CoefficientExtension
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Smoothness
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The single affine extension of the literal projected frame

The extension in `app:ch_regular:eq:coefficient-extension` is applied to the
whole Frobenius-valued frame. Commutation with every real linear functional
transfers the checked scalar Seeley bound to this finite array. The extension
and its support are fixed before the derivative order and the current frame.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow

private theorem cNorm_dual_comp_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K) {m : ℕ} {f : E → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f x) (L : F →L[ℝ] ℝ) :
    cNorm K m (L ∘ f) ≤ (m + 1 : ℝ) * (‖L‖ * cNorm K m f) := by
  have hb := cNorm_le_sum_of_bounds (s := K) (r := m) (f := L ∘ f)
    (C := fun _ ↦ ‖L‖ * cNorm K m f)
    (fun _ _ ↦ mul_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _))
    (fun j hj x hx ↦ ?_)
  · simpa using hb
  rw [L.iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hj)]
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hx hj) (norm_nonneg _))

/-- The same Seeley operator controls every finite-dimensional real coefficient
array from its local ambient jets. This is used for the full reduced-operator
array in `app:ch_regular:eq:coefficient-extension`. -/
theorem exists_cNorm_vector_seeleyExtension_le {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (p : BallExtension.Parameters E) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ f : E → F,
      (∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ f x) →
      cNorm univ m (p.seeleyExtension f) ≤
        C * cNorm (closedBall p.center p.radius) m f := by
  obtain ⟨A, hA, hb⟩ := p.exists_cNorm_seeleyExtension_le m
  refine ⟨(m + 1 : ℝ) * (A * (m + 1)), by positivity, ?_⟩
  intro f hf
  have he : ContDiff ℝ ∞ (p.seeleyExtension f) :=
    p.contDiff_seeleyExtension (fun x hx ↦ (hf x hx).contDiffWithinAt)
  have hscalar (L : F →L[ℝ] ℝ) :
      cNorm univ m (L ∘ p.seeleyExtension f) ≤
        A * ((m + 1 : ℝ) * (‖L‖ * cNorm (closedBall p.center p.radius) m f)) := by
    have hLf : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ (L ∘ f) x :=
      fun x hx ↦ L.contDiff.contDiffAt.comp x (hf x hx)
    have hi : p.closedBallCNorm m (L ∘ f) =
        cNorm (closedBall p.center p.radius) m (L ∘ f) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      apply Set.image_congr
      intro x hx
      rw [iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedBall
        ((hLf x hx).of_le (by simp)) hx]
    have hs := hb (L ∘ f) (fun x hx ↦ (hLf x hx).contDiffWithinAt)
    rw [hi] at hs
    have hmap : p.seeleyExtension (L ∘ f) = L ∘ p.seeleyExtension f :=
      p.seeleyExtension_map L.toLinearMap f
    rw [hmap] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left
      (cNorm_dual_comp_le (isCompact_closedBall _ _)
        (fun x hx ↦ (hf x hx).of_le (by simp)) L) hA.le)
  have hjets (j : ℕ) (hj : j ≤ m) (x : E) :
      ‖iteratedFDeriv ℝ j (p.seeleyExtension f) x‖ ≤
        A * (m + 1 : ℝ) * cNorm (closedBall p.center p.radius) m f := by
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity [cNorm_nonneg (closedBall p.center p.radius) m f])
    intro v
    apply NormedSpace.norm_le_dual_bound ℝ _ (by positivity [cNorm_nonneg (closedBall p.center p.radius) m f])
    intro L
    have hc : ContDiff ℝ ∞ (L ∘ p.seeleyExtension f) := L.contDiff.comp he
    have hsupport : HasCompactSupport (L ∘ p.seeleyExtension f) := by
      have hmap : p.seeleyExtension (L ∘ f) = L ∘ p.seeleyExtension f :=
        p.seeleyExtension_map L.toLinearMap f
      rw [← hmap]
      exact p.hasCompactSupport_seeleyExtension _
    obtain ⟨B, _, hB⟩ := hsupport.exists_bound_iteratedFDeriv hc m
    have hd := norm_iteratedFDeriv_le_cNorm_of_bddAbove
      (s := univ) (f := L ∘ p.seeleyExtension f)
      (show BddAbove ((fun y ↦ ‖iteratedFDeriv ℝ j (L ∘ p.seeleyExtension f) y‖) '' univ)
        from ⟨B, by rintro _ ⟨y, _, rfl⟩; exact hB j hj y⟩) (mem_univ x) hj
    have hv : L (iteratedFDeriv ℝ j (p.seeleyExtension f) x v) =
        iteratedFDeriv ℝ j (L ∘ p.seeleyExtension f) x v :=
      (congrArg (fun T ↦ T v) (L.iteratedFDeriv_comp_left he.contDiffAt (by simp))).symm
    rw [hv]
    apply ((iteratedFDeriv ℝ j (L ∘ p.seeleyExtension f) x).le_opNorm v).trans
    calc
      _ ≤ (A * ((m + 1 : ℝ) *
          (‖L‖ * cNorm (closedBall p.center p.radius) m f))) * ∏ i, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (hd.trans (hscalar L))
          (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
      _ = _ := by ring
  have hh := cNorm_le_sum_of_bounds (s := univ) (r := m) (f := p.seeleyExtension f)
    (C := fun _ ↦ A * (m + 1 : ℝ) * cNorm (closedBall p.center p.radius) m f)
    (fun _ _ ↦ by positivity [cNorm_nonneg (closedBall p.center p.radius) m f]) (fun j hj x _ ↦ hjets j hj x)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, ← mul_assoc] using hh

/-- The literal affine extension of the stress frame, using one Seeley operator
for all components and orders (`app:ch_regular:eq:coefficient-extension`). -/
def affineFrameExtension {n : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (Q : Euclidean n → Fin n → MetricTensor n) : Euclidean n → Fin n → MetricTensor n :=
  (fun _ ↦ cubeStress n) + p.seeleyExtension (Q - fun _ ↦ cubeStress n)

/-- Agreement on the entire fixed coefficient ball, including its boundary
(`app:ch_regular:thm:no-return`). -/
theorem affineFrameExtension_eqOn {n : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (Q : Euclidean n → Fin n → MetricTensor n) :
    EqOn (affineFrameExtension p Q) Q (closedBall p.center p.radius) := by
  intro x hx
  change cubeStress n + p.seeleyExtension (Q - fun _ ↦ cubeStress n) x = Q x
  rw [p.seeleyExtension_eq_on_closedBall _ hx]
  simp

/-- The extended frame is smooth everywhere from local smoothness on the
coefficient ball (`app:ch_regular:eq:coefficient-extension`). -/
theorem contDiff_affineFrameExtension {n : ℕ} (p : BallExtension.Parameters (Euclidean n))
    {Q : Euclidean n → Fin n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q (closedBall p.center p.radius)) :
    ContDiff ℝ ∞ (affineFrameExtension p Q) :=
  contDiff_const.add (p.contDiff_seeleyExtension (hQ.sub contDiffOn_const))

/-- One compact collar supports every extended frame perturbation
(`app:ch_regular:eq:coefficient-extension`). -/
theorem tsupport_affineFrameExtension_sub {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Q : Euclidean n → Fin n → MetricTensor n) :
    tsupport (affineFrameExtension p Q - fun _ ↦ cubeStress n) ⊆
      closedBall p.center (p.radius + p.width / 2) := by
  simpa only [affineFrameExtension, add_sub_cancel_left] using
    p.tsupport_seeleyExtension_subset (Q - fun _ ↦ cubeStress n)

/-- The fixed extension preserves frame closeness at every order, with no
additive background error. This supplies the primitive input to
`NormalizedSymbolBounds` in `app:ch_regular:thm:no-return`. -/
theorem exists_affineFrameExtension_bound {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ Q : Euclidean n → Fin n → MetricTensor n,
      (∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x) →
      cNorm univ m (affineFrameExtension p Q - fun _ ↦ cubeStress n) ≤
        C * cNorm (closedBall p.center p.radius) m (Q - fun _ ↦ cubeStress n) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_vector_seeleyExtension_le
    (F := Fin n → MetricTensor n) p m
  refine ⟨C, hC, fun Q hQ ↦ ?_⟩
  simpa only [affineFrameExtension, add_sub_cancel_left] using hb (Q - fun _ ↦ cubeStress n)
    (fun x hx ↦ (hQ x hx).sub contDiffAt_const)

/-- The actual projected-frame instance of the same affine operator
(`app:ch_regular:thm:no-return`). No independently chosen frame is substituted. -/
def extendedProjectedStress {n N : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) : Euclidean n → Fin n → MetricTensor n :=
  affineFrameExtension p (ProjectedStressFrame.projectedStress F)

end JanetCartan.ProtectedFlow
