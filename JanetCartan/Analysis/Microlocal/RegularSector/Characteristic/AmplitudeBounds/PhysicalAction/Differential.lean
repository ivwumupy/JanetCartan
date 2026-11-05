module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.Products

/-!
# A fixed-shift estimate for the full physical pencil action

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, this
estimates the existing `adaptedPencilApply`. Both the time and transverse
directions hold source time and initial covector fixed. The zeroth-order
matrix is part of the same polynomial first-jet formula. Consumers are the
potential and the columns of `PW₀` and `PW₁`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction

open ActualCarriers FullPhaseCharts.InverseEstimates NullTransport.AmplitudeTame GeometricProfile

variable {n d : ℕ}

/-- The fixed linear projection `(t,s,y,η) ↦ e⁻¹(t,y)` into the physical
coefficient ball in `app:ch_regular_base:lem:characteristic-kernel`. -/
def physicalPosition (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d)) :
    TwoTimePoint (Euclidean d) →L[ℝ] Euclidean n :=
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ ℝ (RootState (Euclidean d))).prod
      ((ContinuousLinearMap.fst ℝ (Euclidean d) (Euclidean d)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (Euclidean d × Euclidean d)).comp
          (ContinuousLinearMap.snd ℝ ℝ (RootState (Euclidean d))))))

/-- The finite input jet for the full physical action in
`app:ch_regular_base:lem:characteristic-kernel`. No operator value is an input. -/
abbrev ActionJet (n d : ℕ) := (Fin n → MetricTensor n) ×
  (MetricTensor n × ((Fin n → ℝ) × (TwoTimePoint (Euclidean d) →L[ℝ] (Fin n → ℝ))))

/-- The literal polynomial first-jet formula, including `Bv`, for the
physical action in `app:ch_regular_base:lem:characteristic-kernel`. -/
def actionJetValue (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (p : ActionJet n d) : Fin n → ℝ :=
  pencil p.1 (e.symm (1, 0)) *ᵥ p.2.2.2 (1, (0, (0, 0))) +
    (∑ j, pencil p.1 (e.symm (0, EuclideanSpace.single j 1)) *ᵥ
      p.2.2.2 (0, (0, (EuclideanSpace.single j 1, 0)))) +
    p.2.1 *ᵥ p.2.2.1

/-- Polynomial smoothness of the physical first-jet formula. The actual
action's regularity is thus a consequence of input smoothness
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiff_actionJetValue (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d)) :
    ContDiff ℝ ∞ (actionJetValue e) := by
  have hc (v : ℝ × Euclidean d) : ContDiff ℝ ∞
      (fun p : ActionJet n d ↦ pencil p.1 (e.symm v)) :=
    contDiff_pencil.comp (contDiff_fst.prodMk contDiff_const)
  have hd (v : TwoTimePoint (Euclidean d)) : ContDiff ℝ ∞
      (fun p : ActionJet n d ↦ p.2.2.2 v) :=
    contDiff_snd.snd.snd.clm_apply contDiff_const
  exact ((contDiff_matrixVectorProduct.comp ((hc _).prodMk (hd _))).add
    (ContDiff.sum fun j _ ↦ contDiff_matrixVectorProduct.comp
      ((hc (0, EuclideanSpace.single j 1)).prodMk
        (hd (0, (0, (EuclideanSpace.single j 1, 0))))))).add
    (contDiff_matrixVectorProduct.comp (contDiff_snd.fst.prodMk contDiff_snd.snd.fst))

/-- A one-derivative, one-high estimate for the EXISTING full physical
action. The fixed coefficient and joint balls, coordinate map, and finite
low bound determine the constants before `Q,B,v` or their open margins.
The actual consumers are `Pk`, `PW₀` and `PW₁` in
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_adaptedPencilApply_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : TwoTimePoint (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Euclidean n) (R M : ℝ)
    (himage : MapsTo (physicalPosition e) (closedBall z ρ) (closedBall x R)) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n)) (V : Set (TwoTimePoint (Euclidean d))),
        IsOpen Ω → IsOpen V → closedBall x R ⊆ Ω → closedBall z ρ ⊆ V →
        MapsTo (physicalPosition e) V Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
          (v : TwoTimePoint (Euclidean d) → Fin n → ℝ),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω → ContDiffOn ℝ ∞ v V →
          cNorm (closedBall x R) 0 Q ≤ M → cNorm (closedBall x R) 0 B ≤ M →
          cNorm (closedBall z ρ) 1 v ≤ M →
          ∀ m, cNorm (closedBall z ρ) m (adaptedPencilApply e Q B v) ≤
            C m * (1 + cNorm (closedBall x R) (m + 1) Q +
              cNorm (closedBall x R) (m + 1) B + cNorm (closedBall z ρ) (m + 1) v) := by
  let L := physicalPosition e
  let K := closedBall z ρ
  let KQ := closedBall x R
  let T := closedBall (0 : ActionJet n d) M
  choose A hA hb using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn z hρ
      (isCompact_closedBall (0 : ActionJet n d) M) (le_refl m)
      (fun p _ ↦ (contDiff_actionJetValue e).contDiffAt.of_le
        (show (m : ℕ∞ω) ≤ ∞ by simp))
  let a := fun m ↦ linearNormCost L m
  have ha m : 0 < a m := linearNormCost_pos L m
  refine ⟨fun m ↦ A m * (2 + a m),
    fun m ↦ mul_pos (hA m) (by linarith [ha m]), ?_⟩
  intro Ω V hΩ hV hKQ hK hmap Q B v hQ hB hv hQM hBM hvM m
  have hQp : ContDiffOn ℝ ∞ (Q ∘ L) V := hQ.comp L.contDiff.contDiffOn hmap
  have hBp : ContDiffOn ℝ ∞ (B ∘ L) V := hB.comp L.contDiff.contDiffOn hmap
  have hd := hv.fderiv_of_isOpen hV (m := ∞) (by simp)
  let f : TwoTimePoint (Euclidean d) → ActionJet n d :=
    fun q ↦ (Q (L q), B (L q), v q, fderiv ℝ v q)
  have hf : ContDiffOn ℝ ∞ f V := hQp.prodMk (hBp.prodMk (hv.prodMk hd))
  have ht : MapsTo f K T := by
    intro q hq
    have hqQ := (norm_le_cNorm_on (isCompact_closedBall _ _) hΩ hKQ hQ 0
      (himage hq)).trans hQM
    have hqB := (norm_le_cNorm_on (isCompact_closedBall _ _) hΩ hKQ hB 0
      (himage hq)).trans hBM
    have hqv := (norm_le_cNorm_on (isCompact_closedBall _ _) hV hK hv 1 hq).trans hvM
    have hqd := (norm_le_cNorm_on (isCompact_closedBall _ _) hV hK hd 0 hq).trans
      ((cNorm_fderiv_le K 0 v).trans hvM)
    change dist (f q) 0 ≤ M
    simpa only [dist_zero_right, f, Prod.norm_def, max_le_iff] using
      And.intro hqQ (And.intro hqB (And.intro hqv hqd))
  have hQhigh := cNorm_comp_linear_le L (isCompact_closedBall _ _) hΩ hKQ hQ himage m
  have hBhigh := cNorm_comp_linear_le L (isCompact_closedBall _ _) hΩ hKQ hB himage m
  have hp₁ := cNorm_pair_le_on_open (isCompact_closedBall z ρ) hV hK hv hd m
  have hp₂ := cNorm_pair_le_on_open (isCompact_closedBall z ρ) hV hK hBp (hv.prodMk hd) m
  have hp₃ := cNorm_pair_le_on_open (isCompact_closedBall z ρ) hV hK hQp
    (hBp.prodMk (hv.prodMk hd)) m
  have hn : cNorm K m f ≤
      a m * cNorm KQ (m + 1) Q + a m * cNorm KQ (m + 1) B +
        2 * cNorm K (m + 1) v := by
    have hQmono := mul_le_mul_of_nonneg_left
      (cNorm_mono_order (f := Q) (s := KQ) (Nat.le_succ m)) (ha m).le
    have hBmono := mul_le_mul_of_nonneg_left
      (cNorm_mono_order (f := B) (s := KQ) (Nat.le_succ m)) (ha m).le
    have hvmono := cNorm_mono_order (f := v) (s := K) (Nat.le_succ m)
    have hdhigh := cNorm_fderiv_le K m v
    dsimp [f, a, K, KQ] at *
    linarith
  have hout := hb m V hV hK f hf ht
  change cNorm K m (adaptedPencilApply e Q B v) ≤ A m * (1 + cNorm K m f) at hout
  apply hout.trans
  have hn' : 1 + cNorm K m f ≤ (2 + a m) *
      (1 + cNorm KQ (m + 1) Q + cNorm KQ (m + 1) B + cNorm K (m + 1) v) := by
    nlinarith [cNorm_nonneg KQ (m + 1) Q, cNorm_nonneg KQ (m + 1) B,
      cNorm_nonneg K (m + 1) v,
      mul_nonneg (ha m).le (cNorm_nonneg K (m + 1) v), ha m]
  exact (mul_le_mul_of_nonneg_left hn' (hA m).le).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction
