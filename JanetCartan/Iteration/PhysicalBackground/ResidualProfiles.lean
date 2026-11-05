module

public import JanetCartan.Iteration.PhysicalBackground.MeanProfiles
public import JanetCartan.Iteration.PhysicalBackground.SourceBounds

/-!
# The literal current residual as a fixed smooth operation on physical jets

The source uses the original fixed vector field `X₀` and measurement cutoff.
Its tangent strain spends exactly two immersion derivatives. Current mean
continuity is provided by `MeanProfiles`, and the projected-frame continuity
is the retained physical-geometry theorem. Thus no small residual is assumed
in the finite-low current-neighborhood step of `app:ch_background:prop:bg-current`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

namespace JanetCartan.PhysicalBackground
open PositiveBackground GeometricProfile
open FullPhaseCharts.InverseEstimates

variable {n N : ℕ}

private abbrev ResidualJet (n N : ℕ) := Euclidean n ×
  (SecondJet (Euclidean n) (Euclidean N) × ((Fin n → MetricTensor n) × MetricTensor n))

private def tangentJetTensor (X₀ : Euclidean n → Euclidean n)
    (p : Euclidean n × SecondJet (Euclidean n) (Euclidean N)) : MetricTensor n :=
  fun i j ↦
    inner ℝ (p.2.1 (EuclideanSpace.single i 1))
      (p.2.1 (fderiv ℝ X₀ p.1 (EuclideanSpace.single j 1)) +
        p.2.2 (EuclideanSpace.single j 1) (X₀ p.1)) +
    inner ℝ
      (p.2.1 (fderiv ℝ X₀ p.1 (EuclideanSpace.single i 1)) +
        p.2.2 (EuclideanSpace.single i 1) (X₀ p.1))
      (p.2.1 (EuclideanSpace.single j 1))

private theorem contDiff_tangentJetTensor (X₀ : Euclidean n → Euclidean n)
    (hX₀ : ContDiff ℝ ∞ X₀) : ContDiff ℝ ∞ (@tangentJetTensor n N X₀) := by
  let E := Euclidean n × SecondJet (Euclidean n) (Euclidean N)
  let C : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    LinearMap.toContinuousLinearMap (LinearMap.id : (Fin n → Fin n → ℝ) →ₗ[ℝ] MetricTensor n)
  have hDX : ContDiff ℝ ∞ (fderiv ℝ X₀) := hX₀.fderiv_right (by simp)
  have hfirst : ContDiff ℝ ∞ (fun p : E ↦ p.2.1) := contDiff_snd.fst
  have hsecond : ContDiff ℝ ∞ (fun p : E ↦ p.2.2) := contDiff_snd.snd
  have hx : ContDiff ℝ ∞ (fun p : E ↦ X₀ p.1) := hX₀.comp contDiff_fst
  have hdx : ContDiff ℝ ∞ (fun p : E ↦ fderiv ℝ X₀ p.1) := hDX.comp contDiff_fst
  have hd (i : Fin n) : ContDiff ℝ ∞ (fun p : E ↦ p.2.1 (EuclideanSpace.single i 1)) :=
    hfirst.clm_apply contDiff_const
  have hv (i : Fin n) : ContDiff ℝ ∞ (fun p : E ↦
      p.2.1 (fderiv ℝ X₀ p.1 (EuclideanSpace.single i 1)) +
        p.2.2 (EuclideanSpace.single i 1) (X₀ p.1)) :=
    (hfirst.clm_apply (hdx.clm_apply contDiff_const)).add
      ((hsecond.clm_apply contDiff_const).clm_apply hx)
  apply C.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact ((hd i).inner ℝ (hv j)).add ((hv i).inner ℝ (hd j))

private theorem tangentJetTensor_eq (X₀ : Euclidean n → Euclidean n)
    (hX₀ : ContDiff ℝ ∞ X₀) (F : Euclidean n → Euclidean N) (hF : ContDiff ℝ ∞ F)
    (x : Euclidean n) :
    tangentJetTensor X₀ (x, secondJet F x) = linearizedMetric F (tangentVariation F X₀) x := by
  have hdFs : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) x := hdFs.differentiable (by simp) x
  have ht : fderiv ℝ (tangentVariation F X₀) x =
      (fderiv ℝ F x).comp (fderiv ℝ X₀ x) + (fderiv ℝ (fderiv ℝ F) x).flip (X₀ x) := by
    change fderiv ℝ (fun y ↦ fderiv ℝ F y (X₀ y)) x = _
    exact fderiv_clm_apply hdF (hX₀.differentiable (by simp) x)
  ext i j
  simp only [tangentJetTensor, secondJet, linearizedMetric, partialDeriv, ht,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

private def residualJetFormula (θ : Euclidean n → ℝ) (X₀ : Euclidean n → Euclidean n)
    (p : ResidualJet n N) : Euclidean n :=
  (- (1 / 2 : ℝ) * θ p.1) • WithLp.toLp 2
    (CubeKernel.tensorContraction p.2.2.1 (tangentJetTensor X₀ (p.1, p.2.1) + p.2.2.2))

private theorem contDiff_residualJetFormula (θ : Euclidean n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiff ℝ ∞ X₀) :
    ContDiff ℝ ∞ (@residualJetFormula n N θ X₀) := by
  have hR : ContDiff ℝ ∞ (fun p : ResidualJet n N ↦ tangentJetTensor X₀ (p.1, p.2.1) + p.2.2.2) :=
    ((contDiff_tangentJetTensor X₀ hX₀).comp (contDiff_fst.prodMk contDiff_snd.fst)).add contDiff_snd.snd.snd
  have hQ : ContDiff ℝ ∞ (fun p : ResidualJet n N ↦ p.2.2.1) := contDiff_snd.snd.fst
  have hred : ContDiff ℝ ∞ (fun p : ResidualJet n N ↦ WithLp.toLp 2
      (CubeKernel.tensorContraction p.2.2.1 (tangentJetTensor X₀ (p.1, p.2.1) + p.2.2.2))) := by
    apply (contDiff_piLp 2).mpr
    intro i
    exact hR.inner ℝ ((contDiff_pi.mp hQ) i)
  exact (contDiff_const.mul (hθ.comp contDiff_fst)).smul hred

private def residualJet (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (H : MetricField n) (x : Euclidean n) : ResidualJet n N :=
  (x, secondJet F x, Q x, H x)

private theorem residualJetFormula_eq (θ : Euclidean n → ℝ)
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiff ℝ ∞ X₀)
    (F : Euclidean n → Euclidean N) (hF : ContDiff ℝ ∞ F)
    (Q : Euclidean n → Fin n → MetricTensor n) (H : MetricField n) :
    residualJetFormula θ X₀ ∘ residualJet F Q H =
      cutReducedSource θ Q (linearizedMetric F (tangentVariation F X₀) + H) := by
  funext x
  simp only [Function.comp_apply, residualJet, residualJetFormula,
    tangentJetTensor_eq X₀ hX₀ F hF, cutReducedSource, Pi.add_apply]

private theorem cNorm_secondJet_sub_le {K : Set (Euclidean n)} (hK : IsCompact K)
    (F F₀ : Euclidean n → Euclidean N) (hF : ContDiff ℝ ∞ F) (hF₀ : ContDiff ℝ ∞ F₀) (m : ℕ) :
    cNorm K m (secondJet F - secondJet F₀) ≤ (m + 1 : ℝ) * cNorm K (m + 2) (F - F₀) := by
  have hd : fderiv ℝ (F - F₀) = fderiv ℝ F - fderiv ℝ F₀ := by
    funext x
    exact fderiv_sub (hF.differentiable (by simp) x) (hF₀.differentiable (by simp) x)
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hDF₀ : ContDiff ℝ ∞ (fderiv ℝ F₀) := hF₀.fderiv_right (by simp)
  have he : secondJet F - secondJet F₀ = secondJet (F - F₀) := by
    funext x
    apply Prod.ext
    · exact (congrFun hd x).symm
    · change fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F₀) x = fderiv ℝ (fderiv ℝ (F - F₀)) x
      rw [hd, fderiv_sub (hDF.differentiable (by simp) x) (hDF₀.differentiable (by simp) x)]
  rw [he]
  exact cNorm_secondJet_le hK m (hF.sub hF₀)

/-- The actual cut tangent-plus-mean residual is finite-order continuous in
its physical immersion, projected frame and actual mean. The immersion costs
exactly two derivatives. `exists_physicalDensityMean_zero_sub_tolerance` and
the retained projected-stress comparison are the concrete producers of the
last two primitive differences. The fixed vector field is the original `X₀`,
not recomputed from the current mean (`app:ch_background:prop:bg-current`). -/
theorem exists_cutPhysicalResidual_sub_tolerance
    {K W : Set (Euclidean n)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (θ : Euclidean n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiff ℝ ∞ X₀)
    (F₀ : Euclidean n → Euclidean N) (hF₀ : ContDiff ℝ ∞ F₀)
    (Q₀ : Euclidean n → Fin n → MetricTensor n) (hQ₀ : ContDiffOn ℝ ∞ Q₀ W)
    (Hseed : MetricField n) (hHseed : ContDiffOn ℝ ∞ Hseed W) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N) (Q : Euclidean n → Fin n → MetricTensor n)
      (H : MetricField n), ContDiff ℝ ∞ F → ContDiffOn ℝ ∞ Q W → ContDiffOn ℝ ∞ H W →
      cNorm K (m + 2) (F - F₀) + cNorm K m (Q - Q₀) + cNorm K m (H - Hseed) < δ →
      cNorm K m
        (cutReducedSource θ Q (linearizedMetric F (tangentVariation F X₀) + H) -
          cutReducedSource θ Q₀ (linearizedMetric F₀ (tangentVariation F₀ X₀) + Hseed)) < ε := by
  have hΦ := contDiff_residualJetFormula (N := N) θ hθ X₀ hX₀
  have hjet₀ : ContDiffOn ℝ ∞ (residualJet F₀ Q₀ Hseed) W :=
    contDiffOn_id.prodMk ((contDiff_secondJet hF₀).contDiffOn.prodMk (hQ₀.prodMk hHseed))
  obtain ⟨L, _hL, _hLU, δ, hδ, hb⟩ :=
    ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.exists_cNorm_comp_sub_lt_with_buffer
      hK isOpen_univ hΦ.contDiffOn (fun x hx ↦ hjet₀.contDiffAt (hW.mem_nhds (hKW hx)))
      (mapsTo_univ _ _) m hε
  refine ⟨δ / (m + 1), div_pos hδ (by positivity), ?_⟩
  intro F Q H hF hQ hH hsmall
  have hjet : ContDiffOn ℝ ∞ (residualJet F Q H) W :=
    contDiffOn_id.prodMk ((contDiff_secondJet hF).contDiffOn.prodMk (hQ.prodMk hH))
  have hQd : ContDiffOn ℝ ∞ (Q - Q₀) W := hQ.sub hQ₀
  have hHd : ContDiffOn ℝ ∞ (H - Hseed) W := hH.sub hHseed
  have hJd : ContDiff ℝ ∞ (secondJet F - secondJet F₀) :=
    (contDiff_secondJet hF).sub (contDiff_secondJet hF₀)
  have hpair := cNorm_prodMk_le_on K hK m
    (fun x hx ↦ (hQd.contDiffAt (hW.mem_nhds (hKW hx))).of_le (by simp))
    (fun x hx ↦ (hHd.contDiffAt (hW.mem_nhds (hKW hx))).of_le (by simp))
  have htriple := cNorm_prodMk_le_on K hK m
    (fun _ _ ↦ hJd.contDiffAt.of_le (by simp))
    (fun x hx ↦ ((hQd.prodMk hHd).contDiffAt (hW.mem_nhds (hKW hx))).of_le (by simp))
  have hquad := cNorm_prodMk_le_on K hK m
    (fun _ _ ↦ (contDiffAt_const (c := (0 : Euclidean n))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    (fun x hx ↦ ((hJd.contDiffOn.prodMk (hQd.prodMk hHd)).contDiffAt (hW.mem_nhds (hKW hx))).of_le (by simp))
  have hdiff : cNorm K m (residualJet F Q H - residualJet F₀ Q₀ Hseed) < δ := by
    have he : residualJet F Q H - residualJet F₀ Q₀ Hseed =
        fun x ↦ ((0 : Euclidean n), (secondJet F - secondJet F₀) x, (Q - Q₀) x, (H - Hseed) x) := by
      funext x
      simp only [residualJet, Pi.sub_apply, Prod.mk_sub_mk, sub_self]
    rw [he]
    apply hquad.trans_lt
    have hbound := htriple.trans (add_le_add (cNorm_secondJet_sub_le hK F F₀ hF hF₀ m) hpair)
    have hsmall' := (lt_div_iff₀ (by positivity : (0 : ℝ) < m + 1)).mp hsmall
    have htarget : cNorm K m (fun x ↦ ((secondJet F - secondJet F₀) x, (Q - Q₀) x, (H - Hseed) x)) < δ := by
      apply hbound.trans_lt
      nlinarith [cNorm_nonneg K m (Q - Q₀), cNorm_nonneg K m (H - Hseed), Nat.cast_nonneg (α := ℝ) m]
    have hz : cNorm K m (fun _ : Euclidean n ↦ (0 : Euclidean n)) = 0 := by
      change cNorm K m (0 : Euclidean n → Euclidean n) = 0
      exact cNorm_zero K m
    rw [hz, zero_add]
    exact htarget
  have h := hb (residualJetFormula θ X₀) (residualJet F Q H) hΦ.contDiffOn
    (fun x hx ↦ hjet.contDiffAt (hW.mem_nhds (hKW hx)))
    (by simpa only [sub_self, cNorm_zero] using hδ) hdiff
  simpa only [residualJetFormula_eq θ X₀ hX₀ F hF,
    residualJetFormula_eq θ X₀ hX₀ F₀ hF₀] using h

/-- The actual cut tangent-plus-mean residual inherits the physical map,
projected-frame and actual mean profiles. Only the map spends two derivatives;
there is no high-high loss. The current producers are `PhysicalHistory`, the
physical projected-stress profile, and `exists_physicalDensityMean_zero_profile`.
All constants precede the current fields and scale, and the original `X₀` and
cutoff are kept unchanged (`app:ch_background:eq:bg-current-profile`). -/
theorem exists_cutPhysicalResidual_profile
    {K W : Set (Euclidean n)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (θ : Euclidean n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiff ℝ ∞ X₀)
    (A B D : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s) (hD : ∀ s, 0 ≤ D s) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (F : Euclidean n → Euclidean N) (Q : Euclidean n → Fin n → MetricTensor n)
        (H : MetricField n), ContDiff ℝ ∞ F → ContDiffOn ℝ ∞ Q W → ContDiffOn ℝ ∞ H W →
        ∀ (r₀ : ℕ) (T : ℝ), 1 ≤ T → HasDerivativeProfile K F (r₀ + 2) T A →
          HasDerivativeProfile K Q r₀ T B → HasDerivativeProfile K H r₀ T D →
          HasDerivativeProfile K
            (cutReducedSource θ Q (linearizedMetric F (tangentVariation F X₀) + H)) r₀ T C := by
  let : MetricSpace (ResidualJet n N) := (inferInstance : NormedAddCommGroup (ResidualJet n N)).toMetricSpace
  let : ProperSpace (ResidualJet n N) := FiniteDimensional.proper ℝ (ResidualJet n N)
  let AJ := fun s : ℕ ↦ (s + 1 : ℝ) * A (s + 2)
  let AI := fun s ↦ cNorm K s (id : Euclidean n → Euclidean n)
  let P := fun s : ℕ ↦ (s + 1 : ℝ) * (B s + D s)
  let R := fun s : ℕ ↦ (s + 1 : ℝ) * (AJ s + P s)
  let Z := fun s : ℕ ↦ (s + 1 : ℝ) * (AI s + R s)
  have hAJ (s) : 0 ≤ AJ s := mul_nonneg (by positivity) (hA _)
  have hAI (s) : 0 ≤ AI s := cNorm_nonneg ..
  have hP (s) : 0 ≤ P s := mul_nonneg (by positivity) (add_nonneg (hB s) (hD s))
  have hR (s) : 0 ≤ R s := mul_nonneg (by positivity) (add_nonneg (hAJ s) (hP s))
  have hZ (s) : 0 ≤ Z s := mul_nonneg (by positivity) (add_nonneg (hAI s) (hR s))
  let Φ := @residualJetFormula n N θ X₀
  have hΦ := contDiff_residualJetFormula (N := N) θ hθ X₀ hX₀
  let L := fun s ↦ cNorm (closedBall (0 : ResidualJet n N) (Z 0)) s Φ
  have hL (s) : 0 ≤ L s := cNorm_nonneg ..
  refine ⟨fun s ↦ ∑ j ∈ Finset.range (s + 1), ResponseTransfer.GradedPrimitives.compositionConstant L Z j,
    fun s ↦ Finset.sum_nonneg (fun j _ ↦ ResponseTransfer.GradedPrimitives.compositionConstant_nonneg hL hZ j), ?_⟩
  intro F Q H hF hQ hH r₀ T hT hFp hQp hHp
  have hJp : HasDerivativeProfile K (secondJet F) r₀ T AJ := by
    intro s
    have hh := (cNorm_secondJet_le hK s hF).trans
      (mul_le_mul_of_nonneg_left (hFp (s + 2)) (by positivity : (0 : ℝ) ≤ s + 1))
    simpa only [AJ, Nat.add_sub_add_right, mul_assoc] using hh
  have hIp : HasDerivativeProfile K (id : Euclidean n → Euclidean n) r₀ T AI := by
    intro s
    exact le_mul_of_one_le_right (cNorm_nonneg ..) (one_le_pow₀ hT)
  have hQa (x) (hx : x ∈ K) := hQ.contDiffAt (hW.mem_nhds (hKW hx))
  have hHa (x) (hx : x ∈ K) := hH.contDiffAt (hW.mem_nhds (hKW hx))
  have hp := DerivativeBounds.hasDerivativeProfile_prodMk hK hQa hHa B D hB hD hT r₀ hQp hHp
  have hr := DerivativeBounds.hasDerivativeProfile_prodMk hK
    (fun _ _ ↦ (contDiff_secondJet hF).contDiffAt) (fun x hx ↦ (hQa x hx).prodMk (hHa x hx))
    AJ P hAJ hP hT r₀ hJp hp
  have hz := DerivativeBounds.hasDerivativeProfile_prodMk hK
    (fun _ _ ↦ contDiffAt_id)
    (fun x hx ↦ (contDiff_secondJet hF).contDiffAt.prodMk ((hQa x hx).prodMk (hHa x hx)))
    AI R hAI hR hT r₀ hIp hr
  change HasDerivativeProfile K (residualJet F Q H) r₀ T Z at hz
  have hjet (x) (hx : x ∈ K) : ContDiffAt ℝ ∞ (residualJet F Q H) x :=
    contDiffAt_id.prodMk ((contDiff_secondJet hF).contDiffAt.prodMk ((hQa x hx).prodMk (hHa x hx)))
  have hrange (x) (hx : x ∈ K) : residualJet F Q H x ∈ closedBall (0 : ResidualJet n N) (Z 0) := by
    have hh := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hjet y hy).of_le (by simp : (0 : ℕ∞ω) ≤ ∞)) hx (Nat.zero_le 0)).trans (hz 0)
    change dist (residualJet F Q H x) 0 ≤ Z 0
    calc
      dist (residualJet F Q H x) 0 = ‖residualJet F Q H x‖ := by
        convert dist_zero_right (residualJet F Q H x) using 1
      _ ≤ Z 0 := by simpa only [norm_iteratedFDeriv_zero, Nat.zero_sub, pow_zero, mul_one] using hh
  have hout := DerivativeBounds.hasDerivativeProfile_fixed_smooth_comp hK hjet
    (fun _ _ ↦ hΦ.contDiffAt) L Z hL hZ hT r₀ hz (fun j x hx ↦
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun _ _ ↦ hΦ.contDiffAt.of_le (by simp : (j : ℕ∞ω) ≤ ∞)) (hrange x hx) le_rfl)
  change HasDerivativeProfile K (residualJetFormula θ X₀ ∘ residualJet F Q H) r₀ T _ at hout
  rw [residualJetFormula_eq θ X₀ hX₀ F hF] at hout
  exact hout

end JanetCartan.PhysicalBackground
