module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Quotient.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Quotient.Buffers

/-!
# Fixed extensions of all eight actual joint quotient coefficients

Every operator, buffer, support and frame threshold precedes the frame and all
orders. The consumer is the final common-reference assembly of
`app:eq:uniform-high-coeff`. The canonical phase is needed only through `m+3`,
so the subsequent sharp immersion estimate retains reserve six.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions
open ActualCarriers CurrentFullPhase FrozenMenu
open FullPhaseCharts ActualPhase ActualComparison ActualEstimates InverseEstimates

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The sum of all eight global extended seminorms, in the SAME joint coordinates
as `currentQuotientCoefficientNorm` (`app:eq:uniform-high-coeff`). -/
def extendedQuotientCoefficientNorm (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z : Euclidean 3) (η : Euclidean (n - 1)) (r : ℝ)
    (ψF : FullQuotientInput n → ℝ) (ψT : TransverseQuotientInput n → ℝ)
    (χF : FullQuotientInput n → ℝ) (χT : TransverseQuotientInput n → ℝ) (m : ℕ) : ℝ :=
  extendedForwardQuotientNorm T Q ψF ψT m +
    extendedInverseQuotientNorm T Q z η r χF χT m

/-- Construct fixed smooth, compactly supported extensions of all eight ACTUAL
full/transverse forward/inverse quotient coefficients and first epsilon
derivatives from primitive valid patch and frozen incidence data. Agreement
retains the complete inverse cores `LF`, `LT` and smaller positive physical/data
boxes with an epsilon interval around zero. All cutoffs and constants precede
the current frame. The first estimate uses the literal coefficient norm at the
SAME order; its actual producer gives the second estimate at canonical phase
order `m+3`, for the parent's common-reference construction with reserve SIX
(`main:prop:current-scale`, `app:eq:uniform-high-coeff`,
`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_actual_quotient_extensions {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    let η := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ ρF > (0 : ℝ), ∃ ρT > (0 : ℝ), ∃ r > (0 : ℝ), ∃ s > (0 : ℝ),
    ∃ e > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∃ cF > (0 : ℝ), ∃ bF > (0 : ℝ), ∃ VF LF : Set (ℝ × Euclidean (n - 1)),
    ∃ cT > (0 : ℝ), ∃ bT > (0 : ℝ), ∃ VT LT : Set (Euclidean (n - 1)),
      s ≤ r ∧ 3 * r < T.family.radius / 8 ∧
      2 * r ≤ ρF ∧ 2 * r ≤ ρT ∧ e ≤ ρF ∧ e ≤ ρT ∧
      4 * r ≤ ρF ∧ 4 * r ≤ ρT ∧ 2 * e ≤ ρF ∧ 2 * e ≤ ρT ∧
      IsOpen VF ∧ IsCompact (closure VF) ∧ IsCompact LF ∧ LF ⊆ VF ∧
      IsOpen VT ∧ IsCompact (closure VT) ∧ IsCompact LT ∧ LT ⊆ VT ∧
    ∃ (ψF χF : FullQuotientInput n → ℝ) (ψT χT : TransverseQuotientInput n → ℝ),
      ContDiff ℝ ∞ ψF ∧ HasCompactSupport ψF ∧
      tsupport ψF ⊆ ball (fullForwardCenter z η) ρF ∧
      ContDiff ℝ ∞ ψT ∧ HasCompactSupport ψT ∧
      tsupport ψT ⊆ ball (transverseForwardCenter z η) ρT ∧
      ContDiff ℝ ∞ χF ∧ HasCompactSupport χF ∧
      tsupport χF ⊆ interior (fullParameterBox z (s / 2) e) ×ˢ VF ∧
      ContDiff ℝ ∞ χT ∧ HasCompactSupport χT ∧
      tsupport χT ⊆ interior (transversePrimitiveBox z (s / 2) e) ×ˢ VT ∧
    ∃ D H : ℕ → ℝ, (∀ m, 0 < D m) ∧ (∀ m, 0 < H m) ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
          (fullParameterSet z s (2 * e)) (dataBox z η r) (dataSet z η (2 * r))
          (dataBox z η (2 * r)) VF LF bF cF
          (FrozenIncidence.referenceEquiv T hP hz hinc hd) ∧
        BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
          (transverseParameterSet z s (2 * e)) (closedBall η r) (ball η (2 * r))
          (closedBall η (2 * r)) VT LT bT cT (ContinuousLinearEquiv.refl ℝ _) ∧
        (∀ f ∈ ({fullForwardCoefficient T Q,
            fullForwardEpsilonCoefficient T Q} : Set (FullQuotientInput n → _)),
          ContDiff ℝ ∞ (fun x ↦ ψF x • f x) ∧
          EqOn (fun x ↦ ψF x • f x) f
            (fullParameterBox z (s / 2) e ×ˢ dataBox z η (2 * r)) ∧
          tsupport (fun x ↦ ψF x • f x) ⊆ tsupport ψF) ∧
        (∀ f ∈ ({transverseForwardCoefficient T Q,
            transverseForwardEpsilonCoefficient T Q} : Set (TransverseQuotientInput n → _)),
          ContDiff ℝ ∞ (fun x ↦ ψT x • f x) ∧
          EqOn (fun x ↦ ψT x • f x) f
            (transversePrimitiveBox z (s / 2) e ×ˢ closedBall η (2 * r)) ∧
          tsupport (fun x ↦ ψT x • f x) ⊆ tsupport ψT) ∧
        (∀ f ∈ ({fullInverseCoefficient T Q z η r,
            fullInverseEpsilonCoefficient T Q z η r} : Set (FullQuotientInput n → _)),
          ContDiff ℝ ∞ (fun x ↦ χF x • f x) ∧
          EqOn (fun x ↦ χF x • f x) f (fullParameterBox z (s / 4) (e / 2) ×ˢ LF) ∧
          tsupport (fun x ↦ χF x • f x) ⊆ tsupport χF) ∧
        (∀ f ∈ ({transverseInverseCoefficient T Q η r,
            transverseInverseEpsilonCoefficient T Q η r} : Set (TransverseQuotientInput n → _)),
          ContDiff ℝ ∞ (fun x ↦ χT x • f x) ∧
          EqOn (fun x ↦ χT x • f x) f (transversePrimitiveBox z (s / 4) (e / 2) ×ˢ LT) ∧
          tsupport (fun x ↦ χT x • f x) ⊆ tsupport χT) ∧
        (∀ m, extendedQuotientCoefficientNorm T Q z η r ψF ψT χF χT m ≤
          D m * currentQuotientCoefficientNorm T Q z η ρF ρT r s e VF VT m) ∧
        ∀ m, extendedQuotientCoefficientNorm T Q z η r ψF ψT χF χT m ≤
          H m * (1 + cNorm (closedBall
            (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2)
            T.family.radius) (m + 3) (HamiltonPhase.phase (T.currentChart Q).coordinates)) := by
  dsimp only
  let η := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  obtain ⟨ρF, hρF, ρT, hρT, r, hr, s, hs, hsr, hphys, _, e, he,
    hrF, hrT, heF, heT, hrF', hrT', heF', heT', δ, hδ, cF, hcF, bF, hbF, VF, LF,
    cT, hcT, bT, hbT, VT, LT, _, _, _, _, A, hA,
    hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV, hforwardRegular, hactual⟩ :=
    exists_actual_regular_quotient_buffers T hP hz hk hinc hd
  obtain ⟨ψF, hψF, hcψF, hsψF, _, hpFF, DFF, hDFF, hDFFbound⟩ :=
    exists_full_forward_quotient_cutoff z η hρF
  obtain ⟨ψT, hψT, hcψT, hsψT, _, hpFT, DFT, hDFT, hDFTbound⟩ :=
    exists_transverse_forward_quotient_cutoff z η hρT
  obtain ⟨χF, hχF, hcχF, hsχF, _, hpF, DF, hDF, hDFbound⟩ :=
    exists_full_inverse_quotient_cutoff z hs he hVF hVFc hLFc hLFV
  obtain ⟨χT, hχT, hcχT, hsχT, _, hpT, DT, hDT, hDTbound⟩ :=
    exists_transverse_inverse_quotient_cutoff z hs he hVT hVTc hLTc hLTV
  let D := fun m ↦ (DFF m + DFT m) + (DF m + DT m)
  have hD m : 0 < D m := add_pos (add_pos (hDFF m) (hDFT m)) (add_pos (hDF m) (hDT m))
  refine ⟨ρF, hρF, ρT, hρT, r, hr, s, hs, e, he, δ, hδ,
    cF, hcF, bF, hbF, VF, LF, cT, hcT, bT, hbT, VT, LT,
    hsr, hphys, hrF, hrT, heF, heT, hrF', hrT', heF', heT', hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV,
    ψF, χF, ψT, χT, hψF, hcψF, hsψF, hψT, hcψT, hsψT,
    hχF, hcχF, hsχF, hχT, hcχT, hsχT,
    D, (fun m ↦ D m * A m * (m + 4 : ℝ)), hD,
    (fun m ↦ mul_pos (mul_pos (hD m) (hA m)) (by positivity)), ?_⟩
  intro Q hQ
  obtain ⟨hf, ht, _, _, hiF, hiT, _, _, _, _, _, hbound⟩ := hactual Q hQ
  have hf' := hf.mono (prod_mono Subset.rfl (prod_mono
    (ball_subset_ball (by linarith : 2 * r ≤ 3 * r))
    (ball_subset_ball (by linarith : 2 * r ≤ 3 * r))))
  have ht' := ht.mono (prod_mono Subset.rfl (ball_subset_ball (by linarith : 2 * r ≤ 3 * r)))
  have hregF := fullInverseCoefficients_contDiffAt T Q z η hs he hbF hf' hiF
  have hregT := transverseInverseCoefficients_contDiffAt T Q z η hs he hbT ht' hiT
  have hregFF := (hforwardRegular Q).1
  have hregFT := (hforwardRegular Q).2
  have hboxF := full_forward_workingBox_subset z η hs hsr hrF' heF'
  have hboxT := transverse_forward_workingBox_subset z η hs hsr hrT' heT'
  have hnorm (m : ℕ) : extendedQuotientCoefficientNorm T Q z η r ψF ψT χF χT m ≤
      D m * currentQuotientCoefficientNorm T Q z η ρF ρT r s e VF VT m := by
    have h₁ := hDFFbound m (fullForwardCoefficient T Q) (fun q hq ↦ (hregFF q hq).1)
    have h₂ := hDFFbound m (fullForwardEpsilonCoefficient T Q) (fun q hq ↦ (hregFF q hq).2)
    have h₃ := hDFTbound m (transverseForwardCoefficient T Q) (fun q hq ↦ (hregFT q hq).1)
    have h₄ := hDFTbound m (transverseForwardEpsilonCoefficient T Q) (fun q hq ↦ (hregFT q hq).2)
    have h₅ := hDFbound m (fullInverseCoefficient T Q z η r) (fun q hq ↦ (hregF q hq).1)
    have h₆ := hDFbound m (fullInverseEpsilonCoefficient T Q z η r) (fun q hq ↦ (hregF q hq).2)
    have h₇ := hDTbound m (transverseInverseCoefficient T Q η r) (fun q hq ↦ (hregT q hq).1)
    have h₈ := hDTbound m (transverseInverseEpsilonCoefficient T Q η r) (fun q hq ↦ (hregT q hq).2)
    have hFFD : DFF m ≤ D m := by dsimp [D]; linarith [hDFT m, hDF m, hDT m]
    have hFTD : DFT m ≤ D m := by dsimp [D]; linarith [hDFF m, hDF m, hDT m]
    have hFD : DF m ≤ D m := by dsimp [D]; linarith [hDFF m, hDFT m, hDT m]
    have hTD : DT m ≤ D m := by dsimp [D]; linarith [hDFF m, hDFT m, hDF m]
    have hh := add_le_add
      (add_le_add
        (add_le_add (h₁.trans (mul_le_mul_of_nonneg_right hFFD (cNorm_nonneg _ _ _)))
          (h₂.trans (mul_le_mul_of_nonneg_right hFFD (cNorm_nonneg _ _ _))))
        (add_le_add (h₃.trans (mul_le_mul_of_nonneg_right hFTD (cNorm_nonneg _ _ _)))
          (h₄.trans (mul_le_mul_of_nonneg_right hFTD (cNorm_nonneg _ _ _)))))
      (add_le_add
        (add_le_add (h₅.trans (mul_le_mul_of_nonneg_right hFD (cNorm_nonneg _ _ _)))
          (h₆.trans (mul_le_mul_of_nonneg_right hFD (cNorm_nonneg _ _ _))))
        (add_le_add (h₇.trans (mul_le_mul_of_nonneg_right hTD (cNorm_nonneg _ _ _)))
          (h₈.trans (mul_le_mul_of_nonneg_right hTD (cNorm_nonneg _ _ _)))))
    apply hh.trans_eq
    let a := cNorm (closedBall (fullForwardCenter z η) ρF) m (fullForwardCoefficient T Q)
    let b := cNorm (closedBall (fullForwardCenter z η) ρF) m (fullForwardEpsilonCoefficient T Q)
    let c := cNorm (closedBall (transverseForwardCenter z η) ρT) m (transverseForwardCoefficient T Q)
    let d := cNorm (closedBall (transverseForwardCenter z η) ρT) m (transverseForwardEpsilonCoefficient T Q)
    let i := cNorm (fullParameterBox z (s / 2) e ×ˢ closure VF) m (fullInverseCoefficient T Q z η r)
    let j := cNorm (fullParameterBox z (s / 2) e ×ˢ closure VF) m (fullInverseEpsilonCoefficient T Q z η r)
    let k := cNorm (transversePrimitiveBox z (s / 2) e ×ˢ closure VT) m (transverseInverseCoefficient T Q η r)
    let l := cNorm (transversePrimitiveBox z (s / 2) e ×ˢ closure VT) m (transverseInverseEpsilonCoefficient T Q η r)
    change ((D m * a + D m * b) + (D m * c + D m * d)) +
      ((D m * i + D m * j) + (D m * k + D m * l)) =
        D m * (((a + b) + (i + j)) + ((c + d) + (k + l)))
    ring
  refine ⟨hiF, hiT, ?_, ?_, ?_, ?_, hnorm, ?_⟩
  · intro f hfmem
    have hfreg : ∀ q ∈ closedBall (fullForwardCenter z η) ρF, ContDiffAt ℝ ∞ f q := by
      rcases hfmem with rfl | hfmem
      · exact fun q hq ↦ (hregFF q hq).1
      · rcases hfmem with rfl
        exact fun q hq ↦ (hregFF q hq).2
    have hh := hpFF f hfreg
    exact ⟨hh.1, hh.2.1.mono hboxF, hh.2.2⟩
  · intro f hfmem
    have hfreg : ∀ q ∈ closedBall (transverseForwardCenter z η) ρT, ContDiffAt ℝ ∞ f q := by
      rcases hfmem with rfl | hfmem
      · exact fun q hq ↦ (hregFT q hq).1
      · rcases hfmem with rfl
        exact fun q hq ↦ (hregFT q hq).2
    have hh := hpFT f hfreg
    exact ⟨hh.1, hh.2.1.mono hboxT, hh.2.2⟩
  · intro f hfmem
    rcases hfmem with rfl | hfmem
    · exact hpF _ (fun q hq ↦ (hregF q hq).1)
    · rcases hfmem with rfl
      exact hpF _ (fun q hq ↦ (hregF q hq).2)
  · intro f hfmem
    rcases hfmem with rfl | hfmem
    · exact hpT _ (fun q hq ↦ (hregT q hq).1)
    · rcases hfmem with rfl
      exact hpT _ (fun q hq ↦ (hregT q hq).2)
  · intro m
    have hh := (hnorm m).trans (mul_le_mul_of_nonneg_left (hbound m) (hD m).le)
    have hp := cNorm_current_le T Q (m + 3) Subset.rfl
    apply hh.trans
    simp only [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hD m).le
    apply mul_le_mul_of_nonneg_left _ (hA m).le
    simp only [Nat.cast_add, Nat.cast_ofNat] at hp
    nlinarith only [hp, show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]

end JanetCartan.CurrentCoefficientProfiles.JointExtensions
