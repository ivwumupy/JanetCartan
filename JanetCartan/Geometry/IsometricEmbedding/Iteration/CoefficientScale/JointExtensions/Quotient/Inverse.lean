module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.QuotientProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Quotient.Cutoff

/-!
# Fixed cutoffs for the actual inverse quotient coefficients

The inverse part of `app:eq:uniform-high-coeff` retains the entire compact
image core from `app:ch_seed:prop:seed-phase-charts`. All coordinates, including
both physical endpoints, covectors, spectators and the open epsilon buffer,
are retained. Regularity past the closed target comes from the actual outer
inverse buffer, rather than from a numerical seminorm bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions
open ActualCarriers CurrentFullPhase FrozenMenu
open FullPhaseCharts ActualPhase ActualComparison ActualEstimates InverseEstimates

/-- The original full joint coordinates of `app:ch_seed:prop:seed-phase-charts`.
No Hilbert norm is substituted for their product norm. -/
abbrev FullQuotientInput (n : ℕ) :=
  (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
    WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1))

/-- The transverse joint coordinates in the literal coefficient seminorm
of `app:eq:uniform-high-coeff`. -/
abbrev TransverseQuotientInput (n : ℕ) :=
  (ℝ × (Euclidean 2 × ℝ × ℝ) × Euclidean (n - 1) × Euclidean (n - 1)) ×
    Euclidean (n - 1)

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The SAME full inverse used by `currentQuotientCoefficientNorm`
(`app:ch_seed:prop:seed-phase-charts`). -/
def fullInverseCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z : Euclidean 3) (η : Euclidean (n - 1)) (r : ℝ) :
    FullQuotientInput n → ℝ × Euclidean (n - 1) :=
  Function.uncurry (phaseChartInverse (fullChartFamily (current T Q) (spatialCarrier T))
    (dataSet z η (2 * r)))

/-- The SAME transverse inverse, in the seminorm's actual coordinate order
(`app:ch_seed:prop:seed-phase-charts`). -/
def transverseInverseCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (η : Euclidean (n - 1)) (r : ℝ) :
    TransverseQuotientInput n → Euclidean (n - 1) :=
  fun q ↦ phaseChartInverse (transverseChartFamily (current T Q) (spatialCarrier T))
    (ball η (2 * r)) (transverseParameterReindex q.1) q.2

/-- The literal first epsilon derivative of the full inverse, before cutoff
(`app:ch_seed:prop:seed-phase-charts`). -/
def fullInverseEpsilonCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (z : Euclidean 3)
    (η : Euclidean (n - 1)) (r : ℝ) : FullQuotientInput n → ℝ × Euclidean (n - 1) :=
  fun q ↦ deriv (fun ε ↦ fullInverseCoefficient T Q z η r ((ε,q.1.2),q.2)) q.1.1

/-- The literal first epsilon derivative of the transverse inverse, before
cutoff (`app:ch_seed:prop:seed-phase-charts`). -/
def transverseInverseEpsilonCoefficient (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (η : Euclidean (n - 1)) (r : ℝ) :
    TransverseQuotientInput n → Euclidean (n - 1) :=
  fun q ↦ deriv (fun ε ↦ transverseInverseCoefficient T Q η r ((ε,q.1.2),q.2)) q.1.1

/-- Both full inverse coefficients are ambient smooth on the entire CLOSED
norm domain. The actual outer buffer proves this also at its boundary
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem fullInverseCoefficients_contDiffAt (Q : _) (z : Euclidean 3)
    (η : Euclidean (n - 1)) {r s e b c : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hs : 0 < s) (he : 0 < e) (hb : 0 < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
      (fullParameterSet z s (2 * e) ×ˢ dataSet z η (2 * r)))
    (hi : BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
      (fullParameterSet z s (2 * e)) (dataBox z η r) (dataSet z η (2 * r))
      (dataBox z η (2 * r)) V L b c G) :
    ∀ q ∈ fullParameterBox z (s / 2) e ×ˢ closure V,
      ContDiffAt ℝ ∞ (fullInverseCoefficient T Q z η r) q ∧
      ContDiffAt ℝ ∞ (fullInverseEpsilonCoefficient T Q z η r) q := by
  have hh := bufferedInverse_outer_regular _ (isOpen_fullParameterSet z s (2 * e))
    (isOpen_dataSet z η (2 * r)) (prod_mono ball_subset_closedBall ball_subset_closedBall)
    hb hf hi
  have ho := (isOpen_fullParameterSet (n := n) z s (2 * e)).prod
    (isOpen_thickening (δ := b / 2) (E := closure V))
  have hd := contDiffOn_deriv_epsilon ho hh.2.1
  intro q hq
  have hp : q.1 ∈ fullParameterSet z s (2 * e) := by
    simpa only [show 2 * (s / 2) = s by ring] using
      (fullParameterBox_geometry z (half_pos hs) he).2.2.2 hq.1
  exact ⟨hh.2.1.contDiffAt (ho.mem_nhds ⟨hp, hh.1 hq.2⟩),
    hd.contDiffAt (ho.mem_nhds ⟨hp, hh.1 hq.2⟩)⟩

/-- Both transverse inverse coefficients are ambient smooth on the closed
primitive box times the entire closed target. The reindexing is the actual
fixed linear map from the quotient producer
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverseInverseCoefficients_contDiffAt (Q : _) (z : Euclidean 3)
    (η : Euclidean (n - 1)) {r s e b c : ℝ}
    {V L : Set (Euclidean (n - 1))}
    (hs : 0 < s) (he : 0 < e) (hb : 0 < b)
    (hf : ContDiffOn ℝ ∞
      (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
      (transverseParameterSet z s (2 * e) ×ˢ ball η (2 * r)))
    (hi : BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
      (transverseParameterSet z s (2 * e)) (closedBall η r) (ball η (2 * r))
      (closedBall η (2 * r)) V L b c (ContinuousLinearEquiv.refl ℝ _)) :
    ∀ q ∈ transversePrimitiveBox z (s / 2) e ×ˢ closure V,
      ContDiffAt ℝ ∞ (transverseInverseCoefficient T Q η r) q ∧
      ContDiffAt ℝ ∞ (transverseInverseEpsilonCoefficient T Q η r) q := by
  have hh := bufferedInverse_outer_regular _ (isOpen_transverseParameterSet z s (2 * e))
    isOpen_ball ball_subset_closedBall hb hf hi
  let O := (transverseParameterReindex (n := n) ⁻¹'
    transverseParameterSet z s (2 * e)) ×ˢ thickening (b / 2) (closure V)
  have ho : IsOpen O := ((isOpen_transverseParameterSet z s (2 * e)).preimage
    transverseParameterReindex.continuous).prod isOpen_thickening
  have hre : ContDiff ℝ ∞ (fun q : TransverseQuotientInput n ↦
      ((transverseParameterReindex (n := n)) q.1, q.2)) :=
    ((transverseParameterReindex.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  have hg : ContDiffOn ℝ ∞ (transverseInverseCoefficient T Q η r) O :=
    hh.2.1.comp (f := fun q : TransverseQuotientInput n ↦
      ((transverseParameterReindex (n := n)) q.1, q.2)) hre.contDiffOn (fun _ hq ↦ hq)
  have hd := contDiffOn_deriv_epsilon ho hg
  intro q hq
  have hp : transverseParameterReindex q.1 ∈ transverseParameterSet z s (2 * e) := by
    have hp := hq.1
    rw [transversePrimitiveBox_eq_preimage] at hp
    simpa only [show 2 * (s / 2) = s by ring] using
      (transverseParameterBox_geometry z (half_pos hs) he).2.2.2 hp
  exact ⟨hg.contDiffAt (ho.mem_nhds ⟨hp, hh.1 hq.2⟩),
    hd.contDiffAt (ho.mem_nhds ⟨hp, hh.1 hq.2⟩)⟩

private theorem closedBall_subset_interior_larger {A : Type*} [PseudoMetricSpace A]
    (x : A) {a b : ℝ} (hab : a < b) :
    closedBall x a ⊆ interior (closedBall x b) :=
  (closedBall_subset_ball hab).trans (interior_maximal ball_subset_closedBall isOpen_ball)

private theorem fullParameterBox_shrink (z : Euclidean 3) {s e : ℝ}
    (hs : 0 < s) (he : 0 < e) :
    fullParameterBox (n := n) z (s / 4) (e / 2) ⊆
      interior (fullParameterBox z (s / 2) e) := by
  simp only [fullParameterBox, interior_prod_eq, interior_Icc]
  exact prod_mono (Icc_subset_Ioo (by linarith) (by linarith))
    (prod_mono (closedBall_subset_interior_larger _ (by linarith))
      (prod_mono (closedBall_subset_interior_larger _ (by linarith))
        (closedBall_subset_interior_larger _ (by linarith))))

private theorem transversePrimitiveBox_shrink (z : Euclidean 3) {s e : ℝ}
    (hs : 0 < s) (he : 0 < e) :
    transversePrimitiveBox (n := n) z (s / 4) (e / 2) ⊆
      interior (transversePrimitiveBox z (s / 2) e) := by
  simp only [transversePrimitiveBox, interior_prod_eq, interior_Icc]
  exact prod_mono (Icc_subset_Ioo (by linarith) (by linarith))
    (prod_mono
      (prod_mono (closedBall_subset_interior_larger _ (by linarith))
        (prod_mono (closedBall_subset_interior_larger _ (by linarith))
          (closedBall_subset_interior_larger _ (by linarith))))
      (prod_mono (closedBall_subset_interior_larger _ (by linarith))
        (closedBall_subset_interior_larger _ (by linarith))))

/-- Fix a full inverse cutoff from the producer's geometric buffers, retaining
its whole compact image core. The regularity input used below is produced by
`fullInverseCoefficients_contDiffAt`, for both literal coefficients. This
buffer-parametric version lets the final eight-coefficient construction use
fresh forward buffers without changing the inverse operator
(`app:ch_seed:prop:seed-phase-charts`, `app:eq:uniform-high-coeff`). -/
theorem exists_full_inverse_quotient_cutoff (z : Euclidean 3) {s e : ℝ}
    (hs : 0 < s) (he : 0 < e) {V L : Set (ℝ × Euclidean (n - 1))}
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hLc : IsCompact L) (hLV : L ⊆ V) :
    ∃ χ : FullQuotientInput n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ interior (fullParameterBox z (s / 2) e) ×ˢ V ∧
      fullParameterBox z (s / 4) (e / 2) ×ˢ L ⊆ interior {x | χ x = 1} ∧
      (∀ f : FullQuotientInput n → ℝ × Euclidean (n - 1),
        (∀ x ∈ fullParameterBox z (s / 2) e ×ˢ closure V, ContDiffAt ℝ ∞ f x) →
        ContDiff ℝ ∞ (fun x ↦ χ x • f x) ∧
        EqOn (fun x ↦ χ x • f x) f (fullParameterBox z (s / 4) (e / 2) ×ˢ L) ∧
        tsupport (fun x ↦ χ x • f x) ⊆ tsupport χ) ∧
      ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
        ∀ m (f : FullQuotientInput n → ℝ × Euclidean (n - 1)),
          (∀ x ∈ fullParameterBox z (s / 2) e ×ˢ closure V, ContDiffAt ℝ ∞ f x) →
          cNorm univ m (fun x ↦ χ x • f x) ≤
            D m * cNorm (fullParameterBox z (s / 2) e ×ˢ closure V) m f := by
  exact exists_quotient_coefficient_cutoff
    ((fullParameterBox_geometry z (by positivity : 0 < s / 4) (half_pos he)).1.prod hLc)
    (isOpen_interior.prod hV) (prod_mono (fullParameterBox_shrink z hs he) hLV)
    ((fullParameterBox_geometry z (half_pos hs) he).1.prod hVc)
    (prod_mono interior_subset subset_closure)

/-- Fix a transverse inverse cutoff in the EXACT primitive coordinates of
`currentQuotientCoefficientNorm`. All of `L` is retained. The actual regularity
producer for its two inputs is `transverseInverseCoefficients_contDiffAt`
(`app:ch_seed:prop:seed-phase-charts`, `app:eq:uniform-high-coeff`). -/
theorem exists_transverse_inverse_quotient_cutoff (z : Euclidean 3) {s e : ℝ}
    (hs : 0 < s) (he : 0 < e) {V L : Set (Euclidean (n - 1))}
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hLc : IsCompact L) (hLV : L ⊆ V) :
    ∃ χ : TransverseQuotientInput n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ interior (transversePrimitiveBox z (s / 2) e) ×ˢ V ∧
      transversePrimitiveBox z (s / 4) (e / 2) ×ˢ L ⊆ interior {x | χ x = 1} ∧
      (∀ f : TransverseQuotientInput n → Euclidean (n - 1),
        (∀ x ∈ transversePrimitiveBox z (s / 2) e ×ˢ closure V, ContDiffAt ℝ ∞ f x) →
        ContDiff ℝ ∞ (fun x ↦ χ x • f x) ∧
        EqOn (fun x ↦ χ x • f x) f (transversePrimitiveBox z (s / 4) (e / 2) ×ˢ L) ∧
        tsupport (fun x ↦ χ x • f x) ⊆ tsupport χ) ∧
      ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
        ∀ m (f : TransverseQuotientInput n → Euclidean (n - 1)),
          (∀ x ∈ transversePrimitiveBox z (s / 2) e ×ˢ closure V, ContDiffAt ℝ ∞ f x) →
          cNorm univ m (fun x ↦ χ x • f x) ≤
            D m * cNorm (transversePrimitiveBox z (s / 2) e ×ˢ closure V) m f := by
  exact exists_quotient_coefficient_cutoff ((isCompact_transversePrimitiveBox z (s / 4) (e / 2)).prod hLc)
    (isOpen_interior.prod hV) (prod_mono (transversePrimitiveBox_shrink z hs he) hLV)
    ((isCompact_transversePrimitiveBox z (s / 2) e).prod hVc)
    (prod_mono interior_subset subset_closure)

/-- The four extended inverse seminorms, using fixed scalar cutoffs on the
literal full/transverse inverse and epsilon derivative functions
(`app:eq:uniform-high-coeff`). -/
def extendedInverseQuotientNorm (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z : Euclidean 3) (η : Euclidean (n - 1)) (r : ℝ)
    (χF : FullQuotientInput n → ℝ) (χT : TransverseQuotientInput n → ℝ) (m : ℕ) : ℝ :=
  (cNorm univ m (fun x ↦ χF x • fullInverseCoefficient T Q z η r x) +
    cNorm univ m (fun x ↦ χF x • fullInverseEpsilonCoefficient T Q z η r x)) +
  (cNorm univ m (fun x ↦ χT x • transverseInverseCoefficient T Q η r x) +
    cNorm univ m (fun x ↦ χT x • transverseInverseEpsilonCoefficient T Q η r x))

/-- Construct the four ACTUAL inverse quotient extensions from primitive valid
patch and frozen incidence data. Buffers, the positive frame threshold, cutoffs,
compact supports and all constants precede the frame. Agreement retains the
producer's entire `LF` and `LT`, on smaller positive parameter boxes with open
epsilon buffers. The SAME-order comparison is with the literal eight-term
`currentQuotientCoefficientNorm`; the second bound instantiates its actual
producer at canonical phase order `m+3`, retaining immersion reserve SIX
(`main:prop:current-scale`, `app:eq:uniform-high-coeff`,
`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_actual_inverse_quotient_extensions {c C : ℝ} (hP : P.IsValid c C)
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
      IsOpen VF ∧ IsCompact (closure VF) ∧ IsCompact LF ∧ LF ⊆ VF ∧
      IsOpen VT ∧ IsCompact (closure VT) ∧ IsCompact LT ∧ LT ⊆ VT ∧
    ∃ (χF : FullQuotientInput n → ℝ) (χT : TransverseQuotientInput n → ℝ),
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
        (∀ m, extendedInverseQuotientNorm T Q z η r χF χT m ≤
          D m * currentQuotientCoefficientNorm T Q z η ρF ρT r s e VF VT m) ∧
        ∀ m, extendedInverseQuotientNorm T Q z η r χF χT m ≤
          H m * (1 + cNorm (closedBall
            (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2)
            T.family.radius) (m + 3) (HamiltonPhase.phase (T.currentChart Q).coordinates)) := by
  dsimp only
  let η := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  obtain ⟨ρF, hρF, ρT, hρT, r, hr, s, hs, hsr, hphys, _, e, he,
    hrF, hrT, heF, heT, δ, hδ, cF, hcF, bF, hbF, VF, LF,
    cT, hcT, bT, hbT, VT, LT, _, _, _, _, A, hA,
    hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV, hactual⟩ :=
    exists_actual_buffered_inverse_phase_bounds T hP hz hk hinc hd
  obtain ⟨χF, hχF, hcχF, hsχF, _, hpF, DF, hDF, hDFbound⟩ :=
    exists_full_inverse_quotient_cutoff z hs he hVF hVFc hLFc hLFV
  obtain ⟨χT, hχT, hcχT, hsχT, _, hpT, DT, hDT, hDTbound⟩ :=
    exists_transverse_inverse_quotient_cutoff z hs he hVT hVTc hLTc hLTV
  let D := fun m ↦ DF m + DT m
  have hD m : 0 < D m := add_pos (hDF m) (hDT m)
  refine ⟨ρF, hρF, ρT, hρT, r, hr, s, hs, e, he, δ, hδ,
    cF, hcF, bF, hbF, VF, LF, cT, hcT, bT, hbT, VT, LT,
    hsr, hphys, hrF, hrT, heF, heT, hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV,
    χF, χT, hχF, hcχF, hsχF, hχT, hcχT, hsχT,
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
  have hnorm (m : ℕ) : extendedInverseQuotientNorm T Q z η r χF χT m ≤
      D m * currentQuotientCoefficientNorm T Q z η ρF ρT r s e VF VT m := by
    have h₁ := hDFbound m _ (fun q hq ↦ (hregF q hq).1)
    have h₂ := hDFbound m _ (fun q hq ↦ (hregF q hq).2)
    have h₃ := hDTbound m _ (fun q hq ↦ (hregT q hq).1)
    have h₄ := hDTbound m _ (fun q hq ↦ (hregT q hq).2)
    have hDFD : DF m ≤ D m := le_add_of_nonneg_right (hDT m).le
    have hDTD : DT m ≤ D m := le_add_of_nonneg_left (hDF m).le
    have hh := add_le_add
      (add_le_add (h₁.trans (mul_le_mul_of_nonneg_right hDFD (cNorm_nonneg _ _ _)))
        (h₂.trans (mul_le_mul_of_nonneg_right hDFD (cNorm_nonneg _ _ _))))
      (add_le_add (h₃.trans (mul_le_mul_of_nonneg_right hDTD (cNorm_nonneg _ _ _)))
        (h₄.trans (mul_le_mul_of_nonneg_right hDTD (cNorm_nonneg _ _ _))))
    apply hh.trans
    simp only [currentQuotientCoefficientNorm, fullInverseCoefficient, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (hD m).le
    exact add_le_add
      (le_add_of_nonneg_left (add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)))
      (le_add_of_nonneg_left (add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)))
  refine ⟨hiF, hiT, ?_, ?_, hnorm, ?_⟩
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
