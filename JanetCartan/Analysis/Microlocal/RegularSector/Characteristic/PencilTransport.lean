module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilChart

/-!
# The literal signed row for the pencil phase

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, substitute
the transported covector into the normalized minor nullvectors before taking
physical derivatives. The potential below is literally `lᵀPk`, including
the zeroth-order matrix, and the signed initial row is literally `lᵀσ`.
The local constructor proves their smoothness and applies the existing
exponential transport on the same Hamilton chart. It does not assume a
solution of the scalar transport equation or a smoothness bound for `Pk`.
The finite cover, fixed masks and uniform symbol estimates remain to be
constructed in the regular-sector theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic

open ActualCarriers

variable {n d : ℕ}

/-- The literal adapted coefficient of a physical direction, with source
time and initial covector held fixed
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def adaptedPencilCoefficient (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (q : TwoTimePoint (Euclidean d))
    (v : ℝ × Euclidean d) : MetricTensor n :=
  pencil (Q (e.symm (q.1, q.2.2.1))) (e.symm v)

/-- The real physical first-order action in the adapted coordinates. All
derivatives hold `s,η` fixed; the full zeroth-order matrix is retained
(`app:ch_regular_base:lem:characteristic-kernel`, the definition of `Pk`). -/
def adaptedPencilApply (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (k : TwoTimePoint (Euclidean d) → Fin n → ℝ) (q : TwoTimePoint (Euclidean d)) : Fin n → ℝ :=
  adaptedPencilCoefficient e Q q (1, 0) *ᵥ fderiv ℝ k q (1, (0, (0, 0))) +
    (∑ j, adaptedPencilCoefficient e Q q (0, EuclideanSpace.single j 1) *ᵥ
      fderiv ℝ k q (0, (0, (EuclideanSpace.single j 1, 0)))) +
    B (e.symm (q.1, q.2.2.1)) *ᵥ k q

/-- The normalized right nullvector evaluated at the actual transported
covector of the phase (`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilChartRight (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (q : TwoTimePoint (Euclidean d)) : Fin n → ℝ :=
  minorRightNullvector (rootPencil e Q h (twoTimeState Φ (C.symm q))) r c

/-- The corresponding normalized left nullvector on that same chart
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilChartLeft (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (q : TwoTimePoint (Euclidean d)) : Fin n → ℝ :=
  let w := twoTimeState Φ (C.symm q)
  minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c

/-- The actual physical potential `lᵀPk`. Derivatives here act on the
substituted nullvector, not on an independent covector parameter
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilTransportPotential (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (q : TwoTimePoint (Euclidean d)) : ℝ :=
  pencilChartLeft e Q h Φ C r c q ⬝ᵥ
    adaptedPencilApply e Q B (pencilChartRight e Q h Φ C r c) q

/-- The signed datum `lᵀσ` with the same selected minor; the scalar mask is
retained exactly (`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilSignedDatum (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (w : RootState (Euclidean d)) : Fin n → ℝ :=
  σ w • minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c

/-- The actual exponential row, with its potential and diagonal data fixed
by the pencil construction (`app:ch_regular_base:lem:characteristic-kernel`). -/
def pencilSignedRow (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) :
    TwoTimePoint (Euclidean d) → Fin n → ℝ :=
  twoTimeRowTransport C (pencilTransportPotential e Q B h Φ C r c)
    (pencilSignedDatum e Q h r c σ)

/-- Primitive coefficient and nullvector smoothness prove smoothness of the
physical derivative, including the connection term
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_adaptedPencilApply
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    {B : Euclidean n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hB : ContDiffOn ℝ ∞ B Ω) {V : Set (TwoTimePoint (Euclidean d))} (hV : IsOpen V)
    (hmap : ∀ q ∈ V, e.symm (q.1, q.2.2.1) ∈ Ω)
    {k : TwoTimePoint (Euclidean d) → Fin n → ℝ} (hk : ContDiffOn ℝ ∞ k V) :
    ContDiffOn ℝ ∞ (adaptedPencilApply e Q B k) V := by
  have hx : ContDiffOn ℝ ∞ (fun q : TwoTimePoint (Euclidean d) ↦
      e.symm (q.1, q.2.2.1)) V := e.symm.contDiff.comp_contDiffOn
    (contDiffOn_fst.prodMk contDiffOn_snd.snd.fst (s := V))
  have hcoef (v : ℝ × Euclidean d) : ContDiffOn ℝ ∞
      (fun q ↦ adaptedPencilCoefficient e Q q v) V :=
    contDiff_pencil.comp_contDiffOn ((hQ.comp hx hmap).prodMk contDiffOn_const)
  have hentry (v : ℝ × Euclidean d) (i j : Fin n) : ContDiffOn ℝ ∞
      (fun q ↦ adaptedPencilCoefficient e Q q v i j) V :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp_contDiffOn (hcoef v)
  have hb (i j : Fin n) : ContDiffOn ℝ ∞
      (fun q ↦ B (e.symm (q.1, q.2.2.1)) i j) V :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp_contDiffOn (hB.comp hx hmap)
  have hdk := hk.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hd (v : TwoTimePoint (Euclidean d)) (i : Fin n) :
      ContDiffOn ℝ ∞ (fun q ↦ fderiv ℝ k q v i) V :=
    (contDiffOn_pi.mp (hdk.clm_apply contDiffOn_const)) i
  apply contDiffOn_pi.mpr
  intro i
  change ContDiffOn ℝ ∞ (fun q ↦
    (∑ j, adaptedPencilCoefficient e Q q (1, 0) i j * fderiv ℝ k q (1, (0, (0, 0))) j) +
      (∑ a, adaptedPencilCoefficient e Q q (0, EuclideanSpace.single a 1) *ᵥ
        fderiv ℝ k q (0, (0, (EuclideanSpace.single a 1, 0)))) i +
      ∑ j, B (e.symm (q.1, q.2.2.1)) i j * k q j) V
  simp only [Finset.sum_apply, mulVec, dotProduct]
  exact ((ContDiffOn.sum fun j _ ↦ (hentry _ i j).mul (hd _ j)).add
    (ContDiffOn.sum fun a _ ↦ ContDiffOn.sum fun j _ ↦
      (hentry _ i j).mul (hd _ j))).add
    (ContDiffOn.sum fun j _ ↦ (hb i j).mul (contDiffOn_pi.mp hk j))

/-- The actual `lᵀPk` is smooth on the phase chart from primitive
coefficient and normalized-nullvector smoothness
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_pencilTransportPotential
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    {B : Euclidean n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hB : ContDiffOn ℝ ∞ B Ω) {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (r c : Fin n) (hmap : ∀ q ∈ C.target, e.symm (q.1, q.2.2.1) ∈ Ω)
    (hk : ContDiffOn ℝ ∞ (pencilChartRight e Q h Φ C r c) C.target)
    (hl : ContDiffOn ℝ ∞ (pencilChartLeft e Q h Φ C r c) C.target) :
    ContDiffOn ℝ ∞ (pencilTransportPotential e Q B h Φ C r c) C.target := by
  exact ContDiffOn.sum (s := Finset.univ) fun i _ ↦ (contDiffOn_pi.mp hl i).mul
    (contDiffOn_pi.mp (contDiffOn_adaptedPencilApply e hQ hB C.open_target hmap hk) i)

/-- The literal source mask is retained by the transported row, including
its sign and zero set. Nonvanishing of the left row is a consequence of
the actual normalization, not an additional assumption
(`app:ch_regular_base:lem:characteristic-kernel`, transported support). -/
theorem pencilSignedRow_eq_zero_iff_mask
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target)
    (hroot : (rootPencil e Q h (C.symm q).2).det = 0)
    (hm : (rootPencil e Q h (C.symm q).2).adjugate r c ≠ 0)
    (ht : minorTransportCoefficient (rootPencil e Q h (C.symm q).2)
      (rootTimeCoefficient e Q (C.symm q).2) r c ≠ 0) :
    pencilSignedRow e Q B h Φ C r c σ q = 0 ↔ σ (C.symm q).2 = 0 := by
  have hl : minorLeftNullvector (rootPencil e Q h (C.symm q).2)
      (rootTimeCoefficient e Q (C.symm q).2) r c ≠ 0 := by
    intro he
    have hn := (minor_normalization hroot hm ht).2.2.1
    rw [he, zero_dotProduct] at hn
    exact zero_ne_one hn
  rw [pencilSignedRow, twoTimeRowTransport_eq_zero_iff hC _ _ hq]
  simp only [pencilSignedDatum, smul_eq_zero, hl, or_false]

/-- Construct the signed row with its actual potential `lᵀPk` and datum
`lᵀσ`, starting with the smooth full pencil coefficients and a simple
characteristic covector. The chart and product box precede the source mask.
No potential, transport solution, or normalized nullvector is assumed
(`app:ch_regular_base:lem:characteristic-kernel`, transport step). -/
theorem exists_pencil_signed_transport
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} {B : Euclidean n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (z : RootState (Euclidean d)) (τ : ℝ) (hx : e.symm (z.1, z.2.1) ∈ Ω)
    (hξ : e.symm (τ, z.2.2) ≠ 0)
    (hp : determinant (Q (e.symm (z.1, z.2.1))) (e.symm (τ, z.2.2)) = 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (z.1, z.2.1))))
      (e.symm (τ, z.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState (Euclidean d)), ∃ h : RootState (Euclidean d) → ℝ,
      ∃ r c : Fin n, ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
      ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
      ∃ δ > (0 : ℝ),
      let I := ball z.1 δ
      let U := ball z.2 δ
      let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
      IsOpen D ∧ z ∈ D ∧ h z = τ ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        (rootPencil e Q h w).det = 0 ∧
        fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 ∧
        (rootPencil e Q h w).adjugate r c ≠ 0 ∧
        minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ≠ 0) ∧
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
      (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
        (twoTimeState Φ (C.symm q)).1 = q.1) ∧
      ContDiffOn ℝ ∞ (fun q ↦ twoTimeState Φ (C.symm q)) C.target ∧
      ContDiffOn ℝ ∞ (pencilChartRight e Q h Φ C r c) C.target ∧
      ContDiffOn ℝ ∞ (pencilChartLeft e Q h Φ C r c) C.target ∧
      ContDiffOn ℝ ∞ (pencilTransportPotential e Q B h Φ C r c) C.target ∧
      IsOpen V ∧ (z.1, z) ∈ V ∧
      (∀ w ∈ I ×ˢ U, (w.1, w) ∈ V ∧ twoTimeState Φ (C.symm (w.1, w)) = w ∧
        twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
      ∀ σ : RootState (Euclidean d) → ℝ, ContDiffOn ℝ ∞ σ D →
        ContDiffOn ℝ ∞ (pencilSignedRow e Q B h Φ C r c σ) V ∧
        (∀ w ∈ I ×ˢ U, pencilSignedRow e Q B h Φ C r c σ (w.1, w) =
          pencilSignedDatum e Q h r c σ w) ∧
        (∀ q ∈ V, fderiv ℝ (pencilSignedRow e Q B h Φ C r c σ) q
          (1, (0, (-rootMomentumGradient h (twoTimeState Φ (C.symm q)), 0))) =
            -(pencilTransportPotential e Q B h Φ C r c q) • pencilSignedRow e Q B h Φ C r c σ q) ∧
        (∀ q ∈ V, pencilSignedRow e Q B h Φ C r c σ q = 0 ↔ σ (C.symm q).2 = 0) := by
  obtain ⟨D, h, r, c, Φ, C, δ, hδ, hD, hz, hbase, hh, hk, hl, hroot,
    hC, hCf, hCs, hstateSmooth, hstate, hphase, hdiff, hbox, hinit, hd⟩ :=
    exists_pencil_minor_twoTimeChart e hΩ hQ z τ hx hξ hp hgap
  let I := ball z.1 δ
  let U := ball z.2 δ
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hV : IsOpen V := hCs.continuousOn.isOpen_inter_preimage C.open_target
    (isOpen_ball.prod (isOpen_ball.prod isOpen_ball))
  have hk' : ContDiffOn ℝ ∞ (pencilChartRight e Q h Φ C r c) C.target :=
    hk.comp hstateSmooth (fun _ hq ↦ (hstate _ hq).1)
  have hl' : ContDiffOn ℝ ∞ (pencilChartLeft e Q h Φ C r c) C.target :=
    hl.comp hstateSmooth (fun _ hq ↦ (hstate _ hq).1)
  have hmap (q : TwoTimePoint (Euclidean d)) (hq : q ∈ C.target) :
      e.symm (q.1, q.2.2.1) ∈ Ω := by
    have hx := (hroot _ (hstate q hq).1).1
    rwa [(hstate q hq).2, (twoTimeChart_inverse_coordinates hC hq).2.2.2] at hx
  have hpot := contDiffOn_pencilTransportPotential e hQ hB r c hmap hk' hl'
  have hdiag (w : RootState (Euclidean d)) (hw : w ∈ I ×ˢ U) :
      (w.1, w) ∈ V ∧ twoTimeState Φ (C.symm (w.1, w)) = w ∧
        twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ := by
    have hws : (w.1, w) ∈ C.source := hbox ⟨hw.1, hw⟩
    have hi := (hinit w hw).1
    have hp : C (w.1, w) = (w.1, w) := by
      simp [hC, twoTimeProjection, twoTimeState, hi]
    have hinv : C.symm (w.1, w) = (w.1, w) := by
      simpa only [hp] using C.left_inv hws
    refine ⟨⟨hp ▸ C.map_source hws, ?_⟩, ?_, twoTimePhase_diagonal hC hi hws⟩
    · change C.symm (w.1, w) ∈ I ×ˢ (I ×ˢ U)
      rw [hinv]
      exact ⟨hw.1, hw⟩
    · simp only [hinv, twoTimeState, sub_self, hi]
  refine ⟨D, h, r, c, Φ, C, δ, hδ, hD, hz, hbase, hh, hroot, hC,
    hphase, hdiff, hstate, hstateSmooth, hk', hl', hpot, hV,
    (hdiag z ⟨mem_ball_self hδ, mem_ball_self hδ⟩).1, hdiag, ?_⟩
  intro σ hσ
  have ha₀ : ContDiffOn ℝ ∞ (pencilSignedDatum e Q h r c σ) (I ×ˢ U) :=
    (hσ.smul hl).mono (fun w hw ↦ (hinit w hw).2)
  have hspec := twoTimeRowTransport_spec hC hCf hCs isOpen_ball
    (convex_ball z.1 δ).ordConnected isOpen_ball hbox hd (mem_ball_self hδ) hpot ha₀
  refine ⟨hspec.1, ?_, hspec.2, ?_⟩
  · intro w hw
    exact twoTimeRowTransport_diagonal hC _ _ (hinit w hw).1 (hbox ⟨hw.1, hw⟩)
  · intro q hq
    have hw : (C.symm q).2 ∈ D := (hinit _ hq.2.2).2
    obtain ⟨_, _, hdet, _, hm, ht⟩ := hroot _ hw
    exact pencilSignedRow_eq_zero_iff_mask e Q B h Φ C hC r c σ hq.1 hdet hm ht

end JanetCartan.RegularSector.Characteristic
