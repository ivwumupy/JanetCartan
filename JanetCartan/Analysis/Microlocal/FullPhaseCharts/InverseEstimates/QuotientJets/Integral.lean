module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Integral

/-!
# All joint jets of the quotient integral

For `app:ch_seed:eq:seed-quotient-integral`, compactness supplies local domination
at every order on the open extension, including at epsilon zero. The consumer
is the forward quotient estimate in `InverseEstimates.QuotientJets`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {A F : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- All joint derivatives pass through the unit integral on an open domain.
The required local jet dominators are derived from compactness, not assumed.
Used for the covector integral in `app:ch_seed:eq:seed-quotient-integral`. -/
theorem iteratedFDeriv_unitIntervalParameterIntegral
    {g : A × ℝ → F} {U : Set A} {W : Set ℝ}
    (hU : IsOpen U) (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hg : ContDiffOn ℝ ∞ g (U ×ˢ W)) {a : A} (ha : a ∈ U) (k : ℕ) :
    iteratedFDeriv ℝ k (fun x ↦ ∫ t in (0 : ℝ)..1, g (x, t)) a =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun x ↦ g (x, t)) a := by
  let H : ℝ × A → F := fun w ↦ g (w.2, w.1)
  have hH : ∀ w ∈ W ×ˢ U, ContDiffAt ℝ ∞ H w := by
    intro w hw
    exact (hg.contDiffAt ((hU.prod hW).mem_nhds ⟨hw.2, hw.1⟩)).comp w
      (contDiffAt_snd.prodMk contDiffAt_fst)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  have hb (j : ℕ) : ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ Metric.closedBall a ρ,
        ‖iteratedFDeriv ℝ j (fun y ↦ H (t, y)) x‖ ≤ C := by
    have hc : ContinuousOn (fun w : ℝ × A ↦
        iteratedFDeriv ℝ j (fun y ↦ H (w.1, y)) w.2)
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall a ρ) := by
      intro w hw
      exact (NormalComparison.contDiffAt_segmentSpatialJet
        (hH w ⟨hIW hw.1, hρU hw.2⟩) j).continuousAt.continuousWithinAt
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall a ρ)).exists_bound_of_continuousOn hc
    exact ⟨C, fun t ht x hx ↦ hC (t, x) ⟨ht, hx⟩⟩
  choose C hC using hb
  exact NormalComparison.iteratedFDeriv_unitIntervalIntegral
    (U := Metric.ball a ρ) (B := C) Metric.isOpen_ball
    (fun w hw ↦ hH w ⟨hIW hw.1, hρU (Metric.ball_subset_closedBall hw.2)⟩)
    (fun j _ t ht x hx ↦ hC j t ht x (Metric.ball_subset_closedBall hx))
    (Metric.mem_ball_self hρ)

/-- A pointwise jet majorant survives the unit integral. Smoothness on the
open extension supplies domination near the point; the numerical bound is
needed only at the point itself (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem norm_iteratedFDeriv_unitIntervalParameterIntegral_le
    {g : A × ℝ → F} {U : Set A} {W : Set ℝ}
    (hU : IsOpen U) (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hg : ContDiffOn ℝ ∞ g (U ×ˢ W)) {a : A} (ha : a ∈ U) (k : ℕ)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ k (fun x ↦ g (x, t)) a‖ ≤ M) :
    ‖iteratedFDeriv ℝ k (fun x ↦ ∫ t in (0 : ℝ)..1, g (x, t)) a‖ ≤ M := by
  rw [iteratedFDeriv_unitIntervalParameterIntegral hU hW hIW hg ha k]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (fun t ht ↦ hM t (by simpa using uIoc_subset_uIcc ht))

variable {P X E : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {S : (P × X) → E → ℝ} {z v : P → E}
  {V : Set P} {U : Set X} {C : Set E} {I W : Set ℝ}

/-- The exact all-order joint jet identity for the literal carrier quotient.
All spectator, physical and epsilon derivatives remain inside the same actual
covector integral, including epsilon zero (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem iteratedFDeriv_carrierQuotient
    (hV : IsOpen V) (hU : IsOpen U) (hC : IsOpen C)
    (hI : IsOpen I) (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ U) ×ˢ C))
    (hz : ContDiffOn ℝ ∞ z V) (hv : ContDiffOn ℝ ∞ v V)
    (hshift : ∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ W, z p + (t * ε) • v p ∈ C)
    {q : (P × ℝ) × X} (hq : q ∈ (V ×ˢ I) ×ˢ U) (k : ℕ) :
    iteratedFDeriv ℝ k (fun a : (P × ℝ) × X ↦
      phaseShiftQuotient S (a.1.1, a.2) (z a.1.1) (v a.1.1) a.1.2) q =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun a : (P × ℝ) × X ↦
        inner ℝ (gradient (S (a.1.1, a.2))
          (z a.1.1 + (t * a.1.2) • v a.1.1)) (v a.1.1)) q := by
  unfold phaseShiftQuotient
  apply iteratedFDeriv_unitIntervalParameterIntegral
    (g := fun w : ((P × ℝ) × X) × ℝ ↦
      inner ℝ (gradient (S (w.1.1.1, w.1.2))
        (z w.1.1.1 + (w.2 * w.1.1.2) • v w.1.1.1)) (v w.1.1.1))
    ((hV.prod hI).prod hU) hW hIW _ hq k
  apply contDiffOn_phaseShiftIntegrand (hV.prod hU) hC hS
    (contDiffOn_fst.fst.prodMk contDiffOn_snd)
    (hz.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1))
    (hv.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1)) contDiffOn_fst.snd
  intro a ha t ht
  exact ⟨⟨ha.1.1, ha.2⟩, hshift a.1.1 ha.1.1 a.1.2 ha.1.2 t ht⟩

end JanetCartan.FullPhaseCharts.InverseEstimates
