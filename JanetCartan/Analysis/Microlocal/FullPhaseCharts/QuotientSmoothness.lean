module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness.Calculus

/-!
# Smooth divided phases and physical two-point gradients

Conditional deductions for `app:ch_seed:eq:seed-exact-phase-quotient`,
`app:ch_seed:eq:seed-quotient-integral`, and `app:ch_seed:prop:seed-phase-charts`.
The actual Hamilton phase and carrier remain inputs. `P` contains the carrier,
data and spectator variables; `X` is physical space and `E` is covector space.
The epsilon interval `I` is open and may contain zero. The fixed open sets `W`
and `T` enlarge the two integration intervals; their containment hypotheses
state exactly where the buffered phase is used. Restriction to any of the
manuscript's fixed compact boxes follows by `ContDiffOn.mono`.

No phase, inverse chart, Jacobian gap, or comparison estimate is constructed here.
All formulas use the published `phaseShiftQuotient` and `averagedPhaseGradient`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts

variable {P X E : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {S : (P × X) → E → ℝ} {z v : P → E}
  {V : Set P} {U B : Set X} {C : Set E} {I W T : Set ℝ}

-- This is notation, not a second definition of the divided phase.
local notation "Φ" => (fun (p : P × ℝ) (x : X) ↦
  phaseShiftQuotient S (Prod.fst p, x) (z (Prod.fst p)) (v (Prod.fst p)) (Prod.snd p))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] in
/-- The integral in `app:ch_seed:eq:seed-quotient-integral` is literally the
published quotient, expressed using the covector Fréchet derivative. -/
theorem carrierQuotient_eq_integral_fderiv (p : P) (x : X) (ε : ℝ) :
    Φ (p, ε) x = ∫ t in (0 : ℝ)..1,
      fderiv ℝ (S (p, x)) (z p + (t * ε) • v p) (v p) := by
  simp only [phaseShiftQuotient, inner_gradient_left]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] in
/-- The zero value in `app:ch_seed:eq:seed-quotient-integral` is the covector
derivative, with no division or nonzero-shift hypothesis. -/
theorem carrierQuotient_zero (p : P) (x : X) :
    Φ (p, 0) x = fderiv ℝ (S (p, x)) (z p) (v p) := by
  simp only [phaseShiftQuotient_zero, inner_gradient_left]

variable (hV : IsOpen V) (hU : IsOpen U) (hC : IsOpen C)
  (hI : IsOpen I) (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
  (hS : ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ U) ×ˢ C))
  (hz : ContDiffOn ℝ ∞ z V) (hv : ContDiffOn ℝ ∞ v V)
  (hshift : ∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ W, z p + (t * ε) • v p ∈ C)

include hV hU hC hI hW hIW hS hz hv hshift

/-- Joint C-infinity regularity through zero for the exact carrier quotient of
`app:ch_seed:eq:seed-quotient-integral`. All analytic inputs are phase and carrier
smoothness and shifted-segment containment on the displayed fixed domains. -/
theorem contDiffOn_carrierQuotient :
    ContDiffOn ℝ ∞ (Function.uncurry Φ) ((V ×ˢ I) ×ˢ U) := by
  apply contDiffOn_phaseShiftQuotient_comp (hV.prod hU) hC ((hV.prod hI).prod hU)
    hW hIW hS (contDiffOn_fst.fst.prodMk contDiffOn_snd)
    (hz.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1))
    (hv.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1)) contDiffOn_fst.snd
  intro q hq t ht
  exact ⟨⟨hq.1.1, hq.2⟩, hshift q.1.1 hq.1.1 q.1.2 hq.1.2 t ht⟩

/-- Exact joint differentiation under the covector integral in
`app:ch_seed:eq:seed-quotient-integral`, at every epsilon including zero. -/
theorem hasFDerivAt_carrierQuotient {q : (P × ℝ) × X}
    (hq : q ∈ (V ×ˢ I) ×ˢ U) :
    HasFDerivAt (Function.uncurry Φ)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun q : (P × ℝ) × X ↦
        inner ℝ (gradient (S (q.1.1, q.2))
          (z q.1.1 + (t * q.1.2) • v q.1.1)) (v q.1.1)) q) q := by
  apply hasFDerivAt_phaseShiftQuotient_comp (hV.prod hU) hC ((hV.prod hI).prod hU)
    hW hIW hS (contDiffOn_fst.fst.prodMk contDiffOn_snd)
    (hz.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1))
    (hv.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1)) contDiffOn_fst.snd _ hq
  intro a ha t ht
  exact ⟨⟨ha.1.1, ha.2⟩, hshift a.1.1 ha.1.1 a.1.2 ha.1.2 t ht⟩

omit hV hU hI hW hz hv [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] in
/-- Agreement with the literal nonzero quotient in
`app:ch_seed:eq:seed-exact-phase-quotient`. Convexity is needed only for this
invocation of the published phase-difference identity. -/
theorem carrierQuotient_eq_div (hconv : Convex ℝ C)
    {p : P} (hp : p ∈ V) {x : X} (hx : x ∈ U) {ε : ℝ} (hε : ε ∈ I) (hne : ε ≠ 0) :
    Φ (p, ε) x = (S (p, x) (z p + ε • v p) - S (p, x) (z p)) / ε := by
  have hzC : z p ∈ C := by
    simpa using hshift p hp ε hε 0 (hIW (by simp))
  have hsC : z p + ε • v p ∈ C := by
    simpa using hshift p hp ε hε 1 (hIW (by simp))
  exact (phase_div_eq_phaseShiftQuotient hC hconv
    (contDiffOn_phase_slice (hS.of_le (by simp)) ⟨hp, hx⟩) hzC hsC hne).symm

omit hV hU hI hW hz hv [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] in
/-- The covector average representation from
`app:ch_seed:eq:seed-quotient-integral`, also at zero. -/
theorem carrierQuotient_eq_inner_average (hconv : Convex ℝ C)
    {p : P} (hp : p ∈ V) {x : X} (hx : x ∈ U) {ε : ℝ} (hε : ε ∈ I) :
    Φ (p, ε) x = inner ℝ
      (averagedPhaseGradient S (p, x) (z p + ε • v p) (z p)) (v p) := by
  apply phaseShiftQuotient_eq_inner_averagedPhaseGradient hC hconv
    (contDiffOn_phase_slice (hS.of_le (by simp)) ⟨hp, hx⟩)
  · simpa using hshift p hp ε hε 0 (hIW (by simp))
  · simpa using hshift p hp ε hε 1 (hIW (by simp))

variable (hB : IsOpen B) (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
  (hphysical : ∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ T, y + t • (x - y) ∈ U)

include hB hT hIT hphysical

/-- Joint smoothness of the actual two-point physical gradient from
`app:ch_seed:prop:seed-phase-charts`, deduced from the original phase inputs. -/
theorem contDiffOn_carrierQuotient_average :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × X × X ↦
      averagedPhaseGradient Φ q.1 q.2.1 q.2.2) ((V ×ˢ I) ×ˢ B ×ˢ B) := by
  apply contDiffOn_averagedPhaseGradient_comp (hV.prod hI) hU
    ((hV.prod hI).prod (hB.prod hB)) hT hIT
    (contDiffOn_carrierQuotient hV hU hC hI hW hIW hS hz hv hshift)
    contDiffOn_fst contDiffOn_snd.fst contDiffOn_snd.snd
  intro q hq t ht
  exact ⟨hq.1, hphysical q.2.1 hq.2.1 q.2.2 hq.2.2 t ht⟩

/-- The full joint derivative of the two-point gradient is the integral of the
actual derivative of its physical-gradient integrand
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem hasFDerivAt_carrierQuotient_average {q : (P × ℝ) × X × X}
    (hq : q ∈ (V ×ˢ I) ×ˢ B ×ˢ B) :
    HasFDerivAt (fun q : (P × ℝ) × X × X ↦ averagedPhaseGradient Φ q.1 q.2.1 q.2.2)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun q : (P × ℝ) × X × X ↦
        gradient (Φ q.1) (q.2.2 + t • (q.2.1 - q.2.2))) q) q := by
  apply hasFDerivAt_averagedPhaseGradient_comp (hV.prod hI) hU
    ((hV.prod hI).prod (hB.prod hB)) hT hIT
    (contDiffOn_carrierQuotient hV hU hC hI hW hIW hS hz hv hshift)
    contDiffOn_fst contDiffOn_snd.fst contDiffOn_snd.snd _ hq
  intro a ha t ht
  exact ⟨ha.1, hphysical a.2.1 ha.2.1 a.2.2 ha.2.2 t ht⟩

/-- The first epsilon derivative of the two-point gradient is smooth jointly on
exactly the same fixed boxes (`app:ch_seed:prop:seed-phase-charts`). -/
theorem contDiffOn_deriv_epsilon_carrierQuotient_average :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × X × X ↦
      deriv (fun ε ↦ averagedPhaseGradient Φ (q.1.1, ε) q.2.1 q.2.2) q.1.2)
      ((V ×ˢ I) ×ˢ B ×ˢ B) := by
  let Ψ : ((P × ℝ) × X × X) → X :=
    fun q ↦ averagedPhaseGradient Φ q.1 q.2.1 q.2.2
  change ContDiffOn ℝ ∞ (fun q : (P × ℝ) × X × X ↦
    deriv (fun ε ↦ Ψ ((q.1.1, ε), q.2)) q.1.2) ((V ×ˢ I) ×ˢ B ×ˢ B)
  have hA : ContDiffOn ℝ ∞ Ψ ((V ×ˢ I) ×ˢ B ×ˢ B) :=
    contDiffOn_carrierQuotient_average hV hU hC hI hW hIW hS hz hv hshift
      hB hT hIT hphysical
  have hF : ContDiffOn ℝ ∞ (fun q : ℝ × (P × X × X) ↦ Ψ ((q.2.1, q.1), q.2.2))
      (I ×ˢ V ×ˢ B ×ˢ B) :=
    hA.comp (f := fun q : ℝ × (P × X × X) ↦ ((q.2.1, q.1), q.2.2))
      ((contDiffOn_snd.fst.prodMk contDiffOn_fst).prodMk contDiffOn_snd.snd)
      (fun _ h ↦ ⟨⟨h.2.1, h.1⟩, h.2.2⟩)
  have hd : ContDiffOn ℝ ∞ (fun q : ℝ × (P × X × X) ↦
      deriv (fun ε ↦ Ψ ((q.2.1, ε), q.2.2)) q.1) (I ×ˢ V ×ˢ B ×ˢ B) :=
    (contDiffOn_parameterFDeriv hI (hV.prod (hB.prod hB)) hF).clm_apply contDiffOn_const
  exact hd.comp (f := fun q : (P × ℝ) × X × X ↦ (q.1.2, q.1.1, q.2))
    (contDiffOn_fst.snd.prodMk (contDiffOn_fst.fst.prodMk contDiffOn_snd))
    (fun _ h ↦ ⟨h.1.2, h.1.1, h.2⟩)

omit hB in
/-- Exact differentiation under the physical-segment integral for the first
epsilon derivative, valid at zero as well (`app:ch_seed:prop:seed-phase-charts`). -/
theorem hasDerivAt_epsilon_carrierQuotient_average
    {p : P} (hp : p ∈ V) {x y : X} (hx : x ∈ B) (hy : y ∈ B)
    {ε : ℝ} (hε : ε ∈ I) :
    HasDerivAt (fun ε ↦ averagedPhaseGradient Φ (p, ε) x y)
      (∫ t in (0 : ℝ)..1,
        deriv (fun ε ↦ gradient (Φ (p, ε)) (y + t • (x - y))) ε) ε := by
  have hQ := contDiffOn_carrierQuotient hV hU hC hI hW hIW hS hz hv hshift
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦
      gradient (Φ (p, q.1)) (y + q.2 • (x - y))) (I ×ˢ T) :=
    contDiffOn_averagedPhaseIntegrand (hV.prod hI) hU hQ
      (contDiffOn_const.prodMk contDiffOn_id) contDiffOn_const contDiffOn_const
      (fun a ha t ht ↦ ⟨⟨hp, ha⟩, hphysical x hx y hy t ht⟩)
  have hd := (hasFDerivAt_unitIntervalParameterIntegral hI hT hIT hg hε).hasDerivAt
  have hi : IntervalIntegrable (fun t ↦ fderiv ℝ
      (fun ε ↦ gradient (Φ (p, ε)) (y + t • (x - y))) ε) volume 0 1 :=
    (((contDiffOn_parameterFDeriv hI hT hg).continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht ↦ ⟨hε, hIT ht⟩)).intervalIntegrable_of_Icc zero_le_one
  rw [ContinuousLinearMap.intervalIntegral_apply hi] at hd
  exact hd

end JanetCartan.FullPhaseCharts
