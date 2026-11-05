module

public import JanetCartan.Analysis.Calculus.PhaseQuotient
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Calculus for the divided phase

These lemmas supply the integral operations used by
`app:ch_seed:prop:seed-phase-charts`. The integration interval has an explicit
open enlargement `W`; the phase and the carrier are inputs, not constructions.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts

variable {P E A : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Joint smoothness of the partial gradient needed in
`app:ch_seed:eq:seed-quotient-integral`, on the original open product. -/
theorem contDiffOn_phaseGradient {S : P → E → ℝ} {V : Set P} {U : Set E}
    (hV : IsOpen V) (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun q : P × E ↦ gradient (S q.1) q.2) (V ×ˢ U) := by
  have hs : ContDiffOn ℝ ∞ (fun q : E × P ↦ S q.2 q.1) (U ×ˢ V) :=
    hS.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ h ↦ ⟨h.2, h.1⟩)
  have hd := (contDiffOn_parameterFDeriv hU hV hs).comp
    (contDiffOn_snd.prodMk contDiffOn_fst)
    (fun (q : P × E) (h : q ∈ V ×ˢ U) ↦ ⟨h.2, h.1⟩)
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hd

variable [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ A] in
/-- The shifted-gradient integrand is jointly smooth before integration
(`app:ch_seed:eq:seed-quotient-integral`). `A` includes all physical, data,
spectator and epsilon variables. -/
theorem contDiffOn_phaseShiftIntegrand
    {S : P → E → ℝ} {V : Set P} {U : Set E} {D : Set A} {W : Set ℝ}
    {p : A → P} {z v : A → E} {e : A → ℝ}
    (hV : IsOpen V) (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hp : ContDiffOn ℝ ∞ p D) (hz : ContDiffOn ℝ ∞ z D)
    (hv : ContDiffOn ℝ ∞ v D) (he : ContDiffOn ℝ ∞ e D)
    (hmem : ∀ a ∈ D, ∀ t ∈ W, (p a, z a + (t * e a) • v a) ∈ V ×ˢ U) :
    ContDiffOn ℝ ∞ (fun q : A × ℝ ↦
      inner ℝ (gradient (S (p q.1)) (z q.1 + (q.2 * e q.1) • v q.1)) (v q.1))
      (D ×ˢ W) := by
  have hp' := hp.comp contDiffOn_fst (fun (q : A × ℝ) (h : q ∈ D ×ˢ W) ↦ h.1)
  have hz' := hz.comp contDiffOn_fst (fun (q : A × ℝ) (h : q ∈ D ×ˢ W) ↦ h.1)
  have hv' := hv.comp contDiffOn_fst (fun (q : A × ℝ) (h : q ∈ D ×ˢ W) ↦ h.1)
  have he' := he.comp contDiffOn_fst (fun (q : A × ℝ) (h : q ∈ D ×ˢ W) ↦ h.1)
  exact ((contDiffOn_phaseGradient hV hU hS).comp
    (hp'.prodMk (hz'.add ((contDiffOn_snd.mul he').smul hv')))
    (fun q hq ↦ hmem q.1 hq.1 q.2 hq.2)).inner ℝ hv'

/-- Smoothness of the literal published quotient through zero, with a smooth
carrier and every spectator retained (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem contDiffOn_phaseShiftQuotient_comp
    {S : P → E → ℝ} {V : Set P} {U : Set E} {D : Set A} {W : Set ℝ}
    {p : A → P} {z v : A → E} {e : A → ℝ}
    (hV : IsOpen V) (hU : IsOpen U) (hD : IsOpen D) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hp : ContDiffOn ℝ ∞ p D) (hz : ContDiffOn ℝ ∞ z D)
    (hv : ContDiffOn ℝ ∞ v D) (he : ContDiffOn ℝ ∞ e D)
    (hmem : ∀ a ∈ D, ∀ t ∈ W, (p a, z a + (t * e a) • v a) ∈ V ×ˢ U) :
    ContDiffOn ℝ ∞ (fun a ↦ phaseShiftQuotient S (p a) (z a) (v a) (e a)) D :=
  contDiffOn_unitIntervalParameterIntegral hD hW hIW
    (contDiffOn_phaseShiftIntegrand hV hU hS hp hz hv he hmem)

/-- The full joint derivative of the divided phase passes under the
integral (`app:ch_seed:eq:seed-quotient-integral`), including at zero shift. -/
theorem hasFDerivAt_phaseShiftQuotient_comp
    {S : P → E → ℝ} {V : Set P} {U : Set E} {D : Set A} {W : Set ℝ}
    {p : A → P} {z v : A → E} {e : A → ℝ}
    (hV : IsOpen V) (hU : IsOpen U) (hD : IsOpen D) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hp : ContDiffOn ℝ ∞ p D) (hz : ContDiffOn ℝ ∞ z D)
    (hv : ContDiffOn ℝ ∞ v D) (he : ContDiffOn ℝ ∞ e D)
    (hmem : ∀ a ∈ D, ∀ t ∈ W, (p a, z a + (t * e a) • v a) ∈ V ×ˢ U)
    {a : A} (ha : a ∈ D) :
    HasFDerivAt (fun a ↦ phaseShiftQuotient S (p a) (z a) (v a) (e a))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun a ↦
        inner ℝ (gradient (S (p a)) (z a + (t * e a) • v a)) (v a)) a) a :=
  hasFDerivAt_unitIntervalParameterIntegral hD hW hIW
    (contDiffOn_phaseShiftIntegrand hV hU hS hp hz hv he hmem) ha

omit [FiniteDimensional ℝ A] in
/-- Smoothness of the physical segment integrand in
`app:ch_seed:prop:seed-phase-charts`. This is used with the proved smooth
integral quotient as `S`. -/
theorem contDiffOn_averagedPhaseIntegrand
    {S : P → E → ℝ} {V : Set P} {U : Set E} {D : Set A} {W : Set ℝ}
    {p : A → P} {x y : A → E}
    (hV : IsOpen V) (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hp : ContDiffOn ℝ ∞ p D) (hx : ContDiffOn ℝ ∞ x D)
    (hy : ContDiffOn ℝ ∞ y D)
    (hmem : ∀ a ∈ D, ∀ t ∈ W, (p a, y a + t • (x a - y a)) ∈ V ×ˢ U) :
    ContDiffOn ℝ ∞ (fun q : A × ℝ ↦
      gradient (S (p q.1)) (y q.1 + q.2 • (x q.1 - y q.1))) (D ×ˢ W) := by
  have hp' := hp.comp contDiffOn_fst (fun (q : A × ℝ) (h : q ∈ D ×ˢ W) ↦ h.1)
  have hx' := hx.comp contDiffOn_fst (fun (q : A × ℝ) (h : q ∈ D ×ˢ W) ↦ h.1)
  have hy' := hy.comp contDiffOn_fst (fun (q : A × ℝ) (h : q ∈ D ×ˢ W) ↦ h.1)
  exact (contDiffOn_phaseGradient hV hU hS).comp
    (hp'.prodMk (hy'.add (contDiffOn_snd.smul (hx'.sub hy'))))
    (fun q hq ↦ hmem q.1 hq.1 q.2 hq.2)

/-- Smoothness of the literal two-point average with every parameter retained
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem contDiffOn_averagedPhaseGradient_comp
    {S : P → E → ℝ} {V : Set P} {U : Set E} {D : Set A} {W : Set ℝ}
    {p : A → P} {x y : A → E}
    (hV : IsOpen V) (hU : IsOpen U) (hD : IsOpen D) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hp : ContDiffOn ℝ ∞ p D) (hx : ContDiffOn ℝ ∞ x D)
    (hy : ContDiffOn ℝ ∞ y D)
    (hmem : ∀ a ∈ D, ∀ t ∈ W, (p a, y a + t • (x a - y a)) ∈ V ×ˢ U) :
    ContDiffOn ℝ ∞ (fun a ↦ averagedPhaseGradient S (p a) (x a) (y a)) D :=
  contDiffOn_unitIntervalParameterIntegral hD hW hIW
    (contDiffOn_averagedPhaseIntegrand hV hU hS hp hx hy hmem)

/-- Exact joint differentiation of the physical average in
`app:ch_seed:prop:seed-phase-charts`. No derivative bound is an input. -/
theorem hasFDerivAt_averagedPhaseGradient_comp
    {S : P → E → ℝ} {V : Set P} {U : Set E} {D : Set A} {W : Set ℝ}
    {p : A → P} {x y : A → E}
    (hV : IsOpen V) (hU : IsOpen U) (hD : IsOpen D) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hp : ContDiffOn ℝ ∞ p D) (hx : ContDiffOn ℝ ∞ x D)
    (hy : ContDiffOn ℝ ∞ y D)
    (hmem : ∀ a ∈ D, ∀ t ∈ W, (p a, y a + t • (x a - y a)) ∈ V ×ˢ U)
    {a : A} (ha : a ∈ D) :
    HasFDerivAt (fun a ↦ averagedPhaseGradient S (p a) (x a) (y a))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun a ↦
        gradient (S (p a)) (y a + t • (x a - y a))) a) a :=
  hasFDerivAt_unitIntervalParameterIntegral hD hW hIW
    (contDiffOn_averagedPhaseIntegrand hV hU hS hp hx hy hmem) ha

end JanetCartan.FullPhaseCharts
