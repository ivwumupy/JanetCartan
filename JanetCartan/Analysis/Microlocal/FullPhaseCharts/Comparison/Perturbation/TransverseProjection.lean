module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Basic
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness.Calculus

/-!
# Transverse projection of the literal full chart

For `app:ch_seed:prop:seed-phase-charts`, the transverse averaged gradient at
fixed time is the transverse component of the full averaged gradient. The
consumer is the transfer of full-chart perturbation bounds to transverse
charts. Smoothness and integrability are derived from the local phase and
carrier on buffered domains, using `app:ch_seed:eq:seed-quotient-integral`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P X E : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ E] in
private theorem contDiffOn_covectorGradient {S : X × E → ℝ} {Ω : Set (X × E)}
    (hΩ : IsOpen Ω) (hS : ContDiffOn ℝ ∞ S Ω) :
    ContDiffOn ℝ ∞ (fun q : X × E ↦ gradient (fun ξ ↦ S (q.1, ξ)) q.2) Ω := by
  intro q hq
  have h : ContDiffAt ℝ ∞ (fun a : (X × E) × E ↦ S (a.1.1, a.2)) (q, q.2) :=
    (hS.contDiffAt (hΩ.mem_nhds hq)).comp (q, q.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact ((InnerProductSpace.toDual ℝ E).symm.contDiff.contDiffAt.comp q
    (h.fderiv contDiffAt_snd (by simp))).contDiffWithinAt

omit [CompleteSpace X] in
/-- Smoothness of the literal integral quotient on physical and data boxes
from local phase/carrier smoothness and shifted-segment containment
(`app:ch_seed:eq:seed-quotient-integral`). This supplies the regularity used
by `transverseChart_eq_fullChart_snd`, including at zero shift. -/
theorem contDiffOn_modulationPhase_of_shift_mem
    {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ} {p : P}
    {D : Set (ℝ × E)} {B : Set X} {Ω : Set (X × E)} {W : Set ℝ}
    (hD : IsOpen D) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hζ : ContDiffOn ℝ ∞ (fun u : ℝ × E ↦ ζ (p, u.1)) D)
    (hshift : ∀ u ∈ D, ∀ x ∈ B, ∀ s ∈ W,
      (x, ζ (p, u.1) + (s * ε) • u.2) ∈ Ω) :
    ContDiffOn ℝ ∞ (Function.uncurry (modulationPhase S ζ ε p)) (D ×ˢ B) := by
  unfold Function.uncurry modulationPhase phaseShiftQuotient
  apply contDiffOn_unitIntervalParameterIntegral (g := fun a : ((ℝ × E) × X) × ℝ ↦
    inner ℝ (gradient (fun ξ ↦ S (a.1.2, ξ))
      (ζ (p, a.1.1.1) + (a.2 * ε) • a.1.1.2)) a.1.1.2) (hD.prod hB) hW hIW
  have hz : ContDiffOn ℝ ∞
      (fun a : ((ℝ × E) × X) × ℝ ↦ ζ (p, a.1.1.1)) ((D ×ˢ B) ×ˢ W) :=
    hζ.comp contDiffOn_fst.fst (fun _ ha ↦ ha.1.1)
  exact ((contDiffOn_covectorGradient hΩ hS).comp
    (contDiffOn_fst.snd.prodMk (hz.add ((contDiffOn_snd.mul contDiffOn_const).smul
      contDiffOn_fst.fst.snd)))
    (fun a ha ↦ hshift a.1.1 ha.1.1 a.1.2 ha.1.2 a.2 ha.2)).inner ℝ
      contDiffOn_fst.fst.snd

/-- The actual averaged-gradient chart is smooth in its data on a buffered
physical segment (`app:ch_seed:prop:seed-phase-charts`). The quotient
regularity required for differentiation is proved from the phase. -/
theorem contDiffOn_modulationChart_of_shift_mem
    {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ} {p : P}
    {D : Set (ℝ × E)} {B : Set X} {Ω : Set (X × E)} {W : Set ℝ} {x x' : X}
    (hD : IsOpen D) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hζ : ContDiffOn ℝ ∞ (fun u : ℝ × E ↦ ζ (p, u.1)) D)
    (hshift : ∀ u ∈ D, ∀ x ∈ B, ∀ s ∈ W,
      (x, ζ (p, u.1) + (s * ε) • u.2) ∈ Ω)
    (hseg : ∀ r ∈ W, x' + r • (x - x') ∈ B) :
    ContDiffOn ℝ ∞ (modulationChart S ζ ε p x x') D := by
  exact contDiffOn_averagedPhaseGradient_comp hD hB hD hW hIW
    (contDiffOn_modulationPhase_of_shift_mem hD hB hΩ hW hIW hS hζ hshift)
    contDiffOn_id contDiffOn_const contDiffOn_const (fun u hu r hr ↦ ⟨hu, hseg r hr⟩)

omit [FiniteDimensional ℝ E] in
private theorem gradient_fixedTime_slice {f : WithLp 2 (ℝ × E) → ℝ} {t : ℝ} {y : E}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (t, y))) :
    gradient (fun y ↦ f (WithLp.toLp 2 (t, y))) y =
      (gradient f (WithLp.toLp 2 (t, y))).ofLp.2 := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E
  have hd : HasFDerivAt (fun y : E ↦ WithLp.toLp 2 (t, y))
      (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ E)) y := by
    convert e.symm.hasFDerivAt.comp y
      ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)) using 1 <;> rfl
  apply ext_inner_right ℝ
  intro v
  have hc := (hf.hasFDerivAt.comp y hd).fderiv
  simp only [Function.comp_def] at hc
  rw [inner_gradient_left, hc]
  change fderiv ℝ f (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (0, v)) = _
  rw [← inner_gradient_left]
  simp only [WithLp.prod_inner_apply, inner_zero_right, zero_add]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem fixedTime_segment (t r : ℝ) (y y' : E) :
    WithLp.toLp 2 (t, y' + r • (y - y')) =
      WithLp.toLp 2 (t, y') + r • (WithLp.toLp 2 (t, y) - WithLp.toLp 2 (t, y')) := by
  apply WithLp.ofLp_injective
  simp

/-- The transverse chart is exactly the transverse projection of the literal
full chart (`app:ch_seed:prop:seed-phase-charts`). The only analytic inputs
are local smoothness of the phase/carrier and containment of shifted points
in the open phase domain. No chart comparison estimate is assumed. -/
theorem transverseChart_eq_fullChart_snd
    {S : WithLp 2 (ℝ × E) × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ} {p : P}
    {D : Set (ℝ × E)} {B : Set (WithLp 2 (ℝ × E))}
    {Ω : Set (WithLp 2 (ℝ × E) × E)} {W : Set ℝ}
    (hD : IsOpen D) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hζ : ContDiffOn ℝ ∞ (fun u : ℝ × E ↦ ζ (p, u.1)) D)
    (hshift : ∀ u ∈ D, ∀ x ∈ B, ∀ s ∈ W,
      (x, ζ (p, u.1) + (s * ε) • u.2) ∈ Ω)
    {t : ℝ} {y y' : E}
    (hseg : ∀ r ∈ Icc (0 : ℝ) 1, WithLp.toLp 2 (t, y' + r • (y - y')) ∈ B)
    {u : ℝ × E} (hu : u ∈ D) :
    transverseChart S ζ ε p t y y' u =
      (fullChart S ζ ε p (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (t, y')) u).2 := by
  have hQ := contDiffOn_modulationPhase_of_shift_mem hD hB hΩ hW hIW hS hζ hshift
  have hslice : ContDiffOn ℝ ∞ (modulationPhase S ζ ε p u) B :=
    hQ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx ↦ ⟨hu, hx⟩)
  have hgrad := continuousOn_gradient_of_contDiffOn hB (hslice.of_le (by simp))
  have hi : IntervalIntegrable (fun r : ℝ ↦ gradient (modulationPhase S ζ ε p u)
      (WithLp.toLp 2 (t, y') + r • (WithLp.toLp 2 (t, y) - WithLp.toLp 2 (t, y'))))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (a := (0 : ℝ)) (b := 1) zero_le_one
    exact hgrad.comp (by fun_prop) (fun r hr ↦ by rw [← fixedTime_segment]; exact hseg r hr)
  let π : WithLp 2 (ℝ × E) →L[ℝ] E :=
    (ContinuousLinearMap.snd ℝ ℝ E).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap
  have hint := π.intervalIntegral_comp_comm hi
  unfold transverseChart fullChart modulationChart averagedPhaseGradient
  change (∫ r in (0 : ℝ)..1, gradient (modulationPhase
    (fun q : E × E ↦ S (WithLp.toLp 2 (t, q.1), q.2)) ζ ε p u)
      (y' + r • (y - y'))) = π (∫ r in (0 : ℝ)..1,
        gradient (modulationPhase S ζ ε p u)
          (WithLp.toLp 2 (t, y') + r • (WithLp.toLp 2 (t, y) - WithLp.toLp 2 (t, y'))))
  rw [← hint]
  apply intervalIntegral.integral_congr
  intro r hr
  have hm := hseg r (by simpa using hr)
  change gradient (fun y ↦ modulationPhase S ζ ε p u (WithLp.toLp 2 (t, y)))
    (y' + r • (y - y')) = _
  rw [gradient_fixedTime_slice ((hslice.contDiffAt (hB.mem_nhds hm)).differentiableAt
    (by simp)), fixedTime_segment]
  rfl

/-- On the open direction neighborhood `{η | (z, η) ∈ D}`, the actual
Fréchet derivative of the transverse chart is the projection of the full
chart's direction derivative (`app:ch_seed:prop:seed-phase-charts`). The
buffered physical segment supplies smoothness of the full chart, so this
asserts existence of the derivative as well as identifying it. -/
theorem hasFDerivAt_transverseChart_projection
    {S : WithLp 2 (ℝ × E) × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ} {p : P}
    {D : Set (ℝ × E)} {B : Set (WithLp 2 (ℝ × E))}
    {Ω : Set (WithLp 2 (ℝ × E) × E)} {W : Set ℝ}
    (hD : IsOpen D) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hζ : ContDiffOn ℝ ∞ (fun u : ℝ × E ↦ ζ (p, u.1)) D)
    (hshift : ∀ u ∈ D, ∀ x ∈ B, ∀ s ∈ W,
      (x, ζ (p, u.1) + (s * ε) • u.2) ∈ Ω)
    {t : ℝ} {y y' : E}
    (hseg : ∀ r ∈ W, WithLp.toLp 2 (t, y' + r • (y - y')) ∈ B)
    {z : ℝ} {η : E} (hu : (z, η) ∈ D) :
    HasFDerivAt (fun η ↦ transverseChart S ζ ε p t y y' (z, η))
      ((ContinuousLinearMap.snd ℝ ℝ E).comp
        (fderiv ℝ (fun η ↦ fullChart S ζ ε p
          (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (t, y')) (z, η)) η)) η := by
  have hC := contDiffOn_modulationChart_of_shift_mem hD hB hΩ hW hIW hS hζ hshift
    (x := WithLp.toLp 2 (t, y)) (x' := WithLp.toLp 2 (t, y'))
    (fun r hr ↦ by rw [← fixedTime_segment]; exact hseg r hr)
  have hF : DifferentiableAt ℝ (fun η ↦ fullChart S ζ ε p
      (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (t, y')) (z, η)) η := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).contDiff.contDiffAt.comp η
      ((hC.contDiffAt (hD.mem_nhds hu)).comp η
        (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hd := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp η hF.hasFDerivAt
  apply hd.congr_of_eventuallyEq
  have he : ∀ᶠ v : E in 𝓝 η, (z, v) ∈ D :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually (hD.mem_nhds hu)
  filter_upwards [he] with v hv
  exact transverseChart_eq_fullChart_snd hD hB hΩ hW hIW hS hζ hshift
    (fun r hr ↦ hseg r (hIW hr)) hv

/-- Equality of the actual `η`-Fréchet derivatives, used to transfer the
full-chart `C¹` perturbation bound to the transverse chart in
`app:ch_seed:prop:seed-phase-charts`. All regularity is derived from the
phase and carrier, including the existence of these derivatives. -/
theorem fderiv_transverseChart_eq_fullChart_snd
    {S : WithLp 2 (ℝ × E) × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ} {p : P}
    {D : Set (ℝ × E)} {B : Set (WithLp 2 (ℝ × E))}
    {Ω : Set (WithLp 2 (ℝ × E) × E)} {W : Set ℝ}
    (hD : IsOpen D) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hζ : ContDiffOn ℝ ∞ (fun u : ℝ × E ↦ ζ (p, u.1)) D)
    (hshift : ∀ u ∈ D, ∀ x ∈ B, ∀ s ∈ W,
      (x, ζ (p, u.1) + (s * ε) • u.2) ∈ Ω)
    {t : ℝ} {y y' : E}
    (hseg : ∀ r ∈ W, WithLp.toLp 2 (t, y' + r • (y - y')) ∈ B)
    {z : ℝ} {η : E} (hu : (z, η) ∈ D) :
    fderiv ℝ (fun η ↦ transverseChart S ζ ε p t y y' (z, η)) η =
      (ContinuousLinearMap.snd ℝ ℝ E).comp
        (fderiv ℝ (fun η ↦ fullChart S ζ ε p
          (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (t, y')) (z, η)) η) :=
  (hasFDerivAt_transverseChart_projection hD hB hΩ hW hIW hS hζ hshift hseg hu).fderiv

end JanetCartan.FullPhaseCharts.Comparison
