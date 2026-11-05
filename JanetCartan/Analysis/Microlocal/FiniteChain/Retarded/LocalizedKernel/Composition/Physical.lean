module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Composition.Integrability
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Physical Fubini and normal translations

Absolute convergence justifies the physical substitutions and integral exchanges
in `app:ch_regular:lem:finite-chain`. These lemmas are consumed by the regularized
lower and literal upper composition identities.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Physical Fubini and the translation `z = (s+d,y)` for the lower factor.
The weights themselves supply compactness in both physical variables
(`app:ch_regular:lem:finite-chain`). -/
theorem integral_lower_normal_translation
    (α β : ℝ × E → ℝ) (L f : ℝ × E → ℂ)
    (hα : Continuous α) (hβ : Continuous β) (hL : Continuous L) (hf : Continuous f)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β) :
    (∫ z : ℝ × E, L z * ∫ d in Ici (0 : ℝ),
      Complex.I * (α z : ℂ) * (β (z.1-d,z.2) : ℂ) * f (z.1-d,z.2)) =
    ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E,
      L (b.1+d,b.2) * (Complex.I * (α (b.1+d,b.2) : ℂ) * (β b : ℂ)) * f b := by
  let g : (ℝ × E) × ℝ → ℂ := fun p =>
    L p.1 * (Complex.I * (α p.1 : ℂ) * (β (p.1.1-p.2,p.1.2) : ℂ) *
      f (p.1.1-p.2,p.1.2))
  have hg : Continuous g := by fun_prop
  have hgs : HasCompactSupport g := by
    let T : (ℝ × E) × (ℝ × E) → (ℝ × E) × ℝ :=
      fun q => (q.1,q.1.1-q.2.1)
    apply HasCompactSupport.of_support_subset_isCompact
      ((hsα.prod hsβ).image (show Continuous T by fun_prop))
    intro p hp
    have ha : α p.1 ≠ 0 := by intro hz; simp [g,hz] at hp
    have hb : β (p.1.1-p.2,p.1.2) ≠ 0 := by intro hz; simp [g,hz] at hp
    exact ⟨(p.1,(p.1.1-p.2,p.1.2)),
      ⟨subset_tsupport α ha, subset_tsupport β hb⟩, by simp [T]⟩
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap_of_hasCompactSupport hg hgs]
  apply integral_congr_ae
  filter_upwards [] with d
  let : (volume : Measure (ℝ × E)).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  rw [← integral_add_right_eq_self (fun b => g (b,d)) (d, (0 : E))]
  apply integral_congr_ae
  filter_upwards [] with b
  simp [g, Prod.add_def, mul_assoc]

/-- Physical Fubini for the literal upper factor, whose common base is already
its output (`app:ch_regular:lem:finite-chain`). -/
theorem integral_upper_normal_swap
    (α β : ℝ × E → ℝ) (L f : ℝ × E → ℂ)
    (hα : Continuous α) (hβ : Continuous β) (hL : Continuous L) (hf : Continuous f)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β) :
    (∫ b : ℝ × E, L b * ∫ d in Ici (0 : ℝ),
      -Complex.I * (β b : ℂ) * (α (b.1+d,b.2) : ℂ) * f (b.1+d,b.2)) =
    ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E,
      L b * (-Complex.I * (β b : ℂ) * (α (b.1+d,b.2) : ℂ)) * f (b.1+d,b.2) := by
  let g : (ℝ × E) × ℝ → ℂ := fun p =>
    L p.1 * (-Complex.I * (β p.1 : ℂ) * (α (p.1.1+p.2,p.1.2) : ℂ) *
      f (p.1.1+p.2,p.1.2))
  have hg : Continuous g := by fun_prop
  have hgs : HasCompactSupport g := by
    let T : (ℝ × E) × (ℝ × E) → (ℝ × E) × ℝ :=
      fun q => (q.2,q.1.1-q.2.1)
    apply HasCompactSupport.of_support_subset_isCompact
      ((hsα.prod hsβ).image (show Continuous T by fun_prop))
    intro p hp
    have ha : α (p.1.1+p.2,p.1.2) ≠ 0 := by intro hz; simp [g,hz] at hp
    have hb : β p.1 ≠ 0 := by intro hz; simp [g,hz] at hp
    exact ⟨((p.1.1+p.2,p.1.2),p.1),
      ⟨subset_tsupport α ha, subset_tsupport β hb⟩, by simp [T]⟩
  simp_rw [← integral_const_mul]
  exact (integral_integral_swap_of_hasCompactSupport hg hgs).trans (by
    apply integral_congr_ae
    filter_upwards [] with d
    apply integral_congr_ae
    filter_upwards [] with b
    simp [mul_assoc])

/-- The physical lower integrand after frequency integration
(`app:ch_regular:lem:finite-chain`). -/
def lowerCompositionIntegrand (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (p : (ℝ × (ℝ × E)) × (ℝ × E)) : ℂ :=
  leftKernel (complementarySymbol r mo) xo (p.1.2.1+p.1.1,p.1.2.2) *
    (Complex.I * (α (p.1.2.1+p.1.1,p.1.2.2) : ℂ) * (β p.1.2 : ℂ)) *
      rightKernel mi p.1.2 p.2 * u p.2

/-- The physical upper integrand, retaining the literal scalar and input time
(`app:ch_regular:lem:finite-chain`). -/
def upperCompositionIntegrand (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (p : (ℝ × (ℝ × E)) × (ℝ × E)) : ℂ :=
  leftKernel (complementarySymbol r mo) xo p.1.2 *
    (-Complex.I * (β p.1.2 : ℂ) * (α (p.1.2.1+p.1.1,p.1.2.2) : ℂ)) *
      rightKernel mi (p.1.2.1+p.1.1,p.1.2.2) p.2 * u p.2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem compactSupport_physical_of_weight_factors
    (α β : ℝ × E → ℝ) (u : ℝ × E → ℂ)
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β) (hu : HasCompactSupport u)
    (f : (ℝ × (ℝ × E)) × (ℝ × E) → ℂ)
    (hf : ∀ p, f p ≠ 0 → α (p.1.2.1+p.1.1,p.1.2.2) ≠ 0 ∧
      β p.1.2 ≠ 0 ∧ u p.2 ≠ 0) : HasCompactSupport f := by
  let T : ((ℝ × E) × (ℝ × E)) × (ℝ × E) →
      (ℝ × (ℝ × E)) × (ℝ × E) := fun q => ((q.1.1.1-q.1.2.1,q.1.2),q.2)
  apply HasCompactSupport.of_support_subset_isCompact
    (((hα.prod hβ).prod hu).image (show Continuous T by fun_prop))
  intro p hp
  obtain ⟨ha,hb,hu⟩ := hf p hp
  exact ⟨(((p.1.2.1+p.1.1,p.1.2.2),p.1.2),p.2),
    ⟨⟨subset_tsupport α ha, subset_tsupport β hb⟩,subset_tsupport u hu⟩, by simp [T]⟩

/-- Joint compact support in normal, base and source variables for physical
lower Fubini (`app:ch_regular:lem:finite-chain`). -/
theorem hasCompactSupport_lowerCompositionIntegrand
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β) (hsu : HasCompactSupport u) :
    HasCompactSupport (lowerCompositionIntegrand α β mi mo r u xo) := by
  apply compactSupport_physical_of_weight_factors α β u hsα hsβ hsu
  intro p hp
  refine ⟨?_, ?_, ?_⟩ <;> intro hz <;> simp [lowerCompositionIntegrand, hz] at hp

/-- Joint compact support for physical upper Fubini
(`app:ch_regular:lem:finite-chain`). -/
theorem hasCompactSupport_upperCompositionIntegrand
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β) (hsu : HasCompactSupport u) :
    HasCompactSupport (upperCompositionIntegrand α β mi mo r u xo) := by
  apply compactSupport_physical_of_weight_factors α β u hsα hsβ hsu
  intro p hp
  refine ⟨?_, ?_, ?_⟩ <;> intro hz <;> simp [upperCompositionIntegrand, hz] at hp

/-- Joint continuity of the physical lower integrand, for the source/normal/base
Fubini exchange (`app:ch_regular:lem:finite-chain`). -/
theorem continuous_lowerCompositionIntegrand
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (hu : Continuous u)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r) :
    Continuous (lowerCompositionIntegrand α β mi mo r u xo) := by
  have hL : Continuous (fun p : (ℝ × (ℝ × E)) × (ℝ × E) =>
      leftKernel (complementarySymbol r mo) xo (p.1.2.1+p.1.1,p.1.2.2)) :=
    (contDiff_leftKernel_complementarySymbol mo r ho hr hsr).continuous.comp
    (continuous_const.prodMk ((continuous_fst.snd.fst.add continuous_fst.fst).prodMk continuous_fst.snd.snd))
  have hR : Continuous (fun p : (ℝ × (ℝ × E)) × (ℝ × E) =>
      rightKernel mi p.1.2 p.2) := (contDiff_rightKernel mi hi hsi).continuous.comp
    (continuous_fst.snd.prodMk continuous_snd)
  unfold lowerCompositionIntegrand
  exact (((hL.mul ((continuous_const.mul (by fun_prop)).mul (by fun_prop))).mul hR).mul
    (hu.comp continuous_snd))

/-- Joint integrability of the physical lower integrand on the normal half-space,
including the common base and source (`app:ch_regular:lem:finite-chain`). -/
theorem integrable_lowerCompositionIntegrand
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (hu : Continuous u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r)
    (hsu : HasCompactSupport u) :
    Integrable (lowerCompositionIntegrand α β mi mo r u xo)
      (((volume.restrict (Ici (0 : ℝ))).prod volume).prod volume) :=
  (continuous_lowerCompositionIntegrand α β mi mo r u xo
    hα hβ hi ho hr hu hsi hsr).integrable_of_hasCompactSupport
      (hasCompactSupport_lowerCompositionIntegrand α β mi mo r u xo hsα hsβ hsu)

/-- Joint continuity of the physical upper integrand, for the source/normal/base
Fubini exchange (`app:ch_regular:lem:finite-chain`). -/
theorem continuous_upperCompositionIntegrand
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (hu : Continuous u)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r) :
    Continuous (upperCompositionIntegrand α β mi mo r u xo) := by
  have hL : Continuous (fun p : (ℝ × (ℝ × E)) × (ℝ × E) =>
      leftKernel (complementarySymbol r mo) xo p.1.2) :=
    (contDiff_leftKernel_complementarySymbol mo r ho hr hsr).continuous.comp
    (continuous_const.prodMk continuous_fst.snd)
  have hR : Continuous (fun p : (ℝ × (ℝ × E)) × (ℝ × E) =>
      rightKernel mi (p.1.2.1+p.1.1,p.1.2.2) p.2) := (contDiff_rightKernel mi hi hsi).continuous.comp
    (((continuous_fst.snd.fst.add continuous_fst.fst).prodMk continuous_fst.snd.snd).prodMk continuous_snd)
  unfold upperCompositionIntegrand
  exact (((hL.mul ((continuous_const.mul (by fun_prop)).mul (by fun_prop))).mul hR).mul
    (hu.comp continuous_snd))

/-- Joint integrability of the physical upper integrand on the normal half-space,
including the common base and source (`app:ch_regular:lem:finite-chain`). -/
theorem integrable_upperCompositionIntegrand
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (hu : Continuous u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r)
    (hsu : HasCompactSupport u) :
    Integrable (upperCompositionIntegrand α β mi mo r u xo)
      (((volume.restrict (Ici (0 : ℝ))).prod volume).prod volume) :=
  (continuous_upperCompositionIntegrand α β mi mo r u xo
    hα hβ hi ho hr hu hsi hsr).integrable_of_hasCompactSupport
      (hasCompactSupport_upperCompositionIntegrand α β mi mo r u xo hsα hsβ hsu)

/-- The precise three-variable exchange used by both regularized composition
identities (`app:ch_regular:lem:finite-chain`). Integrability is supplied by the
preceding physical integrand theorems. -/
theorem integral_source_normal_base_swap
    (f : (ℝ × (ℝ × E)) × (ℝ × E) → ℂ)
    (hf : Integrable f (((volume.restrict (Ici (0 : ℝ))).prod volume).prod volume)) :
    (∫ d in Ici (0 : ℝ), ∫ b : ℝ × E, ∫ xi : ℝ × E, f ((d,b),xi)) =
      ∫ xi : ℝ × E, ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E, f ((d,b),xi) := by
  rw [← integral_prod _ hf.integral_prod_left,
    integral_integral_swap (f := fun db xi => f (db,xi)) hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with xi hxi
  exact integral_prod _ hxi

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
