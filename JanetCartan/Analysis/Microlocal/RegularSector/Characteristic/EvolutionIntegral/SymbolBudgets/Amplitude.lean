module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneProfiles

/-!
# Primitive amplitude budgets for the elapsed full amplitude

All norms are Frobenius norms. The actual differentiated product contains
both physical positions, both physical masks, and the conic multiplier.
The original symbol retains its lower-end buffer. The fixed chart inclusion
is the geometry input; it must place the normalized spatial covectors in the
original buffered spatial symbol chart. In particular, in the order-minus-one
case this is a spatial annular chart, justified on the multiplier cone by
`norm_le_spatial_of_cone`.

Source: `app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular_base:eq:fixed-time-representation`, and
`app:ch_regular_base:eq:fio-input`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles GainOneProfiles
variable {d q : ℕ}

/-- Both fixed physical masks, before multiplication by the original spatial
symbol, in `app:ch_regular_base:eq:fixed-time-representation`. -/
def physicalMasks (χout χsource : Euclidean (d + 1) → ℂ) (p : Point (d + 1)) : ℂ :=
  χout p.1.1 * χsource p.1.2

/-- The fixed multiplier as a joint primitive, independent of both positions.
Its normalized seminorm is the order-zero multiplier budget in the retarded lemma. -/
def jointMultiplier (β : Euclidean (d + 1) → ℂ) (p : Point (d + 1)) : ℂ := β p.2

/-- Original joint normalization for order `-o`, where the consumers use
`o=0` and `o=1`. Both original time variables are differentiated. -/
def twoTimeOrderField (o : ℕ) (R : ℝ) (b : TwoTimeAmplitude d q) :
    TwoTimePoint d → Matrix (Fin q) (Fin q) ℂ :=
  R ^ o • normalizedField R (jointAmplitude b)

/-- The original spatial symbol seminorm, before the elapsed substitution.
This is an actual supremum of joint derivative norms, not an operator budget. -/
def twoTimeOrderSeminorm (o : ℕ) (J : Set (TwoTimePoint d)) (j : ℕ)
    (b : TwoTimeAmplitude d q) : ℝ :=
  sSup (range fun R : {R : ℝ // 1 ≤ R} ↦ cNorm J j (twoTimeOrderField o R b))

/-- Finiteness of the original spatial symbol seminorm in the retarded lemma. -/
def BoundedTwoTimeOrderSeminorm (o : ℕ) (J : Set (TwoTimePoint d)) (j : ℕ)
    (b : TwoTimeAmplitude d q) : Prop :=
  BddAbove (range fun R : {R : ℝ // 1 ≤ R} ↦ cNorm J j (twoTimeOrderField o R b))

/-- Positivity of the original spatial amplitude budget (`fio-input`). -/
theorem twoTimeOrderSeminorm_nonneg (o : ℕ) (J : Set (TwoTimePoint d)) (j : ℕ)
    (b : TwoTimeAmplitude d q) : 0 ≤ twoTimeOrderSeminorm o J j b := by
  apply Real.sSup_nonneg
  rintro _ ⟨R, rfl⟩
  exact cNorm_nonneg _ _ _

/-- Each radius is bounded by the original spatial symbol seminorm. -/
theorem cNorm_twoTimeOrderField_le {o j : ℕ} {J : Set (TwoTimePoint d)}
    {b : TwoTimeAmplitude d q} (hb : BoundedTwoTimeOrderSeminorm o J j b)
    {R : ℝ} (hR : 1 ≤ R) :
    cNorm J j (twoTimeOrderField o R b) ≤ twoTimeOrderSeminorm o J j b :=
  le_csSup hb ⟨⟨R, hR⟩, rfl⟩

/-- The order-zero input uses exactly `PrimitiveProfiles.normalizedSeminorm`.
Source: the single-high estimate `app:ch_regular_base:eq:fio-input`. -/
theorem twoTimeOrderSeminorm_zero (J : Set (TwoTimePoint d)) (j : ℕ)
    (b : TwoTimeAmplitude d q) :
    twoTimeOrderSeminorm 0 J j b = normalizedSeminorm J j (jointAmplitude b) := by
  simp [twoTimeOrderSeminorm, twoTimeOrderField, normalizedSeminorm]

/-- Exact factorization of the normalized elapsed amplitude. In particular,
the physical masks and the lower-time evaluation remain inside all derivatives. -/
theorem elapsedOrderField_eq (o : ℕ) (R r : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) :
    R ^ o • normalizedField R (uncurry (elapsedAmplitude b χout χsource β r)) =
      fun p ↦ physicalMasks χout χsource p •
        (normalizedField R (jointMultiplier β) p • twoTimeOrderField o R b (elapsedPoint r p)) := by
  funext p
  simp only [Pi.smul_apply, normalizedField, uncurry, elapsedAmplitude, physicalMasks,
    jointMultiplier, twoTimeOrderField, jointAmplitude, elapsedPoint_eq, spatialPart_smul]
  rw [mul_smul, smul_comm (R ^ o), smul_comm (R ^ o)]

/-- Constant depending only on the fixed masks, normalized multiplier and
order. It precedes the varying amplitude and elapsed time in `fio-input`. -/
def amplitudeMaskConstant (K : Set (Point (d + 1))) (j : ℕ)
    (χout χsource β : Euclidean (d + 1) → ℂ) : ℝ :=
  ((j + 1 : ℝ) * 2 ^ j) ^ 2 * cNorm K j (physicalMasks χout χsource) *
    normalizedSeminorm K j (jointMultiplier β)

/-- Nonnegativity of the fixed-mask constant in the elapsed symbol budget. -/
theorem amplitudeMaskConstant_nonneg (K : Set (Point (d + 1))) (j : ℕ)
    (χout χsource β : Euclidean (d + 1) → ℂ) :
    0 ≤ amplitudeMaskConstant K j χout χsource β := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (cNorm_nonneg _ _ _))
    (normalizedSeminorm_nonneg _ _ _)

/-- At each radius the actual full amplitude has a budget linear in the
original joint spatial amplitude. The contraction chart inclusion is uniform
in the later `r∈[0,Δ]` use, and no elapsed seminorm estimate is assumed.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cNorm_elapsedOrderField_le
    {K : Set (Point (d + 1))} {J U : Set (TwoTimePoint d)}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (o j : ℕ) (r R : ℝ) (hR : 1 ≤ R)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β)
    (hβbound : BoundedNormalizedSeminorm K j (jointMultiplier β))
    (hb : ContDiffOn ℝ ∞ (twoTimeOrderField o R b) U)
    (hmap : MapsTo (elapsedPoint r) K J) :
    cNorm K j (R ^ o • normalizedField R (uncurry (elapsedAmplitude b χout χsource β r))) ≤
      amplitudeMaskConstant K j χout χsource β * cNorm J j (twoTimeOrderField o R b) := by
  let V := elapsedPoint r ⁻¹' U
  have helapsed : ContDiff ℝ ∞ (elapsedPoint (d := d) r) :=
    elapsedLinear.contDiff.add contDiff_const
  have hV : IsOpen V := hU.preimage helapsed.continuous
  have hKV : K ⊆ V := fun _ hp ↦ hJU (hmap hp)
  have hM : ContDiff ℝ ∞ (physicalMasks χout χsource) :=
    (hχout.comp (contDiff_fst.comp contDiff_fst)).mul
      (hχsource.comp (contDiff_snd.comp contDiff_fst))
  have hB : ContDiff ℝ ∞ (normalizedField R (jointMultiplier β)) :=
    hβ.comp (contDiff_snd.const_smul R)
  have hA : ContDiffOn ℝ ∞ (twoTimeOrderField o R b ∘ elapsedPoint r) V :=
    hb.comp helapsed.contDiffOn (fun _ hp ↦ hp)
  have hBA := cNorm_smul_on_open_le hK hV hKV hB.contDiffOn hA j
  have hMBA := cNorm_smul_on_open_le hK hV hKV hM.contDiffOn
    (hB.contDiffOn.smul hA) j
  rw [elapsedOrderField_eq]
  apply hMBA.trans
  have hnon : 0 ≤ (j + 1 : ℝ) * 2 ^ j := by positivity
  have hinner := mul_le_mul
    (mul_le_mul_of_nonneg_left (cNorm_normalizedField_le hβbound hR) hnon)
    (cNorm_comp_elapsedPoint_le hJ hU hJU hb r hmap j)
    (cNorm_nonneg _ _ _)
    (mul_nonneg hnon (normalizedSeminorm_nonneg _ _ _))
  calc
    _ ≤ ((j + 1 : ℝ) * 2 ^ j * cNorm K j (physicalMasks χout χsource)) *
        (((j + 1 : ℝ) * 2 ^ j * normalizedSeminorm K j (jointMultiplier β)) *
          cNorm J j (twoTimeOrderField o R b)) :=
      mul_le_mul_of_nonneg_left (hBA.trans hinner)
        (mul_nonneg hnon (cNorm_nonneg _ _ _))
    _ = _ := by unfold amplitudeMaskConstant; ring

/-- Ordinary joint smoothness of the original spatial symbol produces all
normalized smoothness inputs. Geometry supplies the buffered dilation inclusion;
no bound for the elapsed amplitude is part of this premise. -/
theorem contDiffOn_twoTimeOrderField {U V : Set (TwoTimePoint d)}
    {b : TwoTimeAmplitude d q} (hb : ContDiffOn ℝ ∞ (jointAmplitude b) V)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    (o : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    ContDiffOn ℝ ∞ (twoTimeOrderField o R b) U :=
  (hb.comp (contDiffOn_fst.prodMk (contDiffOn_snd.const_smul R))
    (hrad R hR)).const_smul (R ^ o)

/-- Uniform original symbol budgets produce the actual order-zero profile
seminorm, with both positions and all masks retained. The constants contain
no varying amplitude seminorm, and are independent of `r` under the stated
fixed chart inclusion. Consumer: `IntegerBounds`, `p=0`, in `fio-input`. -/
theorem elapsedAmplitude_normalizedSeminorm_le
    {K : Set (Point (d + 1))} {J U V : Set (TwoTimePoint d)}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    (j : ℕ) (r : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β)
    (hβbound : BoundedNormalizedSeminorm K j (jointMultiplier β))
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) V)
    (hbbound : BoundedNormalizedSeminorm J j (jointAmplitude b))
    (hmap : MapsTo (elapsedPoint r) K J) :
    BoundedNormalizedSeminorm K j (uncurry (elapsedAmplitude b χout χsource β r)) ∧
      normalizedSeminorm K j (uncurry (elapsedAmplitude b χout χsource β r)) ≤
        amplitudeMaskConstant K j χout χsource β * normalizedSeminorm J j (jointAmplitude b) := by
  have hbound (R : {R : ℝ // 1 ≤ R}) :
      cNorm K j (normalizedField R (uncurry (elapsedAmplitude b χout χsource β r))) ≤
        amplitudeMaskConstant K j χout χsource β * normalizedSeminorm J j (jointAmplitude b) := by
    have h := cNorm_elapsedOrderField_le hK hJ hU hJU 0 j r R R.2 b χout χsource β
      hχout hχsource hβ hβbound (contDiffOn_twoTimeOrderField hb hrad 0 R.2) hmap
    simp only [twoTimeOrderField, pow_zero, one_smul] at h
    exact h.trans (mul_le_mul_of_nonneg_left (cNorm_normalizedField_le hbbound R.2)
      (amplitudeMaskConstant_nonneg _ _ _ _ _))
  constructor
  · exact ⟨_, by rintro _ ⟨R, rfl⟩; exact hbound R⟩
  · apply Real.sSup_le _ (mul_nonneg (amplitudeMaskConstant_nonneg _ _ _ _ _)
      (normalizedSeminorm_nonneg _ _ _))
    rintro _ ⟨R, rfl⟩
    exact hbound R

/-- The full spacetime order-minus-one profile is constructed from the
original spatial order-minus-one seminorm. The normalized spatial chart
inclusion is justified by the multiplier cone; it includes the low-frequency
shoulder and is independent of elapsed time. Consumer: `IntegerBounds`,
`p=-1`, in `app:ch_regular_base:eq:fio-input`. -/
theorem elapsedAmplitude_orderMinusOneSeminorm_le
    {K : Set (Point (d + 1))} {J U V : Set (TwoTimePoint d)}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    (j : ℕ) (r : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β)
    (hβbound : BoundedNormalizedSeminorm K j (jointMultiplier β))
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) V)
    (hbbound : BoundedTwoTimeOrderSeminorm 1 J j b)
    (hmap : MapsTo (elapsedPoint r) K J) :
    BoundedOrderMinusOneSeminorm K j (elapsedAmplitude b χout χsource β r) ∧
      orderMinusOneSeminorm K j (elapsedAmplitude b χout χsource β r) ≤
        amplitudeMaskConstant K j χout χsource β * twoTimeOrderSeminorm 1 J j b := by
  have hbound (R : {R : ℝ // 1 ≤ R}) :
      cNorm K j (orderMinusOneField R (elapsedAmplitude b χout χsource β r)) ≤
        amplitudeMaskConstant K j χout χsource β * twoTimeOrderSeminorm 1 J j b := by
    have h := cNorm_elapsedOrderField_le hK hJ hU hJU 1 j r R R.2 b χout χsource β
      hχout hχsource hβ hβbound (contDiffOn_twoTimeOrderField hb hrad 1 R.2) hmap
    simp only [pow_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (cNorm_twoTimeOrderField_le hbbound R.2)
      (amplitudeMaskConstant_nonneg _ _ _ _ _))
  constructor
  · exact ⟨_, by rintro _ ⟨R, rfl⟩; exact hbound R⟩
  · apply Real.sSup_le _ (mul_nonneg (amplitudeMaskConstant_nonneg _ _ _ _ _)
      (twoTimeOrderSeminorm_nonneg _ _ _ _))
    rintro _ ⟨R, rfl⟩
    exact hbound R

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
