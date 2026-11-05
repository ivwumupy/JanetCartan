module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Row
public import JanetCartan.Analysis.Operator.CoerciveInverse

/-!
# The original inverse and the factor-four positive density

The algebraic assembly in `app:ch_background:eq:bg-current-raising` and
`app:ch_background:eq:bg-density-four`. The inverse here belongs to the
UNCORRECTED row. It is not the corrected positive row's later fixed `Q₀`.
The literal uncut synthesis is applied to its actual adjoint output. The
exterior channel is retained globally and vanishes only on its plateau.

The row realization, its positive gap, and mixed adjoint regularity are
primitive inputs still owed by the continuum producers. The result below
derives cancellation from the inverse equation; it does not assume cancellation
or assert smoothness, smallness, or a gap for the corrected positive row.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.PositiveBackground
open ContinuumRow RawCutoffBounds

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The measured source `-θ q_G(R₀)/2` as an element of the original output
space (`app:ch_background:eq:bg-current-raising`). The smooth physical
representative is supplied by the source construction. -/
def inverseSource (θ : C(Torus n, ℝ)) (residual : OutputL2 n) : OutputL2 n :=
  (- (1 / 2 : ℝ)) • cutoffMultiplier θ residual

/-- The actual raw correction from the uncorrected augmented row, including
its exterior slot (`app:ch_background:eq:bg-current-raising`). -/
def uncorrectedRawCorrection (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ θ : C(Torus n, ℝ)) (residual : OutputL2 n) : AugmentedInput n ι :=
  CoerciveInverse.rightInverse (augmentedRow image U ψ) (inverseSource θ residual)

/-- Literal factor-four synthesis, with no initial-position or upper-frequency
cutoff (`app:ch_background:eq:bg-density-four`). -/
def uncorrectedDensity (d : ι → CarrierData n N)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ θ : C(Torus n, ℝ)) (residual : OutputL2 n)
    (a : ι) : CarrierVariable n → ℝ :=
  UncutDensity.initialDensity (d a) 4
    ((uncorrectedRawCorrection image U ψ θ residual).fst.snd a)

/-- The source cutoff contributes exactly `-1/2`, before any plateau is used
(`app:ch_background:eq:bg-current-raising`). -/
theorem inverseSource_coeFn (θ : C(Torus n, ℝ)) (residual : OutputL2 n) :
    inverseSource θ residual =ᵐ[volume]
      fun x ↦ (- (1 / 2 : ℝ) * θ x) • residual x := by
  filter_upwards [Lp.coeFn_smul (- (1 / 2 : ℝ)) (cutoffMultiplier θ residual),
    cutoffMultiplier_coeFn θ residual] with x hx hθ
  exact hx.trans (by rw [Pi.smul_apply, hθ, smul_smul])

/-- The exterior-augmented normal inverse solves the SAME compact source
(`app:ch_background:eq:bg-current-raising`). -/
theorem augmentedRow_uncorrectedRawCorrection
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ θ : C(Torus n, ℝ)) (residual : OutputL2 n)
    {c : ℝ} (hc : 0 < c)
    (hgap : ∀ w, c * ‖w‖ ^ 2 ≤ ‖(augmentedRow image U ψ).adjoint w‖ ^ 2) :
    augmentedRow image U ψ (uncorrectedRawCorrection image U ψ θ residual) =
      inverseSource θ residual :=
  CoerciveInverse.apply_rightInverse _ hc hgap _

/-- The literal synthesized density has the original carrier plateau product
(`app:ch_background:eq:bg-density-twice`). This statement applies to every
initial position, not merely almost everywhere in the initial variables. -/
theorem externalWeight_mul_uncorrectedDensity
    (d : ι → CarrierData n N) (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ a z η, (d a).angularCutoff z η ≠ 0 → χ a z = 1)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ θ : C(Torus n, ℝ)) (residual : OutputL2 n) (a : ι) (p : CarrierVariable n) :
    χ a p.1 ^ 2 * uncorrectedDensity d image U ψ θ residual a p =
      uncorrectedDensity d image U ψ θ residual a p :=
  UncutDensity.externalWeight_mul_initialDensity (d a) (χ a) (hχ a) 4 _ p

/-- Assemble `4 Re` synthesis and the original inverse to obtain the reduced
mean cancellation on the source/exterior plateaus
(`app:ch_background:eq:bg-current-identity`). The density identity is supplied
by the proved raw-domain theorem, not an assumed `hcancel`. The image term is
still its L² realization; identifying it with the smooth physical tangent
strain is the subsequent geometric realization step. -/
theorem uncorrectedDensity_core_cancellation
    (d : ι → CarrierData n N) (s : ℕ) (hs : n - 1 < 2 * s)
    (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ a z η, (d a).angularCutoff z η ≠ 0 → χ a z = 1)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ a (u : carrierInitialTestSpace n),
      U a (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d a) u.val)
    (hk : ∀ a x, AEStronglyMeasurable (carrierKernel (d a) x) (carrierMeasure n))
    {K : ι → Set CarrierParameter} (hK : ∀ a, IsCompact (K a))
    (hsupp : ∀ a z, z ∉ K a → ∀ η, (d a).angularCutoff z η = 0)
    (hst : ∀ a x, ContinuousOn (UncutDensity.measuredStress (d a) x) (K a))
    {A B : ι → ℝ} (hA : ∀ a, 0 ≤ A a) (hB : ∀ a, 0 ≤ B a)
    (hρ : ∀ a z η, |(d a).angularCutoff z η| ≤ A a)
    (hhi : ∀ a r, |(d a).highCutoff r| ≤ B a)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (ψ θ : C(Torus n, ℝ)) (residual : OutputL2 n)
    {c : ℝ} (hc : 0 < c)
    (hgap : ∀ w, c * ‖w‖ ^ 2 ≤ ‖(augmentedRow image U ψ).adjoint w‖ ^ 2)
    (hreg : uncorrectedRawCorrection image U ψ θ residual ∈
      CarrierSobolev.augmentedInputLevel n ι (s + 1)) :
    ∀ᵐ x ∂volume, ψ x = 1 → θ x = 1 →
      residual x + (2 : ℝ) • image
        (uncorrectedRawCorrection image U ψ θ residual).fst.fst x +
        ∑ a, UncutDensity.measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
          (uncorrectedDensity d image U ψ θ residual a) x = 0 := by
  let h := uncorrectedRawCorrection image U ψ θ residual
  have hden := (UncutDensity.measuredIncrement_canonical d s hs χ hχ U hU hk hK
    hsupp hst hA hB hρ hhi image ψ
    (CoerciveInverse.normalOperator (augmentedRow image U ψ)).inverse
    (inverseSource θ residual) hreg).1
  have hcarrier : h.fst.snd = (carrierRow U).adjoint
      ((CoerciveInverse.normalOperator (augmentedRow image U ψ)).inverse
        (inverseSource θ residual)) := by
    simp only [h, uncorrectedRawCorrection, CoerciveInverse.rightInverse,
      ContinuousLinearMap.coe_comp, Function.comp_apply,
      augmentedRow_adjoint_apply, physicalRow_adjoint_apply]
    rfl
  change (fun x ↦ ∑ a, UncutDensity.measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
    (uncorrectedDensity d image U ψ θ residual a) x) =ᵐ[volume] _ at hden
  rw [← hcarrier] at hden
  have heq : image h.fst.fst + carrierRow U h.fst.snd + exteriorChannel ψ h.snd =
      inverseSource θ residual := by
    simpa only [augmentedRow_apply, physicalRow_apply] using
      augmentedRow_uncorrectedRawCorrection image U ψ θ residual hc hgap
  have heqae : (image h.fst.fst + carrierRow U h.fst.snd + exteriorChannel ψ h.snd :
      OutputL2 n) =ᵐ[volume] inverseSource θ residual := by rw [heq]
  filter_upwards [hden, heqae, inverseSource_coeFn θ residual,
    Lp.coeFn_add (image h.fst.fst + carrierRow U h.fst.snd) (exteriorChannel ψ h.snd),
    Lp.coeFn_add (image h.fst.fst) (carrierRow U h.fst.snd),
    exteriorChannel_coeFn ψ h.snd, Lp.coeFn_smul (2 : ℝ) (carrierRow U h.fst.snd)]
      with x hd he hsource hadd hadd' hext htwo
  intro hψ hθ
  simp only [Pi.add_apply] at hadd hadd'
  change _ = (1 - ψ x) • h.snd x at hext
  change _ = (2 : ℝ) • (carrierRow U h.fst.snd) x at htwo
  rw [hadd, hadd', hext, hψ, sub_self, zero_smul, add_zero] at he
  rw [hsource, hθ, mul_one] at he
  rw [hd, htwo]
  change residual x + (2 : ℝ) • (image h.fst.fst) x +
    (2 : ℝ) • (carrierRow U h.fst.snd) x = 0
  rw [add_assoc, ← smul_add, he, smul_smul]
  norm_num

end JanetCartan.PositiveBackground
