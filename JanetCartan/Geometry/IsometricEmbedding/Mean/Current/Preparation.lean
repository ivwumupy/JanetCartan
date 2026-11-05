module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Representatives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Row
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FiniteNormal
import Mathlib.Tactic.Abel

/-!
# The literal signed preparation update

For `app:ch_mean_pairs:eq:mean-density-recursion`, use the uncut carrier
slots of the SAME augmented adjoint and fixed corrected-positive inverse.
The complete auxiliary output includes the exterior normal globally. The
normal inverse and full mixed regularity remain inputs of their actual
producers; the signed density/channel cancellation is proved here.

This does not yet construct the finite preparation: the actual inverse,
smooth density regularity, current-atom discrepancy and their finite reserves
must still be instantiated. In particular, no synthesis on arbitrary L² data
is asserted to be smooth.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.CurrentMean

open ContinuumRow UncutDensity

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Jointly smooth real densities supported only in the carrier parameter,
as required by `app:ch_mean_pairs:eq:mean-density-recursion`. There is no
cutoff in the initial spatial variable. -/
def smoothSupportedDensity (n : ℕ) (ι : Type*) (K : ι → Set CarrierParameter) :
    Submodule ℝ (ι → CarrierVariable n → ℝ) where
  carrier := {v | ∀ a, ContDiff ℝ ∞ (v a) ∧ ∀ z, z ∉ K a → ∀ y, v a (z, y) = 0}
  zero_mem' := fun _ ↦ ⟨contDiff_const, by simp⟩
  add_mem' := by
    intro v w hv hw a
    refine ⟨(hv a).1.add (hw a).1, ?_⟩
    intro z hz y
    change v a (z, y) + w a (z, y) = 0
    rw [(hv a).2 z hz y, (hw a).2 z hz y, add_zero]
  smul_mem' c v hv a := ⟨(hv a).1.const_smul c, by
    intro z hz y
    change c • v a (z, y) = 0
    rw [(hv a).2 z hz y, smul_zero]⟩

/-- The actual uncut `-2 Re` density increment from the original adjoint
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationDensity (d : ι → CarrierData n N)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n) :
    ι → CarrierVariable n → ℝ :=
  fun a ↦ initialDensity (d a) (-2)
    (((augmentedRow image U ψ).adjoint (Q₀ e)).fst.snd a)

/-- Carrier support of the actual density increment is inherited from the
fixed angular masks, with no spatial or upper frequency cutoff
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationDensity_zero_off_carrier (d : ι → CarrierData n N)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n)
    {K : ι → Set CarrierParameter}
    (hsupp : ∀ a z, z ∉ K a → ∀ θ, (d a).angularCutoff z θ = 0)
    (a : ι) (z : CarrierParameter) (hz : z ∉ K a) (y : Euclidean (n - 1)) :
    preparationDensity d image U ψ Q₀ e a (z, y) = 0 :=
  initialDensity_eq_zero_of_angular (d a) (-2) _ z (hsupp a z hz) y

/-- The uncut complete auxiliary normal for preparation, including the
original exterior component (`main:eq:prepared-residual`). -/
def preparationAuxiliaryOutput (image : OutputL2 n →L[ℝ] OutputL2 n)
    (ψ : C(Torus n, ℝ)) : OutputL2 n →L[ℝ] OutputL2 n :=
  image ∘L image.adjoint + exteriorChannel ψ ∘L exteriorChannel ψ

/-- The carrier and complete auxiliary normals are exactly the original
augmented normal (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationAuxiliaryOutput_add_carrier
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) :
    preparationAuxiliaryOutput image ψ + carrierRow U ∘L (carrierRow U).adjoint =
      augmentedNormal image U ψ := by
  rw [augmentedNormal_eq_sum, ← carrierRow_normal, ← exteriorChannel_comp_self]
  unfold preparationAuxiliaryOutput
  abel

/-- The actual measured transported-density increment, with the original
footpoints and external carrier weights (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationMeasuredDensity (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n) : Torus n → Euclidean n :=
  fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
    (preparationDensity d image U ψ Q₀ e a) x

section CarrierIdentity

variable (d : ι → CarrierData n N) (s : ℕ) (hs : n - 1 < 2 * s)
    (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ a z θ, (d a).angularCutoff z θ ≠ 0 → χ a z = 1)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ a (u : carrierInitialTestSpace n),
      U a (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d a) u.val)
    (hk : ∀ a x, AEStronglyMeasurable (carrierKernel (d a) x) (carrierMeasure n))
    {K : ι → Set CarrierParameter} (hK : ∀ a, IsCompact (K a))
    (hsupp : ∀ a z, z ∉ K a → ∀ θ, (d a).angularCutoff z θ = 0)
    (hst : ∀ a x, ContinuousOn (measuredStress (d a) x) (K a))
    {A B : ι → ℝ} (hA : ∀ a, 0 ≤ A a) (hB : ∀ a, 0 ≤ B a)
    (hρ : ∀ a z θ, |(d a).angularCutoff z θ| ≤ A a)
    (hhi : ∀ a r, |(d a).highCutoff r| ≤ B a)

include hs hχ hU hk hK hsupp hst hA hB hρ hhi

/-- Apply the proved uncut synthesis identity to this SAME density update.
Full mixed regularity is required of the actual adjoint input, not of arbitrary
L² data (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationMeasuredDensity_ae
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n)
    (hreg : (augmentedRow image U ψ).adjoint (Q₀ e) ∈
      CarrierSobolev.augmentedInputLevel n ι (s + 1)) :
    preparationMeasuredDensity d χ image U ψ Q₀ e =ᵐ[volume]
      (-carrierRow U ((carrierRow U).adjoint (Q₀ e)) : OutputL2 n) :=
  (measuredIncrement_canonical d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi
    image ψ Q₀ e hreg).2

/-- The literal measured density increment belongs to the original output
L² space, by its proved channel identity rather than an extra integrability
premise (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationMeasuredDensity_memLp
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n)
    (hreg : (augmentedRow image U ψ).adjoint (Q₀ e) ∈
      CarrierSobolev.augmentedInputLevel n ι (s + 1)) :
    MemLp (preparationMeasuredDensity d χ image U ψ Q₀ e) 2 volume :=
  (Lp.memLp (-carrierRow U ((carrierRow U).adjoint (Q₀ e)))).ae_eq
    (preparationMeasuredDensity_ae d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi
      image ψ Q₀ e hreg).symm

/-- The full cancellation as an equality of the original L² classes, ready
for restriction to smooth sources in the finite preparation. Its measured
term is the actual uncut synthesis (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationCancellation_toLp
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n)
    (hreg : (augmentedRow image U ψ).adjoint (Q₀ e) ∈
      CarrierSobolev.augmentedInputLevel n ι (s + 1))
    (hinverse : augmentedNormal image U ψ (Q₀ e) = e) :
    (preparationMeasuredDensity_memLp d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi
      image ψ Q₀ e hreg).toLp (preparationMeasuredDensity d χ image U ψ Q₀ e) -
        preparationAuxiliaryOutput image ψ (Q₀ e) = -e := by
  have hd := preparationMeasuredDensity_ae d s hs χ hχ U hU hk hK hsupp hst
    hA hB hρ hhi image ψ Q₀ e hreg
  have heq : (preparationMeasuredDensity_memLp d s hs χ hχ U hU hk hK hsupp hst
      hA hB hρ hhi image ψ Q₀ e hreg).toLp
        (preparationMeasuredDensity d χ image U ψ Q₀ e) =
      -carrierRow U ((carrierRow U).adjoint (Q₀ e)) :=
    Lp.ext (MemLp.coeFn_toLp _ |>.trans hd)
  rw [heq]
  have hn : preparationAuxiliaryOutput image ψ (Q₀ e) +
      carrierRow U ((carrierRow U).adjoint (Q₀ e)) = e := by
    change (preparationAuxiliaryOutput image ψ +
      carrierRow U ∘L (carrierRow U).adjoint) (Q₀ e) = e
    rw [preparationAuxiliaryOutput_add_carrier]
    exact hinverse
  calc
    _ = -(preparationAuxiliaryOutput image ψ (Q₀ e) +
        carrierRow U ((carrierRow U).adjoint (Q₀ e))) := by abel
    _ = -e := congrArg Neg.neg hn

/-- The full signed preparation cancellation follows from literal synthesis
and the ORIGINAL augmented normal inverse. This proves the cancellation needed
by `BackgroundPreparation.run_residual_succ`; it is not an assumed `hcancel`.
The equality is global and retains the exterior output
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationCancellation_ae
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n)
    (hreg : (augmentedRow image U ψ).adjoint (Q₀ e) ∈
      CarrierSobolev.augmentedInputLevel n ι (s + 1))
    (hinverse : augmentedNormal image U ψ (Q₀ e) = e) :
    (fun x ↦ preparationMeasuredDensity d χ image U ψ Q₀ e x -
      preparationAuxiliaryOutput image ψ (Q₀ e) x) =ᵐ[volume]
        (fun x ↦ -e x) := by
  have hn : preparationAuxiliaryOutput image ψ (Q₀ e) +
      carrierRow U ((carrierRow U).adjoint (Q₀ e)) = e := by
    change (preparationAuxiliaryOutput image ψ +
      carrierRow U ∘L (carrierRow U).adjoint) (Q₀ e) = e
    rw [preparationAuxiliaryOutput_add_carrier]
    exact hinverse
  have he : -carrierRow U ((carrierRow U).adjoint (Q₀ e)) -
      preparationAuxiliaryOutput image ψ (Q₀ e) = -e := by
    calc
      _ = -(preparationAuxiliaryOutput image ψ (Q₀ e) +
          carrierRow U ((carrierRow U).adjoint (Q₀ e))) := by abel
      _ = -e := congrArg Neg.neg hn
  have hd := preparationMeasuredDensity_ae d s hs χ hχ U hU hk hK hsupp hst
    hA hB hρ hhi image ψ Q₀ e hreg
  filter_upwards [hd, Lp.coeFn_sub
    (-carrierRow U ((carrierRow U).adjoint (Q₀ e)))
    (preparationAuxiliaryOutput image ψ (Q₀ e)), Lp.coeFn_neg e] with x hx hy hz
  simp only [Pi.sub_apply, Pi.neg_apply] at hy hz
  rw [hx, ← hy, he, hz]

end CarrierIdentity
end JanetCartan.CurrentMean
