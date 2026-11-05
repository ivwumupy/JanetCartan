module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Sobolev

/-!
# The literal density identity for the fixed carrier row

The finite sum in `app:ch_background:eq:bg-density-twice` and the carrier
normal in `app:ch_mean_pairs:eq:mean-density-recursion` use the existing
`carrierRow` and the actual carrier slots of `augmentedRow.adjoint`. No new row
or inverse is introduced. For the manuscript's input `A* Q₀ e`, substitute
`Q₀ e` for `w`; the initial-adjoint and inverse owners must prove its full raw
regularity. The shared Sobolev comparison discharges weighted membership in
`measuredIncrement_row_adjoint_sobolev` and `measuredIncrement_canonical`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.UncutDensity
open ContinuumRow RawCutoffBounds ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ} {ι : Type*} [Fintype ι]

section Geometry

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

/-- The full finite sum of actual transported increments is `c/2` times the
fixed real carrier row. Thus `4 Re` gives twice the row and `-2 Re` gives
minus the row (`app:ch_background:eq:bg-density-twice`,
`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem measuredIncrement_sum (c : ℝ) (f : CarrierFamilyL2 n ι)
    (hf : ∀ a, CarrierWeightedMem (etaBesselWeight (s + 1)) (f a)) :
    (fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
      (initialDensity (d a) c (f a)) x) =ᵐ[volume]
      ((c / 2) • carrierRow U f : OutputL2 n) := by
  classical
  have he : ∀ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
      (initialDensity (d a) c (f a)) =ᵐ[volume]
        ((c / 2) • carrierChannel (U a) (f a) : OutputL2 n) := fun a ↦
    measuredIncrement_raw_coeFn (d a) s hs (χ a) (hχ a) (U a) (hU a) (hk a)
      (hK a) (hsupp a) (hst a) (hA a) (hB a) (hρ a) (hhi a) c (f a) (hf a)
  rw [carrierRow_apply, Finset.smul_sum]
  filter_upwards [eventually_all.mpr he,
    Lp.coeFn_finsetSum Finset.univ (fun a ↦ (c / 2) • carrierChannel (U a) (f a))]
      with x hx hsum
  simp only [Finset.sum_apply] at hsum
  exact (Finset.sum_congr rfl (fun a _ ↦ hx a)).trans hsum.symm

/-- Specialize the literal finite density identity to the carrier slots of
the original augmented adjoint. At `w = Q₀ e`, the negative-twice coefficient
is the negative carrier normal applied to `Q₀ e`, exactly the carrier change
in `app:ch_mean_pairs:eq:mean-density-recursion`. The adjoint decomposition is
proved using the existing row, while raw membership remains the explicitly
named initial-regularity obligation. -/
theorem measuredIncrement_row_adjoint
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ))
    (c : ℝ) (w : OutputL2 n)
    (hf : ∀ a, CarrierWeightedMem (etaBesselWeight (s + 1))
      (((augmentedRow image U ψ).adjoint w).fst.snd a)) :
    (fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
      (initialDensity (d a) c (((augmentedRow image U ψ).adjoint w).fst.snd a)) x)
        =ᵐ[volume] ((c / 2) • carrierRow U ((carrierRow U).adjoint w) : OutputL2 n) := by
  have he : ((augmentedRow image U ψ).adjoint w).fst.snd =
      (carrierRow U).adjoint w := by
    rw [augmentedRow_adjoint_apply, physicalRow_adjoint_apply]
    rfl
  have hid := measuredIncrement_sum d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi
    c (((augmentedRow image U ψ).adjoint w).fst.snd) hf
  rw [he] at hid ⊢
  exact hid

/-- The actual augmented adjoint's full mixed `X^(s+1)` membership supplies
every carrier's weighted domain. This closes the domain passage for
`app:ch_background:eq:bg-density-twice`; only the initial-adjoint regularity
itself remains the named producer's obligation. -/
theorem measuredIncrement_row_adjoint_sobolev
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ))
    (c : ℝ) (w : OutputL2 n)
    (hreg : (augmentedRow image U ψ).adjoint w ∈
      CarrierSobolev.augmentedInputLevel n ι (s + 1)) :
    (fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
      (initialDensity (d a) c (((augmentedRow image U ψ).adjoint w).fst.snd a)) x)
        =ᵐ[volume] ((c / 2) • carrierRow U ((carrierRow U).adjoint w) : OutputL2 n) :=
  measuredIncrement_row_adjoint d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi
    image ψ c w (fun a ↦ CarrierSobolev.augmentedInput_carrierWeightedMem hreg a)

/-- Both manuscript coefficients for the carrier slots of the existing
`A* Q₀ e`: the positive-background correction gives twice the carrier normal,
and the preparation correction gives its negative
(`app:ch_background:eq:bg-density-twice`,
`app:ch_mean_pairs:eq:mean-density-recursion`). The parent supplies its fixed
`Q₀` and proves full mixed regularity using the initial-adjoint/inverse
estimates. The identity needs no inverse equation and constructs no new inverse. -/
theorem measuredIncrement_canonical
    (image : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n)
    (hreg : (augmentedRow image U ψ).adjoint (Q₀ e) ∈
      CarrierSobolev.augmentedInputLevel n ι (s + 1)) :
    ((fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
      (initialDensity (d a) 4 (((augmentedRow image U ψ).adjoint (Q₀ e)).fst.snd a)) x)
        =ᵐ[volume] ((2 : ℝ) • carrierRow U ((carrierRow U).adjoint (Q₀ e)) : OutputL2 n)) ∧
    ((fun x ↦ ∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
      (initialDensity (d a) (-2) (((augmentedRow image U ψ).adjoint (Q₀ e)).fst.snd a)) x)
        =ᵐ[volume] (-carrierRow U ((carrierRow U).adjoint (Q₀ e)) : OutputL2 n)) := by
  constructor
  · simpa only [show (4 : ℝ) / 2 = 2 by norm_num] using
      measuredIncrement_row_adjoint_sobolev d s hs χ hχ U hU hk hK hsupp hst
        hA hB hρ hhi image ψ 4 (Q₀ e) hreg
  · simpa only [show (-2 : ℝ) / 2 = -1 by norm_num, neg_one_smul] using
      measuredIncrement_row_adjoint_sobolev d s hs χ hχ U hU hk hK hsupp hst
        hA hB hρ hhi image ψ (-2) (Q₀ e) hreg

end Geometry
end JanetCartan.UncutDensity
