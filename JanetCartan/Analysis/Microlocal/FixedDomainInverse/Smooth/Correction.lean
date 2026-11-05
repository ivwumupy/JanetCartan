module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Smooth.Representatives

/-!
# One smooth realization of the fixed corrected-source operator

For `app:ch_regular:thm:exact-correction`, this constructs a linear map on
all-order restriction Sobolev sources, using the same `correctedSource`
L² class. The contraction and the localized residual's one-gain regularity
are explicit inputs. In particular, the construction applies to the cutoffs
and contraction furnished by `exists_fixed_cutoffs_localSobolevInverse`;
it does not choose a new inverse at each order.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal NNReal

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {W : Set (EuclideanSpace ℝ (Fin n))}

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual smooth-source subspace for `app:ch_regular:thm:exact-correction`:
local L² classes in every integer restriction Sobolev space. -/
def smoothSource (W : Set (EuclideanSpace ℝ (Fin n))) (F : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Submodule ℝ (LocalL2 W F) where
  carrier := {h | ∀ s, MemRestrictionSobolev W s h}
  zero_mem' := fun _ ↦ memRestrictionSobolev_zero_element
  add_mem' := fun hh hk s ↦ (hh s).add (hk s)
  smul_mem' := fun a _ hh s ↦ (hh s).smul a

variable (hW : IsOpen W) {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
  (hp : 2 ≤ p) {x : EuclideanSpace ℝ (Fin n)} (χ₂ χ₃ : ContDiffBump x)
  {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
  (R : LocalL2 W F →L[ℝ] Lp F p ((volume.restrict W).restrict U))

local notation "K" => localizedResidual hp χ₂ χ₃ hU R
local notation "Z" => correctedSource hp χ₂ χ₃ hU R

include hW

/-- Bootstrap of the same corrected L² source at every order, including
regularity of the cutoff input (`app:ch_regular:thm:exact-correction`). -/
theorem correctedSource_memRestrictionSobolev (hK : ‖K‖ < 1)
    (hsupport : tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ W)
    (hgain : ∀ (s : ℕ) (f : LocalL2 W F),
      MemRestrictionSobolev W s f → MemRestrictionSobolev W (s + 1) (K f))
    (h : smoothSource W F) (s : ℕ) : MemRestrictionSobolev W s (Z h) := by
  exact (restrictionSobolevScale W F hW.measurableSet).neumannInverse_mem K hK hgain s
    (memRestrictionSobolev_bumpL2_of_all_orders hW χ₂ hsupport h.val h.property s)

/-- Smooth, compactly supported zero extension of the same corrected L²
source (`app:ch_regular:thm:exact-correction`). No supported representative
is assumed; it is obtained from one-gain regularity and the L² equation. -/
theorem exists_smooth_correctedSource (hK : ‖K‖ < 1)
    (hsupport : tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ W)
    (hgain : ∀ (s : ℕ) (f : LocalL2 W F),
      MemRestrictionSobolev W s f → MemRestrictionSobolev W (s + 1) (K f))
    (h : smoothSource W F) :
    ∃ z : EuclideanSpace ℝ (Fin n) → F,
      ContDiff ℝ ∞ z ∧ z =ᵐ[volume.restrict W] Z h ∧
      tsupport z ⊆ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ∧ W.indicator z = z := by
  exact exists_supported_smoothRepresentative hW (isClosed_tsupport _) hsupport (Z h)
    (correctedSource_memRestrictionSobolev hW hp χ₂ χ₃ hU R hK hsupport hgain h)
    (correctedSource_ae_zero_off_support hp χ₂ χ₃ hU R hK h)

variable (hK : ‖localizedResidual hp χ₂ χ₃ hU R‖ < 1)
  (hsupport : tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ W)
  (hgain : ∀ (s : ℕ) (f : LocalL2 W F), MemRestrictionSobolev W s f →
    MemRestrictionSobolev W (s + 1) (localizedResidual hp χ₂ χ₃ hU R f))

/-- The unique smooth zero-extended realization of the original corrected
source, for `app:ch_regular:thm:exact-correction`. -/
def smoothCorrectedSource (hK : ‖K‖ < 1)
    (hsupport : tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ W)
    (hgain : ∀ (s : ℕ) (f : LocalL2 W F),
      MemRestrictionSobolev W s f → MemRestrictionSobolev W (s + 1) (K f))
    (h : smoothSource W F) : EuclideanSpace ℝ (Fin n) → F :=
  (exists_smooth_correctedSource hW hp χ₂ χ₃ hU R hK hsupport hgain h).choose

/-- Smoothness, exact local L² agreement, support and zero extension of the
chosen correction (`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_spec (h : smoothSource W F) :
    let z := smoothCorrectedSource hW hp χ₂ χ₃ hU R hK hsupport hgain h
    ContDiff ℝ ∞ z ∧ z =ᵐ[volume.restrict W] Z h ∧
      tsupport z ⊆ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ∧ W.indicator z = z :=
  (exists_smooth_correctedSource hW hp χ₂ χ₃ hU R hK hsupport hgain h).choose_spec

local notation "z" => smoothCorrectedSource hW hp χ₂ χ₃ hU R hK hsupport hgain

/-- Compact support of the smooth correction, on the original fixed output
support (`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_hasCompactSupport (h : smoothSource W F) :
    HasCompactSupport (z h) :=
  IsCompact.of_isClosed_subset χ₂.hasCompactSupport (isClosed_tsupport _)
    (smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h).2.2.1

/-- Pointwise vanishing outside the fixed output support, for the smooth
realization of the same L² correction (`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_zero_off_support (h : smoothSource W F)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∉ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)) : z h y = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hz ↦ hy
    ((smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h).2.2.1 hz))

/-- Pointwise source-cutoff invariance, including off the domain
(`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_cutoff
    (hnest : ∀ y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ), χ₃ y = 1)
    (h : smoothSource W F) (y : EuclideanSpace ℝ (Fin n)) : χ₃ y • z h y = z h y := by
  by_cases hy : y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
  · rw [hnest y hy, one_smul]
  · have hz := image_eq_zero_of_notMem_tsupport (fun hz ↦ hy
      ((smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h).2.2.1 hz))
    rw [hz, smul_zero]

/-- Uniqueness on the open domain for any continuous representative of the
corrected L² class (`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_eqOn (h : smoothSource W F)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContinuousOn f W)
    (hfeq : f =ᵐ[volume.restrict W] Z h) : EqOn f (z h) W :=
  Measure.eqOn_open_of_ae_eq
    (hfeq.trans (smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h).2.1.symm)
    hW hf
    (smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h).1.continuous.continuousOn

/-- The zero extension also retains the exact ambient L² zero-extension class
(`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_ae_zeroExtend (h : smoothSource W F) :
    z h =ᵐ[volume] zeroExtend hW.measurableSet (Z h) := by
  have hs := smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h
  have he := (ae_eq_restrict_iff_indicator_ae_eq hW.measurableSet).mp hs.2.1
  rw [hs.2.2.2] at he
  exact he.trans (zeroExtend_coeFn hW.measurableSet (Z h)).symm

/-- Choosing smooth representatives does not destroy additivity of the fixed
L² correction (`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_add (h k : smoothSource W F) : z (h + k) = z h + z k := by
  have hs := smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain (h + k)
  have ht := smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h
  have hu := smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain k
  refine supported_continuousRepresentative_unique hW hs.1.continuous.continuousOn
    (ht.1.add hu.1).continuous.continuousOn hs.2.1 ?_ hs.2.2.2 ?_
  · change (fun y ↦ z h y + z k y) =ᵐ[volume.restrict W] Z (h + k)
    have he : Z (h + k) = Z h + Z k := map_add Z h.val k.val
    rw [he]
    filter_upwards [ht.2.1, hu.2.1, Lp.coeFn_add (Z h) (Z k)] with y hy hk ha
    exact (congrArg₂ (· + ·) hy hk).trans ha.symm
  · change W.indicator (fun y ↦ z h y + z k y) = z h + z k
    rw [indicator_add, ht.2.2.2, hu.2.2.2]
    rfl

/-- Real scalar linearity of the chosen smooth realization
(`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_smul (a : ℝ) (h : smoothSource W F) : z (a • h) = a • z h := by
  have hs := smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain (a • h)
  have ht := smoothCorrectedSource_spec hW hp χ₂ χ₃ hU R hK hsupport hgain h
  refine supported_continuousRepresentative_unique hW hs.1.continuous.continuousOn
    (contDiff_const.smul ht.1).continuous.continuousOn hs.2.1 ?_ hs.2.2.2 ?_
  · change (fun y ↦ a • z h y) =ᵐ[volume.restrict W] Z (a • h)
    have he : Z (a • h) = a • Z h := map_smul Z a h.val
    rw [he]
    filter_upwards [ht.2.1, Lp.coeFn_smul a (Z h)] with y hy ha
    exact (congrArg (a • ·) hy).trans ha.symm
  · ext y
    by_cases hy : y ∈ W
    · simp [hy]
    · have htzero : z h y = 0 := by
        rw [← ht.2.2.2, indicator_of_notMem hy]
      simp [hy, htzero]

/-- The single linear correction on smooth sources, realized as globally
smooth zero-extended functions (`app:ch_regular:thm:exact-correction`). -/
def smoothCorrectedSourceLinear : smoothSource W F →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → F) where
  toFun := z
  map_add' := smoothCorrectedSource_add hW hp χ₂ χ₃ hU R hK hsupport hgain
  map_smul' := smoothCorrectedSource_smul hW hp χ₂ χ₃ hU R hK hsupport hgain

end JanetCartan.FixedDomainInverse
