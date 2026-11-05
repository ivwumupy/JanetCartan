module

public import JanetCartan.Analysis.Extension.Mollification.WeakJet
public import JanetCartan.Analysis.Operator.SmallSupport.ZeroExtension

/-!
# Integer Sobolev restriction spaces: underlying data

For `app:not:fourier`, a local Sobolev element is an actual L² equivalence
class admitting a whole-space L² weak jet. The weak identities are the
integration-by-parts identities used by the mollification construction.
No smooth representative, extension operator, or embedding estimate is
part of the definition.

The auxiliary norm sums the L² operator norms of the weak Fréchet jets.
Comparison with the manuscript's Cartesian derivative norm is a separate
analytic result; no equality with that component norm is asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual local L² classes in `app:not:fourier`. -/
abbrev LocalL2 (U : Set (EuclideanSpace ℝ (Fin n))) (F : Type*)
    [NormedAddCommGroup F] := Lp F 2 (volume.restrict U)

/-- A whole-space weak Sobolev extension of a local L² class
(`app:not:fourier`). All fields concern weak derivatives and almost-everywhere
agreement, and make sense for nonsmooth functions. -/
structure SobolevExtension (U : Set (EuclideanSpace ℝ (Fin n))) (s : ℕ)
    (u : LocalL2 U F) where
  toFun : EuclideanSpace ℝ (Fin n) → F
  jet : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
    (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F
  weakJet : Mollification.HasWeakJetOn volume toFun jet univ s
  memLp_fun : MemLp toFun 2 volume
  memLp_jet : ∀ j ≤ s, MemLp (jet j) 2 volume
  restrict_eq : toFun =ᵐ[volume.restrict U] u

/-- The nonnegative integer restriction space in `app:not:fourier`, as a
predicate on L² equivalence classes, rather than on smooth functions. -/
def MemRestrictionSobolev (U : Set (EuclideanSpace ℝ (Fin n)))
    (s : ℕ) (u : LocalL2 U F) : Prop := Nonempty (SobolevExtension U s u)

namespace SobolevExtension

variable {U : Set (EuclideanSpace ℝ (Fin n))} {s t : ℕ} {u : LocalL2 U F}

/-- Forget higher weak derivatives (`app:not:fourier`). -/
def truncate (e : SobolevExtension U t u) (h : s ≤ t) : SobolevExtension U s u where
  toFun := e.toFun
  jet := e.jet
  weakJet := ⟨e.weakJet.1, fun j hj ↦ e.weakJet.2 j (lt_of_lt_of_le hj h)⟩
  memLp_fun := e.memLp_fun
  memLp_jet := fun j hj ↦ e.memLp_jet j (hj.trans h)
  restrict_eq := e.restrict_eq

/-- An auxiliary whole-space derivative norm (`app:not:fourier`), using the
sum of the L² norms of the Fréchet jets, including the value at order zero. -/
def jetNorm (e : SobolevExtension U s u) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), (eLpNorm (e.jet j) 2 volume).toReal

/-- Nonnegativity of the auxiliary derivative norm (`app:not:fourier`). -/
theorem jetNorm_nonneg (e : SobolevExtension U s u) : 0 ≤ e.jetNorm :=
  Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg

/-- Truncation decreases the auxiliary norm (`app:not:fourier`). -/
theorem jetNorm_truncate_le (e : SobolevExtension U t u) (h : s ≤ t) :
    (e.truncate h).jetNorm ≤ e.jetNorm := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right h 1)) (fun _ _ _ ↦ ENNReal.toReal_nonneg)

/-- The zeroth jet has exactly the L² norm of its value (`app:not:fourier`). -/
theorem eLpNorm_jet_zero (e : SobolevExtension U s u) :
    eLpNorm (e.jet 0) 2 volume = eLpNorm e.toFun 2 volume := by
  apply eLpNorm_congr_norm_ae (e.memLp_jet 0 (Nat.zero_le s)).aestronglyMeasurable
    e.memLp_fun.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by rw [e.weakJet.1]; exact norm_iteratedFDeriv_zero

/-- Every whole-space extension controls the norm of its L² restriction
(`app:not:fourier`). -/
theorem norm_le_jetNorm (e : SobolevExtension U s u) : ‖u‖ ≤ e.jetNorm := by
  have hrestrict : eLpNorm u 2 (volume.restrict U) ≤ eLpNorm e.toFun 2 volume := by
    rw [← eLpNorm_congr_ae e.restrict_eq]
    exact eLpNorm_restrict_le _ _ _ _
  calc
    ‖u‖ ≤ (eLpNorm e.toFun 2 volume).toReal :=
      ENNReal.toReal_mono e.memLp_fun.eLpNorm_ne_top hrestrict
    _ = (eLpNorm (e.jet 0) 2 volume).toReal := by rw [e.eLpNorm_jet_zero]
    _ ≤ e.jetNorm := by
      unfold jetNorm
      exact Finset.single_le_sum (f := fun j ↦ (eLpNorm (e.jet j) 2 volume).toReal)
        (fun _ _ ↦ ENNReal.toReal_nonneg)
        (Finset.mem_range.mpr (Nat.zero_lt_succ s))

/-- At order zero the auxiliary norm is precisely the extension's L² norm
(`app:not:fourier`). -/
theorem jetNorm_zero (e : SobolevExtension U 0 u) :
    e.jetNorm = (eLpNorm e.toFun 2 volume).toReal := by
  simp [jetNorm, e.eLpNorm_jet_zero]

/-- Zero extension supplies an order-zero Sobolev extension of every local L²
class (`app:not:fourier`). No positive-order claim is made for zero extension. -/
def ofOrderZero (hU : MeasurableSet U) (u : LocalL2 U F) : SobolevExtension U 0 u where
  toFun := SmallSupport.zeroExtend hU u
  jet := fun j ↦ iteratedFDeriv ℝ j (SmallSupport.zeroExtend hU u)
  weakJet := ⟨rfl, fun _ h ↦ (Nat.not_lt_zero _ h).elim⟩
  memLp_fun := Lp.memLp _
  memLp_jet := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    apply (Lp.memLp (SmallSupport.zeroExtend hU u)).congr_norm
    · exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n)) F).symm.continuous
        |>.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
    · exact Eventually.of_forall fun x ↦ (norm_iteratedFDeriv_zero).symm
  restrict_eq := by
    filter_upwards [ae_restrict_of_ae (SmallSupport.zeroExtend_coeFn hU u),
      ae_restrict_mem hU] with x hx hxU
    simpa only [indicator_of_mem hxU] using hx

/-- The order-zero extension preserves the actual L² norm (`app:not:fourier`). -/
theorem jetNorm_ofOrderZero (hU : MeasurableSet U) (u : LocalL2 U F) :
    (ofOrderZero hU u).jetNorm = ‖u‖ := by
  rw [jetNorm_zero]
  exact (SmallSupport.zeroExtend hU).norm_map u

end SobolevExtension

variable {U : Set (EuclideanSpace ℝ (Fin n))} {s t : ℕ} {u : LocalL2 U F}

/-- Restriction-space membership is decreasing in the order (`app:not:fourier`). -/
theorem MemRestrictionSobolev.mono (hu : MemRestrictionSobolev U t u) (h : s ≤ t) :
    MemRestrictionSobolev U s u := ⟨hu.some.truncate h⟩

/-- Level zero contains every local L² class (`app:not:fourier`). -/
theorem memRestrictionSobolev_zero (hU : MeasurableSet U) (u : LocalL2 U F) :
    MemRestrictionSobolev U 0 u := ⟨SobolevExtension.ofOrderZero hU u⟩

/-- Infimum of the auxiliary whole-space jet norms over actual extensions
(`app:not:fourier`). Off the restriction space the infimum is zero; estimates
at positive orders therefore always require membership. -/
def restrictionSobolevNorm (U : Set (EuclideanSpace ℝ (Fin n)))
    (s : ℕ) (u : LocalL2 U F) : ℝ :=
  sInf (Set.range (SobolevExtension.jetNorm (U := U) (s := s) (u := u)))

/-- Nonnegativity of the restriction norm (`app:not:fourier`). -/
theorem restrictionSobolevNorm_nonneg : 0 ≤ restrictionSobolevNorm U s u := by
  apply Real.sInf_nonneg
  rintro _ ⟨e, rfl⟩
  exact e.jetNorm_nonneg

/-- Each genuine extension bounds the restriction norm (`app:not:fourier`). -/
theorem restrictionSobolevNorm_le (e : SobolevExtension U s u) :
    restrictionSobolevNorm U s u ≤ e.jetNorm := by
  unfold restrictionSobolevNorm
  apply csInf_le
  · exact ⟨0, fun _ ⟨e, he⟩ ↦ he ▸ e.jetNorm_nonneg⟩
  · exact ⟨e, rfl⟩

/-- The restriction norm dominates the actual local L² norm (`app:not:fourier`). -/
theorem norm_le_restrictionSobolevNorm (hu : MemRestrictionSobolev U s u) :
    ‖u‖ ≤ restrictionSobolevNorm U s u := by
  unfold restrictionSobolevNorm
  refine le_csInf ?_ ?_
  · exact ⟨hu.some.jetNorm, hu.some, rfl⟩
  rintro _ ⟨e, rfl⟩
  exact e.norm_le_jetNorm

/-- Exact L² normalization at order zero (`app:not:fourier`). -/
@[simp] theorem restrictionSobolevNorm_zero (hU : MeasurableSet U) (u : LocalL2 U F) :
    restrictionSobolevNorm U 0 u = ‖u‖ := by
  apply le_antisymm
  · exact (restrictionSobolevNorm_le (SobolevExtension.ofOrderZero hU u)).trans_eq
      (SobolevExtension.jetNorm_ofOrderZero hU u)
  · exact norm_le_restrictionSobolevNorm (memRestrictionSobolev_zero hU u)

/-- The restriction norm increases with the order (`app:not:fourier`). -/
theorem restrictionSobolevNorm_mono (hu : MemRestrictionSobolev U t u) (h : s ≤ t) :
    restrictionSobolevNorm U s u ≤ restrictionSobolevNorm U t u := by
  unfold restrictionSobolevNorm
  refine le_csInf ?_ ?_
  · exact ⟨hu.some.jetNorm, hu.some, rfl⟩
  rintro _ ⟨e, rfl⟩
  exact (restrictionSobolevNorm_le (e.truncate h)).trans (e.jetNorm_truncate_le h)

end JanetCartan.LocalSobolev
