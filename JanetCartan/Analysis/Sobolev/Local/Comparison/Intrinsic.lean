module

public import JanetCartan.Analysis.Sobolev.Local.Basic

/-!
# Intrinsic weak Sobolev data

For `app:not:fourier` and `app:ch_regular_base:lem:ball-extension`, the intrinsic
space consists of local L² classes with locally square-integrable weak jets.
This definition includes neither an extension nor a comparison estimate.
Restriction of a whole-space extension supplies such data and decreases the
sum of the L² operator norms. Cartesian component norms remain separate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}

/-- Restrict the weak first-derivative identities to a smaller domain
(`app:ch_regular_base:lem:ball-extension`). -/
theorem HasWeakFDerivOn.mono {f : E → F} {D : E → E →L[ℝ] F}
    {U V : Set E} (h : HasWeakFDerivOn μ f D V) (hUV : U ⊆ V) :
    HasWeakFDerivOn μ f D U :=
  ⟨h.1.mono_set hUV, h.2.1.mono_set hUV,
    fun ψ hψ hc hs v ↦ h.2.2 ψ hψ hc (hs.trans hUV) v⟩

/-- Restrict a finite weak jet to a smaller domain
(`app:ch_regular_base:lem:ball-extension`). -/
theorem HasWeakJetOn.mono {f : E → F} {J : (j : ℕ) → E → E [×j]→L[ℝ] F}
    {U V : Set E} {m : ℕ} (h : HasWeakJetOn μ f J V m) (hUV : U ⊆ V) :
    HasWeakJetOn μ f J U m :=
  ⟨h.1, fun j hj ↦ (h.2 j hj).mono hUV⟩

end JanetCartan.Mollification

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Sum of local L² Fréchet operator norms, used as the auxiliary intrinsic
norm in `app:ch_regular_base:lem:ball-extension`. -/
def jetL2Norm (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (eLpNorm (J j) 2 (volume.restrict U)).toReal

/-- The auxiliary intrinsic jet norm is nonnegative (`app:not:fourier`). -/
theorem jetL2Norm_nonneg (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) : 0 ≤ jetL2Norm U m J :=
  Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg

/-- Intrinsic weak Hᵐ data representing a local L² class (`app:not:fourier`).
The representative is allowed to differ from the chosen Lp representative on
a null set. All derivative and integrability requirements are local. -/
structure IntrinsicSobolevData (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (u : LocalL2 U F) where
  toFun : EuclideanSpace ℝ (Fin n) → F
  jet : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
    (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F
  weakJet : Mollification.HasWeakJetOn volume toFun jet U m
  memLp_fun : MemLp toFun 2 (volume.restrict U)
  memLp_jet : ∀ j ≤ m, MemLp (jet j) 2 (volume.restrict U)
  restrict_eq : toFun =ᵐ[volume.restrict U] u

/-- Intrinsic weak Hᵐ membership, with no whole-space extension premise
(`app:not:fourier`). -/
def MemIntrinsicSobolev (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (u : LocalL2 U F) : Prop := Nonempty (IntrinsicSobolevData U m u)

namespace IntrinsicSobolevData

variable {U : Set (EuclideanSpace ℝ (Fin n))} {s t : ℕ} {u : LocalL2 U F}

/-- Turn actual weak data into intrinsic data for their L² class
(`app:ch_regular_base:lem:ball-extension`). -/
def ofWeakJet {f : EuclideanSpace ℝ (Fin n) → F}
    {J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    (hw : Mollification.HasWeakJetOn volume f J U s)
    (hf : MemLp f 2 (volume.restrict U))
    (hJ : ∀ j ≤ s, MemLp (J j) 2 (volume.restrict U)) :
    IntrinsicSobolevData U s (hf.toLp f) where
  toFun := f
  jet := J
  weakJet := hw
  memLp_fun := hf
  memLp_jet := hJ
  restrict_eq := hf.coeFn_toLp.symm

/-- Auxiliary intrinsic norm of concrete weak data (`app:not:fourier`). -/
def jetNorm (d : IntrinsicSobolevData U s u) : ℝ := jetL2Norm U s d.jet

/-- Nonnegativity of the intrinsic auxiliary norm (`app:not:fourier`). -/
theorem jetNorm_nonneg (d : IntrinsicSobolevData U s u) : 0 ≤ d.jetNorm :=
  jetL2Norm_nonneg _ _ _

/-- Truncate intrinsic weak data (`app:not:fourier`). -/
def truncate (d : IntrinsicSobolevData U t u) (h : s ≤ t) :
    IntrinsicSobolevData U s u where
  toFun := d.toFun
  jet := d.jet
  weakJet := ⟨d.weakJet.1, fun j hj ↦ d.weakJet.2 j (hj.trans_le h)⟩
  memLp_fun := d.memLp_fun
  memLp_jet := fun j hj ↦ d.memLp_jet j (hj.trans h)
  restrict_eq := d.restrict_eq

/-- The zeroth local jet has the L² norm of its represented class
(`app:not:fourier`). -/
theorem eLpNorm_jet_zero (d : IntrinsicSobolevData U s u) :
    eLpNorm (d.jet 0) 2 (volume.restrict U) = eLpNorm u 2 (volume.restrict U) := by
  rw [← eLpNorm_congr_ae d.restrict_eq]
  apply eLpNorm_congr_norm_ae (d.memLp_jet 0 (Nat.zero_le s)).aestronglyMeasurable
    d.memLp_fun.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by rw [d.weakJet.1]; exact norm_iteratedFDeriv_zero

/-- The local L² norm is bounded by the auxiliary intrinsic jet norm
(`app:not:fourier`). -/
theorem norm_le_jetNorm (d : IntrinsicSobolevData U s u) : ‖u‖ ≤ d.jetNorm := by
  change (eLpNorm u 2 (volume.restrict U)).toReal ≤ _
  rw [← d.eLpNorm_jet_zero]
  exact Finset.single_le_sum (f := fun j ↦
      (eLpNorm (d.jet j) 2 (volume.restrict U)).toReal)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (Finset.mem_range.mpr (Nat.zero_lt_succ s))

/-- Intrinsic order zero is exactly the L² norm (`app:not:fourier`). -/
theorem jetNorm_zero (d : IntrinsicSobolevData U 0 u) : d.jetNorm = ‖u‖ := by
  simp only [jetNorm, jetL2Norm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [d.eLpNorm_jet_zero]
  rfl

end IntrinsicSobolevData

namespace SobolevExtension

variable {U : Set (EuclideanSpace ℝ (Fin n))} {s : ℕ} {u : LocalL2 U F}

/-- Every whole-space weak extension restricts to intrinsic weak data
(`app:ch_regular_base:lem:ball-extension`). -/
def toIntrinsic (e : SobolevExtension U s u) : IntrinsicSobolevData U s u where
  toFun := e.toFun
  jet := e.jet
  weakJet := e.weakJet.mono (subset_univ U)
  memLp_fun := e.memLp_fun.restrict U
  memLp_jet := fun j hj ↦ (e.memLp_jet j hj).restrict U
  restrict_eq := e.restrict_eq

/-- Restriction decreases the sum of the L² jet norms, with constant one
(`app:ch_regular_base:lem:ball-extension`). -/
theorem jetNorm_toIntrinsic_le (e : SobolevExtension U s u) :
    e.toIntrinsic.jetNorm ≤ e.jetNorm := by
  unfold IntrinsicSobolevData.jetNorm jetL2Norm jetNorm
  apply Finset.sum_le_sum
  intro j hj
  exact ENNReal.toReal_mono
    (e.memLp_jet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).eLpNorm_ne_top
    (eLpNorm_restrict_le _ _ _ _)

end SobolevExtension

variable {U : Set (EuclideanSpace ℝ (Fin n))} {s t : ℕ} {u : LocalL2 U F}

/-- The restriction space is contained in the intrinsic weak space
(`app:not:fourier`). -/
theorem MemRestrictionSobolev.intrinsic (h : MemRestrictionSobolev U s u) :
    MemIntrinsicSobolev U s u := ⟨h.some.toIntrinsic⟩

/-- Intrinsic membership decreases with the order (`app:not:fourier`). -/
theorem MemIntrinsicSobolev.mono (h : MemIntrinsicSobolev U t u) (hst : s ≤ t) :
    MemIntrinsicSobolev U s u := ⟨h.some.truncate hst⟩

/-- The intrinsic order-zero space contains every local L² class
(`app:not:fourier`). -/
theorem memIntrinsicSobolev_zero (hU : MeasurableSet U) (u : LocalL2 U F) :
    MemIntrinsicSobolev U 0 u := (memRestrictionSobolev_zero hU u).intrinsic

/-- Infimum of auxiliary intrinsic jet norms over weak representatives
(`app:not:fourier`). Uniqueness of weak jets identifies this with the norm of
any particular intrinsic jet; that uniqueness is not built into this definition. -/
def intrinsicSobolevNorm (U : Set (EuclideanSpace ℝ (Fin n))) (s : ℕ)
    (u : LocalL2 U F) : ℝ :=
  sInf (Set.range (IntrinsicSobolevData.jetNorm (U := U) (s := s) (u := u)))

/-- The intrinsic infimum is nonnegative (`app:not:fourier`). -/
theorem intrinsicSobolevNorm_nonneg : 0 ≤ intrinsicSobolevNorm U s u := by
  apply Real.sInf_nonneg
  rintro _ ⟨d, rfl⟩
  exact d.jetNorm_nonneg

/-- Concrete intrinsic data bound the intrinsic infimum (`app:not:fourier`). -/
theorem intrinsicSobolevNorm_le (d : IntrinsicSobolevData U s u) :
    intrinsicSobolevNorm U s u ≤ d.jetNorm := by
  apply csInf_le
  · exact ⟨0, fun _ ⟨d, hd⟩ ↦ hd ▸ d.jetNorm_nonneg⟩
  · exact ⟨d, rfl⟩

/-- The intrinsic infimum dominates the local L² norm (`app:not:fourier`). -/
theorem norm_le_intrinsicSobolevNorm (h : MemIntrinsicSobolev U s u) :
    ‖u‖ ≤ intrinsicSobolevNorm U s u := by
  apply le_csInf
  · exact ⟨h.some.jetNorm, h.some, rfl⟩
  · rintro _ ⟨d, rfl⟩
    exact d.norm_le_jetNorm

/-- The intrinsic auxiliary norm is bounded by the restriction norm with
constant one (`app:ch_regular_base:lem:ball-extension`). -/
theorem intrinsicSobolevNorm_le_restrictionSobolevNorm
    (h : MemRestrictionSobolev U s u) :
    intrinsicSobolevNorm U s u ≤ restrictionSobolevNorm U s u := by
  apply le_csInf
  · exact ⟨h.some.jetNorm, h.some, rfl⟩
  · rintro _ ⟨e, rfl⟩
    exact (intrinsicSobolevNorm_le e.toIntrinsic).trans e.jetNorm_toIntrinsic_le

/-- The intrinsic norm is exactly normalized at order zero (`app:not:fourier`). -/
@[simp] theorem intrinsicSobolevNorm_zero (hU : MeasurableSet U) (u : LocalL2 U F) :
    intrinsicSobolevNorm U 0 u = ‖u‖ := by
  apply le_antisymm
  · exact (intrinsicSobolevNorm_le_restrictionSobolevNorm
      (memRestrictionSobolev_zero hU u)).trans_eq (restrictionSobolevNorm_zero hU u)
  · exact norm_le_intrinsicSobolevNorm (memIntrinsicSobolev_zero hU u)

end JanetCartan.LocalSobolev
