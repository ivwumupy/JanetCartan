module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.RestrictionFactors.Algebra

/-!
# Real compression of the locally composed complete residual

The real chain composes the actual local real operators. Reality of the
physical complete pair and the even right proof symbol identifies that
product with compression of the complex local product. The restriction
Sobolev norm is transferred by the existing real-part weak-jet estimate.
Consumer: `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph LocalSobolev
open RegularSector.Realization RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral ResidualLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- The same physical complete pair is real in both literal orientations.
In the selected application E is `selectedFiniteCompleteError`; the extra
identity is exactly the normalization in `SelectedBounds`
(`app:ch_regular:eq:chain-tail`). -/
theorem pairedCompleteError_direction_star (Efull : H →L[ℂ] H) (backward : Bool)
    (u : H) :
    let K := Efull + boundedConjugate Efull + 1
    (if backward then K.adjoint else K) (star u) =
      star ((if backward then K.adjoint else K) u) := by
  intro K
  have hk (v : H) : K (star v) = star (K v) := by
    change Efull (star v) + star (Efull (star (star v))) + star v =
      star (Efull v + star (Efull (star v)) + v)
    simp only [star_add, star_star]
    abel
  cases backward
  · exact hk u
  · have he : boundedConjugate K = K := by
      ext1 v
      change star (K (star v)) = K v
      rw [hk, star_star]
    have ha := congrArg ContinuousLinearMap.adjoint he
    rw [boundedConjugate_adjoint] at ha
    have hv := congrArg (fun T : H →L[ℂ] H ↦ T (star u)) ha
    change star (K.adjoint (star (star u))) = K.adjoint (star u) at hv
    simpa only [star_star, ite_true] using hv.symm

private theorem star_restrict (U : Set E) (v : H) :
    restrictL2 U (star v) = star (restrictL2 U v) := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn U (star v), Lp.coeFn_star (restrictL2 U v),
    ae_restrict_of_ae (Lp.coeFn_star v), restrictL2_coeFn U v] with y hy hz hu hv
  rw [hy, hz, hu]
  simp only [Pi.star_apply, hv]

/-- Real inclusion intertwines the actual LOCAL compression with its
complex operator. Only the producer's whole-operator reality is used;
restriction and zero extension stay at their original positions
(`app:ch_regular:eq:chain-tail`). -/
theorem inclusion_localRealCompression_of_star {U : Set E} (hU : MeasurableSet U)
    (T : H →L[ℂ] H) (hT : ∀ v, T (star v) = star (T v)) (u : LocalL2 U RF) :
    l2ComplexInclusion (volume.restrict U) (localRealCompression hU U T u) =
      localRetardedOperator hU U T (l2ComplexInclusion (volume.restrict U) u) := by
  apply inclusion_realPart_of_star_eq
  change star (restrictL2 U (T (SmallSupport.zeroExtend hU
    (l2ComplexInclusion (volume.restrict U) u)))) =
    restrictL2 U (T (SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u)))
  have he := compLp_zeroExtend (euclideanComplexInclusion (ι := Fin q)) hU u
  change l2ComplexInclusion volume (SmallSupport.zeroExtend hU u) =
    SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) at he
  rw [← star_restrict, ← hT, ← he, star_inclusion]

/-- Compression identifies the literal composition of the three real
operators. The inner right localizer and complete error preserve real data;
no commutation of a proof mask through the residual is asserted
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem real_local_factor_eq_compression {U : Set E} (hU : MeasurableSet U)
    (K R Lout : H →L[ℂ] H)
    (hK : ∀ v, K (star v) = star (K v)) (hR : ∀ v, R (star v) = star (R v))
    (u : LocalL2 U RF) :
    (1 - localRealCompression hU U Lout)
        (localRealCompression hU U K (localRealCompression hU U R u)) =
      l2RealPart (volume.restrict U)
        ((1 - localRetardedOperator hU U Lout)
          (localRetardedOperator hU U K
            (localRetardedOperator hU U R (l2ComplexInclusion (volume.restrict U) u)))) := by
  have hi := inclusion_localRealCompression_of_star hU R hR u
  have hk := inclusion_localRealCompression_of_star hU K hK (localRealCompression hU U R u)
  rw [hi] at hk
  change localRealCompression hU U K (localRealCompression hU U R u) -
      l2RealPart (volume.restrict U) (localRetardedOperator hU U Lout
        (l2ComplexInclusion (volume.restrict U)
          (localRealCompression hU U K (localRealCompression hU U R u)))) = _
  rw [hk]
  change _ = l2RealPart (volume.restrict U) (_ - _)
  rw [map_sub]
  congr 1
  change l2RealPart (volume.restrict U)
    (localRetardedOperator hU U K
      (l2ComplexInclusion (volume.restrict U) (localRealCompression hU U R u))) = _
  rw [hi]
  rfl

/-- The complex local factor bound implies the bound for the ACTUAL real
chain. The selected complete pair supplies reality for both directions, and
the even right symbol supplies right-localizer reality. The only analytic
premise is the complex local estimate produced by `RestrictionFactors`;
real compression adds just a fixed fiber-map constant on the same genuine
restriction scale (`app:ch_regular:eq:chain-tail`). -/
theorem real_pairedCompleteError_local_factor_bound
    {U : Set E} (hU : MeasurableSet U) (ρ : ℝ) (mi : LocalizerSymbol (d + 1))
    (heven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ))
    (Efull R Lout : H →L[ℂ] H)
    (hR : ∀ u, R u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (backward : Bool) (m : ℕ) (B : ℝ)
    (hbound : ∀ u : LocalL2 U F,
      let Kfull := Efull + boundedConjugate Efull + 1
      let Kdir := if backward then Kfull.adjoint else Kfull
      let v := (1 - localRetardedOperator hU U Lout)
        (localRetardedOperator hU U Kdir (localRetardedOperator hU U R u))
      v ∈ (restrictionSobolevScale U F hU).level m ∧
        (restrictionSobolevScale U F hU).gradeNorm m v ≤ B * ‖u‖)
    (u : LocalL2 U RF) :
    let Kfull := Efull + boundedConjugate Efull + 1
    let Kdir := if backward then Kfull.adjoint else Kfull
    let v := (1 - localRealCompression hU U Lout)
      (localRealCompression hU U Kdir (localRealCompression hU U R u))
    v ∈ (restrictionSobolevScale U RF hU).level m ∧
      (restrictionSobolevScale U RF hU).gradeNorm m v ≤
        (‖euclideanRealPart (ι := Fin q)‖ + 1) * B * ‖u‖ := by
  intro Kfull Kdir v
  have he := real_local_factor_eq_compression hU Kdir R Lout
    (pairedCompleteError_direction_star Efull backward)
    (boundedRightLocalizer_star_of_even ρ mi heven R hR) u
  change v = _ at he
  rw [he]
  obtain ⟨hm, hn⟩ := hbound (l2ComplexInclusion (volume.restrict U) u)
  obtain ⟨hr, hrn⟩ := compLp_restrictionSobolev_bound (euclideanRealPart (ι := Fin q)) hm
  refine ⟨hr, ?_⟩
  change (restrictionSobolevScale U RF hU).gradeNorm m
    ((euclideanRealPart (ι := Fin q)).compLp _) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU hr]
  apply hrn.trans
  rw [← restrictionSobolevScale_gradeNorm hU hm]
  have hu : ‖l2ComplexInclusion (volume.restrict U) u‖ = ‖u‖ := by
    apply le_antisymm
    · apply (ContinuousLinearMap.le_opNorm _ u).trans
      exact (mul_le_mul_of_nonneg_right (l2ComplexInclusion_norm_le _) (norm_nonneg u)).trans_eq
        (one_mul _)
    · calc
        ‖u‖ = ‖l2RealPart (volume.restrict U) (l2ComplexInclusion (volume.restrict U) u)‖ := by
          rw [realPart_inclusion]
        _ ≤ _ := ((l2RealPart (volume.restrict U)).le_opNorm _).trans
          ((mul_le_mul_of_nonneg_right (l2RealPart_norm_le _) (norm_nonneg _)).trans_eq (one_mul _))
  rw [hu] at hn
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
