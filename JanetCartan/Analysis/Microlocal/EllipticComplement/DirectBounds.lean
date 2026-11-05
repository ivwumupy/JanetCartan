module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.CommonOutput
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoefficientOrder
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.RestrictionBounds

/-!
# Estimates at the exact orders used by the selected direct solver

The common smaller output cutoff is composed on the left of the actual
elliptic term. Supply both indices of the original direct operator estimate
and the low residual bound on arbitrary measurable domains. In particular
the output need not be supported inside the smaller ball on which the
fixed inverse tests the residual. Source: `app:ch_regular_base:thm:sector`,
`app:ch_regular_base:eq:measured-adjoint`, `finite-gap-theorem`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open FiniteMasks.ActualFamily Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open FiniteAssembly FiniteEvolution LocalSobolev FourierIntegral LowBounds Pseudodifferential
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The actual elliptic contributions with the same outer mask as
`selectedFiniteDirectSolver` and `selectedFiniteDirectResidual`. The costs
precede all enlarged thresholds, fields and local domains. The positive
and negative bounds have the original direct indices and additive profile;
the local `L² → H¹` bound is uniform even across a smaller measurement ball
(`sector-theorem-solution`, `sector-theorem-residual`, `finite-gap-theorem`). -/
theorem exists_commonOutput_elliptic_direct_constants
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω) (output : E → ℝ)
    (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output) (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ cost : Fin 2 → ℕ → ℝ, ∃ low : ℝ, (∀ o s, 0 ≤ cost o s) ∧ 0 ≤ low ∧
      ∀ L ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
      ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω → MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
      cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
      let high := fun m : ℕ ↦ 1 + cNorm (closedBall x RQ) (m+sectorLowOrder d) Q +
        cNorm (closedBall x RQ) (m+sectorLowOrder d) B
      ∀ T ∈ ({ellipticSolver f hK L Q, ellipticResidual f hK L Q B} : Set (H →L[ℂ] H)),
      let S := (sourceCutMultiplier output ho.continuous hob).comp T
      (∀ (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H), (V = S ∨ V = S.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧ vectorFourierSobolevNorm (s : ℝ) (V u) ≤
          cost o s * (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u + high (s-o.val)*‖u‖)) ∧
      (∀ (o : Fin 2) (k : ℕ) (V : H →L[ℂ] H), (V = S ∨ V = S.adjoint) → ∀ u,
        MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧ vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤
          ((d+1 : ℝ)*(d+1)*cost o (k+o.val)) * (1 + high k) *
            vectorFourierSobolevNorm (-((k+o.val : ℕ) : ℝ)) u) ∧
      ∀ (U V : Set E) (hU : MeasurableSet U), MeasurableSet V →
        let J := localRetardedOperator hU V S
        (∀ u : LocalL2 U F, MemRestrictionSobolev V 1 (J u) ∧
          restrictionSobolevNorm V 1 (J u) ≤ low*‖u‖) ∧
        (∀ v : LocalL2 V F, MemRestrictionSobolev U 1 (J.adjoint v) ∧
          restrictionSobolevNorm U 1 (J.adjoint v) ≤ low*‖v‖) := by
  have hg := exists_elliptic_gain_constants f hK hΩ hRQΩ
  let C := hg.choose
  have hC : ∀ n, 0 ≤ C n := hg.choose_spec.1
  have hgain := hg.choose_spec.2
  have hm := exists_outputMask_sobolev_constants (q := d+1) output ho hoc hob
  let D := hm.choose
  have hD : ∀ n, 1 ≤ D n := hm.choose_spec.1
  have hmask := hm.choose_spec.2
  have hl := exists_localRetarded_restrictionH1_constant d (d+1)
  let A := hl.choose
  have hA : 0 < A := hl.choose_spec.1
  have hlocal := hl.choose_spec.2
  let cost (o : Fin 2) (s : ℕ) := D s * C (s-o.val) * D (s-o.val)
  have hc (o : Fin 2) (s : ℕ) : 0 ≤ cost o s := mul_nonneg
    (mul_nonneg (zero_le_one.trans (hD s)) (hC _)) (zero_le_one.trans (hD _))
  let low := (A * cost 1 1) * (2 + 2 * max 0 M)
  have hAc := mul_nonneg hA.le (hc 1 1)
  refine ⟨cost, ?_⟩
  refine ⟨low, hc, mul_nonneg hAc (by positivity), ?_⟩
  intro L hL Q B hQ hB hmap hQl hBl high T hT S
  have hs : 2*(d+2)+2 ≤ sectorLowOrder d := by have := (sectorLowOrder_bounds d).2.2; omega
  have hb := hgain L hL Q B hQ hB hmap ((cNorm_mono_order hs).trans hQl)
    ((cNorm_mono_order hs).trans hBl) T hT
  have hhi (m : ℕ) : 0 ≤ high m := by
    dsimp only [high]
    linarith [cNorm_nonneg (closedBall x RQ) (m+sectorLowOrder d) Q,
      cNorm_nonneg (closedBall x RQ) (m+sectorLowOrder d) B]
  have horig (m : ℕ) : 1 + cNorm (closedBall x RQ) (m+(2*(d+2)+2)) Q +
      cNorm (closedBall x RQ) (m+(2*(d+2)+2)) B ≤ high m := add_le_add
    (add_le_add le_rfl (cNorm_mono_order (Nat.add_le_add_left hs m)))
    (cNorm_mono_order (Nat.add_le_add_left hs m))
  have hp (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H) (hV : V = S ∨ V = S.adjoint) :
      ∀ u, MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧ vectorFourierSobolevNorm (s : ℝ) (V u) ≤
          cost o s * (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u + high (s-o.val)*‖u‖) := by
    refine hmask T (s-o.val) s (C (s-o.val)) (high (s-o.val)) (hC _) (hhi _) ?_ V hV
    intro Z hZ u hu
    refine direct_gain_output_order T s o (C _) (high _) ?_ Z hZ u hu
    intro W hW v hv
    obtain ⟨hm, h⟩ := (hb (s-o.val) W hW).1 v hv
    exact ⟨hm, h.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (horig _) (norm_nonneg _))) (hC _))⟩
  refine ⟨hp, ?_, ?_⟩
  · intro o k V hV u
    have ha : V.adjoint = S ∨ V.adjoint = S.adjoint := by
      rcases hV with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (ContinuousLinearMap.adjoint_adjoint _)
    have ht (v : H) (hv : MemVectorFourierSobolev (k : ℝ) v) :
        MemVectorFourierSobolev ((k+o.val : ℕ) : ℝ) (V.adjoint v) ∧
          vectorFourierSobolevNorm ((k+o.val : ℕ) : ℝ) (V.adjoint v) ≤
            cost o (k+o.val) * (vectorFourierSobolevNorm (k : ℝ) v + high k * ‖v‖) := by
      simpa only [Nat.add_sub_cancel] using
        (hp o (k+o.val) V.adjoint ha v (by simpa only [Nat.add_sub_cancel] using hv))
    simpa only [Nat.cast_add, Nat.cast_one] using
      (negativeVectorFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg k)
        (Nat.cast_nonneg (k+o.val)) (hc o (k+o.val)) (hhi k) V ht u)
  · intro U V hU hV J
    obtain ⟨hf, ha⟩ := hlocal S 0 1 (cost 1) (fun s ↦ high (s-1))
      (by simpa only [one_mul, Nat.add_zero, show (1 : Fin 2).val = 1 from rfl] using hp 1) U V hU hV
    have hlow : 1 + high 0 ≤ 2 + 2 * max 0 M := by
      simp only [high, Nat.zero_add]
      linarith only [hQl, hBl, le_max_right 0 M]
    have hle : (A * cost 1 1) * (1 + high 0) ≤ low :=
      mul_le_mul_of_nonneg_left hlow hAc
    simp only [one_mul, Nat.add_zero, Nat.sub_self] at hf ha
    constructor
    · intro u
      exact ⟨(hf u).1, (hf u).2.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg u))⟩
    · intro v
      exact ⟨(ha v).1, (ha v).2.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg v))⟩

end JanetCartan.RegularSector.EllipticComplement
