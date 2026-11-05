module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Positive
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds.LocalPairing

/-!
# Measured negative supported norms and restriction pairings

Apply the existing vector duality to the SAME masked operator and identify
its local output's zero extension by the explicit outer mask. These are
estimates on actual L² classes; no distribution-completion extension is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev Pseudodifferential ArbitraryAccuracy
open Characteristic.RetardedLocalization Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The two explicit masks preserve the positive constructor signature.
Consumer: measured negative duality, at output order `k+1`.
Source: `app:ch_regular_base:eq:sector-theorem-residual`. -/
theorem exists_measuredOperator_fourier_constants
    (χout χin : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χin)
    (hoc : HasCompactSupport χout) (hic : HasCompactSupport χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) :
    ∃ D : ℕ → ℝ, (∀ s, 1 ≤ D s) ∧
      ∀ (T : H →L[ℂ] H) (cost high : ℕ → ℝ),
      (∀ s, 0 ≤ cost s) → (∀ s, 0 ≤ high s) →
      (∀ s, ∀ W : H →L[ℂ] H, (W = T ∨ W = T.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤
            cost s*(vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u+high s*‖u‖)) →
      let S := measuredOperator χout χin ho.continuous hi.continuous hob hib T
      ∀ s, ∀ W : H →L[ℂ] H, (W = S ∨ W = S.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤
            (D s*cost s)*(vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u+high s*‖u‖) := by
  obtain ⟨D, hD, hmask⟩ := exists_commonMask_sobolev_constants (q := q)
    χout χin ho hi hoc hic hob hib
  refine ⟨fun s ↦ D s*D (s-1), fun s ↦ one_le_mul_of_one_le_of_one_le (hD s) (hD _), ?_⟩
  intro T cost high hc hh hT S s W hW u hu
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    hmask T (s-1) s (cost s) (high s) (hc s) (hh s) (hT s) W hW u hu

/-- Supported negative Fourier estimates for both literal measured orientations.
The constant precedes T and the high quantity. At `k=0` this is the global
`H⁻¹ → L²` endpoint of `finite-gap-theorem`; local identities are supplied by
`zeroExtend_local_measuredOperator` and its adjoint counterpart. -/
theorem exists_measuredOperator_negative_constants
    (χout χin : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χin)
    (hoc : HasCompactSupport χout) (hic : HasCompactSupport χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
      ∀ (T : H →L[ℂ] H) (cost high : ℕ → ℝ),
      (∀ s, 0 ≤ cost s) → (∀ s, 0 ≤ high s) →
      (∀ s, ∀ W : H →L[ℂ] H, (W = T ∨ W = T.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤
            cost s*(vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u+high s*‖u‖)) →
      let S := measuredOperator χout χin ho.continuous hi.continuous hob hib T
      ∀ k : ℕ, ∀ W : H →L[ℂ] H, (W = S ∨ W = S.adjoint) → ∀ u,
        MemVectorFourierSobolev (-(k : ℝ)) (W u) ∧
          vectorFourierSobolevNorm (-(k : ℝ)) (W u) ≤
            (D k*cost (k+1)*(1+high (k+1)))*
              vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) u := by
  obtain ⟨D, hD, hfour⟩ := exists_measuredOperator_fourier_constants (q := q)
    χout χin ho hi hoc hic hob hib
  refine ⟨fun k ↦ (q : ℝ)*q*D (k+1), fun k ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg q)) (zero_le_one.trans (hD _)), ?_⟩
  intro T cost high hc hh hT S k W hW u
  have hp := hfour T cost high hc hh hT
  have h := retarded_negative_integer_bounds_of_positive S 1 0 zero_le_one
    (fun s ↦ D s*cost s) high (fun s ↦ mul_nonneg (zero_le_one.trans (hD s)) (hc s)) hh
    (by simpa only [one_mul, Nat.add_zero] using hp) k W hW u
  simpa only [one_mul, Nat.add_zero, mul_assoc] using h

/-- Both original domains carry the negative supported norm of the literal
local output, paired with the genuine restriction test norm. This simultaneously
proves the `H⁻¹ → L²` endpoints. The sole analytic premise is the constructor's
positive Fourier estimate; all support identities are discharged here.
Sources: `negative-duality`, `finite-gap-theorem`, `measured-adjoint`. -/
theorem exists_measuredOperator_local_negative_constants
    (χout χin : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χin)
    (hoc : HasCompactSupport χout) (hic : HasCompactSupport χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
      ∀ (T : H →L[ℂ] H) (cost high : ℕ → ℝ),
      (∀ s, 0 ≤ cost s) → (∀ s, 0 ≤ high s) →
      (∀ s, ∀ W : H →L[ℂ] H, (W = T ∨ W = T.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤
            cost s*(vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u+high s*‖u‖)) →
      ∀ (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V),
      tsupport χin ⊆ U → tsupport χout ⊆ V →
      let L := localRetardedOperator hU V
        (measuredOperator χout χin ho.continuous hi.continuous hob hib T)
      (∀ (k : ℕ) (u : LocalL2 U F),
        vectorFourierSobolevNorm (-(k : ℝ)) (SmallSupport.zeroExtend hV (L u)) ≤
          (D k*cost (k+1)*(1+high (k+1)))*
            vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u)) ∧
      (∀ (k : ℕ) (v : LocalL2 V F),
        vectorFourierSobolevNorm (-(k : ℝ)) (SmallSupport.zeroExtend hU (L.adjoint v)) ≤
          (D k*cost (k+1)*(1+high (k+1)))*
            vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hV v)) ∧
      (∀ (k : ℕ) (u : LocalL2 U F) (v : LocalL2 V F), MemRestrictionSobolev V k v →
        ‖inner ℂ (L u) v‖ ≤
          ((q : ℝ)*scalarLocalDualityConstant (d+1) k)*(D k*cost (k+1)*(1+high (k+1)))*
            vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u)*
              restrictionSobolevNorm V k v) ∧
      (∀ (k : ℕ) (v : LocalL2 V F) (u : LocalL2 U F), MemRestrictionSobolev U k u →
        ‖inner ℂ (L.adjoint v) u‖ ≤
          ((q : ℝ)*scalarLocalDualityConstant (d+1) k)*(D k*cost (k+1)*(1+high (k+1)))*
            vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hV v)*
              restrictionSobolevNorm U k u) ∧
      (∀ u : LocalL2 U F, ‖L u‖ ≤ (D 0*cost 1*(1+high 1))*
        vectorFourierSobolevNorm (-1) (SmallSupport.zeroExtend hU u)) ∧
      (∀ v : LocalL2 V F, ‖L.adjoint v‖ ≤ (D 0*cost 1*(1+high 1))*
        vectorFourierSobolevNorm (-1) (SmallSupport.zeroExtend hV v)) := by
  obtain ⟨D, hD, hneg⟩ := exists_measuredOperator_negative_constants (q := q)
    χout χin ho hi hoc hic hob hib
  refine ⟨D, hD, ?_⟩
  intro T cost high hc hh hT U V hU hV hsi hso L
  have hf k (u : LocalL2 U F) := (hneg T cost high hc hh hT k _ (Or.inl rfl)
    (SmallSupport.zeroExtend hU u)).2
  have ha k (v : LocalL2 V F) := (hneg T cost high hc hh hT k _ (Or.inr rfl)
    (SmallSupport.zeroExtend hV v)).2
  have hef (u : LocalL2 U F) := zeroExtend_local_measuredOperator hU hV χout χin
    ho.continuous hi.continuous hob hib hso T u
  have hea (v : LocalL2 V F) := zeroExtend_local_measuredOperator_adjoint hU hV χout χin
    ho.continuous hi.continuous hob hib hsi T v
  have hf' (k : ℕ) (u : LocalL2 U F) :
      vectorFourierSobolevNorm (-(k : ℝ)) (SmallSupport.zeroExtend hV (L u)) ≤
        (D k*cost (k+1)*(1+high (k+1)))*
          vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hU u) := by
    rw [hef]; exact hf k u
  have ha' (k : ℕ) (v : LocalL2 V F) :
      vectorFourierSobolevNorm (-(k : ℝ)) (SmallSupport.zeroExtend hU (L.adjoint v)) ≤
        (D k*cost (k+1)*(1+high (k+1)))*
          vectorFourierSobolevNorm (-((k+1 : ℕ) : ℝ)) (SmallSupport.zeroExtend hV v) := by
    rw [hea]; exact ha k v
  refine ⟨hf', ha', ?_, ?_, ?_, ?_⟩
  · intro k u v hv
    apply (norm_inner_le_vectorNegativeNorm_mul_restrictionSobolevNorm hV k (L u) v hv).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hf' k u)
        (mul_nonneg (Nat.cast_nonneg q) (scalarLocalDualityConstant_pos (d+1) k).le))
      restrictionSobolevNorm_nonneg
  · intro k v u hu
    apply (norm_inner_le_vectorNegativeNorm_mul_restrictionSobolevNorm hU k (L.adjoint v) u hu).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ha' k v)
        (mul_nonneg (Nat.cast_nonneg q) (scalarLocalDualityConstant_pos (d+1) k).le))
      restrictionSobolevNorm_nonneg
  · intro u
    simpa only [Nat.cast_zero, neg_zero, vectorFourierSobolevNorm_zero,
      LinearIsometry.norm_map, Nat.zero_add, Nat.cast_one] using hf' 0 u
  · intro v
    simpa only [Nat.cast_zero, neg_zero, vectorFourierSobolevNorm_zero,
      LinearIsometry.norm_map, Nat.zero_add, Nat.cast_one] using ha' 0 v

end JanetCartan.RegularSector.FiniteAssembly
