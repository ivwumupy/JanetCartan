module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction

/-!
# Local signed retarded estimates with proved output identification

The actual uncut test action and compact physical masks imply the exact
zero-extension identities in both orientations. The local negative estimate
therefore consumes only the existing primitive constructor's positive bounds,
not an additional assumption about its local outputs. Actual Hamilton geometry
and primitive symbol budgets still belong to the sector construction.
Source: `app:ch_regular_base:eq:negative-duality` and `retarded-kernel`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.RetardedLocalization
open FourierIntegral LowBounds LocalSobolev EvolutionIntegral EvolutionIntegral.UncutTestAction
open Pseudodifferential ArbitraryAccuracy
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- Both local outputs have the EXACT whole-space zero extension. The two
plateau masks are constructed inside the original domains from the literal
compact physical supports. No support or extension identity is assumed of
`Q` or `Q.adjoint`. Its test action is the checked primitive constructor's
output (`app:ch_regular_base:eq:negative-duality`). -/
theorem zeroExtend_localRetardedOperator
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource) (a : ℝ)
    (Q : H →L[ℂ] H)
    (hQ : ∀ u : graphTestSpace (d + 1) q, Q (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (retardedPhysicalIntegral Ψ b χout χsource β hs a u x))
    {U W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hos : tsupport χout ⊆ W) (hss : tsupport χsource ⊆ U) :
    (∀ f : LocalL2 U V,
      SmallSupport.zeroExtend hW.measurableSet
        (localRetardedOperator hU.measurableSet W Q f) =
          Q (SmallSupport.zeroExtend hU.measurableSet f)) ∧
    (∀ g : LocalL2 W V,
      SmallSupport.zeroExtend hU.measurableSet
        ((localRetardedOperator hU.measurableSet W Q).adjoint g) =
          Q.adjoint (SmallSupport.zeroExtend hW.measurableSet g)) := by
  obtain ⟨ψo, ψs, hψo, hψs, _, _, hψob, hψsb, hψos, hψss, hψop, hψsp⟩ :=
    exists_finite_retarded_domain_masks (fun _ : Unit ↦ χout) (fun _ : Unit ↦ χsource)
      hU hW (fun _ ↦ hoc) (fun _ ↦ hsc) (fun _ ↦ hos) (fun _ ↦ hss)
  obtain ⟨hQo, hQs⟩ := retarded_mask_identities Ψ b χout χsource β hs a Q hQ
    ψo ψs hψo.continuous hψs hψob hψsb
    (fun x hx ↦ interior_subset (s := {x | ψo x = 1}) (hψop () hx))
    (fun x hx ↦ interior_subset (s := {x | ψs x = 1}) (hψsp () hx))
  refine ⟨zeroExtend_localRetardedOperator_of_mask hU.measurableSet hW.measurableSet
    Q ψo hψo.continuous hψob hψos hQo, ?_⟩
  intro g
  rw [localRetardedOperator_adjoint hU.measurableSet hW.measurableSet]
  exact zeroExtend_localRetardedOperator_of_mask hW.measurableSet hU.measurableSet
    Q.adjoint ψs hψs.continuous hψsb hψss hQs g

/-- Restriction retains the original norm of each masked output. In
particular the local realization introduces no volume factor into the
negative-one-to-L² estimate used by the fixed inverse. -/
theorem norm_localRetardedOperator
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource) (a : ℝ)
    (Q : H →L[ℂ] H)
    (hQ : ∀ u : graphTestSpace (d + 1) q, Q (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (retardedPhysicalIntegral Ψ b χout χsource β hs a u x))
    {U W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hos : tsupport χout ⊆ W) (hss : tsupport χsource ⊆ U) :
    (∀ f : LocalL2 U V, ‖localRetardedOperator hU.measurableSet W Q f‖ =
      ‖Q (SmallSupport.zeroExtend hU.measurableSet f)‖) ∧
    (∀ g : LocalL2 W V, ‖(localRetardedOperator hU.measurableSet W Q).adjoint g‖ =
      ‖Q.adjoint (SmallSupport.zeroExtend hW.measurableSet g)‖) := by
  obtain ⟨hf, hg⟩ := zeroExtend_localRetardedOperator Ψ b χout χsource β hs a Q hQ
    hU hW hoc hsc hos hss
  constructor
  · intro f
    rw [← hf f, LinearIsometry.norm_map]
  · intro g
    rw [← hg g, LinearIsometry.norm_map]

/-- The supported/restriction negative pairing for the actual local operator
in BOTH orientations. This discharges `hout` in
`retarded_local_negative_pairing_of_positive` from the original retarded
formula and masks. The fixed shift, slab factor and single high coefficient
are unchanged. The stated positive bounds are exactly the signed primitive
constructor's outputs; this deduction does not construct its geometry. -/
theorem localRetardedOperator_negative_pairing
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource) (a : ℝ)
    (Q : H →L[ℂ] H)
    (hQ : ∀ u : graphTestSpace (d + 1) q, Q (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (retardedPhysicalIntegral Ψ b χout χsource β hs a u x))
    {U W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hos : tsupport χout ⊆ W) (hss : tsupport χsource ⊆ U)
    (o μ : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (C Hhi : ℕ → ℝ) (hC : ∀ s, 0 ≤ C s) (hH : ∀ s, 0 ≤ Hhi s)
    (hpos : ∀ s : ℕ, ∀ T : H →L[ℂ] H, (T = Q ∨ T = Q.adjoint) →
      ∀ u, MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T u) ≤ (Δ * C s) *
            (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u + Hhi (s+μ) * ‖u‖))
    (k : ℕ) :
    let B := (((q : ℝ) * scalarLocalDualityConstant (d+1) k) *
      (((q : ℝ) * q * (Δ * C (k+o))) * (1 + Hhi (k+o+μ))))
    (∀ (f : LocalL2 U V) (v : LocalL2 W V), MemRestrictionSobolev W k v →
      ‖inner ℂ (localRetardedOperator hU.measurableSet W Q f) v‖ ≤ B *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ))
          (SmallSupport.zeroExtend hU.measurableSet f) * restrictionSobolevNorm W k v) ∧
    (∀ (g : LocalL2 W V) (v : LocalL2 U V), MemRestrictionSobolev U k v →
      ‖inner ℂ ((localRetardedOperator hU.measurableSet W Q).adjoint g) v‖ ≤ B *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ))
          (SmallSupport.zeroExtend hW.measurableSet g) * restrictionSobolevNorm U k v) := by
  obtain ⟨hf, hg⟩ := zeroExtend_localRetardedOperator Ψ b χout χsource β hs a Q hQ
    hU hW hoc hsc hos hss
  constructor
  · intro f v hv
    exact retarded_local_negative_pairing_of_positive Q o μ hΔ C Hhi hC hH hpos
      k Q (Or.inl rfl) hU.measurableSet hW.measurableSet f _ v (hf f) hv
  · intro g v hv
    exact retarded_local_negative_pairing_of_positive Q o μ hΔ C Hhi hC hH hpos
      k Q.adjoint (Or.inr rfl) hW.measurableSet hU.measurableSet g _ v (hg g) hv

end JanetCartan.RegularSector.Characteristic.RetardedLocalization
