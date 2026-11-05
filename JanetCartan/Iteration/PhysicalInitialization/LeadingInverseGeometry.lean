module

public import JanetCartan.Iteration.PhysicalPrimary.LeadingCurrent

/-!
# Actual retained leading geometry for the same current inverse

Construct the entire open full-phase geometry input of
`PhysicalNormalInverse.exists_capped_source_history_inverse_from_original_leading`
from the SAME `LeadingCell` and the original fixed comparison/carrier supports.
No phase domain, current inverse, or leading envelope is assumed here. The two
other current-inverse inputs are exactly the checked `LeadingCell.compatible`
and `LeadingCell.solution`; the latter uses `B cell` at shift13 and `E` at shift14.
Consumer: `app:ch_background:prop:bg-inverse` on the original physical history.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization
open PhysicalPrimary ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open NullTransport ActualFlow FlowAmplitude
open ContinuumRow LeadingPrimitive CanonicalCarrier

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU) {K : Set (Euclidean n)}
  (centers : Finset (parameterCube P.radius)) (row col : centers → Fin n)
  (ρ R τ Rc τc Mc rcomp δcomp σcover : centers → ℝ)
  (Ωc : centers → Set (Euclidean n × Euclidean 3)) (ρc Bc gc Bfull : centers → ℝ)
  (Mscalar m c : ℝ) (E : ℕ → ℝ) (A H B : centers → ℕ → ℝ)
  (F : Euclidean n → Euclidean (embeddingDimension n))
  (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
  (hdata : RetainedLeadingData T (K := K) centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank)
  (cell : centers)

local notation "C" => LeadingCell.C T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
  Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
local notation "D" => LeadingCell.D T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
  Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
local notation "W" => LeadingCell.W T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
  Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
local notation "a" => ((0 : Euclidean n), (cell.val.val, T.reference.spatialPatch cell.val.val))
local notation "p₀" => ((0 : Euclidean (n - 1)), (cell.val.val, T.reference.spatialPatch cell.val.val))
local notation "Vcomp" => Set.prod (Ioo (-δcomp cell) (δcomp cell))
  (ball ((0 : Euclidean (n - 1)), cell.val.val) (rcomp cell))

/-- All seven original full-phase geometry clauses for the actual retained
current chart. Only the fixed comparison and source-support geometry is needed;
the open current domain and its admissibility are derived from `hdata`. -/
theorem retained_leading_inverse_geometry
    (hR : 0 < R cell) (hτ : 0 < τ cell) (hσ : 0 < σcover cell)
    {Rwork : ℝ} (hK : K ⊆ ball (0 : Euclidean n) Rwork)
    (hcover : closedBall a (2 * σcover cell) ⊆
      (C).symm '' (Icc (-τ cell / 2) (τ cell / 2) ×ˢ closedBall p₀ (R cell / 64)))
    (Eouter : Set (Euclidean n × CarrierParameter))
    (hgraph : MapsTo (carrierGraph T) Eouter (closedBall a (σcover cell)))
    (hcoordinates : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) Eouter Vcomp) :
    IsOpen (C ⁻¹' D) ∧ MapsTo Prod.fst (C ⁻¹' D) (ball 0 Rwork) ∧
      C ⁻¹' D ⊆ domain T ∧ closedBall a (2 * σcover cell) ⊆ C ⁻¹' D ∧
      W ⊆ C ⁻¹' D ∧ MapsTo (carrierGraph T) Eouter (C ⁻¹' D) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) Eouter Vcomp := by
  have hD := LeadingCell.fact15 T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hin := LeadingCell.fact16 T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hout := LeadingCell.fact18 T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hdomain := LeadingCell.fact0 T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hphysical := LeadingCell.fact1 T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hW : W ⊆ C ⁻¹' D := by
    change (C).symm '' (Icc (-τ cell / 2) (τ cell / 2) ×ˢ closedBall p₀ (R cell / 64)) ⊆ _
    rintro w ⟨q, hq, rfl⟩
    change C ((C).symm q) ∈ D
    rw [(C).apply_symm_apply]
    apply hin
    change q.1 ∈ Ioo (-τ cell) (τ cell) ∧ q.2 ∈ ball p₀ (R cell / 32)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hh := hq.1.1
      linarith
    · have hh := hq.1.2
      linarith
    · exact (mem_closedBall.mp hq.2).trans_lt (by linarith)
  have hsmall : closedBall a (2 * σcover cell) ⊆ C ⁻¹' D := hcover.trans hW
  have hclosed : C ⁻¹' D ⊆ closedBall a (2 * ρ cell) :=
    hout.trans ball_subset_closedBall
  refine ⟨hD.preimage (C).continuous, ?_, hclosed.trans hdomain, hsmall, hW, ?_, hcoordinates⟩
  · intro q hq
    exact hK (interior_subset ((hphysical (hclosed hq)).2.2))
  · exact (hgraph.mono_right (closedBall_subset_closedBall (by linarith))).mono_right hsmall

end JanetCartan.PhysicalInitialization
