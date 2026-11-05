module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil

/-!
# Restricting the common Hamilton phase to a carrier patch

Steps 1–2 of `app:ch_seed:prop:seed-actual-menu`: the carrier phase is the
zero-energy restriction of the same full-energy phase. The Hamilton flow and
inverse chart are supplied by the Hamilton-phase construction; their existence
and uniform estimates are not asserted here.
-/

@[expose] public noncomputable section

open scoped Topology

namespace JanetCartan.ActualCarriers

open JanetCartan.HamiltonPhase

section Restriction

variable {E U Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U}

/-- The actual phase `Θ(x,z) = S(x,ζ(z))`, where `S` is the zero-energy
restriction of the common phase (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
def carrierPhase (C : ProjectionChart Φ) (ζ : Z → U) (x : E) (z : Z) : ℝ :=
  phase C.coordinates (x, (0, ζ z))

/-- The physical gradient of the restricted phase is the transported momentum
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem hasGradientAt_carrierPhase [CompleteSpace E] (C : ProjectionChart Φ) (ζ : Z → U)
    {x : E} {z : Z} (hz : (x, (0, ζ z)) ∈ C.target) :
    HasGradientAt (fun y ↦ carrierPhase C ζ y z)
      (Φ.momentum (chartLift C.coordinates (x, (0, ζ z)))) x := by
  have ha := C.source_admissible _ (C.maps_to_source _ hz)
  exact Φ.hasFDerivAt_phase_position (C.hasFDerivAt_coordinates _ hz) ha.1 ha.2
    (Filter.eventuallyEq_of_mem (C.isOpen_target.mem_nhds hz)
      (fun w hw ↦ C.right_inverse w hw))

/-- The actual carrier gradient remains in the Hamiltonian's phase-space
domain (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem carrierPhase_gradient_mem_domain [CompleteSpace E]
    (C : ProjectionChart Φ) (ζ : Z → U) {x : E} {z : Z}
    (hz : (x, (0, ζ z)) ∈ C.target) :
    (x, gradient (fun y ↦ carrierPhase C ζ y z) x) ∈ H.domain := by
  rw [(hasGradientAt_carrierPhase C ζ hz).gradient]
  have ha := C.source_admissible _ (C.maps_to_source _ hz)
  have hm := Φ.state_mem _ ha.1 _ ha.2
  simpa only [C.right_inverse _ hz] using hm

/-- Restricting the full-energy eikonal equation gives zero energy exactly
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem carrierPhase_eikonal [CompleteSpace E]
    (C : ProjectionChart Φ) (ζ : Z → U) {x : E} {z : Z}
    (hz : (x, (0, ζ z)) ∈ C.target) :
    H.h (x, gradient (fun y ↦ carrierPhase C ζ y z) x) = 0 :=
  C.eikonal hz

end Restriction

/-- For `h_F = |ξ|^(1-n) p_F`, zero energy gives the exact current
characteristic equation (`app:ch_seed:prop:seed-actual-menu`, Steps 1–2).
The symbol identification and exclusion of zero momentum are explicit inputs;
constructing the Hamilton chart for that symbol remains a prerequisite. -/
theorem carrierPhase_determinant_eq_zero {n : ℕ} {U Z : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    {H : HomogeneousSymbol (Euclidean n)} {Φ : HamiltonFlow H U}
    (C : ProjectionChart Φ) (ζ : Z → U)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hsymbol : ∀ w ∈ H.domain,
      H.h w = ‖w.2‖ ^ (1 - (n : ℤ)) * determinant (Q w.1) w.2)
    (hnonzero : ∀ w ∈ H.domain, w.2 ≠ 0)
    {x : Euclidean n} {z : Z} (hz : (x, (0, ζ z)) ∈ C.target) :
    determinant (Q x) (gradient (fun y ↦ carrierPhase C ζ y z) x) = 0 := by
  have hm := carrierPhase_gradient_mem_domain C ζ hz
  have he := carrierPhase_eikonal C ζ hz
  rw [hsymbol _ hm] at he
  exact (mul_eq_zero.mp he).resolve_left
    (zpow_ne_zero _ (norm_ne_zero_iff.mpr (hnonzero _ hm)))

end JanetCartan.ActualCarriers
