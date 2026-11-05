module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Differential

/-!
# Stationarity of the localized elapsed integral

The kernel in `app:ch_regular_base:eq:fixed-time-representation` is localized
using the literal graph phases of `app:ch_regular:eq:joint-kernel-phase`.
Elapsed time is an additional integration variable. Its derivative imposes
zero source energy in the interior, whereas the boundary has only the five
tangential equations. The consumer is the half-space localization proof of
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set
open scoped InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph

variable {d : ℕ}

attribute [local fun_prop] DifferentiableAt.inner

/-- The localized elapsed phase, with elapsed time followed by both physical
bases and all three physical covectors. Reversal exchanges the physical
positions as in the literal adjoint (`app:ch_regular:eq:joint-kernel-phase`). -/
def jointElapsedPhase (backward : Bool) (Ψ : TwoTimePhase d)
    (x y : Euclidean (d + 1)) (p : ℝ × JointVariables (Euclidean (d + 1))) : ℝ :=
  jointPhase backward (elapsedPhase Ψ p.1) x y p.2

/-- The sixth derivative of the localized forward kernel is minus its
original source energy. Localizers introduce no elapsed-time phase term
(`app:ch_regular:lem:finite-chain`). -/
theorem hasDerivAt_jointElapsedPhase_forward_elapsed
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    HasDerivAt (fun s ↦ jointElapsedPhase false (chartPhase C) x y (s, p))
      (-rootSuspension h (elapsedInputBase C r p.1.1 p.2.1, p.2.1)) r := by
  simp only [jointElapsedPhase, jointPhase, Bool.false_eq_true, ↓reduceIte, forwardPhase]
  exact (((hasDerivAt_elapsedChartPhase_elapsed hphase).sub_const _).add_const _).add_const _

/-- Literal adjunction changes the sign of the elapsed derivative while
keeping the original source energy and original amplitude positions
(`app:ch_regular:lem:finite-chain`). -/
theorem hasDerivAt_jointElapsedPhase_reverse_elapsed
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    HasDerivAt (fun s ↦ jointElapsedPhase true (chartPhase C) x y (s, p))
      (rootSuspension h (elapsedInputBase C r p.1.1 p.2.1, p.2.1)) r := by
  simp only [jointElapsedPhase, jointPhase, ↓reduceIte, reversePhase]
  simpa only [neg_neg] using
    (((hasDerivAt_elapsedChartPhase_elapsed hphase).const_sub _).add_const _).add_const _

/-- All five boundary-tangential equations of the actual forward elapsed
kernel, including both base equations (`app:ch_regular:eq:joint-stationary`). -/
theorem forwardStationary_elapsed_iff
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (r : ℝ) (x y u z ξ η ζ : Euclidean (d + 1))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r u ξ))
      (elapsedChartPoint r u ξ)) :
    ForwardStationary (elapsedPhase (chartPhase C) r) x y u z ξ η ζ ↔
      ζ = elapsedOutputCovector h Φ C r u ξ ∧ η = ξ ∧
      z = elapsedInputBase C r u ξ ∧ z = y ∧ x = u := by
  rw [forwardStationary_iff _ _ _ _ _ _ _ _
    (hasFDerivAt_elapsedChartPhase_output hphase).differentiableAt
    (hasFDerivAt_elapsedChartPhase_covector hphase).differentiableAt,
    (hasFDerivAt_elapsedChartPhase_output hphase).fderiv,
    (hasFDerivAt_elapsedChartPhase_covector hphase).fderiv,
    innerSL_inj, innerSL_inj]
  tauto

/-- All five equations for the literal reversed kernel. The localizer output
is the original graph source (`app:ch_regular:eq:joint-stationary`). -/
theorem reverseStationary_elapsed_iff
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (r : ℝ) (x y u z ξ η ζ : Euclidean (d + 1))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r u ξ))
      (elapsedChartPoint r u ξ)) :
    ReverseStationary (elapsedPhase (chartPhase C) r) x y u z ξ η ζ ↔
      η = elapsedOutputCovector h Φ C r u ξ ∧ ζ = ξ ∧
      z = elapsedInputBase C r u ξ ∧ u = y ∧ x = z := by
  rw [reverseStationary_iff_swap, forwardStationary_elapsed_iff r y x u z ξ ζ η hphase]
  tauto

private theorem fderiv_prod_eq_zero_iff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} {r : ℝ} {p : V}
    (hF : DifferentiableAt ℝ F (r, p)) :
    fderiv ℝ F (r, p) = 0 ↔
      deriv (fun s ↦ F (s, p)) r = 0 ∧ fderiv ℝ (fun v ↦ F (r, v)) p = 0 := by
  let D := fderiv ℝ F (r, p)
  have hr : HasDerivAt (fun s ↦ F (s, p)) (D (1, 0)) r := by
    convert! hF.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r p))
  have hp := (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) r p)).fderiv
  simp only [Function.comp_def] at hp
  rw [hr.deriv, hp]
  constructor
  · intro hz
    simp [D, hz]
  · rintro ⟨hr, hp⟩
    apply ContinuousLinearMap.ext
    rintro ⟨s, v⟩
    have hv : D (0, v) = 0 := by
      simpa using congrArg (fun L : V →L[ℝ] ℝ ↦ L v) hp
    have he : (s, v) = s • (1, (0 : V)) + (0, v) := by simp
    change D (s, v) = 0
    rw [he, map_add, map_smul, hr, hv]
    simp

/-- Differentiability of the whole integration phase follows from the
actual two-time chart differential at the supported point. No global smooth
extension or regularity at zero spatial frequency is assumed
(`app:ch_regular:lem:finite-chain`). -/
theorem differentiableAt_jointElapsedPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (backward : Bool) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint p.1 p.2.1.1 p.2.2.1))
      (elapsedChartPoint p.1 p.2.1.1 p.2.2.1)) :
    DifferentiableAt ℝ (jointElapsedPhase backward (chartPhase C) x y) p := by
  have hchart : DifferentiableAt ℝ
      (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
        elapsedChartPoint w.1 w.2.1.1 w.2.2.1) p := by
    unfold elapsedChartPoint
    change DifferentiableAt ℝ (fun w ↦
      (w.2.1.1 0, (w.2.1.1 0 - w.1, (spatialPartCLM w.2.1.1,
        spatialPartCLM w.2.2.1)))) p
    fun_prop
  have hc := hphase.differentiableAt.comp p hchart
  have he : DifferentiableAt ℝ
      (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
        elapsedPhase (chartPhase C) w.1 w.2.1.1 w.2.2.1) p := by
    change DifferentiableAt ℝ (fun w ↦
      (w.2.1.1 0 - w.1) * w.2.2.1 0 +
        twoTimePhase C (elapsedChartPoint w.1 w.2.1.1 w.2.2.1)) p
    exact DifferentiableAt.add (by fun_prop) hc
  cases backward
  · change DifferentiableAt ℝ (fun w ↦
      elapsedPhase (chartPhase C) w.1 w.2.1.1 w.2.2.1 -
        inner ℝ w.2.1.2 w.2.2.1 + inner ℝ (w.2.1.2-y) w.2.2.2.1 +
        inner ℝ (x-w.2.1.1) w.2.2.2.2) p
    exact ((he.sub (by fun_prop)).add (by fun_prop)).add (by fun_prop)
  · change DifferentiableAt ℝ (fun w ↦
      inner ℝ w.2.1.2 w.2.2.1 - elapsedPhase (chartPhase C) w.1 w.2.1.1 w.2.2.1 +
        inner ℝ (w.2.1.1-y) w.2.2.2.1 + inner ℝ (x-w.2.1.2) w.2.2.2.2) p
    exact (((by fun_prop : DifferentiableAt ℝ _ p).sub he).add (by fun_prop)).add
      (by fun_prop)

/-- Joint differentiability at a supported physical base/covector pair follows
from the original two-time differential (`app:ch_regular:eq:joint-stationary`). -/
theorem differentiableAt_elapsedChartPhase_uncurry
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {u ξ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r u ξ))
      (elapsedChartPoint r u ξ)) :
    DifferentiableAt ℝ (Function.uncurry (elapsedPhase (chartPhase C) r))
      (u, ξ) := by
  have hc : DifferentiableAt ℝ (fun w : Euclidean (d + 1) × Euclidean (d + 1) ↦
      elapsedChartPoint r w.1 w.2) (u, ξ) := by
    unfold elapsedChartPoint
    change DifferentiableAt ℝ (fun w : Euclidean (d + 1) × Euclidean (d + 1) ↦
      (w.1 0, (w.1 0 - r,
      (spatialPartCLM w.1, spatialPartCLM w.2)))) _
    fun_prop
  change DifferentiableAt ℝ (fun w : Euclidean (d + 1) × Euclidean (d + 1) ↦
    (w.1 0 - r) * w.2 0 + twoTimePhase C (elapsedChartPoint r w.1 w.2)) _
  have hd := hphase.differentiableAt.comp (u, ξ) hc
  exact DifferentiableAt.add (by fun_prop) hd

/-- The full derivative vanishes precisely when all five physical equations
and the original zero-energy equation hold. This is the interior stationary
branch of `app:ch_regular:lem:finite-chain`. -/
theorem fderiv_jointElapsedPhase_forward_eq_zero_iff
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    fderiv ℝ (jointElapsedPhase false (chartPhase C) x y) (r, p) = 0 ↔
      ForwardStationary (elapsedPhase (chartPhase C) r)
        x y p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2 ∧
      rootSuspension h (elapsedInputBase C r p.1.1 p.2.1, p.2.1) = 0 := by
  have hj := differentiableAt_jointElapsedPhase false x y (r, p) hphase
  have hφ := differentiableAt_elapsedChartPhase_uncurry hphase
  rw [fderiv_prod_eq_zero_iff hj,
    (hasDerivAt_jointElapsedPhase_forward_elapsed x y r p hphase).deriv, neg_eq_zero]
  change _ ∧ fderiv ℝ (jointPhase false (elapsedPhase (chartPhase C) r) x y) p = 0 ↔ _
  rw [fderiv_jointPhase_forward_eq_zero_iff _ _ _ _ hφ]
  tauto

/-- The same six equations for the literal adjoint. Its zero-energy equation
is imposed at the original graph source, which is the reversed output
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_jointElapsedPhase_reverse_eq_zero_iff
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1)) :
    fderiv ℝ (jointElapsedPhase true (chartPhase C) x y) (r, p) = 0 ↔
      ReverseStationary (elapsedPhase (chartPhase C) r)
        x y p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2 ∧
      rootSuspension h (elapsedInputBase C r p.1.1 p.2.1, p.2.1) = 0 := by
  rw [fderiv_prod_eq_zero_iff (differentiableAt_jointElapsedPhase true x y (r, p) hphase),
    (hasDerivAt_jointElapsedPhase_reverse_elapsed x y r p hphase).deriv]
  change _ ∧ fderiv ℝ (jointPhase true (elapsedPhase (chartPhase C) r) x y) p = 0 ↔ _
  rw [fderiv_jointPhase_reverse_eq_zero_iff _ _ _ _
    (differentiableAt_elapsedChartPhase_uncurry hphase)]
  tauto

private theorem forwardStationary_relation
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x y u z ξ η ζ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r u ξ))
      (elapsedChartPoint r u ξ))
    (hs : ForwardStationary (elapsedPhase (chartPhase C) r) x y u z ξ η ζ) :
    x = u ∧ y = z ∧ η = ξ ∧
      ForwardRelation (elapsedPhase (chartPhase C) r) z ξ u ζ := by
  obtain ⟨ho, hi, hb, hz, hx⟩ := (forwardStationary_elapsed_iff r x y u z ξ η ζ hphase).mp hs
  exact ⟨hx, hz.symm, hi, (forwardRelation_elapsedChartPhase_iff hphase).mpr ⟨hb, ho⟩⟩

/-- Projection of the actual interior critical set is the original
zero-characteristic flow, with its exact elapsed time and physical bases.
This does not assert protection of arbitrary-energy fixed-time graphs
(`app:ch_regular:lem:finite-chain`). -/
theorem forward_interior_stationary_flow
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hzero : fderiv ℝ (jointElapsedPhase false (chartPhase C) x y) (r, p) = 0) :
    (x, p.2.2.2) = rootSuspensionState h 0 (Φ (spacetimeRootState (y, p.2.2.1), r)) ∧
      rootSuspension h (y, p.2.2.1) = 0 ∧ y 0 + r = x 0 := by
  obtain ⟨hs, he⟩ := (fderiv_jointElapsedPhase_forward_eq_zero_iff x y r p hphase).mp hzero
  obtain ⟨hx, hy, hη, hrel⟩ := forwardStationary_relation hphase hs
  have hb := (forwardRelation_elapsedChartPhase_iff hphase).mp hrel |>.1
  rw [← hb] at he
  obtain ⟨hf, ht⟩ := forwardRelation_elapsedChartPhase_flow hC hq hclock hphase hrel
  rw [he] at hf
  simpa only [hx, hy, hη] using And.intro hf (And.intro he ht)

/-- The literal adjoint interior relation is the inverse of the SAME
zero-characteristic flow. The old graph source is the new output, and its
elapsed time runs from that output to the new input
(`app:ch_regular:lem:finite-chain`). -/
theorem reverse_interior_stationary_flow
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hzero : fderiv ℝ (jointElapsedPhase true (chartPhase C) x y) (r, p) = 0) :
    (y, p.2.2.1) = rootSuspensionState h 0 (Φ (spacetimeRootState (x, p.2.2.2), r)) ∧
      rootSuspension h (x, p.2.2.2) = 0 ∧ x 0 + r = y 0 := by
  obtain ⟨hs, he⟩ := (fderiv_jointElapsedPhase_reverse_eq_zero_iff x y r p hphase).mp hzero
  rw [reverseStationary_iff_swap] at hs
  obtain ⟨hy, hx, hζ, hrel⟩ := forwardStationary_relation hphase hs
  have hb := (forwardRelation_elapsedChartPhase_iff hphase).mp hrel |>.1
  rw [← hb] at he
  obtain ⟨hf, ht⟩ := forwardRelation_elapsedChartPhase_flow hC hq hclock hphase hrel
  rw [he] at hf
  simpa only [hx, hy, hζ] using And.intro hf (And.intro he ht)

/-- At the genuine boundary `r = 0`, only the tangential derivative is used.
Its stationary points lie on the full diagonal, with no zero-energy
restriction (`app:ch_regular:lem:finite-chain`). -/
theorem boundary_stationary_diagonal
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint 0 p.1.1 p.2.1 ∈ C.target)
    (hi : Φ ((C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2, 0) =
      (C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 p.1.1 p.2.1))
      (elapsedChartPoint 0 p.1.1 p.2.1))
    (hzero : fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (0, w)) p = 0) :
    x = y ∧ p.2.2.2 = p.2.2.1 := by
  have hφ := differentiableAt_elapsedChartPhase_uncurry hphase
  cases backward
  · obtain hs := (fderiv_jointPhase_forward_eq_zero_iff _ x y p hφ).mp hzero
    obtain ⟨hx, hy, hη, hrel⟩ := forwardStationary_relation hphase hs
    obtain ⟨hb, hξ⟩ := elapsed_graph_zero_diagonal hC hq hi hphase hrel
    exact ⟨hx.trans (hb.symm.trans hy.symm), hξ.trans hη.symm⟩
  · obtain hs := (fderiv_jointPhase_reverse_eq_zero_iff _ x y p hφ).mp hzero
    rw [reverseStationary_iff_swap] at hs
    obtain ⟨hy, hx, hζ, hrel⟩ := forwardStationary_relation hphase hs
    obtain ⟨hb, hξ⟩ := elapsed_graph_zero_diagonal hC hq hi hphase hrel
    exact ⟨hx.trans (hb.trans hy.symm), hζ.trans hξ.symm⟩

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
