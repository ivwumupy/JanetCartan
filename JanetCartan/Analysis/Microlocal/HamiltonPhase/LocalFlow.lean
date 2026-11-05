module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Flow
public import JanetCartan.Analysis.ODE.SmoothDependence.SmoothFlow

/-!
# Constructing the Hamilton flow from local ODE solutions

For `app:lem:common-hamilton-phase`, Picard–Lindelöf supplies the flow and its
variational equation. The input initial momentum is the transverse energy root;
constructing that root and the inverse projection are separate steps.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Hamilton's autonomous vector field, in position/momentum order
(`app:lem:common-hamilton-phase`). -/
def HomogeneousSymbol.vectorField (H : HomogeneousSymbol E) (z : E × E) : E × E :=
  (H.hp z, -H.hx z)

/-- The first component of the actual field derivative is the prescribed
momentum-gradient derivative (`app:lem:common-hamilton-phase`). -/
theorem HomogeneousSymbol.vectorField_fderiv_fst (H : HomogeneousSymbol E)
    {z : E × E} (hz : z ∈ H.domain) (hd : DifferentiableAt ℝ H.vectorField z)
    (v : E × E) :
    (fderiv ℝ H.vectorField z v).1 = H.hpDerivative z v := by
  exact congrArg (fun A : E × E →L[ℝ] E ↦ A v)
    (hd.hasFDerivAt.fst.unique (H.hasFDerivAt_hp z hz))

section Reparameterization

variable {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The full derivative after inserting section data into an ODE flow
(`app:lem:common-hamilton-phase`). -/
theorem hasFDerivAt_sectionFlow {ψ : F × ℝ → F} {ι : P → F}
    {s : P} {t : ℝ} {v : F} {A : P →L[ℝ] F}
    (hψ : DifferentiableAt ℝ ψ (ι s, t))
    (ht : HasDerivAt (fun r ↦ ψ (ι s, r)) v t)
    (hι : HasFDerivAt ι A s) :
    HasFDerivAt (fun q : ℝ × P ↦ ψ (ι q.2, q.1))
      (flowDifferential v ((ODE.flowInitialDerivative ψ (ι s) t).comp A)) (t, s) := by
  have hleft : (fderiv ℝ ψ (ι s, t)).comp (ContinuousLinearMap.inl ℝ F ℝ) =
      ODE.flowInitialDerivative ψ (ι s) t :=
    (hψ.hasFDerivAt.comp (ι s) ((hasFDerivAt_id _).prodMk (hasFDerivAt_const t _))).fderiv.symm
  have hright : (fderiv ℝ ψ (ι s, t)).comp (ContinuousLinearMap.inr ℝ F ℝ) =
      ContinuousLinearMap.toSpanSingleton ℝ v :=
    (hψ.hasFDerivAt.comp t ((hasFDerivAt_const (ι s) _).prodMk
      (hasFDerivAt_id _))).unique ht.hasFDerivAt
  have hc := hψ.hasFDerivAt.comp (t, s)
    ((hι.comp (t, s) (ContinuousLinearMap.snd ℝ ℝ P).hasFDerivAt).prodMk
      (ContinuousLinearMap.fst ℝ ℝ P).hasFDerivAt)
  convert! hc using 1
  apply ContinuousLinearMap.ext
  intro q
  have hl := congrArg (fun L : F →L[ℝ] F ↦ L (A q.2)) hleft
  have hr := congrArg (fun L : ℝ →L[ℝ] F ↦ L q.1) hright
  change _ = (fderiv ℝ ψ (ι s, t)) (A q.2, q.1)
  rw [show (A q.2, q.1) = (A q.2, 0) + (0, q.1) by simp, map_add]
  simpa [flowDifferential, ContinuousLinearMap.comp_apply, add_comm] using
    congrArg₂ (· + ·) hl.symm hr.symm

end Reparameterization

/-- A genuine Hamilton flow on a two-sided time interval and an open neighborhood
of the chosen section datum. Its derivatives and variational equation come from
Picard–Lindelöf, not from phase identities (`app:lem:common-hamilton-phase`).
The section input is a `Cⁿ` momentum map satisfying the initial energy and
tangential momentum conditions. The constructed position and momentum are jointly
`Cⁿ` on the entire open product domain, including `n = ∞`. -/
theorem exists_localHamiltonFlow [CompleteSpace E] (n : ℕ∞) (hn : 1 ≤ n)
    (H : HomogeneousSymbol E) (hfield : ContDiffOn ℝ n H.vectorField H.domain)
    (j : U →L[ℝ] E) {P : Set (InitialData U)} (hP : IsOpen P)
    (p : InitialData U → E) (hp : ContDiffOn ℝ n p P)
    (hmem : ∀ s ∈ P, (j s.1, p s) ∈ H.domain)
    (henergy : ∀ s ∈ P, H.h (j s.1, p s) = s.2.1)
    (hmomentum : ∀ s ∈ P, ∀ v : U, ⟪p s, j v⟫_ℝ = ⟪s.2.2, v⟫_ℝ)
    {s₀ : InitialData U} (hs₀ : s₀ ∈ P) :
    ∃ Φ : HamiltonFlow H U, ∃ ε > (0 : ℝ),
      Φ.time = Ioo (-ε) ε ∧ s₀ ∈ Φ.parameters ∧ Φ.parameters ⊆ P ∧
      Φ.sectionMap = j ∧
      ContDiffOn ℝ n Φ.position (Φ.time ×ˢ Φ.parameters) ∧
      ContDiffOn ℝ n Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
      ∀ s ∈ Φ.parameters, Φ.momentum (0, s) = p s := by
  have hn₀ : (n : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) this)
  let ι : InitialData U → E × E := fun s ↦ (j s.1, p s)
  have hι (s : InitialData U) (hs : s ∈ P) : DifferentiableAt ℝ ι s :=
    (j.differentiableAt.comp s differentiableAt_fst).prodMk
      ((hp.differentiableOn hn₀ s hs).differentiableAt (hP.mem_nhds hs))
  obtain ⟨r, hr, ε, hε, ψ, hcd, _, hi, hd, hψmem, _, hJ, _⟩ :=
    ODE.exists_contDiffOn_localFlow_in_open n hn H.isOpen_domain (hmem s₀ hs₀)
      hfield 0
  let Q := P ∩ ι ⁻¹' ball (ι s₀) r
  have hιc : ContinuousOn ι P := fun s hs ↦ (hι s hs).continuousAt.continuousWithinAt
  have hQ : IsOpen Q := hιc.isOpen_inter_preimage hP isOpen_ball
  have hsQ : s₀ ∈ Q := ⟨hs₀, mem_ball_self hr⟩
  have hε₀ : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by constructor <;> linarith
  let Z : ℝ × InitialData U → E × E := fun q ↦ ψ (ι q.2, q.1)
  let V : ℝ × InitialData U → InitialData U →L[ℝ] E × E :=
    fun q ↦ (ODE.flowInitialDerivative ψ (ι q.2) q.1).comp (fderiv ℝ ι q.2)
  have hZmem (t : ℝ) (ht : t ∈ Ioo (0 - ε) (0 + ε)) (s : InitialData U)
      (hs : s ∈ Q) : Z (t, s) ∈ H.domain :=
    hψmem _ (ball_subset_closedBall hs.2) _ (Ioo_subset_Icc_self ht)
  have hZ (t : ℝ) (ht : t ∈ Ioo (0 - ε) (0 + ε)) (s : InitialData U)
      (hs : s ∈ Q) :
      HasFDerivAt Z (flowDifferential (H.vectorField (Z (t, s))) (V (t, s))) (t, s) :=
    hasFDerivAt_sectionFlow
      ((hcd.differentiableOn hn₀ (ι s, t) ⟨hs.2, ht⟩).differentiableAt
        ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hs.2, ht⟩))
      (hd _ (ball_subset_closedBall hs.2) t ht) (hι s hs.1).hasFDerivAt
  have hinit (s : InitialData U) (hs : s ∈ Q) : Z (0, s) = ι s :=
    hi _ (ball_subset_closedBall hs.2)
  let Φ : HamiltonFlow H U := {
    time := Ioo (0 - ε) (0 + ε)
    isOpen_time := isOpen_Ioo
    isPreconnected_time := isPreconnected_Ioo
    zero_mem_time := hε₀
    parameters := Q
    isOpen_parameters := hQ
    sectionMap := j
    position := fun q ↦ (Z q).1
    momentum := fun q ↦ (Z q).2
    positionVariation := fun q ↦ (ContinuousLinearMap.fst ℝ E E).comp (V q)
    momentumVariation := fun q ↦ (ContinuousLinearMap.snd ℝ E E).comp (V q)
    state_mem := hZmem
    position_derivative := by
      intro t ht s hs
      convert! (hZ t ht s hs).fst using 1
    momentum_derivative := by
      intro t ht s hs
      convert! (hZ t ht s hs).snd using 1
    variation_equation := by
      intro t ht s hs v
      have hvar := (hJ _ hs.2 t ht).clm_apply (hasDerivAt_const t (fderiv ℝ ι s v))
      have hfst := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hvar
      have he := H.vectorField_fderiv_fst (hZmem t ht s hs)
        ((hfield.differentiableOn hn₀ _ (hZmem t ht s hs)).differentiableAt
          (H.isOpen_domain.mem_nhds (hZmem t ht s hs))) (V (t, s) v)
      have hfst' : HasDerivAt (fun r ↦ (V (r, s) v).1)
          ((fderiv ℝ H.vectorField (Z (t, s)) (V (t, s) v)).1) t := by
        simpa [V, Z, Function.comp_def] using hfst
      rw [he] at hfst'
      exact hfst'
    initial_position := by
      intro s hs
      exact congrArg Prod.fst (hinit s hs)
    initial_energy := by
      intro s hs
      change H.h (Z (0, s)) = _
      rw [hinit s hs]
      exact henergy s hs.1
    initial_momentum := by
      intro s hs v
      rw [hinit s hs]
      exact hmomentum s hs.1 v }
  have hιcd : ContDiffOn ℝ n ι P :=
    ((j.contDiff.comp contDiff_fst).contDiffOn).prodMk hp
  have hZcd : ContDiffOn ℝ n Z (Φ.time ×ˢ Q) :=
    hcd.comp ((hιcd.comp contDiffOn_snd (fun q hq ↦ hq.2.1)).prodMk contDiffOn_fst)
      (fun q hq ↦ ⟨hq.2.2, hq.1⟩)
  refine ⟨Φ, ε, hε, ?_, hsQ, inter_subset_left, rfl, hZcd.fst, hZcd.snd, ?_⟩
  · simp [Φ]
  · intro s hs
    exact congrArg Prod.snd (hinit s hs)

end JanetCartan.HamiltonPhase
