module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.UniformTransport
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.Construction

/-!
# Instantiate comparison transport on the actual coefficient-root producer

The root, original flow, initial and whole-segment buffers and elapsed cap are
literal outputs of `UniformGeometry.exists_uniform_fieldRoot_conicGeometry`.
This adapter closes the root-side hypotheses of the comparison estimate;
`Construction` independently closes the comparison-chart and coefficient-budget
hypotheses on the initialized no-return family. Both are used by the finite
root selector in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic EvolutionIntegratedLocalization
open HamiltonPhase ProtectedFlow PhaseCover ActualCarriers RootFamily

variable {d : ℕ}

/-- Enlarging the allowed elapsed cap keeps the original accepted segment and
its physical masks (`app:ch_regular:lem:finite-chain`). No reparametrization
or additional segment is introduced. -/
theorem physicalDirectRelation_mono_elapsed_bound {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ Δ' : ℝ} (hΔ : Δ ≤ Δ')
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hpq : physicalDirectRelation i h Φ U K W χsource χout Δ p q) :
    physicalDirectRelation i h Φ U K W χsource χout Δ' p q := by
  obtain ⟨j, backward, a, b, hab, hp, hq⟩ := hpq
  obtain ⟨elapsed, he, hc, hs, ho, hrel⟩ := hab
  exact ⟨j, backward, a, b, ⟨elapsed, ⟨he.1, he.2.trans hΔ⟩, hc, hs, ho, hrel⟩, hp, hq⟩

/-- Construct the literal coefficient root and flow together with the uniform
comparison-graph estimate. The original conic producer's elapsed cap `γ`,
initial radius `(3 * ρ) / 2`, and whole-segment radius `3 * ρ` are retained.
Arbitrary restrictions of those buffers and arbitrary physical factor supports
are allowed, in both orientations and for each original elapsed cap `Δ ≤ γ`.

The comparison jets are supplied by
`exists_initialized_signed_no_return_with_graph_bounds`; all root equations,
normalized transverse gaps, annular bounds and ODE facts are discharged here
from the actual conic producer, before the varying coefficient field
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_fieldRoot_comparison_transport
    {R M c C Lx α β : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hc : 0 < c) (hC : 0 < C) (hLx : 0 ≤ Lx) (hα : 0 < α) (hαβ : α ≤ β)
    (A₀ : Fin (d + 1) → MetricTensor (d + 1)) (ξ : Euclidean (d + 1))
    (row col : Fin (d + 1)) (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0)
    (hm : (pencil A₀ ξ).adjugate row col ≠ 0) :
    ∃ (i : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ)
      (Hroot : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ)
      (ε ρ T γ L : ℝ),
      0 < ε ∧ 0 < ρ ∧ 0 < T ∧ 0 < γ ∧ γ < T ∧ 1 ≤ L ∧
      let e := coordinateSplit i
      let z : RootState (Euclidean d) := (0, (0, (e ξ).2))
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), MapsTo Q univ (closedBall A₀ ε) →
        cNorm (closedBall 0 R) 3 Q ≤ M →
        let h := fieldRoot e Q Hroot
        let D := fieldDomain e univ ℓ (e ξ).2 ε
        ContDiffOn ℝ ∞ h D ∧
        ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
          ODE.IsSmoothFlowOn (rootHamiltonField h) z (3 * ρ) ((3 * ρ) / 2) T Φ ∧
          ∀ (U K : Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
            (χsource χout : Unit → Euclidean (d + 1) → ℂ) (Δ : ℝ),
            U ⊆ closedBall z ((3 * ρ) / 2) → K ⊆ closedBall z (3 * ρ) →
            W ⊆ closedBall 0 R → Δ ≤ γ →
          ∀ (g : ComparisonGeometry (Euclidean (d + 1)))
            (chart : ComparisonChart (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) g),
            R ≤ 2 * g.radius →
            (∀ η ∈ g.parameters, ∀ x ∈ closedBall 0 R,
              ‖fderiv ℝ (chart.gradientMap η) x‖ ≤ Lx) →
            (∀ η ∈ g.parameters, ∀ x ∈ closedBall 0 R,
              c ≤ ‖chart.gradientMap η x‖ ∧ ‖chart.gradientMap η x‖ ≤ C) →
          ∀ η ∈ g.parameters, ∀ scale ∈ Icc α β, ∀ p q,
            physicalDirectRelation (fun _ : Unit ↦ i) (fun _ ↦ h) (fun _ ↦ Φ)
              (fun _ ↦ U) (fun _ ↦ K) W χsource χout Δ p q →
            ‖q.2 - scale • chart.gradientMap η q.1‖ ≤
              L * ‖p.2 - scale • chart.gradientMap η p.1‖ := by
  obtain ⟨i, ℓ, Uroot, Vroot, Hroot, ε, hε, κ, hκ, μ, _hμ, ν, _hν, G, hG,
    δ, _hδ, ρ, hρ, A, _hA, T, hT, σ, _hσ, βroot, _hβroot, B, _hB,
    _hσR, hσT, _hβη, _hsourceDomain, γ, hγ, _hγβ, hγσ,
    _hcenterCone, _hconeOpen, _hconeConvex, _hconeZero, _hconeClosure,
    κcone, _hκcone, Bmix, _hBmix, Lmix, _hLmix, Jjet, _hJjet, Sjet, _hSjet,
    _hi, _hℓ, _hU, _hV, _hbase, _hH, _hsub, _hband, hD, _hcent,
    hstate, hfields⟩ := UniformGeometry.exists_uniform_fieldRoot_conicGeometry
      isOpen_univ (0 : Euclidean (d + 1)) hR (subset_univ _) A₀ ξ row col hξ hp hreg hm hM
  let e := coordinateSplit i
  let z : RootState (Euclidean d) := (0, (0, (e ξ).2))
  have hγT : γ < T := by linarith
  obtain ⟨L, hL, htransport⟩ := exists_uniform_physicalDirectRelation_comparison_transport
    (fun _ : Unit ↦ ℓ) (fun _ ↦ (e ξ).2) (fun _ ↦ ε) (fun _ ↦ G) (fun _ ↦ hG.le)
    hR hM hc hC hLx hκ hγ.le hα hαβ
  refine ⟨i, ℓ, Hroot, ε, ρ, T, γ, L, hε, hρ, hT, hγ, hγT, hL, ?_⟩
  dsimp only
  intro Q hQ hrange hbudget
  obtain ⟨hh, _hhom, _hrootBounds, _hlow, _hgraded, _hgaps, hroot,
    Φ, Croot, hΦ, _hrest⟩ := hfields Q hQ.contDiffOn hrange hbudget
  have hz : ((e (0 : Euclidean (d + 1))).1,
      ((e (0 : Euclidean (d + 1))).2, (e ξ).2)) = z := by simp [z]
  have hKD : closedBall z (3 * ρ) ⊆ fieldDomain e univ ℓ (e ξ).2 ε := by
    intro v hv
    exact (hstate v (hz.symm ▸ hv)).1
  have hprimitive (v) (hv : v ∈ closedBall z (3 * ρ)) :
      v.2.2 ∈ closedBall (e ξ).2 ε ∧ (1 / 2 : ℝ) ≤ ℓ v.2.2 ∧
        |fieldRoot e Q Hroot v| ≤ ℓ v.2.2 * G := by
    obtain ⟨_, _, hball, hsec⟩ := hstate v (hz.symm ▸ hv)
    obtain ⟨_, _, _, _, _, _, hval, _⟩ := hroot v (hKD hv)
    exact ⟨hball, hsec, hval⟩
  have hroot' (v) (hv : v ∈ fieldDomain e univ ℓ (e ξ).2 ε) :
      v.2.2 ≠ 0 ∧
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (fieldRoot e Q Hroot v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q (e.symm (v.1, v.2.1))))
        (e.symm (fieldRoot e Q Hroot v, v.2.2)) (e.symm (1, 0)) ≠ 0 := by
    obtain ⟨hn, hd, _, _, hgap, _⟩ := hroot v hv
    refine ⟨hn, hd, ?_⟩
    intro he
    have hgap' : κ ≤ |determinantNormalization (e.symm (fieldRoot e Q Hroot v, v.2.2)) *
        fderiv ℝ (determinant (Q (e.symm (v.1, v.2.1)) ))
          (e.symm (fieldRoot e Q Hroot v, v.2.2)) (e.symm (1, 0))| := hgap
    rw [he, mul_zero, abs_zero] at hgap'
    exact (not_le_of_gt hκ) hgap'
  have hgap' (v) (hv : v ∈ closedBall z (3 * ρ)) :
      κ ≤ |pencilRootSpeed Q e (fieldRoot e Q Hroot) v| :=
    (hroot v (hKD hv)).2.2.2.2.1
  have hΦ' : ODE.IsSmoothFlowOn (rootHamiltonField (fieldRoot e Q Hroot))
      z (3 * ρ) ((3 * ρ) / 2) T Φ := hz ▸ hΦ
  refine ⟨hh, Φ, hΦ', ?_⟩
  intro U K W χsource χout Δ hU hK hW hΔ g chart hgr hderiv hnorm η hη scale hscale p q hpq
  exact (htransport Q hQ hbudget (fun _ ↦ i) (fun _ ↦ fieldRoot e Q Hroot)
    (fun _ ↦ Φ) (fun _ ↦ U) (fun _ ↦ K) (fun _ ↦ fieldDomain e univ ℓ (e ξ).2 ε)
    W χsource χout (fun _ ↦ hD) (fun _ ↦ hh) (fun _ ↦ hroot')
    (fun _ ↦ hK.trans hKD) hW (fun _ v hv ↦ hprimitive v (hK hv))
    (fun _ v hv ↦ hgap' v (hK hv)) (fun _ ↦ z) (fun _ ↦ 3 * ρ)
    (fun _ ↦ (3 * ρ) / 2) (fun _ ↦ T) (fun _ ↦ hΦ') (fun _ ↦ hγT)
    (fun _ ↦ hU) g chart hgr hderiv hnorm η hη).2 scale hscale p q
      (physicalDirectRelation_mono_elapsed_bound hΔ hpq)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
