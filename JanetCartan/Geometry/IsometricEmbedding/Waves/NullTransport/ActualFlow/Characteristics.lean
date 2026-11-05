module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.UniformExistence

/-!
# Characteristics for the literal adapted null direction

Construct the forward characteristic map, including exact conservation of
carrier labels. The prescribed closed state ball and the low bounds give a
fixed time interval. The coefficient patch is the one supplied by
`exists_projected_null_coefficients` (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.ActualFlow
open ActualCarriers FrozenMenu CurrentFullPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Integration of the unit adapted-time velocity of the actual lifted
direction (`app:ch_waves:thm:leading`). -/
theorem lifted_trajectory_time (row col : Fin n)
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I) (h0 : 0 ∈ I)
    {γ : ℝ → ℝ × (Euclidean (n - 1) × Euclidean 3)}
    (hγ : ∀ t ∈ I, HasDerivAt γ (liftedDirection T Q row col (γ t)) t)
    {t : ℝ} (ht : t ∈ I) : (γ t).1 = t + (γ 0).1 := by
  have hd (s) (hs : s ∈ I) : HasDerivAt (fun s ↦ (γ s).1) 1 s := (hγ s hs).fst
  exact hI.eqOn_of_deriv_eq hIc
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
    (differentiable_id.add_const _).differentiableOn
    (fun s hs ↦ by rw [(hd s hs).deriv, ((hasDerivAt_id s).add_const _).deriv])
    h0 (by simp) ht

/-- The actual lifted ODE keeps every normalized carrier parameter fixed,
including for negative times (`app:ch_waves:thm:leading`). -/
theorem lifted_trajectory_carrier (row col : Fin n)
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I) (h0 : 0 ∈ I)
    {γ : ℝ → ℝ × (Euclidean (n - 1) × Euclidean 3)}
    (hγ : ∀ t ∈ I, HasDerivAt γ (liftedDirection T Q row col (γ t)) t)
    {t : ℝ} (ht : t ∈ I) : (γ t).2.2 = (γ 0).2.2 := by
  have hd (s) (hs : s ∈ I) : HasDerivAt (fun s ↦ (γ s).2.2) 0 s := (hγ s hs).snd.snd
  exact hI.is_const_of_deriv_eq_zero hIc
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hd s hs).deriv) ht h0

/-- Construct smooth forward characteristics for the SAME actual coefficient
field. The full autonomous flow is retained for the variational and one-high
estimates. The low bounds are on `liftedDirection`, obtained from the named
physical direction by the fixed linear coordinates; they do not assume any
flow bounds (`app:ch_waves:thm:leading`). -/
theorem exists_lifted_characteristics (row col : Fin n)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hbuffer : closedBall (0, p₀) R ⊆
      (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω)
    (hvalue : ∀ q ∈ closedBall (0, p₀) R, ‖liftedDirection T Q row col q‖ ≤ M)
    (hderiv : ∀ q ∈ closedBall (0, p₀) R, ‖fderiv ℝ (liftedDirection T Q row col) q‖ ≤ M) :
    ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
        ℝ × (Euclidean (n - 1) × Euclidean 3),
      ContDiffOn ℝ ∞ Ψ
        (ball (0, p₀) (R / 2) ×ˢ Ioo (-existenceTime R M) (existenceTime R M)) ∧
      (∀ q ∈ closedBall (0, p₀) (R / 2), Ψ (q, 0) = q) ∧
      (∀ q ∈ closedBall (0, p₀) (R / 2), ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
        HasDerivAt (fun s ↦ Ψ (q, s)) (liftedDirection T Q row col (Ψ (q, t))) t) ∧
      (∀ q ∈ closedBall (0, p₀) (R / 2), ∀ t ∈ Icc (-existenceTime R M) (existenceTime R M),
        Ψ (q, t) ∈ closedBall (0, p₀) R) ∧
      (∀ a b : ℝ, -existenceTime R M < a → b < existenceTime R M →
        ∀ s ⊆ ball (0, p₀) (R / 2), ∀ j : ℕ,
          HasJetEvolutionOn (fun t q ↦ Ψ (q, t)) s j a b
            (fun k t q ↦ ODE.jetEvolutionCoefficient k (liftedDirection T Q row col) (Ψ (q, t)))
            (fun k t q ↦ ODE.jetEvolutionForcing k (liftedDirection T Q row col)
              (fun p ↦ Ψ (p, t)) q)) ∧
      ∃ Φ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        Φ = (fun q ↦ (Ψ ((0, q.2), q.1)).2) ∧
        ContDiffOn ℝ ∞ Φ
          (Ioo (-existenceTime R M) (existenceTime R M) ×ˢ ball p₀ (R / 2)) ∧
        (∀ p ∈ ball p₀ (R / 2), Φ (0, p) = p) ∧
        (∀ p ∈ ball p₀ (R / 2), ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
          Ψ ((0, p), t) = (t, Φ (t, p))) ∧
        (∀ p ∈ ball p₀ (R / 2), ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
          (Φ (t, p)).2 = p.2) ∧
        MapsTo (fun q ↦ (q.1, Φ q))
          (Ioo (-existenceTime R M) (existenceTime R M) ×ˢ ball p₀ (R / 2))
          ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω) ∧
        (∀ p ∈ ball p₀ (R / 2), ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
          HasDerivAt (fun s ↦ Φ (s, p))
            ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
              ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
                (t, Φ (t, p))))).2, 0) t) := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let ε := existenceTime R M
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε :=
    ⟨neg_neg_of_pos (existenceTime_pos hR hM), existenceTime_pos hR hM⟩
  obtain ⟨Ψ, hΨ, _, hi, hode, hrange, _, _, hjets⟩ :=
    exists_smoothFlow_on_fixed_ball (hΩ.preimage C.symm.continuous)
      (contDiffOn_liftedDirection T Q row col hd) hR hM hbuffer hvalue hderiv
  let Φ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3 :=
    fun q ↦ (Ψ ((0, q.2), q.1)).2
  have hsection {p : Euclidean (n - 1) × Euclidean 3} (hp : p ∈ ball p₀ (R / 2)) :
      ((0 : ℝ), p) ∈ ball (0, p₀) (R / 2) := by simpa using hp
  have htime (p) (hp : p ∈ ball p₀ (R / 2)) (t) (ht : t ∈ Ioo (-ε) ε) :
      Ψ ((0, p), t) = (t, Φ (t, p)) := by
    refine Prod.ext ?_ rfl
    have h := lifted_trajectory_time T Q row col isOpen_Ioo (convex_Ioo _ _).isPreconnected
      h0 (hode (0, p) (ball_subset_closedBall (hsection hp))) ht
    simpa [hi (0, p) (ball_subset_closedBall (hsection hp))] using h
  refine ⟨Ψ, hΨ, hi, hode, hrange, hjets, Φ, rfl, ?_, ?_, htime, ?_, ?_, ?_⟩
  · exact hΨ.snd.comp ((contDiffOn_const.prodMk contDiffOn_snd).prodMk contDiffOn_fst)
      (fun q hq ↦ ⟨hsection hq.2, hq.1⟩)
  · intro p hp
    exact congrArg Prod.snd (hi (0, p) (ball_subset_closedBall (hsection hp)))
  · intro p hp t ht
    have h := lifted_trajectory_carrier T Q row col isOpen_Ioo
      (convex_Ioo _ _).isPreconnected h0
      (hode (0, p) (ball_subset_closedBall (hsection hp))) ht
    simpa [Φ, hi (0, p) (ball_subset_closedBall (hsection hp))] using h
  · rintro ⟨t, p⟩ ⟨ht, hp⟩
    change (t, Φ (t, p)) ∈ C.symm ⁻¹' Ω
    rw [← htime p hp t ht]
    exact hbuffer (hrange (0, p) (ball_subset_closedBall (hsection hp)) t
      (Ioo_subset_Icc_self ht))
  · intro p hp t ht
    have h := (hode (0, p) (ball_subset_closedBall (hsection hp)) t ht).snd
    rw [htime p hp t ht] at h
    exact h

end JanetCartan.NullTransport.ActualFlow
