module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Localization

/-!
# Global auxiliary data agreeing with the local family

The auxiliary data supply the hypotheses of the compact transport calculus
for `app:ch_osc:prop:osc-normal`, without changing the original input data.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
local notation "E" => Euclidean n

/-- A globally smooth auxiliary amplitude with fixed compact spatial support,
agreeing with the original amplitude on the entire closed parameter interval.
This supplies the compact calculus in `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.exists_localizedAmplitude (F : UniformNormalData G C) :
    ∃ (a : ℝ → E → E → Fin r → ℂ) (S : Set (E × E)),
      IsCompact S ∧ S ⊆ G.X ×ˢ G.D ∧ G.X₀ ×ˢ G.D₀ ⊆ S ∧
      (∀ i, ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ a p.1 p.2.1 p.2.2 i)) ∧
      (∀ i s z, z ∉ S → a s z.1 z.2 i = 0) ∧
      ∀ s ∈ Icc 0 G.ε₀, ∀ x u, a s x u = F.amplitude s x u := by
  have hU := F.isOpen_parameterDomain.prod (G.isOpen_X.prod G.isOpen_D)
  have hf : ContDiffOn ℝ ∞ (fun p : ℝ × (E × E) ↦ F.amplitude p.1 p.2.1 p.2.2)
      (F.parameterDomain ×ˢ (G.X ×ˢ G.D)) := by
    intro p hp
    exact (F.amplitude_contDiffAt hp.1 hp.2.1 hp.2.2).contDiffWithinAt
  obtain ⟨b, hb, hbc, hbs, hbz, hbe⟩ := exists_contDiff_localization hU
    (isCompact_Icc.prod (G.compact_X₀.prod G.compact_D₀))
    (prod_mono F.parameter_subset (prod_mono G.X₀_subset G.D₀_subset)) hf
  let S := Prod.snd '' tsupport b ∪ (G.X₀ ×ˢ G.D₀)
  refine ⟨fun s x u ↦ b (s, (x, u)), S,
    (hbc.image continuous_snd).union (G.compact_X₀.prod G.compact_D₀), ?_,
    subset_union_right, ?_, ?_, ?_⟩
  · rintro z (⟨p, hp, rfl⟩ | hz)
    · exact (hbs hp).2
    · exact ⟨G.X₀_subset hz.1, G.D₀_subset hz.2⟩
  · intro i
    exact (contDiff_pi.mp hb) i
  · intro i s z hz
    have hz' : (s, z) ∉ tsupport b := fun hp ↦ hz (Or.inl ⟨_, hp, rfl⟩)
    exact congrFun (image_eq_zero_of_notMem_tsupport hz') i
  · intro s hs x u
    by_cases hz : (x, u) ∈ G.X₀ ×ˢ G.D₀
    · exact (hbe (s, (x, u)) ⟨hs, hz⟩).eq_of_nhds
    · have hzero := F.amplitude_eq_zero_off_carrier hs hz
      exact (hbz _ hzero).trans hzero.symm

/-- A smooth auxiliary phase agrees locally with the given phase at every
admissible parameter on a specified compact spatial carrier. It is used only
to invoke compact calculus in `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.exists_localizedPhase (F : UniformNormalData G C)
    {S : Set (E × E)} (hS : IsCompact S) (hSU : S ⊆ G.X ×ˢ G.D) :
    ∃ φ : ℝ → E → E → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2) ∧
      ∀ s ∈ Icc 0 G.ε₀, ∀ z ∈ S,
        (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2) =ᶠ[𝓝 (s, z)]
          (fun p ↦ F.phase p.1 p.2.1 p.2.2) := by
  have hf : ContDiffOn ℝ ∞ (fun p : ℝ × (E × E) ↦ F.phase p.1 p.2.1 p.2.2)
      (F.parameterDomain ×ˢ (G.X ×ˢ G.D)) := by
    intro p hp
    exact (F.phase_contDiffAt hp.1 hp.2.1 hp.2.2).contDiffWithinAt
  obtain ⟨b, hb, _, _, _, he⟩ := exists_contDiff_localization
    (F.isOpen_parameterDomain.prod (G.isOpen_X.prod G.isOpen_D))
    (isCompact_Icc.prod hS) (prod_mono F.parameter_subset hSU) hf
  exact ⟨fun s x u ↦ b (s, (x, u)), hb, fun s hs z hz ↦ he (s, z) ⟨hs, hz⟩⟩

/-- Smooth localization of the actual averaged-gradient velocity near a
compact spatial carrier. No new velocity hypothesis is imposed in
`app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.exists_localizedVelocity (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {S : Set (E × E)} (hS : IsCompact S) (hSU : S ⊆ G.X ×ˢ G.D) :
    ∃ w : (E × E) → E → E, ContDiff ℝ ∞ (Function.uncurry w) ∧
      ∀ x y u, (x, u) ∈ S → (y, u) ∈ S →
        (Function.uncurry w) =ᶠ[𝓝 ((x, y), u)]
          (fun p : (E × E) × E ↦ F.transportVelocity ε p.1.1 p.1.2 p.2) := by
  let Q : Set ((E × E) × E) := ((Prod.fst '' S) ×ˢ (Prod.fst '' S)) ×ˢ (Prod.snd '' S)
  have hQ : IsCompact Q :=
    ((hS.image continuous_fst).prod (hS.image continuous_fst)).prod
      (hS.image continuous_snd)
  have hQU : Q ⊆ (G.X ×ˢ G.X) ×ˢ G.D := by
    intro p hp
    obtain ⟨z, hz, hx⟩ := hp.1.1
    obtain ⟨v, hv, hy⟩ := hp.1.2
    obtain ⟨t, ht, hu⟩ := hp.2
    exact ⟨⟨hx ▸ (hSU hz).1, hy ▸ (hSU hv).1⟩, hu ▸ (hSU ht).2⟩
  have hf : ContDiffOn ℝ ∞
      (fun p : (E × E) × E ↦ F.transportVelocity ε p.1.1 p.1.2 p.2)
      ((G.X ×ˢ G.X) ×ˢ G.D) := by
    intro p hp
    exact ((F.transportVelocity_contDiffAt (q := (ε, (p.1.1, (p.1.2, p.2))))
      ⟨hε, hp.1.1, hp.1.2, hp.2⟩).comp p
      (contDiffAt_const.prodMk (contDiffAt_fst.fst.prodMk
        (contDiffAt_fst.snd.prodMk contDiffAt_snd)))).contDiffWithinAt
  obtain ⟨b, hb, _, _, _, he⟩ := exists_contDiff_localization
    ((G.isOpen_X.prod G.isOpen_X).prod G.isOpen_D) hQ hQU hf
  refine ⟨fun z u ↦ b (z, u), hb, ?_⟩
  intro x y u hx hy
  exact he ((x, y), u) ⟨⟨⟨_, hx, rfl⟩, ⟨_, hy, rfl⟩⟩, ⟨_, hx, rfl⟩⟩

/-- The localized phase and velocity satisfy the geometric premise of the
compact calculus, using the actual averaged-gradient inverse
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.localized_phase_transport_identity
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {φ : ℝ → E → E → ℝ} {w : (E × E) → E → E}
    {x y u : E} (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D)
    (heφx : (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2) =ᶠ[𝓝 (ε, (x, u))]
      (fun p ↦ F.phase p.1 p.2.1 p.2.2))
    (heφy : (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2) =ᶠ[𝓝 (ε, (y, u))]
      (fun p ↦ F.phase p.1 p.2.1 p.2.2))
    (hew : w (x, y) u = F.transportVelocity ε x y u) :
    deriv (fun s ↦ φ s x u - φ s y u) ε =
      fderiv ℝ (fun v ↦ φ ε x v - φ ε y v) u (w (x, y) u) := by
  have het := (heφx.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt).sub
    (heφy.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt)
  have heu := (heφx.comp_tendsto
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt).sub
    (heφy.comp_tendsto
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt)
  change (fun s ↦ φ s x u - φ s y u) =ᶠ[𝓝 ε]
    (fun s ↦ F.phase s x u - F.phase s y u) at het
  change (fun v ↦ φ ε x v - φ ε y v) =ᶠ[𝓝 u]
    (fun v ↦ F.phase ε x v - F.phase ε y v) at heu
  rw [het.deriv_eq, heu.fderiv_eq, hew]
  exact F.phase_transport_identity hε hx hy hu

end JanetCartan.NormalComparison
