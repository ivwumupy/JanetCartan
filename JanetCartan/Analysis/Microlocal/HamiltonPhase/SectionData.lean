module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Flow
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Patch
public import Mathlib.Analysis.Convex.Topology

/-!
# Initial data on a transverse Hamilton section

For `app:lem:common-hamilton-phase`, solve the energy equation on the initial
section using the constructed scalar implicit function. All homogeneity claims
are restricted to the local chart; the symbol is never extended outside its
given domain.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Scaling of the canonical variables, leaving the section point fixed
(`app:lem:common-hamilton-phase`). -/
def scaleSectionData (r : ℝ) (s : InitialData U) : InitialData U := (s.1, r • s.2)

/-- Unit canonical scaling fixes the section datum (`app:lem:common-hamilton-phase`). -/
@[simp] theorem scaleSectionData_one (s : InitialData U) : scaleSectionData 1 s = s := by
  simp [scaleSectionData]

/-- Canonical scalings compose multiplicatively (`app:lem:common-hamilton-phase`). -/
@[simp] theorem scaleSectionData_mul (r t : ℝ) (s : InitialData U) :
    scaleSectionData r (scaleSectionData t s) = scaleSectionData (r * t) s := by
  simp [scaleSectionData, mul_smul]

/-- Initial phase-space point with an unresolved normal momentum
(`app:lem:common-hamilton-phase`). -/
def transverseSectionState (j : U →ₗᵢ[ℝ] E) (ν : E)
    (w : InitialData U × ℝ) : E × E := (j w.1.1, w.2 • ν + j w.1.2.2)

/-- The scalar energy equation to which the local-root theorem is applied
(`app:lem:common-hamilton-phase`). -/
def sectionEnergyEquation (H : HomogeneousSymbol E) (j : U →ₗᵢ[ℝ] E) (ν : E)
    (w : InitialData U × ℝ) : ℝ := H.h (transverseSectionState j ν w) - w.1.2.1

/-- Smooth linear insertion of the transverse momentum coordinate
(`app:lem:common-hamilton-phase`). -/
theorem contDiff_transverseSectionState (j : U →ₗᵢ[ℝ] E) (ν : E) :
    ContDiff ℝ ∞ (transverseSectionState j ν) :=
  (j.contDiff.comp contDiff_fst.fst).prodMk
    ((contDiff_snd.smul contDiff_const).add (j.contDiff.comp contDiff_fst.snd.snd))

/-- The transverse derivative is the normal component of the Hamilton velocity
(`app:lem:common-hamilton-phase`). -/
theorem scalarDerivative_sectionEnergyEquation (H : HomogeneousSymbol E)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {w : InitialData U × ℝ}
    (hw : transverseSectionState j ν w ∈ H.domain) :
    CharacteristicRoot.scalarDerivative (sectionEnergyEquation H j ν) w =
      ⟪H.hp (transverseSectionState j ν w), ν⟫_ℝ := by
  let L : (InitialData U × ℝ) →L[ℝ] E × E :=
    (j.toContinuousLinearMap.comp ((ContinuousLinearMap.fst ℝ U (ℝ × U)).comp
      (ContinuousLinearMap.fst ℝ (InitialData U) ℝ))).prod
    (((ContinuousLinearMap.snd ℝ (InitialData U) ℝ).smulRight ν) +
      j.toContinuousLinearMap.comp ((ContinuousLinearMap.snd ℝ ℝ U).comp
        ((ContinuousLinearMap.snd ℝ U (ℝ × U)).comp
          (ContinuousLinearMap.fst ℝ (InitialData U) ℝ))))
  have hL : HasFDerivAt (transverseSectionState j ν) L w := L.hasFDerivAt
  have hd := ((H.hasFDerivAt_h _ hw).comp w hL).sub
    (((ContinuousLinearMap.fst ℝ ℝ U).comp
      ((ContinuousLinearMap.snd ℝ U (ℝ × U)).comp
        (ContinuousLinearMap.fst ℝ (InitialData U) ℝ))).hasFDerivAt)
  change HasFDerivAt (sectionEnergyEquation H j ν) _ w at hd
  rw [CharacteristicRoot.scalarDerivative, hd.fderiv]
  simp [L, hamiltonDifferential]

/-- Momentum reconstructed from a scalar normal root
(`app:lem:common-hamilton-phase`). -/
def sectionRootMomentum (j : U →ₗᵢ[ℝ] E) (ν : E) (g : InitialData U → ℝ)
    (s : InitialData U) : E := g s • ν + j s.2.2

/-- The tangential canonical pairing follows from the orthogonal isometric
section, independently of the energy equation (`app:lem:common-hamilton-phase`). -/
theorem sectionRootMomentum_pairing (j : U →ₗᵢ[ℝ] E) (ν : E)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0) (g : InitialData U → ℝ)
    (s : InitialData U) (v : U) :
    ⟪sectionRootMomentum j ν g s, j v⟫_ℝ = ⟪s.2.2, v⟫_ℝ := by
  simp [sectionRootMomentum, inner_add_left, inner_smul_left, horth, j.inner_map_map]

/-- The scalar root is the normal momentum for a unit normal
(`app:lem:common-hamilton-phase`). -/
theorem sectionRootMomentum_normal (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ‖ν‖ = 1)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0) (g : InitialData U → ℝ)
    (s : InitialData U) : ⟪ν, sectionRootMomentum j ν g s⟫_ℝ = g s := by
  simp [sectionRootMomentum, inner_add_right, inner_smul_right, horth,
    hν]

/-- Local radial scaling extends between any two points of a convex chart.
The proof only follows rays inside that chart (`app:lem:common-hamilton-phase`). -/
private theorem homogeneous_on_convex_of_eventually
    {P : Set (InitialData U)} (hP : IsOpen P) (hPc : Convex ℝ P)
    {g : InitialData U → ℝ}
    (hg : ∀ s ∈ P, ∀ᶠ r : ℝ in 𝓝 1, g (scaleSectionData r s) = r * g s)
    {s : InitialData U} (hs : s ∈ P) {r : ℝ} (hr : 0 < r)
    (hrs : scaleSectionData r s ∈ P) : g (scaleSectionData r s) = r * g s := by
  let I : Set ℝ := {t | scaleSectionData t s ∈ P} ∩ Ioi 0
  have hscale : Continuous (fun t : ℝ ↦ scaleSectionData t s) :=
    continuous_const.prodMk (continuous_id.smul continuous_const)
  have hI : IsOpen I := (hP.preimage hscale).inter isOpen_Ioi
  have hIc : Convex ℝ I := by
    apply Convex.inter ?_ (convex_Ioi 0)
    intro a ha b hb c d hc hd hcd
    have hh := hPc ha hb hc hd hcd
    change scaleSectionData (c • a + d • b) s ∈ P
    have he : scaleSectionData (c • a + d • b) s =
        c • scaleSectionData a s + d • scaleSectionData b s := by
      apply Prod.ext
      · simp [scaleSectionData, ← add_smul, hcd]
      · simp [scaleSectionData, add_smul, mul_smul]
    rwa [he]
  have h1 : (1 : ℝ) ∈ I := ⟨by simpa using hs, zero_lt_one⟩
  have hrI : r ∈ I := ⟨hrs, hr⟩
  let q : ℝ → ℝ := fun t ↦ g (scaleSectionData t s) / t
  have hq : ∀ t ∈ I, HasDerivAt q 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.2
    have hc : Tendsto (fun a : ℝ ↦ a / t) (𝓝 t) (𝓝 1) := by
      simpa [ht0] using ((continuousAt_id : ContinuousAt (fun a : ℝ ↦ a) t).div_const t).tendsto
    have he : q =ᶠ[𝓝 t] (fun _ ↦ q t) := by
      filter_upwards [hc.eventually (hg _ ht.1),
        eventually_ne_nhds ht0] with a ha ha0
      dsimp [q]
      have heq : g (scaleSectionData a s) = a / t * g (scaleSectionData t s) := by
        simpa [div_mul_cancel₀ _ ht0] using ha
      rw [heq]
      field_simp
    exact (hasDerivAt_const t (q t)).congr_of_eventuallyEq he
  have he := hI.is_const_of_deriv_eq_zero hIc.isPreconnected
    (fun t ht ↦ (hq t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hq t ht).deriv) hrI h1
  have he' : g (scaleSectionData r s) / r = g s := by simpa [q] using he
  exact (div_eq_iff (ne_of_gt hr)).mp he' |>.trans (mul_comm _ _)

/-- Construct the normal energy root and smooth initial Hamilton momentum on
an open convex neighborhood of the base datum (`app:lem:common-hamilton-phase`).

The last assertion is degree-one homogeneity whenever both canonical data lie
in this local chart. The convex chart is radially truncated: no global conic
extension of `H.h` is assumed. These are precisely the initial-data inputs of
`exists_localHamiltonFlow` in `HamiltonPhase.LocalFlow`. -/
theorem exists_transverseSectionData [CompleteSpace U]
    (H : HomogeneousSymbol E) (hH : ContDiffOn ℝ ∞ H.h H.domain)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ‖ν‖ = 1)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ H.domain)
    (henergy : H.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ (P : Set (InitialData U)) (g : InitialData U → ℝ),
      IsOpen P ∧ Convex ℝ P ∧ s₀ ∈ P ∧ g s₀ = τ₀ ∧
      ContDiffOn ℝ ∞ g P ∧ ContDiffOn ℝ ∞ (sectionRootMomentum j ν g) P ∧
      (∀ s ∈ P,
        (j s.1, sectionRootMomentum j ν g s) ∈ H.domain ∧
        H.h (j s.1, sectionRootMomentum j ν g s) = s.2.1 ∧
        ⟪ν, sectionRootMomentum j ν g s⟫_ℝ = g s ∧
        ∀ v : U, ⟪sectionRootMomentum j ν g s, j v⟫_ℝ = ⟪s.2.2, v⟫_ℝ) ∧
      (∀ s ∈ P, ∀ r : ℝ, 0 < r → scaleSectionData r s ∈ P →
        g (scaleSectionData r s) = r * g s ∧
        sectionRootMomentum j ν g (scaleSectionData r s) =
          r • sectionRootMomentum j ν g s) := by
  let f := sectionEnergyEquation H j ν
  let S := transverseSectionState j ν ⁻¹' H.domain
  have hS : IsOpen S := H.isOpen_domain.preimage
    (contDiff_transverseSectionState j ν).continuous
  have hf : ContDiffOn ℝ ∞ f S :=
    (hH.comp (contDiff_transverseSectionState j ν).contDiffOn
      (fun _ hw ↦ hw)).sub contDiff_fst.snd.fst.contDiffOn
  have hz : f (s₀, τ₀) = 0 := sub_eq_zero.mpr henergy
  have hd : CharacteristicRoot.scalarDerivative f (s₀, τ₀) ≠ 0 := by
    rw [scalarDerivative_sectionEnergyEquation H j ν hbase]
    exact htrans
  let hf₀ := hf.contDiffAt (hS.mem_nhds hbase)
  let g := CharacteristicRoot.localRoot hf₀ hd
  obtain ⟨P₀, V, c, hP₀, hsP₀, hV, _, _, hg, hgraph, huniq⟩ :=
    CharacteristicRoot.exists_localRoot_patch hS hf hbase hz hd
  obtain ⟨ε, hε, hεP⟩ := Metric.isOpen_iff.mp hP₀ s₀ hsP₀
  let P := ball s₀ ε
  have hPg : ContDiffOn ℝ ∞ g P := hg.mono hεP
  have hlocal (s : InitialData U) (hs : s ∈ P) :
      ∀ᶠ r : ℝ in 𝓝 1, g (scaleSectionData r s) = r * g s := by
    have hs₀ := hεP hs
    have hscale : ContinuousAt (fun r : ℝ ↦ scaleSectionData r s) 1 :=
      continuousAt_const.prodMk (continuousAt_id.smul continuousAt_const)
    have hsp : ∀ᶠ r : ℝ in 𝓝 1, scaleSectionData r s ∈ P₀ := by
      apply hscale.preimage_mem_nhds
      simpa using hP₀.mem_nhds hs₀
    have htv : ∀ᶠ r : ℝ in 𝓝 1, r * g s ∈ V := by
      apply (continuousAt_id.mul continuousAt_const).preimage_mem_nhds
      simpa using hV.mem_nhds (hgraph s hs₀).1
    have hhom := H.homogeneous _ (hgraph s hs₀).2.1
    filter_upwards [hsp, htv, hhom] with r hrP hrV hrH
    apply (huniq _ hrP _ hrV).mp
    change H.h (transverseSectionState j ν (scaleSectionData r s, r * g s)) -
      r * s.2.1 = 0
    have hstate : transverseSectionState j ν (scaleSectionData r s, r * g s) =
        ((transverseSectionState j ν (s, g s)).1,
          r • (transverseSectionState j ν (s, g s)).2) := by
      simp [transverseSectionState, scaleSectionData, smul_add, mul_smul]
    rw [hstate, hrH]
    have he : H.h (transverseSectionState j ν (s, g s)) = s.2.1 :=
      sub_eq_zero.mp (hgraph s hs₀).2.2.1
    rw [he, sub_self]
  refine ⟨P, g, isOpen_ball, convex_ball s₀ ε, mem_ball_self hε,
    CharacteristicRoot.localRoot_base hf₀ hd, hPg, ?_, ?_, ?_⟩
  · exact (hPg.smul contDiffOn_const).add
      (j.contDiff.comp contDiff_snd.snd).contDiffOn
  · intro s hs
    have hgs := hgraph s (hεP hs)
    exact ⟨hgs.2.1, sub_eq_zero.mp hgs.2.2.1,
      sectionRootMomentum_normal j ν hν horth g s,
      sectionRootMomentum_pairing j ν horth g s⟩
  · intro s hs r hr hrs
    have he := homogeneous_on_convex_of_eventually isOpen_ball (convex_ball s₀ ε)
      hlocal hs hr hrs
    refine ⟨he, ?_⟩
    simp only [sectionRootMomentum, he]
    simp [scaleSectionData, smul_add, mul_smul]

end JanetCartan.HamiltonPhase
