module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.IntegratedChannels

/-!
# Smoothness and support of the actual transport channels

Regularity prerequisites for constructing the channels in
`app:ch_osc:prop:osc-normal`, derived from smooth amplitudes and velocity.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison
open CompactTransport AmplitudeBound
variable {n : ℕ}
local notation "E" => Euclidean n

/-- The scalar entries of the exact transport coefficients in
`app:ch_osc:prop:osc-normal`. `none` is the divergence coefficient. -/
def compactTransportEntry (A : ℝ → (E × E) → E → ℂ)
    (w : (E × E) → E → E) (s : ℝ) (k : Option (Fin n)) (z : E × E) (u : E) : ℂ :=
  match k with
  | none => transportCoefficient (fun v ↦ deriv (fun t ↦ A t z v) s)
      (fun j v ↦ (w z v j : ℂ) * A s z v) u
  | some j => -((w z u j : ℂ) * A s z u)

/-- Smoothness of the literal coefficient entries, with no derivative bounds
assumed (`app:ch_osc:prop:osc-normal`). -/
theorem contDiff_compactTransportEntry
    {A : ℝ → (E × E) → E → ℂ} {w : (E × E) → E → E}
    (hA : ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦ A p.1 p.2.1 p.2.2))
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) (s : ℝ) (k : Option (Fin n)) :
    ContDiff ℝ ∞ (Function.uncurry (compactTransportEntry A w s k)) := by
  have hAs : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A s p.1 p.2) :=
    hA.comp (contDiff_const.prodMk contDiff_id)
  have hB (j : Fin n) : ContDiff ℝ ∞
      (fun p : (E × E) × E ↦ (w p.1 p.2 j : ℂ) * A s p.1 p.2) :=
    (Complex.ofRealCLM.contDiff.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp hw)).mul hAs
  cases k with
  | some j => exact (hB j).neg
  | none =>
    apply ContDiff.sub
    · have ha' : ContDiff ℝ ∞
          (fun p : ((E × E) × E) × ℝ ↦ A p.2 p.1.1 p.1.2) :=
        hA.comp (contDiff_snd.prodMk contDiff_fst)
      exact (ha'.fderiv contDiff_const (by simp)).clm_apply contDiff_const
    · apply ContDiff.sum
      intro j _
      have hb' : ContDiff ℝ ∞
          (fun p : ((E × E) × E) × E ↦ (w p.1.1 p.2 j : ℂ) * A s p.1.1 p.2) :=
        (hB j).comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact (hb'.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

/-- Transport preserves both physical carriers and the compact input carrier
(`app:ch_osc:prop:osc-normal`). No property of the velocity outside the carrier
is required for this support assertion. -/
theorem compactTransportEntry_eq_zero_off_product
    {X V : Set E} (hV : IsClosed V) {A : ℝ → (E × E) → E → ℂ}
    (hs : ∀ t p, p ∉ (X ×ˢ X) ×ˢ V → A t p.1 p.2 = 0)
    (w : (E × E) → E → E) (s : ℝ) (k : Option (Fin n))
    (p : (E × E) × E) (hp : p ∉ (X ×ˢ X) ×ˢ V) :
    compactTransportEntry A w s k p.1 p.2 = 0 := by
  cases k with
  | some j => simp [compactTransportEntry, hs s p hp]
  | none =>
    by_cases hz : p.1 ∈ X ×ˢ X
    · exact transportCoefficient_eq_zero_off_carrier hV
        (fun t u hu ↦ hs t (p.1, u) (fun h ↦ hu h.2)) s (w p.1)
        (fun hu ↦ hp ⟨hz, hu⟩)
    · have he (t : ℝ) (u : E) : A t p.1 u = 0 :=
        hs t (p.1, u) (fun h ↦ hz h.1)
      simp [compactTransportEntry, transportCoefficient, he, partialDeriv]

/-- The mask channel associated with the coefficient index in
`app:ch_osc:prop:osc-normal`. Only the value and first derivatives occur. -/
def compactTransportMask (m : E → ℝ) (k : Option (Fin n)) (u : E) : ℂ :=
  match k with
  | none => (m u : ℂ)
  | some j => (partialDeriv m u j : ℝ)

/-- Smoothness of the first mask derivatives follows from local smoothness;
no higher derivative bound is used (`app:ch_osc:prop:osc-normal`). -/
theorem contDiffOn_compactTransportMask {D : Set E} (hD : IsOpen D)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m D) (k : Option (Fin n)) :
    ContDiffOn ℝ ∞ (compactTransportMask m k) D := by
  cases k with
  | none => exact Complex.ofRealCLM.contDiff.comp_contDiffOn hm
  | some j =>
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    exact (hm.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
end JanetCartan.NormalComparison
