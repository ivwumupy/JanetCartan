module

public import JanetCartan.Analysis.Operator.RetardedSobolev.MixedEnergy
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Classical test fields and their L² jets

The coordinates and derivative energies of `app:ch_osc:prop:osc-retarded-tube`.
All derivatives below are the actual classical derivatives, including order zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace JanetCartan.RetardedSobolev.Spaces

/-- Compactly supported smooth complex fields in the coordinates of
`app:ch_osc:setup:osc-retarded`. -/
def testSubmodule (d : ℕ) : Submodule ℂ ((ℝ × (Fin d → ℝ)) → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.const_smul c, hf.2.smul_left⟩

/-- Test fields for `app:ch_osc:prop:osc-retarded-tube`. -/
abbrev Test (d : ℕ) := testSubmodule d

/-- Ordered Cartesian transverse words and time orders of total order at most `m`
(`app:ch_osc:prop:osc-retarded-tube`). Repeated mixed partials are counted. -/
abbrev JetIndex (d m : ℕ) :=
  Σ k : Fin (m + 1), (Fin k.val → Fin d) × Fin (m - k.val + 1)

/-- The actual mixed derivative indexed by a word
(`app:ch_osc:prop:osc-retarded-tube`). The argument order matches `MixedEnergy`. -/
def jet {d m : ℕ} (i : JetIndex d m) (f : (ℝ × (Fin d → ℝ)) → ℂ)
    (p : (Fin d → ℝ) × ℝ) : ℂ :=
  timeJet i.2.2.val
    (transverseJet (List.ofFn (fun j ↦ Pi.single (i.2.1 j) 1)) f) (p.2, p.1)

private theorem transverseJet_add {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f g : ℝ × Y → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (vs : List Y) :
    transverseJet vs (f + g) = transverseJet vs f + transverseJet vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [transverseJet, ih]
    funext x
    exact congrArg (fun L : Y →L[ℝ] ℂ ↦ L v) (fderiv_add
      (((contDiff_transverseJet hf vs).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x.2)
      (((contDiff_transverseJet hg vs).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x.2))

private theorem transverseJet_smul {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (c : ℂ) (f : ℝ × Y → ℂ) (vs : List Y) :
    transverseJet vs (c • f) = c • transverseJet vs f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [transverseJet, ih]
    funext x
    change (fderiv ℝ (c • fun y ↦ transverseJet vs f (x.1, y)) x.2) v = _
    rw [fderiv_const_smul_field]
    rfl

/-- Linearity of classical mixed jets (`app:ch_osc:prop:osc-retarded-tube`). -/
def jetLinear {d m : ℕ} (i : JetIndex d m) :
    Test d →ₗ[ℂ] (((Fin d → ℝ) × ℝ) → ℂ) where
  toFun f := jet i f
  map_add' f g := by
    funext p
    simp only [jet, Submodule.coe_add, transverseJet_add f.property.1 g.property.1]
    apply iteratedDeriv_add
    · exact (((contDiff_transverseJet f.property.1 _).comp
        (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt
    · exact (((contDiff_transverseJet g.property.1 _).comp
        (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt
  map_smul' c f := by
    funext p
    simp [jet, transverseJet_smul, timeJet]

/-- Every classical jet is L² for locally finite measures
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem jet_memLp {d m : ℕ} (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] (i : JetIndex d m) (f : Test d) :
    MemLp (jet i f) 2 μ := by
  have hc := contDiff_timeJet (contDiff_transverseJet f.property.1
    (List.ofFn (fun j ↦ Pi.single (i.2.1 j) 1))) i.2.2.val
  have hs := hasCompactSupport_timeJet (contDiff_transverseJet f.property.1
    (List.ofFn (fun j ↦ Pi.single (i.2.1 j) 1)))
    (hasCompactSupport_transverseJet f.property.1 f.property.2 _) i.2.2.val
  exact (hc.continuous.comp continuous_swap).memLp_of_hasCompactSupport
    (hs.comp_homeomorph (Homeomorph.prodComm _ _))

/-- The finite vector of genuine L² derivatives
(`app:ch_osc:prop:osc-retarded-tube`), with the finite product norm. -/
def jetMap {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] : Test d →ₗ[ℂ] (JetIndex d m → Lp ℂ 2 μ) where
  toFun f i := (jet_memLp μ i f).toLp (jet i f)
  map_add' f g := by
    funext i
    have h := (jetLinear i).map_add f g
    change jet i ↑(f + g) = jet i ↑f + jet i ↑g at h
    change (jet_memLp μ i (f + g)).toLp _ = _
    simp only [h]
    exact MemLp.toLp_add (jet_memLp μ i f) (jet_memLp μ i g)
  map_smul' c f := by
    funext i
    have h := (jetLinear i).map_smul c f
    change jet i ↑(c • f) = c • jet i ↑f at h
    change (jet_memLp μ i (c • f)).toLp _ = _
    simp only [h]
    exact MemLp.toLp_const_smul c (jet_memLp μ i f)

end JanetCartan.RetardedSobolev.Spaces
