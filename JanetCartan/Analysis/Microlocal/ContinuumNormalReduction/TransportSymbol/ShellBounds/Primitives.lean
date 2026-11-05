module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.Profiles

/-!
# Primitive mask and field jets before substitution

The consumer is the literal transport shell amplitude bound. In particular the
angular mask is composed with η/|η| and the high mask with |η| here, rather than
assuming their composed jets. Source:
`app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
open FourierIntegral.NormalOneHigh
variable {n N : ℕ}

/-- Fixed evaluation coordinates for all original primitives. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def shellEvaluationCoordinates (p : InputVariables n) :=
  ((p.1.1, p.1.2, (p.2.1, ‖p.2.2‖⁻¹ • p.2.2), ‖p.2.2‖),
    (p.1.1, p.2.1), (p.1.2, p.2.1), p.2.2)

/-- Angular and radial evaluation are smooth on a normalized shell. -/
theorem shellEvaluationCoordinates_contDiffAt {p : InputVariables n} (hp : p.2.2 ≠ 0) :
    ContDiffAt ℝ ∞ (@shellEvaluationCoordinates n) p := by
  have hr : ContDiffAt ℝ ∞ (fun p : InputVariables n ↦ ‖p.2.2‖) p :=
    contDiffAt_snd.snd.norm ℝ hp
  have hd := (hr.inv (norm_ne_zero_iff.mpr hp)).smul contDiffAt_snd.snd
  exact (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk
    ((contDiffAt_snd.fst.prodMk hd).prodMk hr))).prodMk
    ((contDiffAt_fst.fst.prodMk contDiffAt_snd.fst).prodMk
      ((contDiffAt_fst.snd.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd))

/-- Jets of the original masks and geometric fields in their own variables,
plus the absolute Jacobian. These are the precise primitive inputs to the
shell theorem; buffered interpolation supplies each profile from low/high
primitive norms. Source: `app:ch_background:eq:bg-mixed-input`. -/
structure PrimitiveShellProfiles (s : ℕ) (H M : ℝ) (a : Coefficients n N)
    (J : InputVariables n → ℝ) (p : InputVariables n) : Prop where
  leftMeasurement : ShellJetProfile s H M a.measurement p.1.1
  rightMeasurement : ShellJetProfile s H M a.measurement p.1.2
  angular : ShellJetProfile s H M a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2)
  high : ShellJetProfile s H M a.high ‖p.2.2‖
  jacobian : ShellJetProfile s H M J p
  leftNormal : ShellJetProfile s H M a.normal (p.1.1, p.2.1)
  rightNormal : ShellJetProfile s H M a.normal (p.1.2, p.2.1)
  leftReduced : ShellJetProfile s H M a.reduced (p.1.1, p.2.1)
  rightReduced : ShellJetProfile s H M a.reduced (p.1.2, p.2.1)

/-- Primitive profiles give the joint evaluation-array profile on a fixed
compact normalized shell. All nonlinear mask compositions are proved here.
No product of high norms occurs. Source:
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem exists_shellPrimitiveValues_profile (s : ℕ) (hs : 2 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    {P : Set (InputVariables n)} (hP : IsCompact P)
    (hη : ∀ p ∈ P, p.2.2 ≠ 0) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ) (H : ℝ),
      1 ≤ H → ∀ p ∈ P, PrimitiveShellProfiles s H M a J p →
      ShellJetProfile s H C (shellPrimitiveValues a J) p := by
  obtain ⟨R, hR, hcoord⟩ := exists_fixedShellJetProfile hP
    (fun p hp ↦ shellEvaluationCoordinates_contDiffAt (hη p hp)) s hs
  let D := M + ∑ i ∈ Finset.range (s + 1), compositionBudget (fun _ ↦ M) (fun _ ↦ R) i
  have hMD : M ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg
    (fun i _ ↦ compositionBudget_nonneg (fun _ ↦ hM) (fun _ ↦ hR.le) i))
  let B := D + R
  have hB : 0 < B := by dsimp [B]; linarith
  have hDB : D ≤ B := le_add_of_nonneg_right hR.le
  have hRB : R ≤ B := le_add_of_nonneg_left (hM.trans hMD)
  refine ⟨10 * B, mul_pos (by norm_num) hB, ?_⟩
  intro a J H hH p hp h
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hc := hcoord H hH p hp
  have hm1 := (h.leftMeasurement.comp (f := fun q : InputVariables n ↦ q.1.1) (x := p) hc.fst.fst hM hR.le hHpos).mono hDB hHpos.le
  have hm2 := (h.rightMeasurement.comp (f := fun q : InputVariables n ↦ q.1.2) (x := p) hc.fst.snd.fst hM hR.le hHpos).mono hDB hHpos.le
  have ha := (h.angular.comp (f := fun q : InputVariables n ↦ (q.2.1, ‖q.2.2‖⁻¹ • q.2.2)) (x := p) hc.fst.snd.snd.fst hM hR.le hHpos).mono hDB hHpos.le
  have hh := (h.high.comp (f := fun q : InputVariables n ↦ ‖q.2.2‖) (x := p) hc.fst.snd.snd.snd hM hR.le hHpos).mono hDB hHpos.le
  have hj := h.jacobian.mono (hMD.trans hDB) hHpos.le
  have he := hc.snd.snd.snd.mono hRB hHpos.le
  have hn1 := (h.leftNormal.comp (f := fun q : InputVariables n ↦ (q.1.1, q.2.1)) (x := p) hc.snd.fst hM hR.le hHpos).mono hDB hHpos.le
  have hn2 := (h.rightNormal.comp (f := fun q : InputVariables n ↦ (q.1.2, q.2.1)) (x := p) hc.snd.snd.fst hM hR.le hHpos).mono hDB hHpos.le
  have hq1 := (h.leftReduced.comp (f := fun q : InputVariables n ↦ (q.1.1, q.2.1)) (x := p) hc.snd.fst hM hR.le hHpos).mono hDB hHpos.le
  have hq2 := (h.rightReduced.comp (f := fun q : InputVariables n ↦ (q.1.2, q.2.1)) (x := p) hc.snd.snd.fst hM hR.le hHpos).mono hDB hHpos.le
  have hscalar := hm1.prod (hm2.prod (ha.prod (hh.prod hj hB.le hB.le hHpos.le)
    hB.le (by positivity) hHpos.le) hB.le (by positivity) hHpos.le)
    hB.le (by positivity) hHpos.le
  have hvector := he.prod (hn1.prod (hn2.prod (hq1.prod hq2 hB.le hB.le hHpos.le)
    hB.le (by positivity) hHpos.le) hB.le (by positivity) hHpos.le)
    hB.le (by positivity) hHpos.le
  convert hscalar.prod hvector (by positivity) (by positivity) hHpos.le using 1 <;>
    first | rfl | ring

/-- Adjoining the unchanged positions and spectator to the genuine inverse
costs only fixed constants. The inverse-jet producer need only bound u itself.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_inverseCoordinates_profile (s : ℕ) (hs : 2 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    {Q : Set (Variables n × Euclidean 2)} (hQ : IsCompact Q) :
    ∃ C > 0, ∀ (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (H : ℝ),
      1 ≤ H → ∀ p ∈ Q, ShellJetProfile s H M u p →
      ShellJetProfile s H C (inverseCoordinates u) p := by
  obtain ⟨R, hR, hid⟩ := exists_fixedShellJetProfile hQ
    (f := id) (fun _ _ ↦ contDiffAt_id) s hs
  let B := M + R
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨5 * B, mul_pos (by norm_num) hB, ?_⟩
  intro u H hH p hp hu
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hc := (hid H hH p hp).mono (show R ≤ B by dsimp [B]; linarith) hH0
  have hu' := hu.mono (show M ≤ B by dsimp [B]; linarith) hH0
  have hxy := hc.fst.fst.prod hc.fst.snd.fst hB.le hB.le hH0
  have hrest := (hu'.fst.prod hc.snd hB.le hB.le hH0).prod hu'.snd
    (by positivity) hB.le hH0
  convert hxy.prod hrest (by positivity) (by positivity) hH0 using 1 <;>
    first | rfl | ring

end JanetCartan.ContinuumNormalReduction.TransportSymbol
