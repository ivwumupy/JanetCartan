module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothPairing

/-!
# Real smooth realization of the physical pair

The real test space is the preimage of the existing compact graph test space
under the fixed real/complex inclusion. Compression uses the existing literal
L² real compression. Smooth representatives intertwine with inclusion
pointwise, so the physical equation is unchanged (`real-sector-normalization`,
`sector-theorem-identity`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open FourierIntegral Realization
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Real compact smooth sources, using the preimage of the shared graph test
space (`sector-theorem-solution`). -/
def realSectorTestSpace (d q : ℕ) : Submodule ℝ (Euclidean (d+1) → EuclideanSpace ℝ (Fin q)) :=
  ((graphTestSpace (d+1) q).restrictScalars ℝ).comap
    (euclideanComplexInclusion.toLinearMap.compLeft (Euclidean (d+1)))

/-- Every real compact smooth function is an allowed source; no extra
regularity or support premise is hidden in the preimage definition
(`sector-theorem-solution`). -/
theorem mem_realSectorTestSpace {u : E → RF}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : u ∈ realSectorTestSpace d q := by
  change ContDiff ℝ ∞ (fun y ↦ euclideanComplexInclusion (u y)) ∧ _
  exact ⟨(euclideanComplexInclusion : RF →L[ℝ] F).contDiff.comp hu,
    hc.comp_left (map_zero euclideanComplexInclusion)⟩

/-- The literal pointwise inclusion of real tests into the shared complex
graph test space (`real-sector-normalization`). -/
def realSectorTestInclusion : realSectorTestSpace d q →ₗ[ℝ] graphTestSpace (d+1) q where
  toFun u := ⟨fun y ↦ euclideanComplexInclusion (u.val y), u.property⟩
  map_add' u v := by apply Subtype.ext; funext y; exact map_add _ _ _
  map_smul' c u := by
    apply Subtype.ext
    funext y
    change euclideanComplexInclusion (c • u.val y) = c • euclideanComplexInclusion (u.val y)
    exact map_smul euclideanComplexInclusion c (u.val y)

/-- The genuine real Lebesgue L² class of a real test
(`sector-theorem-solution`). -/
def realSectorTestToLp : realSectorTestSpace d q →ₗ[ℝ]
    Lp RF 2 (volume : Measure E) :=
  (l2RealPart volume).toLinearMap.comp
    ((graphTestToLp.restrictScalars ℝ).comp realSectorTestInclusion)

/-- The constructed real class agrees with the original function, without a
change of measure or Sobolev model (`sector-theorem-solution`). -/
theorem realSectorTestToLp_coeFn (u : realSectorTestSpace d q) :
    realSectorTestToLp u =ᵐ[volume] u.val := by
  filter_upwards [euclideanRealPart.coeFn_compLpL
    (graphTestToLp (realSectorTestInclusion u)),
    (graphTest_memLp (realSectorTestInclusion u)).coeFn_toLp] with y hy hz
  change euclideanRealPart.compLpL 2 volume
    (graphTestToLp (realSectorTestInclusion u)) y = u.val y
  have hz' : graphTestToLp (realSectorTestInclusion u) y =
      (realSectorTestInclusion u).val y := hz
  rw [hy, hz']
  rfl

/-- The same real test class intertwines with the actual complex inclusion
(`real-sector-normalization`). -/
theorem inclusion_realSectorTestToLp (u : realSectorTestSpace d q) :
    l2ComplexInclusion volume (realSectorTestToLp u) =
      graphTestToLp (realSectorTestInclusion u) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL (realSectorTestToLp u),
    realSectorTestToLp_coeFn u, (graphTest_memLp (realSectorTestInclusion u)).coeFn_toLp]
    with y hy hz hw
  exact hy.trans ((congrArg euclideanComplexInclusion hz).trans hw.symm)

/-- Construct a single real linear smooth realization of the literal
compression of the physical plus pair. Inclusion agrees pointwise with the
S+cSc realization on every real test (`real-sector-normalization`,
`sector-theorem-identity`). -/
theorem exists_smooth_real_physical_pair (T : H →L[ℂ] H)
    (P : graphTestSpace (d+1) q →ₗ[ℂ] (E → F))
    (hP : ∀ u, ContDiff ℝ ∞ (P u) ∧ P u =ᵐ[volume]
      physicalPairedSectorSum {()} (fun _ : Unit ↦ T) (graphTestToLp u)) :
    ∃ R : realSectorTestSpace d q →ₗ[ℝ] (E → RF), ∀ u,
      ContDiff ℝ ∞ (R u) ∧
      R u =ᵐ[volume] realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ T))
        (realSectorTestToLp u) ∧
      (fun y ↦ euclideanComplexInclusion (R u y)) = P (realSectorTestInclusion u) := by
  let R : realSectorTestSpace d q →ₗ[ℝ] (E → RF) :=
    (euclideanRealPart.toLinearMap.compLeft E).comp
      ((P.restrictScalars ℝ).comp realSectorTestInclusion)
  refine ⟨R, ?_⟩
  intro u
  have hr : ContDiff ℝ ∞ (R u) := by
    change ContDiff ℝ ∞ ((euclideanRealPart : F →L[ℝ] RF) ∘ P (realSectorTestInclusion u))
    exact euclideanRealPart.contDiff.comp (hP _).1
  have he : R u =ᵐ[volume]
      realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) (realSectorTestToLp u) := by
    have hi := inclusion_realSectorTestToLp u
    filter_upwards [(hP (realSectorTestInclusion u)).2,
      euclideanRealPart.coeFn_compLpL
        (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)
          (l2ComplexInclusion volume (realSectorTestToLp u)))] with y hy hz
    change euclideanRealPart (P (realSectorTestInclusion u) y) =
      euclideanRealPart.compLpL 2 volume
        (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)
          (l2ComplexInclusion volume (realSectorTestToLp u))) y
    rw [hz, hi, hy]
  refine ⟨hr, he, ?_⟩
  have hae : (fun y ↦ euclideanComplexInclusion (R u y)) =ᵐ[volume]
      P (realSectorTestInclusion u) := by
    have hid := inclusion_realCompression_physicalPairedSectorSum
      ({()} : Finset Unit) (fun _ : Unit ↦ T) (realSectorTestToLp u)
    rw [inclusion_realSectorTestToLp] at hid
    filter_upwards [he,
      euclideanComplexInclusion.coeFn_compLpL
        (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) (realSectorTestToLp u)),
      (hP (realSectorTestInclusion u)).2] with y hy hz hw
    rw [hy, ← hz]
    exact (congrArg (fun v : H ↦ v y) hid).trans hw.symm
  funext y
  exact Measure.eqOn_open_of_ae_eq
    (f := fun y ↦ euclideanComplexInclusion (R u y))
    (by simpa only [Measure.restrict_univ] using hae)
    isOpen_univ (euclideanComplexInclusion.continuous.comp hr.continuous).continuousOn
    (hP _).1.continuous.continuousOn (mem_univ y)

end JanetCartan.RegularSector.FiniteAssembly
