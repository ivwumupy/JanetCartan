module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.LocalizedData

/-!
# Exact coefficients after localization

Localization preserves the literal coefficients of `app:ch_osc:prop:osc-normal`,
including parameter derivatives at the endpoints of the closed interval.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
local notation "E" => Euclidean n
local instance coefficientTransferMatrixTopology (r : ℕ) :
    TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The actual transport flux is globally smooth at each admissible parameter,
by its compact support and local smoothness. This justifies evaluating its
matrix derivative entrywise in `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.normalTransportFlux_contDiff_global
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (k : Fin n) :
    ContDiff ℝ ∞ (fun q : E × (E × E) ↦ F.normalTransportFlux ε k q.1 q.2.1 q.2.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q ∈ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)
  · exact (F.normalTransportFlux_contDiffOn_spatial hε k).contDiffAt
      ((G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)).mem_nhds
        ⟨G.X₀_subset hq.1, G.X₀_subset hq.2.1, G.D₀_subset hq.2.2⟩)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (F.normalTransportFlux_eventuallyEq_zero hε k hq)

/-- The compact scalar calculus uses exactly the original matrix transport
coefficient, not a new coefficient depending on the auxiliary extensions
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.localizedTransportEntry_eq
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {a : ℝ → E → E → Fin r → ℂ}
    (ha : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ a p.1 p.2.1 p.2.2 i))
    (hea : ∀ s ∈ Icc 0 G.ε₀, ∀ x u, a s x u = F.amplitude s x u)
    {w : (E × E) → E → E}
    (hew : ∀ x y u, x ∈ G.X₀ → y ∈ G.X₀ → u ∈ G.D₀ →
      w (x, y) u = F.transportVelocity ε x y u)
    (k : Option (Fin n)) (x y u : E) (i j : Fin r) :
    compactTransportEntry (fun s z v ↦ a s z.1 v i * star (a s z.2 v j)) w ε k (x, y) u =
      F.extendedTransportCoefficient ε k (x, (y, u)) i j := by
  let A := fun s v ↦ a s x v i * star (a s y v j)
  let ev := (matrixEntryEvaluation i j).restrictScalars ℝ
  have hA s (hs : s ∈ Icc 0 G.ε₀) v :
      A s v = ev (normalAmplitude (F.amplitude s) x y v) := by
    dsimp only [A]
    rw [hea s hs x v, hea s hs y v]
    rfl
  have hflux (l : Fin n) :
      (fun v ↦ (w (x, y) v l : ℂ) * A ε v) =
        fun v ↦ ev (F.normalTransportFlux ε l x y v) := by
    funext v
    rw [hA ε hε v]
    by_cases hv : (x, (y, v)) ∈ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)
    · rw [hew x y v hv.1 hv.2.1 hv.2.2]
      rfl
    · simp [normalTransportFlux, F.normalAmplitude_eq_zero_off_support hε hv]
  have hdA : deriv (fun s ↦ A s u) ε =
      ev (deriv (fun s ↦ normalAmplitude (F.amplitude s) x y u) ε) := by
    by_cases hq : (x, (y, u)) ∈ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)
    · have hd := ((F.normalAmplitude_contDiffOn_joint.contDiffAt
          ((F.isOpen_parameterDomain.prod
            (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
            ⟨F.parameter_subset hε, G.X₀_subset hq.1,
              G.X₀_subset hq.2.1, G.D₀_subset hq.2.2⟩)).comp ε
          (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
      have he := (ev.hasFDerivAt.comp_hasDerivAt ε hd.hasDerivAt).hasDerivWithinAt.congr
        (fun s hs ↦ hA s hs u) (hA ε hε u)
      have hd' : DifferentiableAt ℝ (fun s ↦ A s u) ε :=
        (((ha i).comp (contDiff_id.prodMk (contDiff_const (c := (x, u))))).mul
          (Complex.conjCLE.contDiff.comp
            ((ha j).comp (contDiff_id.prodMk (contDiff_const (c := (y, u))))))).differentiable (by simp) ε
      exact (uniqueDiffOn_Icc G.ε₀_pos ε hε).eq_deriv _ hd'.hasDerivAt.hasDerivWithinAt he
    · rw [F.normalAmplitude_parameterDeriv_eq_zero_off_support hε hq, map_zero]
      apply HasDerivWithinAt.deriv_eq_zero (s := Icc 0 G.ε₀) _
        (uniqueDiffOn_Icc G.ε₀_pos ε hε)
      apply (hasDerivWithinAt_const ε (Icc 0 G.ε₀) (0 : ℂ)).congr
      · intro s hs
        rw [hA s hs u, F.normalAmplitude_eq_zero_off_support hs hq, map_zero]
      · rw [hA ε hε u, F.normalAmplitude_eq_zero_off_support hε hq, map_zero]
  have hdflux (l : Fin n) :
      partialDeriv (fun v ↦ (w (x, y) v l : ℂ) * A ε v) u l =
        ev (partialDeriv (F.normalTransportFlux ε l x y) u l) := by
    rw [hflux l]
    have hd : DifferentiableAt ℝ (F.normalTransportFlux ε l x y) u :=
      ((F.normalTransportFlux_contDiff_global hε l).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).differentiable
        (by simp) u
    change fderiv ℝ (fun v ↦ ev (F.normalTransportFlux ε l x y v)) u
      (EuclideanSpace.single l 1) = _
    exact congrArg (fun T : E →L[ℝ] ℂ ↦ T (EuclideanSpace.single l 1))
      (ev.hasFDerivAt.comp u hd.hasFDerivAt).fderiv
  rw [F.extendedTransportCoefficient_eq hε]
  cases k with
  | some l =>
    change -((w (x, y) u l : ℂ) * A ε u) = _
    rw [congrFun (hflux l) u]
    rfl
  | none =>
    change deriv (fun s ↦ A s u) ε -
      ∑ l, partialDeriv (fun v ↦ (w (x, y) v l : ℂ) * A ε v) u l =
      ev (deriv (fun s ↦ normalAmplitude (F.amplitude s) x y u) ε -
        ∑ l, partialDeriv (F.normalTransportFlux ε l x y) u l)
    rw [hdA, map_sub, map_sum]
    simp_rw [hdflux]

end JanetCartan.NormalComparison
