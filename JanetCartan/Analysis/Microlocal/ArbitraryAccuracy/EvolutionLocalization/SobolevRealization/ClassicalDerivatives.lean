module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Input
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.List.OfFn

/-!
# Coordinate derivatives of the actual classical jet norm

The scalar Fourier comparison needed in `app:ch_regular:eq:chain-tail`
uses bounded differentiation from order `m + 1` to order `m`. These are
actual test derivatives, with no weak-derivative or norm-comparison premise.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev RetardedSobolev.Spaces

set_option backward.isDefEq.respectTransparency false

variable {d : ℕ}

/-- An actual constant-direction derivative of a test field, for the scalar
Fourier comparison in `app:ch_regular:eq:chain-tail`. -/
def directionalTest (v : ℝ × (Fin d → ℝ)) : Test d →ₗ[ℂ] Test d where
  toFun f := ⟨fun x => fderiv ℝ f.val x v,
    (f.property.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    f.property.2.fderiv_apply ℝ v⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact congrArg (fun L : (ℝ × (Fin d → ℝ)) →L[ℝ] ℂ => L v)
      (fderiv_add (f.property.1.differentiable (by simp) x)
        (g.property.1.differentiable (by simp) x))
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (c • f.val) x v = c • fderiv ℝ f.val x v
    rw [fderiv_const_smul_field]
    rfl

private theorem directionalDeriv_comm {f : (ℝ × (Fin d → ℝ)) → ℂ}
    (hf : ContDiff ℝ ∞ f) (v w : ℝ × (Fin d → ℝ)) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) =
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y w) x v) := by
  funext x
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const v),
    fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simpa using (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) |>.eq w v

private theorem transverseDeriv_timeDeriv {f : (ℝ × (Fin d → ℝ)) → ℂ}
    (hf : ContDiff ℝ ∞ f) (v : Fin d → ℝ) :
    transverseDeriv v (timeDeriv f) = timeDeriv (transverseDeriv v f) := by
  have ht : ContDiff ℝ ∞ (timeDeriv f) := by
    rw [timeDeriv_eq_fderiv (hf.differentiable (by simp))]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hx : ContDiff ℝ ∞ (transverseDeriv v f) := by
    exact contDiff_transverseJet hf [v]
  rw [transverseDeriv_eq_fderiv v (ht.differentiable (by simp)),
    timeDeriv_eq_fderiv (hx.differentiable (by simp)),
    timeDeriv_eq_fderiv (hf.differentiable (by simp)),
    transverseDeriv_eq_fderiv v (hf.differentiable (by simp))]
  exact directionalDeriv_comm hf (1, 0) (0, v)

private theorem transverseJet_timeDeriv {f : (ℝ × (Fin d → ℝ)) → ℂ}
    (hf : ContDiff ℝ ∞ f) (vs : List (Fin d → ℝ)) :
    transverseJet vs (timeDeriv f) = timeDeriv (transverseJet vs f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [transverseJet, ih, transverseDeriv_timeDeriv (contDiff_transverseJet hf vs)]
    rfl

private theorem timeJet_timeDeriv (j : ℕ) (f : (ℝ × (Fin d → ℝ)) → ℂ) :
    timeJet j (timeDeriv f) = timeJet (j + 1) f := by
  funext x
  simp only [timeJet, timeDeriv, iteratedDeriv_succ']

private theorem transverseJet_append (vs ws : List (Fin d → ℝ))
    (f : (ℝ × (Fin d → ℝ)) → ℂ) :
    transverseJet (vs ++ ws) f = transverseJet vs (transverseJet ws f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append, transverseJet, ih]

/-- Reindex the same derivative at one higher budget, for the order-lowering
map consumed by the Fourier comparison in `app:ch_regular:eq:chain-tail`. -/
def raiseJetIndex {m : ℕ} (i : JetIndex d m) : JetIndex d (m + 1) :=
  ⟨⟨i.1.val, by omega⟩, i.2.1, ⟨i.2.2.val, by change i.2.2.val < m + 1 - i.1.val + 1; omega⟩⟩

/-- Reindex one more time derivative, retaining the transverse word
(`app:ch_regular:eq:chain-tail`). -/
def timeDerivativeIndex {m : ℕ} (i : JetIndex d m) : JetIndex d (m + 1) :=
  ⟨⟨i.1.val, by omega⟩, i.2.1, ⟨i.2.2.val + 1, by change i.2.2.val + 1 < m + 1 - i.1.val + 1; omega⟩⟩

/-- Reindex one more transverse derivative at the end of the ordered word
(`app:ch_regular:eq:chain-tail`). -/
def transverseDerivativeIndex {m : ℕ} (a : Fin d) (i : JetIndex d m) :
    JetIndex d (m + 1) :=
  ⟨⟨i.1.val + 1, by omega⟩, Fin.snoc i.2.1 a, ⟨i.2.2.val, by change i.2.2.val < m + 1 - (i.1.val + 1) + 1; omega⟩⟩

/-- Raising the derivative budget preserves the actual jet
(`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem jet_raiseJetIndex {m : ℕ} (i : JetIndex d m)
    (f : (ℝ × (Fin d → ℝ)) → ℂ) : jet (raiseJetIndex i) f = jet i f := rfl

/-- Time differentiation of a test field is one of its higher completed jets
(`app:ch_regular:eq:chain-tail`). -/
theorem jet_directionalTest_time {m : ℕ} (i : JetIndex d m) (f : Test d) :
    jet i (directionalTest (1, 0) f).val = jet (timeDerivativeIndex i) f.val := by
  have he : (directionalTest (1, 0) f).val = timeDeriv f.val :=
    (timeDeriv_eq_fderiv (f.property.1.differentiable (by simp))).symm
  funext p
  simp only [he, jet, transverseJet_timeDeriv f.property.1, timeJet_timeDeriv,
    timeDerivativeIndex]

/-- Transverse differentiation is exactly the appended higher jet, with its
ordered word retained (`app:ch_regular:eq:chain-tail`). -/
theorem jet_directionalTest_transverse {m : ℕ} (a : Fin d) (i : JetIndex d m) (f : Test d) :
    jet i (directionalTest (0, Pi.single a 1) f).val =
      jet (transverseDerivativeIndex a i) f.val := by
  have he : (directionalTest (0, Pi.single a 1) f).val = transverseDeriv (Pi.single a 1) f.val :=
    (transverseDeriv_eq_fderiv _ (f.property.1.differentiable (by simp))).symm
  have hw : List.ofFn (fun j => (Pi.single ((Fin.snoc (α := fun _ => Fin d) i.2.1 a) j) 1 : Fin d → ℝ)) =
      List.ofFn (fun j => (Pi.single (i.2.1 j) 1 : Fin d → ℝ)) ++ [Pi.single a 1] := by
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  funext p
  simp only [he, jet, transverseDerivativeIndex, hw, transverseJet_append,
    transverseJet]

/-- Coordinate differentiation has norm at most one from the classical
order-`m + 1` jet norm to order `m`, for `app:ch_regular:eq:chain-tail`. -/
theorem norm_jetMap_directionalTest_time_le (m : ℕ) (f : Test d) :
    ‖jetMap m volume (directionalTest (1, 0) f)‖ ≤ ‖jetMap (m + 1) volume f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have he : jetMap m volume (directionalTest (1, 0) f) i =
      jetMap (m + 1) volume f (timeDerivativeIndex i) := by
    apply Lp.ext
    filter_upwards [(jet_memLp volume i (directionalTest (1, 0) f)).coeFn_toLp,
      (jet_memLp volume (timeDerivativeIndex i) f).coeFn_toLp] with p hp hq
    simpa only [jetMap, LinearMap.coe_mk, AddHom.coe_mk] using hp.trans ((congrFun (jet_directionalTest_time i f) p).trans hq.symm)
  rw [he]
  exact norm_le_pi_norm _ _

/-- Each transverse coordinate derivative has the same lossless bound from
order `m + 1` to order `m` (`app:ch_regular:eq:chain-tail`). -/
theorem norm_jetMap_directionalTest_transverse_le (m : ℕ) (a : Fin d) (f : Test d) :
    ‖jetMap m volume (directionalTest (0, Pi.single a 1) f)‖ ≤
      ‖jetMap (m + 1) volume f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have he : jetMap m volume (directionalTest (0, Pi.single a 1) f) i =
      jetMap (m + 1) volume f (transverseDerivativeIndex a i) := by
    apply Lp.ext
    filter_upwards [(jet_memLp volume i (directionalTest (0, Pi.single a 1) f)).coeFn_toLp,
      (jet_memLp volume (transverseDerivativeIndex a i) f).coeFn_toLp] with p hp hq
    simpa only [jetMap, LinearMap.coe_mk, AddHom.coe_mk] using hp.trans ((congrFun (jet_directionalTest_transverse a i f) p).trans hq.symm)
  rw [he]
  exact norm_le_pi_norm _ _

/-- The fixed Cartesian coefficient cost of a direction; it is chosen before
any operator or datum in `app:ch_regular:eq:chain-tail`. -/
def directionCost (v : ℝ × (Fin d → ℝ)) : ℝ := |v.1| + ∑ a, |v.2 a|

/-- The coordinate cost is nonnegative (`app:ch_regular:eq:chain-tail`). -/
theorem directionCost_nonneg (v : ℝ × (Fin d → ℝ)) : 0 ≤ directionCost v := by
  exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- Decomposition of the actual directional derivative into time and spatial
coordinate derivatives (`app:ch_regular:eq:chain-tail`). -/
theorem directionalTest_eq_coordinates (v : ℝ × (Fin d → ℝ)) (f : Test d) :
    directionalTest v f = (v.1 : ℂ) • directionalTest (1, 0) f +
      ∑ a, (v.2 a : ℂ) • directionalTest (0, Pi.single a 1) f := by
  have hv : v = v.1 • (1, 0) +
      ∑ a, v.2 a • ((0, Pi.single a 1) : ℝ × (Fin d → ℝ)) := by
    ext b <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  apply Subtype.ext
  funext x
  change fderiv ℝ f.val x v = _
  conv_lhs => rw [hv, map_add, map_sum, map_smul]
  simp only [map_smul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum,
    Pi.add_apply, Pi.smul_apply, Finset.sum_apply, directionalTest,
    LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul, smul_eq_mul]

/-- Every fixed direction gives a quantitative order-lowering bound in the
actual jet norm (`app:ch_regular:eq:chain-tail`). -/
theorem norm_jetMap_directionalTest_le (m : ℕ) (v : ℝ × (Fin d → ℝ)) (f : Test d) :
    ‖jetMap m volume (directionalTest v f)‖ ≤
      directionCost v * ‖jetMap (m + 1) volume f‖ := by
  rw [directionalTest_eq_coordinates, map_add, map_smul, map_sum]
  calc
    _ ≤ ‖(v.1 : ℂ) • jetMap m volume (directionalTest (1, 0) f)‖ +
        ∑ a, ‖jetMap m volume ((v.2 a : ℂ) • directionalTest (0, Pi.single a 1) f)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = |v.1| * ‖jetMap m volume (directionalTest (1, 0) f)‖ +
        ∑ a, |v.2 a| * ‖jetMap m volume (directionalTest (0, Pi.single a 1) f)‖ := by
      simp only [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |v.1| * ‖jetMap (m + 1) volume f‖ +
        ∑ a, |v.2 a| * ‖jetMap (m + 1) volume f‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_jetMap_directionalTest_time_le m f)
        (abs_nonneg _)) (Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
          (norm_jetMap_directionalTest_transverse_le m a f) (abs_nonneg _)))
    _ = _ := by rw [directionCost, add_mul, Finset.sum_mul]

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
