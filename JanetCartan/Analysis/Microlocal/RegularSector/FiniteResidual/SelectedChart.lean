module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Collars
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.WeakDerivative
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.CommonOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.CommonWeakDerivative
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.SupportedIdentity
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.CommonIdentity

/-!
# The retained selected chart in the complete tested residual

The common physical mask identities are proved for the actual retained L²
operators. The separately chosen spatial collars give equal source and
algebraic symbols, including their full physical derivatives. The actual
output geometry supplies the retained box, time slab, time plateau and
smooth coefficient extensions.

The common frequency regularizations and both strong limits are constructed
for the retained supported phase. Compact smooth inputs have an actual weak
derivative for the same localized solver. Literal multiplication identifies
the smaller-output PDO and preserves the tested equation on its plateau.
The complete common-mask solver and all three residual terms are identified
with localization of the canonical operators, preserving `Op(α)-I`.
The original algebraic gain also supplies the common solver's weak derivative
directly, without another inverse estimate or smaller-mask symbol budget.
The supported-chart identity proves the complete tested equation for all L²
inputs. Its common-mask assembly uses the SAME retained solver, all three
residual terms and the original physical algebraic gain. For compact smooth
inputs it constructs the weak derivative and proves the a.e. equation on the
common measurement ball, preserving `Op(α)-I` explicitly. These deductions
consume the precise primitive construction outputs and four PDO budgets;
physical-coordinate finite summation and global sector estimates remain with
the regular-sector construction (`energy-complete-residual`).
-/
