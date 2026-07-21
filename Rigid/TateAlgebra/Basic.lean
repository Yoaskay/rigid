import Mathlib.RingTheory.MvPowerSeries.Restricted

set_option linter.style.header false

/-!
# The underlying ring of a Tate algebra

This file defines the strict Tate algebra as restricted multivariate power series of unit
polyradius. It provides constants, variables, coefficients, and extensionality. The Gauss norm is
defined in `Rigid.TateAlgebra.GaussNorm`.
-/

universe u v

namespace Rigid

variable (R : Type u) [NormedCommRing R] [IsUltrametricDist R]
variable (ι : Type v)

/-- The underlying ring of the strict Tate algebra in variables indexed by `ι`.

An element is a multivariate power series whose coefficients tend to zero along the cofinite
filter. -/
abbrev TateAlgebra :=
  ↥(MvPowerSeries.IsRestricted.subring (R := R) (fun _ : ι ↦ (1 : ℝ)))

namespace TateAlgebra

/-- The coefficient of a monomial in a Tate series. -/
def coeff (n : ι →₀ ℕ) (f : TateAlgebra R ι) : R :=
  MvPowerSeries.coeff n f.1

@[simp]
theorem coeff_apply (n : ι →₀ ℕ) (f : TateAlgebra R ι) :
    coeff R ι n f = MvPowerSeries.coeff n f.1 := rfl

/-- Two Tate series are equal when all their coefficients are equal. -/
@[ext]
theorem ext {f g : TateAlgebra R ι} (h : ∀ n, coeff R ι n f = coeff R ι n g) : f = g := by
  apply Subtype.ext
  exact MvPowerSeries.ext h

/-- The constant-series embedding into the Tate algebra. -/
noncomputable def C : R →+* TateAlgebra R ι :=
  (MvPowerSeries.C : R →+* MvPowerSeries ι R).codRestrict
    (MvPowerSeries.IsRestricted.subring (fun _ : ι ↦ (1 : ℝ)))
    fun a ↦ MvPowerSeries.isRestricted_C (fun _ : ι ↦ (1 : ℝ)) a

@[simp]
theorem coe_C (a : R) :
    (C R ι a : MvPowerSeries ι R) = MvPowerSeries.C a := rfl

@[simp]
theorem coeff_C [DecidableEq ι] (n : ι →₀ ℕ) (a : R) :
    coeff R ι n (C R ι a) = if n = 0 then a else 0 :=
  MvPowerSeries.coeff_C n a

@[simp]
theorem coeff_zero_C (a : R) : coeff R ι 0 (C R ι a) = a :=
  MvPowerSeries.coeff_zero_C a

end TateAlgebra

noncomputable instance tateAlgebraAlgebra : Algebra R (TateAlgebra R ι) :=
  (TateAlgebra.C R ι).toAlgebra

@[simp]
theorem algebraMap_apply (a : R) :
    algebraMap R (TateAlgebra R ι) a = TateAlgebra.C R ι a := rfl

/-- The coordinate corresponding to a variable of the Tate algebra. -/
noncomputable def tateVariable (i : ι) : TateAlgebra R ι := by
  refine ⟨MvPowerSeries.X i, ?_⟩
  rw [MvPowerSeries.X_def]
  exact MvPowerSeries.isRestricted_monomial (fun _ : ι ↦ (1 : ℝ)) _ _

@[simp]
theorem coe_tateVariable (i : ι) :
    (tateVariable R ι i : MvPowerSeries ι R) = MvPowerSeries.X i := rfl

@[simp]
theorem coeff_tateVariable [DecidableEq ι] (n : ι →₀ ℕ) (i : ι) :
    TateAlgebra.coeff R ι n (tateVariable R ι i) =
      if n = Finsupp.single i 1 then 1 else 0 :=
  MvPowerSeries.coeff_X n i

@[simp]
theorem coeff_single_tateVariable (i : ι) :
    TateAlgebra.coeff R ι (Finsupp.single i 1) (tateVariable R ι i) = 1 :=
  MvPowerSeries.coeff_index_single_self_X i

end Rigid
