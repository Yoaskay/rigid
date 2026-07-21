import Rigid.TateAlgebra.Basic
import Mathlib.Topology.Order.LiminfLimsup

set_option linter.style.header false

/-!
# The Gauss norm on a Tate algebra

This file defines the Gauss norm as the supremum of the coefficient norms and establishes its
first order-theoretic properties. The normed-ring structure and multiplicativity are left to later
files.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v)

/-- The Gauss norm of a strict Tate series, defined as the supremum of its coefficient norms. -/
noncomputable def gaussNorm (f : TateAlgebra K ι) : ℝ :=
  sSup (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖)

noncomputable instance tateAlgebraNorm : Norm (TateAlgebra K ι) :=
  ⟨gaussNorm K ι⟩

/-- The coefficient norms of a Tate series tend to zero along the cofinite filter. -/
theorem tendsto_norm_coeff_zero (f : TateAlgebra K ι) :
    Tendsto (fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) cofinite (𝓝 0) := by
  have h := f.2
  change Tendsto
    (fun n : ι →₀ ℕ ↦
      ‖MvPowerSeries.coeff n f.1‖ * n.prod (fun _ e ↦ (1 : ℝ) ^ e))
    cofinite (𝓝 0) at h
  convert h using 1
  ext n
  simp [Finsupp.prod]

/-- The coefficient norms of a Tate series are bounded above. -/
theorem bddAbove_range_norm_coeff (f : TateAlgebra K ι) :
    BddAbove (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) :=
  (tendsto_norm_coeff_zero K ι f).bddAbove_range_of_cofinite

/-- Every coefficient norm is bounded by the Gauss norm. -/
theorem norm_coeff_le_gaussNorm (f : TateAlgebra K ι) (n : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff n f.1‖ ≤ gaussNorm K ι f :=
  le_csSup (bddAbove_range_norm_coeff K ι f) ⟨n, rfl⟩

/-- The Gauss norm is nonnegative. -/
theorem gaussNorm_nonneg (f : TateAlgebra K ι) : 0 ≤ gaussNorm K ι f :=
  (norm_nonneg (MvPowerSeries.coeff 0 f.1)).trans
    (norm_coeff_le_gaussNorm K ι f 0)

/-- The Gauss norm is the supremum norm on coefficients. -/
theorem norm_eq_sSup_coeff (f : TateAlgebra K ι) :
    ‖f‖ = sSup (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) := rfl

@[simp]
theorem gaussNorm_zero : gaussNorm K ι (0 : TateAlgebra K ι) = 0 := by
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    simp
  · exact gaussNorm_nonneg K ι 0

@[simp]
theorem norm_zero : ‖(0 : TateAlgebra K ι)‖ = 0 :=
  gaussNorm_zero K ι

@[simp]
theorem gaussNorm_C (a : K) : gaussNorm K ι (TateAlgebra.C K ι a) = ‖a‖ := by
  classical
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    rw [TateAlgebra.coe_C]
    dsimp only
    rw [MvPowerSeries.coeff_C]
    split_ifs <;> simp
  · simpa using norm_coeff_le_gaussNorm K ι (TateAlgebra.C K ι a) 0

@[simp]
theorem norm_C (a : K) : ‖TateAlgebra.C K ι a‖ = ‖a‖ :=
  gaussNorm_C K ι a

@[simp]
theorem gaussNorm_tateVariable (i : ι) : gaussNorm K ι (tateVariable K ι i) = 1 := by
  classical
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    rw [coe_tateVariable]
    dsimp only
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  · simpa using
      norm_coeff_le_gaussNorm K ι (tateVariable K ι i) (Finsupp.single i 1)

@[simp]
theorem norm_tateVariable (i : ι) : ‖tateVariable K ι i‖ = 1 :=
  gaussNorm_tateVariable K ι i

end Rigid
