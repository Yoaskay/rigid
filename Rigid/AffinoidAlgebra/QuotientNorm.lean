import Mathlib.Analysis.Normed.Group.Quotient

set_option linter.style.header false

/-!
# Quotient norms

This file expresses that the norm on the target of a map is the quotient norm. The definition
records both surjectivity and the infimum formula on every fiber.
-/

universe v w

namespace Rigid

section QuotientNorm

variable {B : Type v} [SeminormedAddCommGroup B]
variable {C : Type w} [SeminormedAddCommGroup C]

/-- A map is a quotient-norm presentation when it is surjective and the norm of every target
element is the infimum of the norms of all its preimages. -/
def IsQuotientNorm (f : B → C) : Prop :=
  Function.Surjective f ∧
    ∀ y : C, ‖y‖ = sInf ((fun x : B ↦ ‖x‖) '' {x | f x = y})

namespace IsQuotientNorm

variable {f : B → C}

/-- A quotient-norm presentation is surjective. -/
theorem surjective (hf : IsQuotientNorm f) : Function.Surjective f :=
  hf.1

/-- The target norm is the infimum of the source norms in each fiber. -/
theorem norm_eq_sInf_fiber (hf : IsQuotientNorm f) (y : C) :
    ‖y‖ = sInf ((fun x : B ↦ ‖x‖) '' {x | f x = y}) :=
  hf.2 y

/-- A quotient-norm presentation is norm-nonincreasing. -/
theorem norm_le (hf : IsQuotientNorm f) (x : B) : ‖f x‖ ≤ ‖x‖ := by
  rw [hf.norm_eq_sInf_fiber]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨y, -, rfl⟩
    exact norm_nonneg y
  · exact ⟨x, rfl, rfl⟩

/-- Every target element has lifts with norm arbitrarily close to its quotient norm. -/
theorem exists_preimage_norm_lt (hf : IsQuotientNorm f) {ε : ℝ} (hε : 0 < ε) (y : C) :
    ∃ x : B, f x = y ∧ ‖x‖ < ‖y‖ + ε := by
  obtain ⟨x, hx⟩ := hf.surjective y
  have hne : ((fun x : B ↦ ‖x‖) '' {x | f x = y}).Nonempty :=
    ⟨‖x‖, x, hx, rfl⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne hε
  rw [← hf.norm_eq_sInf_fiber] at hlt
  exact ⟨x, hx, hlt⟩

end IsQuotientNorm

end QuotientNorm

end Rigid
