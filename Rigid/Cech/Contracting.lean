import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Rigid.Cech.Coface

set_option linter.style.header false

/-!
# Contracting homotopies for augmented coface complexes

This file packages the elementary exactness argument used for restricted Čech complexes which
have a distinguished member containing the covered domain.  The geometric construction of the
homotopy is kept separate: once the two contracting identities are available, exactness of the
whole augmented alternating complex is formal.
-/

open CategoryTheory

universe u v

namespace Rigid.Cech

variable {R : Type u} [Ring R]

namespace CofaceModule.Augmented

variable {C : CofaceModule.{u, v} R} (A : C.Augmented)

/-- A contracting homotopy for an augmented coface complex, written elementwise.

`h₀` contracts cochain degree zero to the augmentation object, while `h (n + 1)` contracts
cochain degree `n + 1` to degree `n`.  The indexing agrees with the degrees of the augmented
complex: `h n` maps its term in degree `n + 1` to its term in degree `n`. -/
structure ContractingHomotopy where
  h₀ : C.X 0 →ₗ[R] A.augmentationObject
  h : ∀ n : ℕ, C.X (n + 1) →ₗ[R] C.X n
  h₀_augmentation (x : A.augmentationObject) :
    h₀ (A.ε.hom x) = x
  degree_zero (x : C.X 0) :
    A.ε.hom (h₀ x) + h 0 (C.differential 0 |>.hom x) = x
  degree_succ (n : ℕ) (x : C.X (n + 1)) :
    (C.differential n).hom (h n x) +
        h (n + 1) ((C.differential (n + 1)).hom x) = x

namespace ContractingHomotopy

/-- An augmented coface complex admitting a contracting homotopy is acyclic. -/
theorem acyclic (H : A.ContractingHomotopy) : A.complex.Acyclic := by
  intro n
  rcases n with _ | _ | n
  · rw [A.complex.exactAt_iff' 0 0 1 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ x : A.augmentationObject, A.ε.hom x = 0 →
      ∃ y : A.augmentationObject, 0 = x
    intro x hx
    refine ⟨0, ?_⟩
    have := H.h₀_augmentation x
    rw [hx, map_zero] at this
    exact this
  · rw [A.complex.exactAt_iff' 0 1 2 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ x : C.X 0, (C.differential 0).hom x = 0 →
      ∃ y : A.augmentationObject, A.ε.hom y = x
    intro x hx
    refine ⟨H.h₀ x, ?_⟩
    have h := H.degree_zero x
    rw [hx, map_zero] at h
    simpa using h
  · rw [A.complex.exactAt_iff' (n + 1) ((n + 1) + 1)
      (((n + 1) + 1) + 1) (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
      HomologicalComplex.shortComplexFunctor'_obj_g, CochainComplex.of_d]
    dsimp only [CofaceModule.Augmented.terms,
      CofaceModule.Augmented.differential]
    change ∀ x : C.X (n + 1),
      (C.differential (n + 1)).hom x = 0 →
        ∃ y : C.X n, (C.differential n).hom y = x
    intro x hx
    refine ⟨H.h n x, ?_⟩
    have h := H.degree_succ n x
    rw [hx, map_zero] at h
    simpa using h

end ContractingHomotopy

end CofaceModule.Augmented

end Rigid.Cech
