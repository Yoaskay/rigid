import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

set_option linter.style.header false

/-!
# Alternating complexes from coface maps

The Čech complex only uses the coface maps of a cosimplicial object.  This file packages that
smaller interface, so a presheaf on rational subdomains does not have to be bundled as a full
functor out of the simplex category merely in order to form its Čech differential.
-/

open CategoryTheory
open CategoryTheory.Preadditive

open scoped BigOperators

universe u v

namespace Rigid.Cech

variable (R : Type u) [Ring R]

/-- A sequence of modules with coface maps satisfying the cosimplicial coface identity. -/
structure CofaceModule where
  X : ℕ → ModuleCat.{v} R
  δ (n : ℕ) (i : Fin (n + 2)) : X n ⟶ X (n + 1)
  δ_comp_δ (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    δ n i ≫ δ (n + 1) j.succ = δ n j ≫ δ (n + 1) i.castSucc

namespace CofaceModule

variable {R}

/-- The alternating sum of the coface maps. -/
def differential (C : CofaceModule R) (n : ℕ) : C.X n ⟶ C.X (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • C.δ n i

/-- The alternating coface differential squares to zero. -/
theorem differential_comp (C : CofaceModule R) (n : ℕ) :
    C.differential n ≫ C.differential (n + 1) = 0 := by
  simp only [differential, comp_sum, sum_comp]
  rw [Finset.sum_comm, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT]
      ring
    · have hle : (φ (i, j) hij).1 ≤ i := by
        simpa [S, φ] using! hij
      simpa only [φ, Fin.castSucc_castLT] using
        (C.δ_comp_δ n (φ (i, j) hij).1 i hle).symm

/-- The ordinary (unaugmented) alternating coface complex. -/
noncomputable def complex (C : CofaceModule R) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of C.X C.differential C.differential_comp

@[simp]
theorem complex_X (C : CofaceModule R) (n : ℕ) : C.complex.X n = C.X n :=
  rfl

/-- Coface data together with an augmentation. -/
structure Augmented (C : CofaceModule R) where
  augmentationObject : ModuleCat.{v} R
  ε : augmentationObject ⟶ C.X 0
  ε_comp : ε ≫ C.δ 0 0 = ε ≫ C.δ 0 1

namespace Augmented

/-- Terms of the augmented complex, with the augmentation placed in degree zero. -/
abbrev terms {C : CofaceModule R} (A : C.Augmented) : ℕ → ModuleCat.{v} R
  | 0 => A.augmentationObject
  | n + 1 => C.X n

/-- Differential of the augmented complex. -/
abbrev differential {C : CofaceModule R} (A : C.Augmented) :
    ∀ n, A.terms n ⟶ A.terms (n + 1)
  | 0 => A.ε
  | n + 1 => C.differential n

theorem differential_comp {C : CofaceModule R} (A : C.Augmented) (n : ℕ) :
    A.differential n ≫ A.differential (n + 1) = 0 := by
  cases n with
  | zero =>
      rw [differential, differential, CofaceModule.differential, Fin.sum_univ_two,
        Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul, one_zsmul]
      change A.ε ≫ (C.δ 0 0 + -C.δ 0 1) = 0
      rw [comp_add, comp_neg, A.ε_comp, add_neg_cancel]
  | succ n =>
      exact C.differential_comp n

/-- The augmented alternating coface complex. -/
noncomputable abbrev complex {C : CofaceModule R} (A : C.Augmented) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of A.terms A.differential A.differential_comp

@[simp]
theorem complex_X_zero {C : CofaceModule R} (A : C.Augmented) :
    A.complex.X 0 = A.augmentationObject :=
  rfl

@[simp]
theorem complex_X_succ {C : CofaceModule R} (A : C.Augmented) (n : ℕ) :
    A.complex.X (n + 1) = C.X n :=
  rfl

end Augmented

end CofaceModule

end Rigid.Cech
