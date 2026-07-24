import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option linter.style.header false

/-!
# The double-complex staircase argument

This file contains the algebraic core of the Čech comparison theorem.  We use a first-quadrant
double complex of vector spaces whose horizontal and vertical differentials commute.  If every
column is exact and every positive row is exact, then the bottom row is exact.

The proof is the finite staircase argument of BGR 8.1.4: move a vertical differential leftwards
using exactness of the positive rows, solve the resulting vertical cocycle in the first column,
and then unwind the staircase.
-/

open CategoryTheory

universe u v

namespace Rigid.Cech

variable (K : Type u) [Field K]

/-- A first-quadrant double complex of `K`-vector spaces, with commuting differentials.

The signs needed for a total complex are deliberately absent: the staircase comparison argument
uses only the two square-zero identities and commutation. -/
structure DoubleComplexGrid where
  X : ℕ → ℕ → ModuleCat.{v} K
  horizontal (p q : ℕ) : X p q →ₗ[K] X (p + 1) q
  vertical (p q : ℕ) : X p q →ₗ[K] X p (q + 1)
  horizontal_horizontal (p q : ℕ) (x : X p q) :
    horizontal (p + 1) q (horizontal p q x) = 0
  vertical_vertical (p q : ℕ) (x : X p q) :
    vertical p (q + 1) (vertical p q x) = 0
  horizontal_vertical (p q : ℕ) (x : X p q) :
    horizontal p (q + 1) (vertical p q x) =
      vertical (p + 1) q (horizontal p q x)

namespace DoubleComplexGrid

variable {K} (D : DoubleComplexGrid.{u, v} K)

/-- Elementwise exactness of a horizontal row. -/
def RowExact (q : ℕ) : Prop :=
  Function.Injective (D.horizontal 0 q) ∧
    ∀ (p : ℕ) (x : D.X (p + 1) q),
      D.horizontal (p + 1) q x = 0 →
        ∃ y : D.X p q, D.horizontal p q y = x

/-- Elementwise exactness of a vertical column. -/
def ColumnExact (p : ℕ) : Prop :=
  Function.Injective (D.vertical p 0) ∧
    ∀ (q : ℕ) (x : D.X p (q + 1)),
      D.vertical p (q + 1) x = 0 →
        ∃ y : D.X p q, D.vertical p q y = x

/-- A horizontal row, regarded as a cochain complex. -/
noncomputable def row (q : ℕ) : CochainComplex (ModuleCat K) ℕ :=
  CochainComplex.of
    (fun p ↦ D.X p q)
    (fun p ↦ ModuleCat.ofHom (D.horizontal p q))
    (fun p ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact D.horizontal_horizontal p q)

/-- A vertical column, regarded as a cochain complex. -/
noncomputable def column (p : ℕ) : CochainComplex (ModuleCat K) ℕ :=
  CochainComplex.of
    (D.X p)
    (fun q ↦ ModuleCat.ofHom (D.vertical p q))
    (fun q ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact D.vertical_vertical p q)

/-- Elementwise row exactness is equivalent to acyclicity of the associated row complex. -/
theorem rowExact_iff_acyclic (q : ℕ) :
    D.RowExact q ↔ (D.row q).Acyclic := by
  constructor
  · rintro ⟨hinj, hexact⟩ n
    rcases n with _ | n
    · rw [(D.row q).exactAt_iff' 0 0 1 (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff]
      change
        ∀ x : D.X 0 q, D.horizontal 0 q x = 0 →
          ∃ y : D.X 0 q, 0 = x
      intro x hx
      exact ⟨0, (hinj (by simpa using hx)).symm⟩
    · rw [(D.row q).exactAt_iff' n (n + 1) ((n + 1) + 1) (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff]
      simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', row,
        CochainComplex.of_d]
      intro x hx
      exact hexact n x hx
  · intro h
    constructor
    · intro x y hxy
      have hzero : D.horizontal 0 q (x - y) = 0 := by
        simpa only [map_sub, sub_eq_zero] using hxy
      have h0 := h 0
      rw [(D.row q).exactAt_iff' 0 0 1 (by simp) (by simp)] at h0
      rw [ShortComplex.moduleCat_exact_iff] at h0
      change
        ∀ z : D.X 0 q, D.horizontal 0 q z = 0 →
          ∃ w : D.X 0 q, 0 = z at h0
      obtain ⟨_, hz⟩ := h0 (x - y) hzero
      exact sub_eq_zero.mp hz.symm
    · intro p x hx
      have hp := h (p + 1)
      rw [(D.row q).exactAt_iff' p (p + 1) ((p + 1) + 1) (by simp) (by simp)] at hp
      rw [ShortComplex.moduleCat_exact_iff] at hp
      simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', row,
        CochainComplex.of_d] at hp
      have hp' :
          ∀ z : D.X (p + 1) q, D.horizontal (p + 1) q z = 0 →
            ∃ w : D.X p q, D.horizontal p q w = z := by
        intro z hz
        exact hp z hz
      exact hp' x hx

/-- Elementwise column exactness is equivalent to acyclicity of the associated column complex. -/
theorem columnExact_iff_acyclic (p : ℕ) :
    D.ColumnExact p ↔ (D.column p).Acyclic := by
  let T : DoubleComplexGrid K :=
    { X := fun q _ ↦ D.X p q
      horizontal := fun q _ ↦ D.vertical p q
      vertical := fun _ _ ↦ 0
      horizontal_horizontal := fun q _ ↦ D.vertical_vertical p q
      vertical_vertical := by simp
      horizontal_vertical := by simp }
  change T.RowExact 0 ↔ (T.row 0).Acyclic
  exact T.rowExact_iff_acyclic 0

/-- A finite left-moving staircase beginning with a horizontal and vertical cocycle.

For `z : X (p+1) q`, its head is a horizontal preimage in `X p q`; successive heads are
horizontal preimages of the vertical differentials of their predecessors. -/
inductive Staircase : ∀ (p q : ℕ), D.X (p + 1) q → Type (max u v)
  | base {q : ℕ} {z : D.X 1 q}
      (a : D.X 0 q)
      (horizontal_a : D.horizontal 0 q a = z)
      (vertical_a : D.vertical 0 q a = 0) :
      Staircase 0 q z
  | step {p q : ℕ} {z : D.X (p + 2) q}
      (a : D.X (p + 1) q)
      (horizontal_a : D.horizontal (p + 1) q a = z)
      (tail : Staircase p (q + 1) (D.vertical (p + 1) q a)) :
      Staircase (p + 1) q z

/-- Exact rows construct a staircase from any simultaneous horizontal and vertical cocycle. -/
theorem exists_staircase_positive
    (hrow : ∀ q, D.RowExact (q + 1))
    (p q : ℕ) (z : D.X (p + 1) (q + 1))
    (hz_horizontal : D.horizontal (p + 1) (q + 1) z = 0)
    (hz_vertical : D.vertical (p + 1) (q + 1) z = 0) :
    Nonempty (D.Staircase p (q + 1) z) := by
  induction p generalizing q with
  | zero =>
      obtain ⟨a, ha⟩ := (hrow q).2 0 z hz_horizontal
      have hva_horizontal :
          D.horizontal 0 (q + 2) (D.vertical 0 (q + 1) a) = 0 := by
        rw [D.horizontal_vertical, ha, hz_vertical]
      have hva : D.vertical 0 (q + 1) a = 0 :=
        (hrow (q + 1)).1 (by simpa only [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm, map_zero] using hva_horizontal)
      exact ⟨.base a ha hva⟩
  | succ p ih =>
      obtain ⟨a, ha⟩ := (hrow q).2 (p + 1) z hz_horizontal
      have hva_horizontal :
          D.horizontal (p + 1) (q + 2)
              (D.vertical (p + 1) (q + 1) a) = 0 := by
        rw [D.horizontal_vertical, ha, hz_vertical]
      have hva_vertical :
          D.vertical (p + 1) (q + 2)
              (D.vertical (p + 1) (q + 1) a) = 0 :=
        D.vertical_vertical (p + 1) (q + 1) a
      obtain ⟨tail⟩ :=
        ih (q + 1) (D.vertical (p + 1) (q + 1) a)
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hva_horizontal)
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hva_vertical)
      exact ⟨.step a ha tail⟩

/-- Unwind a staircase one row down using exactness of the columns. -/
theorem Staircase.unwind
    (hcolumn : ∀ p, D.ColumnExact p)
    {p q : ℕ} {z : D.X (p + 1) (q + 1)}
    (s : D.Staircase p (q + 1) z) :
    ∃ w : D.X p q,
      D.horizontal p (q + 1) (D.vertical p q w) = z :=
  match p with
  | 0 => by
      cases s with
      | base a ha hva =>
          obtain ⟨w, hw⟩ := (hcolumn 0).2 q a hva
          exact ⟨w, by rw [hw, ha]⟩
  | p + 1 => by
      cases s with
      | step a ha tail =>
          obtain ⟨c, hc⟩ := Staircase.unwind hcolumn tail
          have hcycle :
              D.vertical (p + 1) (q + 1)
                  (a - D.horizontal p (q + 1) c) = 0 := by
            rw [map_sub, ← D.horizontal_vertical, hc, sub_self]
          obtain ⟨w, hw⟩ := (hcolumn (p + 1)).2 q _ hcycle
          refine ⟨w, ?_⟩
          rw [hw, map_sub, ha, D.horizontal_horizontal, sub_zero]
termination_by p

/-- **Double-complex staircase lemma.** If all columns and all positive rows of a
first-quadrant double complex of vector spaces are exact, then its bottom row is exact. -/
theorem rowExact_zero_of_columns_and_positive_rows
    (hcolumn : ∀ p, D.ColumnExact p)
    (hrow : ∀ q, D.RowExact (q + 1)) :
    D.RowExact 0 := by
  constructor
  · intro x y hxy
    have hhorizontal :
        D.horizontal 0 0 (x - y) = 0 := by
      simpa only [map_sub, sub_eq_zero] using hxy
    have hvertical_horizontal :
        D.horizontal 0 1 (D.vertical 0 0 (x - y)) = 0 := by
      rw [D.horizontal_vertical, hhorizontal, map_zero]
    have hvertical : D.vertical 0 0 (x - y) = 0 :=
      (hrow 0).1 (by simpa using hvertical_horizontal)
    have hzero : x - y = 0 := (hcolumn 0).1 (by simpa using hvertical)
    exact sub_eq_zero.mp hzero
  · intro p x hx
    have hz_horizontal :
        D.horizontal (p + 1) 1 (D.vertical (p + 1) 0 x) = 0 := by
      rw [D.horizontal_vertical, hx, map_zero]
    have hz_vertical :
        D.vertical (p + 1) 1 (D.vertical (p + 1) 0 x) = 0 :=
      D.vertical_vertical (p + 1) 0 x
    obtain ⟨staircase⟩ :=
      D.exists_staircase_positive hrow p 0
        (D.vertical (p + 1) 0 x) hz_horizontal hz_vertical
    obtain ⟨w, hw⟩ := Staircase.unwind (D := D) hcolumn staircase
    have hcycle :
        D.vertical (p + 1) 0 (x - D.horizontal p 0 w) = 0 := by
      rw [map_sub, ← D.horizontal_vertical, hw, sub_self]
    have hzero : x - D.horizontal p 0 w = 0 :=
      (hcolumn (p + 1)).1 (by simpa using hcycle)
    exact ⟨w, (sub_eq_zero.mp hzero).symm⟩

/-- Acyclic columns and acyclic positive rows force the bottom row to be acyclic. -/
theorem row_zero_acyclic_of_columns_and_positive_rows
    (hcolumn : ∀ p, (D.column p).Acyclic)
    (hrow : ∀ q, (D.row (q + 1)).Acyclic) :
    (D.row 0).Acyclic := by
  rw [← D.rowExact_iff_acyclic]
  apply D.rowExact_zero_of_columns_and_positive_rows
  · intro p
    exact (D.columnExact_iff_acyclic p).2 (hcolumn p)
  · intro q
    exact (D.rowExact_iff_acyclic (q + 1)).2 (hrow q)

end DoubleComplexGrid

end Rigid.Cech
