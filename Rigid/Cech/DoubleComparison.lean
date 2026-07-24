import Rigid.Cech.Comparison
import Rigid.Cech.Double

set_option linter.style.header false

/-!
# Čech comparison through the fully augmented double complex

For two finite families with the same ambient domain, this file adjoins the common ambient
sections to the normalized double Čech complex.  The abstract staircase lemma then gives the
usual comparison principle: acyclicity of one cover and of all the restricted rows and columns
implies acyclicity of the other cover.
-/

open CategoryTheory

universe u v w

namespace Rigid.Cech

variable {K : Type u} [Field K]
variable {P : Presheaf.{u, v, w} K}

namespace Presheaf.Family

/-- The objects of the normalized double Čech complex, augmented in both directions. -/
noncomputable abbrev fullyAugmentedDoubleX (𝒰 𝒱 : P.Family) :
    ℕ → ℕ → ModuleCat K
  | p, 0 => 𝒰.normalizedAugmentedCofaceModule.terms p
  | p, q + 1 => (horizontalAugmentedCofaceModule 𝒰 𝒱 q).terms p

/-- Horizontal differential of the fully augmented double Čech complex. -/
noncomputable abbrev fullyAugmentedHorizontal (𝒰 𝒱 : P.Family) :
    ∀ p q, fullyAugmentedDoubleX 𝒰 𝒱 p q →ₗ[K]
      fullyAugmentedDoubleX 𝒰 𝒱 (p + 1) q
  | p, 0 => (𝒰.normalizedAugmentedCofaceModule.differential p).hom
  | p, q + 1 => (horizontalAugmentedCofaceModule 𝒰 𝒱 q).differential p |>.hom

/-- Vertical differential of the fully augmented double Čech complex.  The map at the common
corner is supplied explicitly, since the generic presheaf interface does not identify mutually
contained domain objects. -/
noncomputable abbrev fullyAugmentedVertical (𝒰 𝒱 : P.Family)
    (verticalCorner :
      P.sections 𝒰.ambient →ₗ[K] 𝒱.NormalizedCochains 0) :
    ∀ p q, fullyAugmentedDoubleX 𝒰 𝒱 p q →ₗ[K]
      fullyAugmentedDoubleX 𝒰 𝒱 p (q + 1)
  | 0, 0 => verticalCorner
  | 0, q + 1 => (𝒱.normalizedCofaceModule.differential q).hom
  | p + 1, 0 => verticalAugmentation 𝒰 𝒱 p
  | p + 1, q + 1 => (verticalCofaceModule 𝒰 𝒱 p).differential q |>.hom

/-- The fully augmented normalized double Čech complex as an abstract double-complex grid. -/
noncomputable abbrev fullyAugmentedDoubleGrid (𝒰 𝒱 : P.Family)
    (verticalCorner :
      P.sections 𝒰.ambient →ₗ[K] 𝒱.NormalizedCochains 0)
    (verticalCorner_comp :
      ModuleCat.ofHom verticalCorner ≫
          𝒱.normalizedCofaceModule.differential 0 = 0)
    (corner_comm :
      ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
          ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 0) =
        ModuleCat.ofHom verticalCorner ≫
          ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 0)) :
    DoubleComplexGrid K where
  X := fullyAugmentedDoubleX 𝒰 𝒱
  horizontal := fullyAugmentedHorizontal 𝒰 𝒱
  vertical := fullyAugmentedVertical 𝒰 𝒱 verticalCorner
  horizontal_horizontal := by
    intro p q x
    cases q with
    | zero =>
        cases p with
        | zero =>
            exact congrArg
              (fun φ ↦ φ.hom x)
              (𝒰.normalizedAugmentedCofaceModule.differential_comp 0)
        | succ p =>
            exact congrArg
              (fun φ ↦ φ.hom x)
              (𝒰.normalizedCofaceModule.differential_comp p)
    | succ q =>
        cases p with
        | zero =>
            exact congrArg
              (fun φ ↦ φ.hom x)
              ((horizontalAugmentedCofaceModule 𝒰 𝒱 q).differential_comp 0)
        | succ p =>
            exact congrArg
              (fun φ ↦ φ.hom x)
              ((horizontalCofaceModule 𝒰 𝒱 q).differential_comp p)
  vertical_vertical := by
    intro p q x
    cases q with
    | zero =>
        cases p with
        | zero =>
            exact congrArg (fun φ ↦ φ.hom x) verticalCorner_comp
        | succ p =>
            exact congrArg
              (fun φ ↦ φ.hom x)
              ((verticalAugmentedCofaceModule 𝒰 𝒱 p).differential_comp 0)
    | succ q =>
        cases p with
        | zero =>
            exact congrArg
              (fun φ ↦ φ.hom x)
              (𝒱.normalizedCofaceModule.differential_comp q)
        | succ p =>
            exact congrArg
              (fun φ ↦ φ.hom x)
              ((verticalCofaceModule 𝒰 𝒱 p).differential_comp q)
  horizontal_vertical := by
    intro p q x
    cases p with
    | zero =>
        cases q with
        | zero =>
            change
              (ModuleCat.ofHom verticalCorner ≫
                  ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 0)).hom x =
                (ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
                  ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 0)).hom x
            exact congrArg (fun φ ↦ φ.hom x) corner_comm.symm
        | succ q =>
            change
              (𝒱.normalizedCofaceModule.differential q ≫
                  ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 (q + 1))).hom x =
                (ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q) ≫
                  (verticalCofaceModule 𝒰 𝒱 0).differential q).hom x
            simpa only [CofaceModule.differential] using
              congrArg (fun φ ↦ φ.hom x)
                (horizontalAugmentation_comp_verticalDifferential 𝒰 𝒱 q).symm
    | succ p =>
        cases q with
        | zero =>
            change
              (ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p) ≫
                  (horizontalCofaceModule 𝒰 𝒱 0).differential p).hom x =
                (𝒰.normalizedCofaceModule.differential p ≫
                  ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 (p + 1))).hom x
            simpa only [CofaceModule.differential] using
              congrArg (fun φ ↦ φ.hom x)
                (verticalAugmentation_comp_horizontalDifferential 𝒰 𝒱 p)
        | succ q =>
            change
              ((verticalCofaceModule 𝒰 𝒱 p).differential q ≫
                  (horizontalCofaceModule 𝒰 𝒱 (q + 1)).differential p).hom x =
                ((horizontalCofaceModule 𝒰 𝒱 q).differential p ≫
                  (verticalCofaceModule 𝒰 𝒱 (p + 1)).differential q).hom x
            simpa only [CofaceModule.differential] using
              congrArg (fun φ ↦ φ.hom x)
                (horizontalDifferential_comp_verticalDifferential 𝒰 𝒱 p q).symm

/-- The bottom row of the fully augmented grid is the normalized Čech complex of `𝒰`. -/
theorem fullyAugmentedDoubleGrid_row_zero (𝒰 𝒱 : P.Family)
    (verticalCorner :
      P.sections 𝒰.ambient →ₗ[K] 𝒱.NormalizedCochains 0)
    (verticalCorner_comp :
      ModuleCat.ofHom verticalCorner ≫
          𝒱.normalizedCofaceModule.differential 0 = 0)
    (corner_comm :
      ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
          ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 0) =
        ModuleCat.ofHom verticalCorner ≫
          ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 0)) :
    (fullyAugmentedDoubleGrid 𝒰 𝒱 verticalCorner
      verticalCorner_comp corner_comm).row 0 =
      𝒰.normalizedCechComplex := by
  rfl

/-- Positive rows are the horizontally augmented double Čech rows. -/
theorem fullyAugmentedDoubleGrid_row_succ (𝒰 𝒱 : P.Family)
    (verticalCorner :
      P.sections 𝒰.ambient →ₗ[K] 𝒱.NormalizedCochains 0)
    (verticalCorner_comp :
      ModuleCat.ofHom verticalCorner ≫
          𝒱.normalizedCofaceModule.differential 0 = 0)
    (corner_comm :
      ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
          ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 0) =
        ModuleCat.ofHom verticalCorner ≫
          ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 0))
    (q : ℕ) :
    (fullyAugmentedDoubleGrid 𝒰 𝒱 verticalCorner
      verticalCorner_comp corner_comm).row (q + 1) =
      (horizontalAugmentedCofaceModule 𝒰 𝒱 q).complex := by
  rfl

/-- A positive column is canonically isomorphic to the corresponding vertically augmented
double Čech column.  The component isomorphisms are identities; the explicit isomorphism only
accounts for the two different recursive presentations of the same terms. -/
noncomputable def fullyAugmentedDoubleGridColumnSuccIso (𝒰 𝒱 : P.Family)
    (verticalCorner :
      P.sections 𝒰.ambient →ₗ[K] 𝒱.NormalizedCochains 0)
    (verticalCorner_comp :
      ModuleCat.ofHom verticalCorner ≫
          𝒱.normalizedCofaceModule.differential 0 = 0)
    (corner_comm :
      ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
          ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 0) =
        ModuleCat.ofHom verticalCorner ≫
          ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 0))
    (p : ℕ) :
    (fullyAugmentedDoubleGrid 𝒰 𝒱 verticalCorner
      verticalCorner_comp corner_comm).column (p + 1) ≅
      (verticalAugmentedCofaceModule 𝒰 𝒱 p).complex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ by
      cases n <;> exact Iso.refl _)
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      cases i <;> rfl)

/-- **Normalized Čech comparison theorem.** If `𝒱` is acyclic and all positive augmented
rows and columns of the double Čech complex are acyclic, then `𝒰` is acyclic. -/
theorem normalizedCechComplex_acyclic_of_double
    (𝒰 𝒱 : P.Family)
    (verticalCorner :
      P.sections 𝒰.ambient →ₗ[K] 𝒱.NormalizedCochains 0)
    (verticalCorner_comp :
      ModuleCat.ofHom verticalCorner ≫
          𝒱.normalizedCofaceModule.differential 0 = 0)
    (corner_comm :
      ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
          ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 0) =
        ModuleCat.ofHom verticalCorner ≫
          ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 0))
    (hfirstColumn :
      (fullyAugmentedDoubleGrid 𝒰 𝒱 verticalCorner
        verticalCorner_comp corner_comm).column 0 |>.Acyclic)
    (hrow : ∀ q, (horizontalAugmentedCofaceModule 𝒰 𝒱 q).complex.Acyclic)
    (hcolumn : ∀ p, (verticalAugmentedCofaceModule 𝒰 𝒱 p).complex.Acyclic) :
    𝒰.normalizedCechComplex.Acyclic := by
  let D := fullyAugmentedDoubleGrid 𝒰 𝒱 verticalCorner
    verticalCorner_comp corner_comm
  have hDcolumn : ∀ p, (D.column p).Acyclic := by
    rintro (_ | p)
    · simpa [D] using hfirstColumn
    · intro i
      exact (hcolumn p i).of_iso
        (fullyAugmentedDoubleGridColumnSuccIso 𝒰 𝒱 verticalCorner
          verticalCorner_comp corner_comm p).symm
  have hDrow : ∀ q, (D.row (q + 1)).Acyclic := by
    intro q
    rw [fullyAugmentedDoubleGrid_row_succ]
    exact hrow q
  have hD := D.row_zero_acyclic_of_columns_and_positive_rows hDcolumn hDrow
  rw [fullyAugmentedDoubleGrid_row_zero] at hD
  exact hD

end Presheaf.Family

end Rigid.Cech
