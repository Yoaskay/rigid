import Rigid.AffinoidSpectrum.Cech
import Rigid.AffinoidSpectrum.CechRefinement
import Rigid.AffinoidSpectrum.CechRestriction
import Rigid.Cech.DoubleComparison
import Rigid.Cech.RefinementContracting

set_option linter.style.header false

/-!
# Double-Čech comparison for rational covers

This file specializes the fully augmented double complex to two rational covers of the same
rational subdomain.  Their ambient section modules are definitionally the same, so the first
column is the normalized Čech complex of the second cover.
-/

open CategoryTheory

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

variable (hA : IsAffinoidAlgebra K A)
variable {U : AffinoidRationalSubdomain K A}

private theorem doubleCorner_comm (𝒰 𝒱 : Cover K A U) :
    let F := 𝒰.cechFamily K A hA
    let G := 𝒱.cechFamily K A hA
    ModuleCat.ofHom F.normalizedAugmentation ≫
        ModuleCat.ofHom (Cech.Presheaf.Family.verticalAugmentation F G 0) =
      ModuleCat.ofHom G.normalizedAugmentation ≫
        ModuleCat.ofHom (Cech.Presheaf.Family.horizontalAugmentation F G 0) := by
  dsimp only
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    (rationalPresheaf K A hA).restriction _
        ((rationalPresheaf K A hA).restriction _ s) =
      (rationalPresheaf K A hA).restriction _
        ((rationalPresheaf K A hA).restriction _ s)
  rw [← LinearMap.comp_apply, Cech.Presheaf.restriction_comp,
    ← LinearMap.comp_apply, Cech.Presheaf.restriction_comp]

/-- The fully augmented double Čech grid of two rational covers of the same domain. -/
noncomputable abbrev doubleCechGrid (𝒰 𝒱 : Cover K A U) :
    Cech.DoubleComplexGrid K :=
  let F := 𝒰.cechFamily K A hA
  let G := 𝒱.cechFamily K A hA
  Cech.Presheaf.Family.fullyAugmentedDoubleGrid F G
    G.normalizedAugmentation
    (G.normalizedAugmentedCofaceModule.differential_comp 0)
    (doubleCorner_comm K A hA 𝒰 𝒱)

/-- The first column of the rational double Čech grid is the complex of its second cover. -/
noncomputable def doubleCechGridColumnZeroIso (𝒰 𝒱 : Cover K A U) :
    (doubleCechGrid K A hA 𝒰 𝒱).column 0 ≅
      𝒱.normalizedCechComplex K A hA :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ by
      cases n <;> exact Iso.refl _)
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      cases i <;> rfl)

/-- Rational-cover form of the normalized double-Čech comparison theorem. -/
theorem normalizedCechComplex_acyclic_of_double
    (𝒰 𝒱 : Cover K A U)
    (h𝒱 : (𝒱.normalizedCechComplex K A hA).Acyclic)
    (hrow : ∀ q,
      (Cech.Presheaf.Family.horizontalAugmentedCofaceModule
        (𝒰.cechFamily K A hA) (𝒱.cechFamily K A hA) q).complex.Acyclic)
    (hcolumn : ∀ p,
      (Cech.Presheaf.Family.verticalAugmentedCofaceModule
        (𝒰.cechFamily K A hA) (𝒱.cechFamily K A hA) p).complex.Acyclic) :
    (𝒰.normalizedCechComplex K A hA).Acyclic := by
  apply Cech.Presheaf.Family.normalizedCechComplex_acyclic_of_double
    (𝒰.cechFamily K A hA) (𝒱.cechFamily K A hA)
    (𝒱.cechFamily K A hA).normalizedAugmentation
    ((𝒱.cechFamily K A hA).normalizedAugmentedCofaceModule.differential_comp 0)
    (doubleCorner_comm K A hA 𝒰 𝒱)
  · intro i
    exact (h𝒱 i).of_iso (doubleCechGridColumnZeroIso K A hA 𝒰 𝒱).symm
  · exact hrow
  · exact hcolumn

/-- Acyclicity descends from an acyclic refinement when all restricted columns are acyclic. -/
theorem normalizedCechComplex_acyclic_of_refinement
    (𝒰 𝒱 : Cover K A U) (r : Refinement K A 𝒱 𝒰)
    (h𝒱 : (𝒱.normalizedCechComplex K A hA).Acyclic)
    (hcolumn : ∀ p,
      (Cech.Presheaf.Family.verticalAugmentedCofaceModule
        (𝒰.cechFamily K A hA) (𝒱.cechFamily K A hA) p).complex.Acyclic) :
    (𝒰.normalizedCechComplex K A hA).Acyclic := by
  apply normalizedCechComplex_acyclic_of_double K A hA 𝒰 𝒱 h𝒱
  · intro q
    exact (r.cechRefinement K A hA).horizontalAugmentedCofaceModule_acyclic q
  · exact hcolumn

/-- Acyclicity ascends to a refinement when all restrictions of the refined cover to coarse
tuple intersections are acyclic. -/
theorem refinement_normalizedCechComplex_acyclic
    (𝒰 𝒱 : Cover K A U) (r : Refinement K A 𝒱 𝒰)
    (h𝒰 : (𝒰.normalizedCechComplex K A hA).Acyclic)
    (hrow : ∀ q,
      (Cech.Presheaf.Family.horizontalAugmentedCofaceModule
        (𝒱.cechFamily K A hA) (𝒰.cechFamily K A hA) q).complex.Acyclic) :
    (𝒱.normalizedCechComplex K A hA).Acyclic := by
  apply normalizedCechComplex_acyclic_of_double K A hA 𝒱 𝒰 h𝒰 hrow
  intro p
  exact (r.cechRefinement K A hA).verticalAugmentedCofaceModule_acyclic p

/-- **Čech refinement comparison.** If `𝒱` refines `𝒰` and the restriction of `𝒱` to every
nonempty tuple intersection of `𝒰` is acyclic, then `𝒰` is acyclic exactly when `𝒱` is.

This is BGR 8.2.1, Corollary 3, in normalized-complex form. -/
theorem normalizedCechComplex_acyclic_iff_of_refinement
    (𝒰 𝒱 : Cover K A U) (r : Refinement K A 𝒱 𝒰)
    (hrestrict : ∀ p (σ : (𝒰.cechFamily K A hA).StrictTuple p),
      let W := (𝒰.cechFamily K A hA).tupleInter p σ
      let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
        ((𝒰.cechFamily K A hA).subset (σ 0))
      ((𝒱.restrictTo K A W hWU).normalizedCechComplex K A hA).Acyclic) :
    (𝒰.normalizedCechComplex K A hA).Acyclic ↔
      (𝒱.normalizedCechComplex K A hA).Acyclic := by
  constructor
  · intro h𝒰
    apply refinement_normalizedCechComplex_acyclic K A hA 𝒰 𝒱 r h𝒰
    intro q
    have hvertical :=
      verticalAugmentedCofaceModule_acyclic_of_restrictTo
        K A hA 𝒰 𝒱 q (hrestrict q)
    intro n
    exact (hvertical n).of_iso
      (Cech.Presheaf.Family.verticalAugmentedCofaceModuleIso
        (𝒰.cechFamily K A hA) (𝒱.cechFamily K A hA) q)
  · intro h𝒱
    apply normalizedCechComplex_acyclic_of_refinement K A hA 𝒰 𝒱 r h𝒱
    intro p
    exact verticalAugmentedCofaceModule_acyclic_of_restrictTo
      K A hA 𝒰 𝒱 p (hrestrict p)

/-- Covers which refine one another have equivalent normalized Čech acyclicity.  The two
refinements supply contractions in the two directions of the comparison double complex. -/
theorem normalizedCechComplex_acyclic_iff_of_mutual_refinement
    (𝒰 𝒱 : Cover K A U)
    (r𝒱𝒰 : Refinement K A 𝒱 𝒰) (r𝒰𝒱 : Refinement K A 𝒰 𝒱) :
    (𝒰.normalizedCechComplex K A hA).Acyclic ↔
      (𝒱.normalizedCechComplex K A hA).Acyclic := by
  constructor
  · intro h𝒰
    apply refinement_normalizedCechComplex_acyclic K A hA 𝒰 𝒱 r𝒱𝒰 h𝒰
    intro q
    exact (r𝒰𝒱.cechRefinement K A hA).horizontalAugmentedCofaceModule_acyclic q
  · intro h𝒱
    apply normalizedCechComplex_acyclic_of_refinement K A hA 𝒰 𝒱 r𝒱𝒰 h𝒱
    intro p
    exact (r𝒰𝒱.cechRefinement K A hA).verticalAugmentedCofaceModule_acyclic p

end AffinoidRationalSubdomain.Cover

end Rigid
