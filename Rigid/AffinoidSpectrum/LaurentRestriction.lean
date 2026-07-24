import Rigid.AffinoidSpectrum.CechRebase
import Rigid.AffinoidSpectrum.CechRestriction
import Rigid.AffinoidSpectrum.LaurentCech

set_option linter.style.header false

/-!
# Laurent covers restricted to rational subdomains

The restriction of the two-member Laurent cover associated with `f : A` to a rational subdomain
`W` becomes, after rebasing to `W.Sections`, the ordinary Laurent cover associated with the image
of `f`.  Hence every such restricted cover is acyclic.
-/

open CategoryTheory

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

variable (hA : IsAffinoidAlgebra K A)

private noncomputable abbrev restrictedLaurent
    (W : AffinoidRationalSubdomain K A) (f : A) :
    Cover K A W :=
  (laurent K A f).restrictTo K A W (by
    rw [carrier_whole]
    exact Set.subset_univ _)

private noncomputable abbrev rebasedRestrictedLaurent
    (W : AffinoidRationalSubdomain K A) (f : A) :
    Cover K W.Sections (whole K W.Sections) :=
  (restrictedLaurent K A W f).rebase K A

private noncomputable abbrev restrictedElement
    (W : AffinoidRationalSubdomain K A) (f : A) : W.Sections :=
  RationalLocalization.baseMap K A W.n W.g W.f f

/-- After restricting and rebasing a Laurent cover, each member has the same carrier as the
corresponding standard Laurent chart over the section algebra. -/
theorem rebase_restrictTo_laurent_domain_carrier_eq
    (W : AffinoidRationalSubdomain K A) (f : A) (i : Fin 2) :
    ((((laurent K A f).restrictTo K A W (by
        rw [carrier_whole]
        exact Set.subset_univ _)).rebase K A).domain i).carrier =
      ((laurent K W.Sections
        (RationalLocalization.baseMap K A W.n W.g W.f f)).domain i).carrier := by
  ext y
  fin_cases i
  · rw [mem_rebase_carrier_iff]
    change
      ambientPoint K A W y ∈ (inter K A W (laurentLE K A f)).carrier ↔
        y ∈ (laurentLE K W.Sections (restrictedElement K A W f)).carrier
    rw [carrier_inter, Set.mem_inter_iff, mem_carrier_laurentLE,
      mem_carrier_laurentLE, ← ambientPoint_apply K A W]
    constructor
    · exact And.right
    · exact fun h ↦ ⟨ambientPoint_mem_carrier K A W y, h⟩
  · rw [mem_rebase_carrier_iff]
    change
      ambientPoint K A W y ∈ (inter K A W (laurentGE K A f)).carrier ↔
        y ∈ (laurentGE K W.Sections (restrictedElement K A W f)).carrier
    rw [carrier_inter, Set.mem_inter_iff, mem_carrier_laurentGE,
      mem_carrier_laurentGE, ← ambientPoint_apply K A W]
    constructor
    · exact And.right
    · exact fun h ↦ ⟨ambientPoint_mem_carrier K A W y, h⟩

private theorem rebasedRestrictedLaurent_tupleInter_carrier_eq
    (W : AffinoidRationalSubdomain K A) (f : A) (n : ℕ)
    (τ : ((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
      (isAffinoidAlgebra_sections K A hA W)).StrictTuple n) :
    (((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).tupleInter n τ).carrier =
      (((laurent K W.Sections (restrictedElement K A W f)).cechFamily
        K W.Sections (isAffinoidAlgebra_sections K A hA W)).tupleInter n τ).carrier := by
  induction n with
  | zero =>
      exact rebase_restrictTo_laurent_domain_carrier_eq K A W f (τ 0)
  | succ n ih =>
      rw [Cech.Presheaf.Family.tupleInter, Cech.Presheaf.Family.tupleInter,
        carrier_inter, carrier_inter]
      let τ₀ :
          ((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
            (isAffinoidAlgebra_sections K A hA W)).StrictTuple n :=
        Fin.castSuccOrderEmb.comp τ
      have hi := ih τ₀
      change
        (((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
          (isAffinoidAlgebra_sections K A hA W)).tupleInter n
            (fun i ↦ τ i.castSucc)).carrier =
          (((laurent K W.Sections (restrictedElement K A W f)).cechFamily
            K W.Sections (isAffinoidAlgebra_sections K A hA W)).tupleInter n
              (fun i ↦ τ i.castSucc)).carrier at hi
      rw [hi, rebase_restrictTo_laurent_domain_carrier_eq K A W f]

private noncomputable def rebasedRestrictedLaurentTupleSectionsLinearEquiv
    (W : AffinoidRationalSubdomain K A) (f : A) (n : ℕ)
    (τ : ((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
      (isAffinoidAlgebra_sections K A hA W)).StrictTuple n) :
    (((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).tupleInter n τ).Sections ≃ₗ[K]
      (((laurent K W.Sections (restrictedElement K A W f)).cechFamily
        K W.Sections (isAffinoidAlgebra_sections K A hA W)).tupleInter n τ).Sections :=
  sectionsLinearEquivOfCarrierEq K W.Sections
    (isAffinoidAlgebra_sections K A hA W) _ _
    (rebasedRestrictedLaurent_tupleInter_carrier_eq K A hA W f n τ)

set_option synthInstance.maxHeartbeats 100000 in
-- Dependent products of rational-localization section modules make instance synthesis deep.
private noncomputable def rebasedRestrictedLaurentCochainsLinearEquiv
    (W : AffinoidRationalSubdomain K A) (f : A) (n : ℕ) :
    ((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).NormalizedCochains n ≃ₗ[K]
      ((laurent K W.Sections (restrictedElement K A W f)).cechFamily
        K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).NormalizedCochains n :=
  LinearEquiv.piCongrRight (R := K) fun τ ↦
    rebasedRestrictedLaurentTupleSectionsLinearEquiv K A hA W f n τ

set_option synthInstance.maxHeartbeats 100000 in
-- The normalized cochain module is a dependent product of localization modules.
private theorem rebasedRestrictedLaurent_augmentation_comm
    (W : AffinoidRationalSubdomain K A) (f : A) :
    (rebasedRestrictedLaurentCochainsLinearEquiv K A hA W f 0).toLinearMap.comp
        ((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
          (isAffinoidAlgebra_sections K A hA W)).normalizedAugmentation =
      ((laurent K W.Sections (restrictedElement K A W f)).cechFamily
        K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).normalizedAugmentation := by
  apply LinearMap.ext
  intro s
  funext τ
  change
    restriction K W.Sections (isAffinoidAlgebra_sections K A hA W) _
        (restriction K W.Sections (isAffinoidAlgebra_sections K A hA W) _ s) =
      restriction K W.Sections (isAffinoidAlgebra_sections K A hA W) _ s
  rw [← ContinuousAlgHom.comp_apply, restriction_comp]

set_option maxHeartbeats 800000 in
-- Unfolding both carrier-equivalent localization complexes is elaboration-intensive.
set_option synthInstance.maxHeartbeats 100000 in
-- Their cochain modules are dependent products of rational-localization section modules.
private theorem rebasedRestrictedLaurent_coface_comm
    (W : AffinoidRationalSubdomain K A) (f : A)
    (n : ℕ) (i : Fin (n + 2)) :
    (rebasedRestrictedLaurentCochainsLinearEquiv K A hA W f (n + 1)).toLinearMap.comp
        (((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
          (isAffinoidAlgebra_sections K A hA W)).normalizedCoface n i) =
      (((laurent K W.Sections (restrictedElement K A W f)).cechFamily
        K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).normalizedCoface n i).comp
        (rebasedRestrictedLaurentCochainsLinearEquiv K A hA W f n).toLinearMap := by
  apply LinearMap.ext
  intro s
  funext τ
  change
    restriction K W.Sections (isAffinoidAlgebra_sections K A hA W) _
        (restriction K W.Sections (isAffinoidAlgebra_sections K A hA W) _
          (s (i.succAboveOrderEmb.comp τ))) =
      restriction K W.Sections (isAffinoidAlgebra_sections K A hA W) _
        (restriction K W.Sections (isAffinoidAlgebra_sections K A hA W) _
          (s (i.succAboveOrderEmb.comp τ)))
  rw [← ContinuousAlgHom.comp_apply, restriction_comp,
    ← ContinuousAlgHom.comp_apply, restriction_comp]

set_option synthInstance.maxHeartbeats 100000 in
-- The explicit scalar ring prevents synthesis from exploring localization algebra structures.
private noncomputable def rebasedRestrictedLaurentCochainsModuleIso
    (W : AffinoidRationalSubdomain K A) (f : A) (n : ℕ) :
    ((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).normalizedCofaceModule.X n ≅
      ((laurent K W.Sections (restrictedElement K A W f)).cechFamily
        K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).normalizedCofaceModule.X n :=
  (rebasedRestrictedLaurentCochainsLinearEquiv K A hA W f n).toModuleIso

set_option synthInstance.maxHeartbeats 100000 in
-- Alternating sums retain the dependent-product module structure during elaboration.
private theorem rebasedRestrictedLaurent_differential_comm
    (W : AffinoidRationalSubdomain K A) (f : A) (n : ℕ) :
    ((rebasedRestrictedLaurent K A W f).cechFamily K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).normalizedCofaceModule.differential n ≫
      (rebasedRestrictedLaurentCochainsModuleIso K A hA W f (n + 1)).hom =
    (rebasedRestrictedLaurentCochainsModuleIso K A hA W f n).hom ≫
      ((laurent K W.Sections (restrictedElement K A W f)).cechFamily
        K W.Sections
        (isAffinoidAlgebra_sections K A hA W)).normalizedCofaceModule.differential n := by
  simp only [Cech.CofaceModule.differential,
    CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.zsmul_comp]
  rw [CategoryTheory.Preadditive.comp_sum]
  simp only [CategoryTheory.Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply ModuleCat.hom_ext
  exact rebasedRestrictedLaurent_coface_comm K A hA W f n i

set_option synthInstance.maxHeartbeats 100000 in
-- Components in positive degree are dependent products of section modules.
private noncomputable abbrev rebasedRestrictedLaurentComponentIso
    (W : AffinoidRationalSubdomain K A) (f : A) :
    ∀ n, (
      ((rebasedRestrictedLaurent K A W f).normalizedCechComplex K W.Sections
          (isAffinoidAlgebra_sections K A hA W)).X n ≅
        ((laurent K W.Sections (restrictedElement K A W f)).normalizedCechComplex
          K W.Sections (isAffinoidAlgebra_sections K A hA W)).X n)
  | 0 => Iso.refl _
  | n + 1 => rebasedRestrictedLaurentCochainsModuleIso K A hA W f n

set_option synthInstance.maxHeartbeats 100000 in
-- Constructing the chain isomorphism elaborates all dependent-product components.
private noncomputable def rebasedRestrictedLaurentCechIso
    (W : AffinoidRationalSubdomain K A) (f : A) :
    (rebasedRestrictedLaurent K A W f).normalizedCechComplex K W.Sections
        (isAffinoidAlgebra_sections K A hA W) ≅
      (laurent K W.Sections (restrictedElement K A W f)).normalizedCechComplex
        K W.Sections (isAffinoidAlgebra_sections K A hA W) :=
  HomologicalComplex.Hom.isoOfComponents
    (rebasedRestrictedLaurentComponentIso K A hA W f)
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      dsimp only [normalizedCechComplex]
      cases i with
      | zero =>
          apply ModuleCat.hom_ext
          exact (rebasedRestrictedLaurent_augmentation_comm K A hA W f).symm
      | succ n =>
          simpa only [Cech.CofaceModule.Augmented.complex,
            CochainComplex.of_d, Cech.CofaceModule.Augmented.differential,
            rebasedRestrictedLaurentComponentIso] using
              (rebasedRestrictedLaurent_differential_comm K A hA W f n).symm)

/-- The restriction of a two-member Laurent cover to any rational subdomain is acyclic. -/
theorem restrictTo_laurent_normalizedCechComplex_acyclic
    (W : AffinoidRationalSubdomain K A) (f : A) :
    ((restrictedLaurent K A W f).normalizedCechComplex K A hA).Acyclic := by
  rw [normalizedCechComplex_acyclic_iff_rebase K A hA]
  intro n
  exact (laurent_normalizedCechComplex_acyclic K W.Sections
    (isAffinoidAlgebra_sections K A hA W) (restrictedElement K A W f) n).of_iso
      (rebasedRestrictedLaurentCechIso K A hA W f).symm

end AffinoidRationalSubdomain.Cover

end Rigid
