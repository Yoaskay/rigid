import Rigid.AffinoidSpectrum.RationalCover
import Rigid.AffinoidSpectrum.RationalPresheaf
import Rigid.Cech.Normalized
import Rigid.Cech.Presheaf

set_option linter.style.header false

/-!
# Čech complexes of finite rational covers

This file specializes the generic finite Čech construction to the rational-localization
presheaf.  Exactness is kept separate from the construction: it is supplied by the Laurent-cover
and comparison arguments.
-/

open CategoryTheory

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain

/-- The rational-localization presheaf, in the exact amount of generality needed by the generic
finite Čech construction. -/
noncomputable abbrev rationalPresheaf (hA : IsAffinoidAlgebra K A) : Cech.Presheaf K where
  Domain := AffinoidRationalSubdomain K A
  subset U V := U.carrier ⊆ V.carrier
  subset_refl _ := Set.Subset.rfl
  subset_trans hWV hVU := hWV.trans hVU
  inter := inter K A
  inter_subset_left := inter_subset_left K A
  inter_subset_right := inter_subset_right K A
  subset_inter := by
    intro U V W hWU hWV
    rw [carrier_inter]
    exact fun x hx ↦ ⟨hWU hx, hWV hx⟩
  sections U := ModuleCat.of K U.Sections
  restriction h := (restriction K A hA h).toLinearMap
  restriction_id U := by
    simpa using congrArg (fun φ : ContinuousAlgHom K U.Sections U.Sections ↦ φ.toLinearMap)
      (restriction_id K A hA U)
  restriction_comp hVU hWV := by
    exact congrArg (fun φ : ContinuousAlgHom K _ _ ↦ φ.toLinearMap)
      (restriction_comp K A hA hVU hWV)

namespace Cover

/-- A rational cover, regarded as a finite family in the rational-localization presheaf. -/
noncomputable abbrev cechFamily (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    (rationalPresheaf K A hA).Family where
  ambient := U
  card := 𝒰.m
  domain := 𝒰.domain
  subset := 𝒰.subset

/-- The augmented unnormalized Čech complex of a finite rational cover. -/
noncomputable def cechComplex (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    CochainComplex (ModuleCat K) ℕ :=
  (𝒰.cechFamily K A hA).augmentedCechComplex

/-- Degree zero of the augmented rational Čech complex is the ring of sections on the covered
domain. -/
noncomputable def cechComplexDegreeZeroIso (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    (𝒰.cechComplex K A hA).X 0 ≅ ModuleCat.of K U.Sections :=
  (𝒰.cechFamily K A hA).augmentedCechComplexDegreeZeroIso

/-- The augmented normalized Čech complex of a finite rational cover. -/
noncomputable def normalizedCechComplex (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    CochainComplex (ModuleCat K) ℕ :=
  (𝒰.cechFamily K A hA).normalizedCechComplex

/-- Degree zero of the augmented normalized rational Čech complex is the ring of sections on the
covered domain. -/
noncomputable def normalizedCechComplexDegreeZeroIso (hA : IsAffinoidAlgebra K A)
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    (𝒰.normalizedCechComplex K A hA).X 0 ≅ ModuleCat.of K U.Sections :=
  (𝒰.cechFamily K A hA).normalizedCechComplexDegreeZeroIso

end Cover

end AffinoidRationalSubdomain

end Rigid
