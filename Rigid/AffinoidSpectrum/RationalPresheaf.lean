import Rigid.AffinoidAlgebra.BanachRealization
import Rigid.AffinoidAlgebra.SpectralPresentation
import Rigid.AffinoidSpectrum.RationalCover
import Rigid.AffinoidSpectrum.Restriction

set_option linter.style.header false

/-!
# The rational-localization presheaf

This file makes the restriction map between arbitrary rational subdomains unconditional for an
affinoid ambient algebra.  It packages the spectral-criterion argument already used in the
comparator and proves identity and composition, which are the functoriality facts needed by Čech
complexes.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain

/-- Restriction of analytic functions along an inclusion of rational subdomains. -/
noncomputable def restriction (hA : IsAffinoidAlgebra K A)
    {U V : AffinoidRationalSubdomain K A}
    (hUV : U.carrier ⊆ V.carrier) : ContinuousAlgHom K V.Sections U.Sections := by
  by_cases hU : Nontrivial U.Sections
  · letI := hU
    have hAtop : (inferInstance : TopologicalSpace A) =
        affinoidTopology K A hA :=
      topology_eq_affinoidTopology_of_presentation K A
        hA.presentation.n hA.presentation.ideal hA.presentation.equiv
    let π : ContinuousAlgHom K (TateAlgebra K (Fin hA.presentation.n)) A :=
      { toAlgHom := hA.presentation.toAlgHom
        cont := continuous_tateAlgebra_to_affinoid K hA hAtop hA.presentation.toAlgHom }
    let hUaff := isAffinoidAlgebra_rationalLocalization_of_surjective
      K A hA.presentation.n π hA.presentation.toAlgHom_surjective U.n U.g U.f
    let P := hUaff.presentation
    have htop : (inferInstance : TopologicalSpace U.Sections) = P.residueTopology := by
      exact topology_eq_affinoidTopology_of_presentation K U.Sections
        P.n P.ideal P.equiv
    exact restrictionOfSpectralCriterion K A hUV
      (SpectralPolynomial.hasPowerBoundedSpectralCriterion_of_affinoidPresentation
        K P htop)
  · letI : Subsingleton U.Sections := not_nontrivial_iff_subsingleton.mp hU
    exact restrictionOfPointwisePowerBounded K A hUV fun i ↦ by
      rw [Subsingleton.elim
        (RationalLocalization.quotientCoordinate K A
          (f := V.f)
          (RationalLocalization.baseMap K A U.n U.g U.f)
          (isUnit_baseMap_denominator_of_subset K A hUV) i) 0]
      exact isPowerBounded_zero

@[simp]
theorem restriction_id (hA : IsAffinoidAlgebra K A) (U : AffinoidRationalSubdomain K A) :
    restriction K A hA (U := U) (V := U) Set.Subset.rfl =
      ContinuousAlgHom.id K U.Sections := by
  unfold restriction
  dsimp only
  split
  · apply restrictionOfPointwisePowerBounded_id
  · apply restrictionOfPointwisePowerBounded_id

@[simp]
theorem restriction_comp (hA : IsAffinoidAlgebra K A)
    {U V W : AffinoidRationalSubdomain K A}
    (hUV : U.carrier ⊆ V.carrier) (hWU : W.carrier ⊆ U.carrier) :
    (restriction K A hA hWU).comp (restriction K A hA hUV) =
      restriction K A hA (hWU.trans hUV) := by
  unfold restriction
  dsimp only
  repeat' split
  all_goals
    try unfold restrictionOfSpectralCriterion
    apply restrictionOfPointwisePowerBounded_comp

/-- Restriction to a rational subdomain agrees with its canonical base map on ambient
functions. -/
@[simp]
theorem restriction_comp_baseMap (hA : IsAffinoidAlgebra K A)
    {U V : AffinoidRationalSubdomain K A}
    (hUV : U.carrier ⊆ V.carrier) :
    (restriction K A hA hUV).comp
        (RationalLocalization.baseMap K A V.n V.g V.f) =
      RationalLocalization.baseMap K A U.n U.g U.f := by
  unfold restriction
  dsimp only
  split
  · apply restrictionOfPointwisePowerBounded_comp_baseMap
  · apply restrictionOfPointwisePowerBounded_comp_baseMap

/-- Two rational data cutting out the same point set have canonically linearly equivalent
section algebras. -/
noncomputable def sectionsLinearEquivOfCarrierEq (hA : IsAffinoidAlgebra K A)
    (U V : AffinoidRationalSubdomain K A) (hUV : U.carrier = V.carrier) :
    U.Sections ≃ₗ[K] V.Sections where
  toFun := restriction K A hA hUV.ge
  invFun := restriction K A hA hUV.le
  left_inv x := by
    have hcomp := restriction_comp K A hA hUV.ge hUV.le
    have hid := restriction_id K A hA U
    exact congrArg (fun φ : ContinuousAlgHom K U.Sections U.Sections ↦ φ x)
      (hcomp.trans hid)
  right_inv x := by
    have hcomp := restriction_comp K A hA hUV.le hUV.ge
    have hid := restriction_id K A hA V
    exact congrArg (fun φ : ContinuousAlgHom K V.Sections V.Sections ↦ φ x)
      (hcomp.trans hid)
  map_add' x y := map_add _ x y
  map_smul' c x := map_smul _ c x

/-- Evaluation identifies the section algebra of the whole rational subdomain with the ambient
algebra. -/
noncomputable def wholeSectionsLinearEquiv (hA : IsAffinoidAlgebra K A) :
    (whole K A).Sections ≃ₗ[K] A := by
  change RationalLocalization K A 0 1 Fin.elim0 ≃ₗ[K] A
  let ev : ContinuousAlgHom K (RationalLocalization K A 0 1 Fin.elim0) A :=
    RationalLocalization.lift K A 0 1 Fin.elim0
      (ContinuousAlgHom.id K A) Fin.elim0
      (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  let base : ContinuousAlgHom K A (RationalLocalization K A 0 1 Fin.elim0) :=
    RationalLocalization.baseMap K A 0 1 Fin.elim0
  refine
    { toFun := ev
      invFun := base
      left_inv := ?_
      right_inv := ?_
      map_add' := fun x y ↦ map_add ev x y
      map_smul' := fun c x ↦ map_smul ev c x }
  · intro x
    have hevbase : ev.comp base = ContinuousAlgHom.id K A := by
      change
        (RationalLocalization.lift K A 0 1 Fin.elim0
          (ContinuousAlgHom.id K A) Fin.elim0
          (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)).comp
            (RationalLocalization.baseMap K A 0 1 Fin.elim0) =
          ContinuousAlgHom.id K A
      exact RationalLocalization.lift_comp_baseMap K A 0 1 Fin.elim0
        (ContinuousAlgHom.id K A) Fin.elim0
        (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
    have hbaseev : base.comp ev =
        ContinuousAlgHom.id K (RationalLocalization K A 0 1 Fin.elim0) := by
      apply RationalLocalization.hom_ext K A 0 1 Fin.elim0
      · rw [ContinuousAlgHom.comp_assoc, hevbase,
          ContinuousAlgHom.comp_id, ContinuousAlgHom.id_comp]
      · intro i
        exact Fin.elim0 i
    exact congrArg (fun φ : ContinuousAlgHom K (RationalLocalization K A 0 1 Fin.elim0)
      (RationalLocalization K A 0 1 Fin.elim0) ↦ φ x) hbaseev
  · intro x
    have hevbase : ev.comp base = ContinuousAlgHom.id K A := by
      change
        (RationalLocalization.lift K A 0 1 Fin.elim0
          (ContinuousAlgHom.id K A) Fin.elim0
          (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)).comp
            (RationalLocalization.baseMap K A 0 1 Fin.elim0) =
          ContinuousAlgHom.id K A
      exact RationalLocalization.lift_comp_baseMap K A 0 1 Fin.elim0
        (ContinuousAlgHom.id K A) Fin.elim0
        (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
    exact congrArg (fun φ : ContinuousAlgHom K A A ↦ φ x) hevbase

@[simp]
theorem wholeSectionsLinearEquiv_symm_apply (hA : IsAffinoidAlgebra K A) (x : A) :
    (wholeSectionsLinearEquiv K A hA).symm x =
      RationalLocalization.baseMap K A (whole K A).n (whole K A).g
        (whole K A).f x :=
  rfl

end AffinoidRationalSubdomain

end Rigid
