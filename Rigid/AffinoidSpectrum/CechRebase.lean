import Rigid.AffinoidSpectrum.Cech
import Rigid.AffinoidSpectrum.RationalRebase

set_option linter.style.header false

/-!
# Rebasing rational Čech complexes

A rational cover of a rational subdomain `U` may be regarded as a cover of the whole spectrum of
`U.Sections`.  This file identifies the tuple intersections, and then their section modules, on
the two sides.  It is the chain-level form of BGR 8.2.2, Proposition 1.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

variable (hA : IsAffinoidAlgebra K A)
variable {U : AffinoidRationalSubdomain K A}

/-- Membership in a tuple intersection of a rebased cover is detected after applying the
canonical map to the original affinoid spectrum. -/
theorem mem_rebase_tupleInter_carrier_iff
    (𝒱 : Cover K A U) (n : ℕ) (σ : Fin (n + 1) → Fin 𝒱.m)
    (y : BerkovichSpectrumOver K U.Sections) :
    y ∈ (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).tupleInter n σ).carrier ↔
      ambientPoint K A U y ∈
        ((𝒱.cechFamily K A hA).tupleInter n σ).carrier := by
  induction n with
  | zero =>
      exact mem_rebase_carrier_iff K A U (𝒱.domain (σ 0)) y
  | succ n ih =>
      rw [Cech.Presheaf.Family.tupleInter, Cech.Presheaf.Family.tupleInter,
        carrier_inter, carrier_inter, Set.mem_inter_iff, Set.mem_inter_iff]
      exact and_congr
        (ih (fun i ↦ σ i.castSucc))
        (mem_rebase_carrier_iff K A U
          (𝒱.domain (σ (Fin.last (n + 1)))) y)

/-- The actual tuple intersection of the rebased cover and the rebase of the original tuple
intersection cut out the same rational subdomain. -/
theorem rebase_tupleInter_carrier_eq
    (𝒱 : Cover K A U) (n : ℕ) (σ : Fin (n + 1) → Fin 𝒱.m) :
    (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).tupleInter n σ).carrier =
      (AffinoidRationalSubdomain.rebase K A U
        ((𝒱.cechFamily K A hA).tupleInter n σ)).carrier := by
  ext y
  rw [mem_rebase_tupleInter_carrier_iff K A hA 𝒱 n σ,
    mem_rebase_carrier_iff K A]

/-- Every tuple intersection of a cover of `U` is contained in `U`. -/
theorem tupleInter_subset_ambient
    (𝒱 : Cover K A U) (n : ℕ) (σ : Fin (n + 1) → Fin 𝒱.m) :
    ((𝒱.cechFamily K A hA).tupleInter n σ).carrier ⊆ U.carrier :=
  ((𝒱.cechFamily K A hA).tupleInter_subset_domain n σ 0).trans
    ((𝒱.cechFamily K A hA).subset (σ 0))

/-- Sections on corresponding tuple intersections before and after rebasing are canonically
linearly equivalent. -/
noncomputable def rebaseTupleInterSectionsLinearEquiv
    (𝒱 : Cover K A U) (n : ℕ) (σ : Fin (n + 1) → Fin 𝒱.m) :
    (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).tupleInter n σ).Sections ≃ₗ[K]
      ((𝒱.cechFamily K A hA).tupleInter n σ).Sections :=
  (sectionsLinearEquivOfCarrierEq K U.Sections
      (isAffinoidAlgebra_sections K A hA U)
      (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).tupleInter n σ)
      (AffinoidRationalSubdomain.rebase K A U
        ((𝒱.cechFamily K A hA).tupleInter n σ))
      (rebase_tupleInter_carrier_eq K A hA 𝒱 n σ)).trans
    (rebaseSectionsLinearEquiv K A hA
      (tupleInter_subset_ambient K A hA 𝒱 n σ))

/-- The whole spectrum of `U.Sections` and the rebase of `U` itself have the same carrier. -/
theorem whole_carrier_eq_rebase_self :
    (whole K U.Sections).carrier =
      (AffinoidRationalSubdomain.rebase K A U U).carrier := by
  ext y
  simp only [carrier_whole, Set.mem_univ,
    mem_rebase_carrier_iff K A U U]
  exact iff_of_true trivial (ambientPoint_mem_carrier K A U y)

/-- The degree-zero (ambient-section) equivalence for a rebased cover. -/
noncomputable def rebaseAmbientSectionsLinearEquiv :
    (whole K U.Sections).Sections ≃ₗ[K] U.Sections :=
  (sectionsLinearEquivOfCarrierEq K U.Sections
      (isAffinoidAlgebra_sections K A hA U)
      (whole K U.Sections)
      (AffinoidRationalSubdomain.rebase K A U U)
      (whole_carrier_eq_rebase_self K A)).trans
    (rebaseSectionsLinearEquiv K A hA Set.Subset.rfl)

/-- The pointwise equivalence on normalized cochains of a cover and its rebase. -/
noncomputable def rebaseNormalizedCochainsLinearEquiv
    (𝒱 : Cover K A U) (n : ℕ) :
    ((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).NormalizedCochains n ≃ₗ[K]
      (𝒱.cechFamily K A hA).NormalizedCochains n :=
  LinearEquiv.piCongrRight (R := K) fun σ ↦
    rebaseTupleInterSectionsLinearEquiv K A hA 𝒱 n σ

/-- The same cochain equivalence as an isomorphism in `ModuleCat`, with the scalar ring fixed
explicitly so typeclass search does not inspect the dependent product for other module
structures. -/
noncomputable def rebaseNormalizedCochainsModuleIso
    (𝒱 : Cover K A U) (n : ℕ) :
    (((𝒱.rebase K A).cechFamily K U.Sections
      (isAffinoidAlgebra_sections K A hA U)).normalizedCofaceModule.X n) ≅
      (𝒱.cechFamily K A hA).normalizedCofaceModule.X n := by
  let X := ((𝒱.rebase K A).cechFamily K U.Sections
    (isAffinoidAlgebra_sections K A hA U)).normalizedCofaceModule.X n
  let Y := (𝒱.cechFamily K A hA).normalizedCofaceModule.X n
  letI : AddCommGroup X := X.isAddCommGroup
  letI : Module K X := X.isModule
  letI : AddCommGroup Y := Y.isAddCommGroup
  letI : Module K Y := Y.isModule
  let e₀ := rebaseNormalizedCochainsLinearEquiv K A hA 𝒱 n
  let e : X ≃ₗ[K] Y :=
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := e₀.map_smul }
  exact e.toModuleIso

/-- The component equivalences underlying the rebasing isomorphism of Čech complexes. -/
noncomputable abbrev rebaseNormalizedCechComponentLinearEquiv
    (𝒱 : Cover K A U) :
    ∀ n,
      ((𝒱.rebase K A).normalizedCechComplex K U.Sections
          (isAffinoidAlgebra_sections K A hA U)).X n ≃ₗ[K]
        (𝒱.normalizedCechComplex K A hA).X n
  | 0 => rebaseAmbientSectionsLinearEquiv K A hA
  | n + 1 => rebaseNormalizedCochainsLinearEquiv K A hA 𝒱 n

noncomputable abbrev rebaseNormalizedCechComponentIso
    (𝒱 : Cover K A U) :
    ∀ n,
      ((𝒱.rebase K A).normalizedCechComplex K U.Sections
          (isAffinoidAlgebra_sections K A hA U)).X n ≅
        (𝒱.normalizedCechComplex K A hA).X n
  | 0 => (rebaseAmbientSectionsLinearEquiv K A hA).toModuleIso
  | n + 1 => rebaseNormalizedCochainsModuleIso K A hA 𝒱 n

private noncomputable abbrev rebaseNormalizedAugmentation
    (𝒱 : Cover K A U) :
    (whole K U.Sections).Sections →ₗ[K]
      ((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).NormalizedCochains 0 :=
  ((𝒱.rebase K A).cechFamily K U.Sections
    (isAffinoidAlgebra_sections K A hA U)).normalizedAugmentation

private noncomputable abbrev rebaseNormalizedCoface
    (𝒱 : Cover K A U) (n : ℕ) (i : Fin (n + 2)) :
    ((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).NormalizedCochains n →ₗ[K]
      ((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).NormalizedCochains (n + 1) :=
  ((𝒱.rebase K A).cechFamily K U.Sections
    (isAffinoidAlgebra_sections K A hA U)).normalizedCoface n i

private theorem rebase_normalizedAugmentation_comm
    (𝒱 : Cover K A U) :
    (rebaseNormalizedCechComponentLinearEquiv K A hA 𝒱 1).toLinearMap.comp
        (rebaseNormalizedAugmentation K A hA 𝒱) =
      (𝒱.cechFamily K A hA).normalizedAugmentation.comp
        (rebaseNormalizedCechComponentLinearEquiv K A hA 𝒱 0).toLinearMap := by
  apply LinearMap.ext
  intro s
  funext σ
  change
    (rebaseTupleInterSectionsLinearEquiv K A hA 𝒱 0 σ)
      (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).normalizedAugmentation s σ) =
    (𝒱.cechFamily K A hA).normalizedAugmentation
      (rebaseAmbientSectionsLinearEquiv K A hA s) σ
  change
    ((rebaseToSections K A hA
        (tupleInter_subset_ambient K A hA 𝒱 0 σ)).comp
      (restriction K U.Sections
        (isAffinoidAlgebra_sections K A hA U)
        (rebase_tupleInter_carrier_eq K A hA 𝒱 0 σ).ge))
      ((restriction K U.Sections
        (isAffinoidAlgebra_sections K A hA U)
        (((𝒱.rebase K A).cechFamily K U.Sections
          (isAffinoidAlgebra_sections K A hA U)).subset (σ 0))) s) =
    (restriction K A hA ((𝒱.cechFamily K A hA).subset (σ 0)))
      (((rebaseToSections K A hA Set.Subset.rfl).comp
        (restriction K U.Sections
          (isAffinoidAlgebra_sections K A hA U)
          (whole_carrier_eq_rebase_self K A).ge)) s)
  exact congrArg
    (fun φ : ContinuousAlgHom K (whole K U.Sections).Sections
      ((𝒱.cechFamily K A hA).tupleInter 0 σ).Sections ↦ φ s)
    (rebaseToSections_natural_of_carrier_eq K A hA
      Set.Subset.rfl
      ((𝒱.cechFamily K A hA).subset (σ 0))
      (whole_carrier_eq_rebase_self K A)
      (rebase_tupleInter_carrier_eq K A hA 𝒱 0 σ)
      (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).subset (σ 0))).symm

private theorem rebase_normalizedCoface_comm
    (𝒱 : Cover K A U) (n : ℕ) (i : Fin (n + 2)) :
    (rebaseNormalizedCechComponentLinearEquiv K A hA 𝒱
        (n + 2)).toLinearMap.comp
      (rebaseNormalizedCoface K A hA 𝒱 n i) =
    ((𝒱.cechFamily K A hA).normalizedCoface n i).comp
      (rebaseNormalizedCechComponentLinearEquiv K A hA 𝒱
        (n + 1)).toLinearMap := by
  apply LinearMap.ext
  intro s
  funext σ
  change
    (rebaseTupleInterSectionsLinearEquiv K A hA 𝒱 (n + 1) σ)
      (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).normalizedCoface n i s σ) =
    (𝒱.cechFamily K A hA).normalizedCoface n i
      (rebaseNormalizedCochainsLinearEquiv K A hA 𝒱 n s) σ
  change
    ((rebaseToSections K A hA
        (tupleInter_subset_ambient K A hA 𝒱 (n + 1) σ)).comp
      (restriction K U.Sections
        (isAffinoidAlgebra_sections K A hA U)
        (rebase_tupleInter_carrier_eq K A hA 𝒱 (n + 1) σ).ge))
      ((restriction K U.Sections
        (isAffinoidAlgebra_sections K A hA U)
        (Cech.Presheaf.Family.tupleInter_subset_strictDelete
          ((𝒱.rebase K A).cechFamily K U.Sections
            (isAffinoidAlgebra_sections K A hA U)) i σ)) (s _)) =
    (restriction K A hA
      ((𝒱.cechFamily K A hA).tupleInter_subset_strictDelete i σ)
      (((rebaseToSections K A hA
          (tupleInter_subset_ambient K A hA 𝒱 n
            ((𝒱.cechFamily K A hA).strictDelete i σ))).comp
        (restriction K U.Sections
          (isAffinoidAlgebra_sections K A hA U)
          (rebase_tupleInter_carrier_eq K A hA 𝒱 n
            ((𝒱.cechFamily K A hA).strictDelete i σ)).ge)) (s _)))
  exact congrArg
    (fun φ : ContinuousAlgHom K
      (((𝒱.rebase K A).cechFamily K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).tupleInter n
          (((𝒱.rebase K A).cechFamily K U.Sections
            (isAffinoidAlgebra_sections K A hA U)).strictDelete i σ)).Sections
      ((𝒱.cechFamily K A hA).tupleInter (n + 1) σ).Sections ↦ φ (s _))
    (rebaseToSections_natural_of_carrier_eq K A hA
      (tupleInter_subset_ambient K A hA 𝒱 n
        ((𝒱.cechFamily K A hA).strictDelete i σ))
      ((𝒱.cechFamily K A hA).tupleInter_subset_strictDelete i σ)
      (rebase_tupleInter_carrier_eq K A hA 𝒱 n
        ((𝒱.cechFamily K A hA).strictDelete i σ))
      (rebase_tupleInter_carrier_eq K A hA 𝒱 (n + 1) σ)
      (Cech.Presheaf.Family.tupleInter_subset_strictDelete
        ((𝒱.rebase K A).cechFamily K U.Sections
          (isAffinoidAlgebra_sections K A hA U)) i σ)).symm

private theorem rebase_normalizedDifferential_comm
    (𝒱 : Cover K A U) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (Cech.CofaceModule.differential
        (((𝒱.rebase K A).cechFamily K U.Sections
          (isAffinoidAlgebra_sections K A hA U)).normalizedCofaceModule) n)
      (rebaseNormalizedCochainsModuleIso K A hA 𝒱 (n + 1)).hom =
    CategoryTheory.CategoryStruct.comp
      (rebaseNormalizedCochainsModuleIso K A hA 𝒱 n).hom
      (Cech.CofaceModule.differential
        ((𝒱.cechFamily K A hA).normalizedCofaceModule) n) := by
  simp only [Cech.CofaceModule.differential,
    CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.zsmul_comp]
  rw [CategoryTheory.Preadditive.comp_sum]
  simp only [CategoryTheory.Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply ModuleCat.hom_ext
  dsimp only [rebaseNormalizedCochainsModuleIso]
  exact rebase_normalizedCoface_comm K A hA 𝒱 n k

/-- The augmented normalized Čech complex of a cover is canonically isomorphic to the complex of
the same cover rebased to the whole spectrum of the ambient section algebra. -/
noncomputable def rebaseNormalizedCechIso
    (𝒱 : Cover K A U) :
    (𝒱.rebase K A).normalizedCechComplex K U.Sections
        (isAffinoidAlgebra_sections K A hA U) ≅
      𝒱.normalizedCechComplex K A hA :=
  HomologicalComplex.Hom.isoOfComponents
    (rebaseNormalizedCechComponentIso K A hA 𝒱)
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      dsimp only [normalizedCechComplex]
      cases i with
      | zero =>
          apply ModuleCat.hom_ext
          dsimp only [rebaseNormalizedCechComponentIso]
          exact (rebase_normalizedAugmentation_comm K A hA 𝒱).symm
      | succ n =>
          simpa only [Cech.CofaceModule.Augmented.complex,
            CochainComplex.of_d, Cech.CofaceModule.Augmented.differential,
            rebaseNormalizedCechComponentIso] using
              (rebase_normalizedDifferential_comm K A hA 𝒱 n).symm)

/-- A rational cover is acyclic exactly when its rebase to the whole spectrum of `U.Sections`
is acyclic. -/
theorem normalizedCechComplex_acyclic_iff_rebase
    (𝒱 : Cover K A U) :
    (𝒱.normalizedCechComplex K A hA).Acyclic ↔
      ((𝒱.rebase K A).normalizedCechComplex K U.Sections
        (isAffinoidAlgebra_sections K A hA U)).Acyclic := by
  constructor
  · intro h n
    exact (h n).of_iso (rebaseNormalizedCechIso K A hA 𝒱).symm
  · intro h n
    exact (h n).of_iso (rebaseNormalizedCechIso K A hA 𝒱)

end AffinoidRationalSubdomain.Cover

end Rigid
