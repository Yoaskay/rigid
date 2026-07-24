import Rigid.AffinoidSpectrum.Cech
import Rigid.Cech.Fiber

set_option linter.style.header false

/-!
# Restrictions of rational covers

Intersecting every member of a rational cover with a rational subdomain gives a rational cover
of that subdomain.  Its normalized Čech complex is the fixed-subdomain fiber occurring in the
normalized double Čech complex.  This is the chain-level restriction identification used in
BGR 8.2.1, Comparison Theorem 2.
-/

open CategoryTheory

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

/-- Restrict a rational cover to a rational subdomain of its ambient domain. -/
noncomputable abbrev restrictTo
    {U : AffinoidRationalSubdomain K A} (𝒱 : Cover K A U)
    (W : AffinoidRationalSubdomain K A) (hWU : W.carrier ⊆ U.carrier) :
    Cover K A W where
  m := 𝒱.m
  domain j := inter K A W (𝒱.domain j)
  subset j := inter_subset_left K A W (𝒱.domain j)
  covers := by
    ext x
    constructor
    · intro hx
      rw [𝒱.covers] at hWU
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hWU hx)
      exact Set.mem_iUnion.mpr ⟨j, by
        rw [carrier_inter]
        exact ⟨hx, hxj⟩⟩
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      exact (by
        rw [carrier_inter] at hxj
        exact hxj.1)

@[simp]
theorem restrictTo_m
    {U : AffinoidRationalSubdomain K A} (𝒱 : Cover K A U)
    (W : AffinoidRationalSubdomain K A) (hWU : W.carrier ⊆ U.carrier) :
    (𝒱.restrictTo K A W hWU).m = 𝒱.m :=
  rfl

@[simp]
theorem restrictTo_domain
    {U : AffinoidRationalSubdomain K A} (𝒱 : Cover K A U)
    (W : AffinoidRationalSubdomain K A) (hWU : W.carrier ⊆ U.carrier)
    (j : Fin 𝒱.m) :
    (𝒱.restrictTo K A W hWU).domain j = inter K A W (𝒱.domain j) :=
  rfl

variable (hA : IsAffinoidAlgebra K A)
variable {U : AffinoidRationalSubdomain K A}

/-- Tuple intersections in a restricted cover have the same carrier as intersecting the fixed
subdomain with the corresponding tuple intersection of the original cover. -/
theorem restrictTo_tupleInter_carrier_eq
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) (n : ℕ)
    (τ : (𝒱.cechFamily K A hA).StrictTuple n) :
    (((𝒱.restrictTo K A W hWU).cechFamily K A hA).tupleInter n τ).carrier =
      (inter K A W ((𝒱.cechFamily K A hA).tupleInter n τ)).carrier := by
  induction n with
  | zero =>
      simp only [Cech.Presheaf.Family.tupleInter]
  | succ n ih =>
      simp only [Cech.Presheaf.Family.tupleInter, carrier_inter,
        Set.ext_iff, Set.mem_inter_iff] at ih ⊢
      intro x
      let τ₀ : (𝒱.cechFamily K A hA).StrictTuple n :=
        Fin.castSuccOrderEmb.comp τ
      have hi := ih τ₀ x
      change
        x ∈ (((𝒱.restrictTo K A W hWU).cechFamily K A hA).tupleInter n
            (fun i ↦ τ i.castSucc)).carrier ↔
          x ∈ W.carrier ∧
            x ∈ ((𝒱.cechFamily K A hA).tupleInter n
              (fun i ↦ τ i.castSucc)).carrier at hi
      rw [hi]
      constructor
      · rintro ⟨⟨hxW, hxTuple⟩, hxLast⟩
        exact ⟨hxW, hxTuple, hxLast.2⟩
      · rintro ⟨hxW, hxTuple, hxLast⟩
        exact ⟨⟨hxW, hxTuple⟩, hxW, hxLast⟩

/-- Sections on tuple intersections of a restricted cover are canonically equivalent to the
corresponding fixed-subdomain double-Čech fiber. -/
noncomputable def restrictToTupleInterSectionsLinearEquiv
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) (n : ℕ)
    (τ : (𝒱.restrictTo K A W hWU).cechFamily K A hA |>.StrictTuple n) :
    (((𝒱.restrictTo K A W hWU).cechFamily K A hA).tupleInter n τ).Sections ≃ₗ[K]
      (inter K A W ((𝒱.cechFamily K A hA).tupleInter n τ)).Sections :=
  sectionsLinearEquivOfCarrierEq K A hA _ _
    (restrictTo_tupleInter_carrier_eq K A hA 𝒱 W hWU n τ)

/-- Pointwise equivalence between normalized cochains of a restricted cover and fixed-subdomain
vertical fiber cochains. -/
noncomputable def restrictToNormalizedCochainsLinearEquiv
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) (n : ℕ) :
    ((𝒱.restrictTo K A W hWU).cechFamily K A hA).NormalizedCochains n ≃ₗ[K]
      (∀ τ : (𝒱.cechFamily K A hA).StrictTuple n,
        (inter K A W ((𝒱.cechFamily K A hA).tupleInter n τ)).Sections) :=
  LinearEquiv.piCongrRight (R := K) fun τ ↦
    restrictToTupleInterSectionsLinearEquiv K A hA 𝒱 W hWU n τ

private theorem restrictTo_normalizedAugmentation_comm
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) :
    (restrictToNormalizedCochainsLinearEquiv K A hA 𝒱 W hWU 0).toLinearMap.comp
        ((𝒱.restrictTo K A W hWU).cechFamily K A hA).normalizedAugmentation =
      Cech.Presheaf.Family.verticalFiberAugmentation
        (Cech.Presheaf.Family.singletonFamily
          (P := rationalPresheaf K A hA) W)
        (𝒱.cechFamily K A hA)
        (Cech.Presheaf.Family.singletonStrictTuple
          (P := rationalPresheaf K A hA) W) := by
  apply LinearMap.ext
  intro s
  funext τ
  change
    restriction K A hA _
        (restriction K A hA _ s) =
      restriction K A hA _ s
  rw [← ContinuousAlgHom.comp_apply, restriction_comp]

private theorem restrictTo_normalizedCoface_comm
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) (n : ℕ) (i : Fin (n + 2)) :
    (restrictToNormalizedCochainsLinearEquiv K A hA 𝒱 W hWU
        (n + 1)).toLinearMap.comp
      (((𝒱.restrictTo K A W hWU).cechFamily K A hA).normalizedCoface n i) =
    (Cech.Presheaf.Family.verticalFiberCoface
        (Cech.Presheaf.Family.singletonFamily
          (P := rationalPresheaf K A hA) W)
        (𝒱.cechFamily K A hA)
        (Cech.Presheaf.Family.singletonStrictTuple
          (P := rationalPresheaf K A hA) W) n i).comp
      (restrictToNormalizedCochainsLinearEquiv K A hA 𝒱 W hWU n).toLinearMap := by
  apply LinearMap.ext
  intro s
  funext τ
  change
    restriction K A hA _
        (restriction K A hA _ (s (i.succAboveOrderEmb.comp τ))) =
      restriction K A hA _
        (restriction K A hA _ (s (i.succAboveOrderEmb.comp τ)))
  rw [← ContinuousAlgHom.comp_apply, restriction_comp,
    ← ContinuousAlgHom.comp_apply, restriction_comp]

/-- The normalized cochains of a restricted rational cover and the corresponding fixed-domain
fiber are isomorphic as modules. -/
noncomputable def restrictToNormalizedCochainsModuleIso
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) (n : ℕ) :
    ((𝒱.restrictTo K A W hWU).cechFamily K A hA).normalizedCofaceModule.X n ≅
      (Cech.Presheaf.Family.fixedDomainCofaceModule
        (P := rationalPresheaf K A hA) W
        (𝒱.cechFamily K A hA)).X n :=
  (restrictToNormalizedCochainsLinearEquiv K A hA 𝒱 W hWU n).toModuleIso

private theorem restrictTo_normalizedDifferential_comm
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) (n : ℕ) :
    ((𝒱.restrictTo K A W hWU).cechFamily K A hA).normalizedCofaceModule.differential n ≫
        (restrictToNormalizedCochainsModuleIso K A hA 𝒱 W hWU (n + 1)).hom =
      (restrictToNormalizedCochainsModuleIso K A hA 𝒱 W hWU n).hom ≫
        (Cech.Presheaf.Family.fixedDomainCofaceModule
          (P := rationalPresheaf K A hA) W
          (𝒱.cechFamily K A hA)).differential n := by
  simp only [Cech.CofaceModule.differential,
    CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.zsmul_comp]
  rw [CategoryTheory.Preadditive.comp_sum]
  simp only [CategoryTheory.Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply ModuleCat.hom_ext
  exact restrictTo_normalizedCoface_comm K A hA 𝒱 W hWU n i

private noncomputable abbrev restrictToCechComponentIso
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) :
    ∀ n, (
      ((𝒱.restrictTo K A W hWU).normalizedCechComplex K A hA).X n ≅
        (Cech.Presheaf.Family.fixedDomainAugmentedCofaceModule
          (P := rationalPresheaf K A hA) W
          (𝒱.cechFamily K A hA)).complex.X n)
  | 0 => Iso.refl _
  | n + 1 => restrictToNormalizedCochainsModuleIso K A hA 𝒱 W hWU n

/-- The normalized Čech complex of a restricted rational cover is canonically isomorphic to the
fixed-domain augmented fiber of the double Čech complex. -/
noncomputable def restrictToNormalizedCechIso
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) :
    (𝒱.restrictTo K A W hWU).normalizedCechComplex K A hA ≅
      (Cech.Presheaf.Family.fixedDomainAugmentedCofaceModule
        (P := rationalPresheaf K A hA) W
        (𝒱.cechFamily K A hA)).complex :=
  HomologicalComplex.Hom.isoOfComponents
    (restrictToCechComponentIso K A hA 𝒱 W hWU)
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      dsimp only [normalizedCechComplex]
      cases i with
      | zero =>
          apply ModuleCat.hom_ext
          exact (restrictTo_normalizedAugmentation_comm K A hA 𝒱 W hWU).symm
      | succ n =>
          simpa only [Cech.CofaceModule.Augmented.complex,
            CochainComplex.of_d, Cech.CofaceModule.Augmented.differential,
            restrictToCechComponentIso] using
              (restrictTo_normalizedDifferential_comm K A hA 𝒱 W hWU n).symm)

/-- A rational cover restricted to a rational subdomain is acyclic exactly when the associated
fixed-domain fiber is acyclic. -/
theorem restrictTo_normalizedCechComplex_acyclic_iff
    (𝒱 : Cover K A U) (W : AffinoidRationalSubdomain K A)
    (hWU : W.carrier ⊆ U.carrier) :
    ((𝒱.restrictTo K A W hWU).normalizedCechComplex K A hA).Acyclic ↔
      (Cech.Presheaf.Family.fixedDomainAugmentedCofaceModule
        (P := rationalPresheaf K A hA) W
        (𝒱.cechFamily K A hA)).complex.Acyclic := by
  constructor
  · intro h n
    exact (h n).of_iso (restrictToNormalizedCechIso K A hA 𝒱 W hWU)
  · intro h n
    exact (h n).of_iso (restrictToNormalizedCechIso K A hA 𝒱 W hWU).symm

/-- If all restrictions of `𝒱` to the tuple intersections of `𝒰` are acyclic, then every
vertical column of the double Čech complex is acyclic. -/
theorem verticalAugmentedCofaceModule_acyclic_of_restrictTo
    (𝒰 𝒱 : Cover K A U) (p : ℕ)
    (hrestrict : ∀ σ : (𝒰.cechFamily K A hA).StrictTuple p,
      let W := (𝒰.cechFamily K A hA).tupleInter p σ
      let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
        ((𝒰.cechFamily K A hA).subset (σ 0))
      ((𝒱.restrictTo K A W hWU).normalizedCechComplex K A hA).Acyclic) :
    (Cech.Presheaf.Family.verticalAugmentedCofaceModule
      (𝒰.cechFamily K A hA) (𝒱.cechFamily K A hA) p).complex.Acyclic := by
  apply Cech.Presheaf.Family.verticalAugmentedCofaceModule_acyclic_of_fibers
  intro σ
  let W := (𝒰.cechFamily K A hA).tupleInter p σ
  let hWU := ((𝒰.cechFamily K A hA).tupleInter_subset_domain p σ 0).trans
    ((𝒰.cechFamily K A hA).subset (σ 0))
  have hfixed :=
    (restrictTo_normalizedCechComplex_acyclic_iff K A hA 𝒱 W hWU).1
      (hrestrict σ)
  exact hfixed

end AffinoidRationalSubdomain.Cover

end Rigid
