import Rigid.Cech.Double

set_option linter.style.header false

/-!
# Transposing the normalized double Čech complex

The vertical augmented complex for `(𝒰,𝒱)` is canonically isomorphic to the horizontal
augmented complex for `(𝒱,𝒰)`.  Since the abstract presheaf only supplies a chosen binary
intersection, the isomorphism explicitly restricts between `U ∩ V` and `V ∩ U`.
-/

open CategoryTheory

universe u v w

namespace Rigid.Cech

variable {K : Type u} [Field K]
variable {P : Presheaf.{u, v, w} K}

namespace Presheaf

/-- The two chosen orders of a binary intersection are mutually contained. -/
theorem inter_swap_subset (U V : P.Domain) :
    P.subset (P.inter V U) (P.inter U V) :=
  P.subset_inter (P.inter_subset_right V U) (P.inter_subset_left V U)

/-- Sections on the two chosen orders of a binary intersection are canonically equivalent. -/
noncomputable def interSectionsSwap (U V : P.Domain) :
    P.sections (P.inter U V) ≃ₗ[K] P.sections (P.inter V U) where
  toFun := P.restriction (P.inter_swap_subset U V)
  invFun := P.restriction (P.inter_swap_subset V U)
  left_inv x := by
    rw [← LinearMap.comp_apply, P.restriction_comp]
    simpa only [LinearMap.id_apply] using congrArg
      (fun f : P.sections (P.inter U V) →ₗ[K] P.sections (P.inter U V) ↦ f x)
      (P.restriction_id (P.inter U V))
  right_inv x := by
    rw [← LinearMap.comp_apply, P.restriction_comp]
    simpa only [LinearMap.id_apply] using congrArg
      (fun f : P.sections (P.inter V U) →ₗ[K] P.sections (P.inter V U) ↦ f x)
      (P.restriction_id (P.inter V U))
  map_add' := map_add _
  map_smul' := map_smul _

namespace Family

/-- Transpose double cochains and swap the two intersection factors. -/
noncomputable def doubleCochainsSwap (𝒰 𝒱 : P.Family) (p q : ℕ) :
    DoubleCochains 𝒰 𝒱 p q ≃ₗ[K] DoubleCochains 𝒱 𝒰 q p where
  toFun s τ σ :=
    P.interSectionsSwap (𝒰.tupleInter p σ) (𝒱.tupleInter q τ) (s σ τ)
  invFun s σ τ :=
    (P.interSectionsSwap (𝒰.tupleInter p σ) (𝒱.tupleInter q τ)).symm (s τ σ)
  left_inv s := by
    funext σ τ
    exact (P.interSectionsSwap
      (𝒰.tupleInter p σ) (𝒱.tupleInter q τ)).left_inv (s σ τ)
  right_inv s := by
    funext τ σ
    exact (P.interSectionsSwap
      (𝒰.tupleInter p σ) (𝒱.tupleInter q τ)).right_inv (s τ σ)
  map_add' x y := by
    funext τ σ
    exact map_add _ _ _
  map_smul' a x := by
    funext τ σ
    exact map_smul _ _ _

theorem verticalAugmentation_doubleCochainsSwap
    (𝒰 𝒱 : P.Family) (p : ℕ) :
    (doubleCochainsSwap 𝒰 𝒱 p 0).toLinearMap.comp
        (verticalAugmentation 𝒰 𝒱 p) =
      horizontalAugmentation 𝒱 𝒰 p := by
  apply LinearMap.ext
  intro s
  funext τ σ
  simp only [LinearMap.comp_apply, doubleCochainsSwap, interSectionsSwap,
    verticalAugmentation, horizontalAugmentation]
  change P.restriction _ (P.restriction _ (s σ)) =
    P.restriction _ (s σ)
  rw [← LinearMap.comp_apply, P.restriction_comp]

theorem verticalCoface_doubleCochainsSwap
    (𝒰 𝒱 : P.Family) (p q : ℕ) (j : Fin (q + 2)) :
    (doubleCochainsSwap 𝒰 𝒱 p (q + 1)).toLinearMap.comp
        (verticalCoface 𝒰 𝒱 p q j) =
      (horizontalCoface 𝒱 𝒰 q p j).comp
        (doubleCochainsSwap 𝒰 𝒱 p q).toLinearMap := by
  apply LinearMap.ext
  intro s
  funext τ σ
  simp only [LinearMap.comp_apply, doubleCochainsSwap, interSectionsSwap,
    verticalCoface, horizontalCoface]
  change P.restriction _ (P.restriction _
      (s σ (𝒱.strictDelete j τ))) =
    P.restriction _ (P.restriction _
      (s σ (𝒱.strictDelete j τ)))
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

theorem verticalDifferential_doubleCochainsSwap
    (𝒰 𝒱 : P.Family) (p q : ℕ) :
    (verticalCofaceModule 𝒰 𝒱 p).differential q ≫
        ModuleCat.ofHom
          (doubleCochainsSwap 𝒰 𝒱 p (q + 1)).toLinearMap =
      ModuleCat.ofHom (doubleCochainsSwap 𝒰 𝒱 p q).toLinearMap ≫
        (horizontalCofaceModule 𝒱 𝒰 p).differential q := by
  simp only [CofaceModule.differential, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply ModuleCat.hom_ext
  exact verticalCoface_doubleCochainsSwap 𝒰 𝒱 p q j

/-- The transposition equivalence as an isomorphism of module objects. -/
noncomputable def doubleCochainsSwapModuleIso
    (𝒰 𝒱 : P.Family) (p q : ℕ) :
    (verticalCofaceModule 𝒰 𝒱 p).X q ≅
      (horizontalCofaceModule 𝒱 𝒰 p).X q :=
  (doubleCochainsSwap 𝒰 𝒱 p q).toModuleIso

noncomputable abbrev verticalAugmentedCofaceModuleComponentIso
    (𝒰 𝒱 : P.Family) (p : ℕ) :
    ∀ n,
      (verticalAugmentedCofaceModule 𝒰 𝒱 p).complex.X n ≅
        (horizontalAugmentedCofaceModule 𝒱 𝒰 p).complex.X n
  | 0 => Iso.refl _
  | q + 1 => doubleCochainsSwapModuleIso 𝒰 𝒱 p q

/-- Transposition identifies a vertical augmented complex with the corresponding horizontal
augmented complex for the swapped pair. -/
noncomputable def verticalAugmentedCofaceModuleIso
    (𝒰 𝒱 : P.Family) (p : ℕ) :
    (verticalAugmentedCofaceModule 𝒰 𝒱 p).complex ≅
      (horizontalAugmentedCofaceModule 𝒱 𝒰 p).complex :=
  HomologicalComplex.Hom.isoOfComponents
    (verticalAugmentedCofaceModuleComponentIso 𝒰 𝒱 p)
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      cases i with
      | zero =>
          apply ModuleCat.hom_ext
          dsimp only [verticalAugmentedCofaceModuleComponentIso,
            CofaceModule.Augmented.complex, CochainComplex.of_d,
            CofaceModule.Augmented.differential]
          exact (verticalAugmentation_doubleCochainsSwap 𝒰 𝒱 p).symm
      | succ q =>
          dsimp only [verticalAugmentedCofaceModuleComponentIso,
            doubleCochainsSwapModuleIso, CofaceModule.Augmented.complex,
            CochainComplex.of_d, CofaceModule.Augmented.differential]
          simp only [CochainComplex.of_d, LinearEquiv.toModuleIso_hom]
          change
            ModuleCat.ofHom
                (doubleCochainsSwap 𝒰 𝒱 p q).toLinearMap ≫
                (horizontalCofaceModule 𝒱 𝒰 p).differential q =
              (verticalCofaceModule 𝒰 𝒱 p).differential q ≫
                ModuleCat.ofHom
                  (doubleCochainsSwap 𝒰 𝒱 p (q + 1)).toLinearMap
          exact (verticalDifferential_doubleCochainsSwap 𝒰 𝒱 p q).symm)

end Family

end Presheaf

end Rigid.Cech
