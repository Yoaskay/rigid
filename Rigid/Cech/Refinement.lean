import Rigid.Cech.Presheaf

set_option linter.style.header false

/-!
# Maps of Čech complexes induced by refinements

A refinement chooses, for every member of a finer finite family, a containing member of the
coarser family.  Contravariance of the presheaf then gives the usual map from coarse Čech
cochains to fine Čech cochains.  This is the chain-level map used in the BGR double-complex
comparison argument.
-/

open CategoryTheory

universe u v w

namespace Rigid.Cech

variable {R : Type u} [Ring R]
variable {P : Presheaf.{u, v, w} R}

namespace Presheaf.Family

/-- A finite family `𝒱` refines `𝒰` if every member of `𝒱` is contained in a chosen member of
`𝒰`. -/
structure Refinement (𝒱 𝒰 : P.Family) where
  index : Fin 𝒱.card → Fin 𝒰.card
  subset : ∀ j, P.subset (𝒱.domain j) (𝒰.domain (index j))

namespace Refinement

variable {𝒲 𝒱 𝒰 : P.Family}

/-- Every finite family refines itself. -/
def refl (𝒰 : P.Family) : Refinement 𝒰 𝒰 where
  index := id
  subset _ := P.subset_refl _

/-- Refinements compose. -/
def trans (h𝒲𝒱 : Refinement 𝒲 𝒱) (h𝒱𝒰 : Refinement 𝒱 𝒰) :
    Refinement 𝒲 𝒰 where
  index := h𝒱𝒰.index ∘ h𝒲𝒱.index
  subset j := P.subset_trans (h𝒲𝒱.subset j) (h𝒱𝒰.subset (h𝒲𝒱.index j))

/-- An intersection in the finer family is contained in the corresponding intersection in the
coarser family. -/
theorem tupleInter_subset (r : Refinement 𝒱 𝒰) (n : ℕ)
    (σ : Fin (n + 1) → Fin 𝒱.card) :
    P.subset (𝒱.tupleInter n σ) (𝒰.tupleInter n (r.index ∘ σ)) := by
  apply 𝒰.subset_tupleInter
  intro i
  exact P.subset_trans (𝒱.tupleInter_subset_domain n σ i) (r.subset (σ i))

/-- Degreewise restriction of coarse Čech cochains to a refinement. -/
def cochainMap (r : Refinement 𝒱 𝒰) (n : ℕ) :
    𝒰.Cochains n →ₗ[R] 𝒱.Cochains n where
  toFun s σ := P.restriction (r.tupleInter_subset n σ) (s (r.index ∘ σ))
  map_add' _ _ := by
    ext σ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ
    exact map_smul _ _ _

/-- The refinement maps commute with every Čech coface map. -/
theorem cochainMap_comp_coface (r : Refinement 𝒱 𝒰) (n : ℕ)
    (i : Fin (n + 2)) :
    ModuleCat.ofHom (r.cochainMap n) ≫ ModuleCat.ofHom (𝒱.coface n i) =
      ModuleCat.ofHom (𝒰.coface n i) ≫ ModuleCat.ofHom (r.cochainMap (n + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ
  change
    P.restriction _ (P.restriction _
      (s (r.index ∘ (𝒱.delete i σ)))) =
    P.restriction _ (P.restriction _
      (s (𝒰.delete i (r.index ∘ σ))))
  change
    ((P.restriction _).comp (P.restriction _)) (s _) =
      ((P.restriction _).comp (P.restriction _)) (s _)
  rw [P.restriction_comp, P.restriction_comp]
  simp only [delete, Function.comp_def]
  congr 1

/-- The map of ordinary Čech complexes induced by a refinement. -/
noncomputable def complexMap (r : Refinement 𝒱 𝒰) :
    𝒰.cofaceModule.complex ⟶ 𝒱.cofaceModule.complex :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (r.cochainMap n))
    (fun n ↦ by
      simp only [CofaceModule.complex, CochainComplex.of_d,
        CofaceModule.differential]
      rw [Preadditive.comp_sum, Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      congr 1
      exact r.cochainMap_comp_coface n i)

end Refinement

end Presheaf.Family

end Rigid.Cech
