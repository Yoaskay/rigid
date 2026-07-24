import Rigid.Cech.Presheaf

set_option linter.style.header false

/-!
# Normalized finite Čech complexes

For a finite ordered family, the normalized Čech complex is indexed by strictly increasing
tuples.  Unlike the unnormalized complex, it is bounded by the cardinality of the family.  This is
the form used in the finite double-complex comparison argument and in the reduction of a
two-member Laurent cover to a short exact sequence.
-/

open CategoryTheory

universe u v w

namespace Rigid.Cech

variable (R : Type u) [Ring R]
variable {R}
variable {P : Presheaf.{u, v, w} R}

namespace Presheaf.Family

/-- A strictly increasing tuple of indices of length `n + 1`. -/
abbrev StrictTuple (𝒰 : P.Family) (n : ℕ) :=
  Fin (n + 1) ↪o Fin 𝒰.card

/-- Degree-`n` normalized Čech cochains. -/
abbrev NormalizedCochains (𝒰 : P.Family) (n : ℕ) :=
  ∀ σ : 𝒰.StrictTuple n, P.sections (𝒰.tupleInter n σ)

/-- Delete one entry from a strictly increasing tuple. -/
def strictDelete (𝒰 : P.Family) {n : ℕ} (i : Fin (n + 2))
    (σ : 𝒰.StrictTuple (n + 1)) : 𝒰.StrictTuple n :=
  i.succAboveOrderEmb.comp σ

/-- The full tuple intersection is contained in the intersection after deleting an entry. -/
theorem tupleInter_subset_strictDelete (𝒰 : P.Family) {n : ℕ} (i : Fin (n + 2))
    (σ : 𝒰.StrictTuple (n + 1)) :
    P.subset (𝒰.tupleInter (n + 1) σ)
      (𝒰.tupleInter n (𝒰.strictDelete i σ)) := by
  simpa only [strictDelete, OrderEmbedding.coe_comp, Function.comp_def,
    Fin.succAboveOrderEmb_apply] using
    𝒰.tupleInter_subset_precomp σ i.succAbove

/-- One normalized Čech coface map. -/
def normalizedCoface (𝒰 : P.Family) (n : ℕ) (i : Fin (n + 2)) :
    𝒰.NormalizedCochains n →ₗ[R] 𝒰.NormalizedCochains (n + 1) where
  toFun s σ :=
    P.restriction (𝒰.tupleInter_subset_strictDelete i σ)
      (s (𝒰.strictDelete i σ))
  map_add' _ _ := by
    ext σ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ
    exact map_smul _ _ _

private theorem strictDelete_strictDelete {n : ℕ} (𝒰 : P.Family)
    (i j : Fin (n + 2)) (hij : i ≤ j)
    (σ : 𝒰.StrictTuple (n + 2)) :
    𝒰.strictDelete i (𝒰.strictDelete j.succ σ) =
      𝒰.strictDelete j (𝒰.strictDelete i.castSucc σ) := by
  ext k
  simp only [strictDelete, OrderEmbedding.coe_comp, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  exact congrArg Fin.val (congrArg σ (by
    simpa only [SimplexCategory.δ, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      Fin.succAboveOrderEmb_apply] using
      SimplexCategory.congr_toOrderHom_apply
        (SimplexCategory.δ_comp_δ hij) k))

/-- The normalized Čech coface maps satisfy the cosimplicial identity. -/
theorem normalizedCoface_comp_normalizedCoface (𝒰 : P.Family) (n : ℕ)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    ModuleCat.ofHom (𝒰.normalizedCoface n i) ≫
        ModuleCat.ofHom (𝒰.normalizedCoface (n + 1) j.succ) =
      ModuleCat.ofHom (𝒰.normalizedCoface n j) ≫
        ModuleCat.ofHom (𝒰.normalizedCoface (n + 1) i.castSucc) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ
  change
    P.restriction _
        (P.restriction _ (s (𝒰.strictDelete i (𝒰.strictDelete j.succ σ)))) =
      P.restriction _
        (P.restriction _ (s (𝒰.strictDelete j (𝒰.strictDelete i.castSucc σ))))
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]
  have hθ :
      i.succAboveOrderEmb.comp j.succ.succAboveOrderEmb =
        j.succAboveOrderEmb.comp i.castSucc.succAboveOrderEmb := by
    ext k
    have hk := SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_δ hij) k
    have hk' := congrArg Fin.val hk
    change
      (j.succ.succAbove (i.succAbove k)).val =
        (i.castSucc.succAbove (j.succAbove k)).val
    simpa only [SimplexCategory.δ, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      Fin.succAboveOrderEmb_apply] using hk'
  convert congrArg
      (fun θ : Fin (n + 1) ↪o Fin (n + 1 + 1 + 1) ↦
        P.restriction
          (𝒰.tupleInter_subset_precomp (p := n) (q := n + 1 + 1) σ θ)
          (s (θ.comp σ))) hθ using 1 <;>
    simp only [strictDelete, OrderEmbedding.coe_comp, Function.comp_def] <;>
    congr 1

/-- The coface data underlying the normalized finite Čech complex. -/
noncomputable abbrev normalizedCofaceModule (𝒰 : P.Family) : CofaceModule R where
  X n := ModuleCat.of R (𝒰.NormalizedCochains n)
  δ n i := ModuleCat.ofHom (𝒰.normalizedCoface n i)
  δ_comp_δ := 𝒰.normalizedCoface_comp_normalizedCoface

/-- Restriction from the ambient domain to normalized degree-zero Čech cochains. -/
def normalizedAugmentation (𝒰 : P.Family) :
    P.sections 𝒰.ambient →ₗ[R] 𝒰.NormalizedCochains 0 where
  toFun s σ := P.restriction (𝒰.subset (σ 0)) s
  map_add' _ _ := by
    ext σ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ
    exact map_smul _ _ _

/-- The normalized augmentation followed by the two degree-zero cofaces agrees. -/
theorem normalizedAugmentation_comp (𝒰 : P.Family) :
    ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
        ModuleCat.ofHom (𝒰.normalizedCoface 0 0) =
      ModuleCat.ofHom 𝒰.normalizedAugmentation ≫
        ModuleCat.ofHom (𝒰.normalizedCoface 0 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ
  change
    (𝒰.normalizedCoface 0 0) (𝒰.normalizedAugmentation s) σ =
      (𝒰.normalizedCoface 0 1) (𝒰.normalizedAugmentation s) σ
  simp only [normalizedCoface, normalizedAugmentation, strictDelete,
    LinearMap.coe_mk, AddHom.coe_mk, OrderEmbedding.coe_comp, Function.comp_apply]
  change
    ((P.restriction _).comp (P.restriction _)) s =
      ((P.restriction _).comp (P.restriction _)) s
  rw [P.restriction_comp, P.restriction_comp]

/-- The augmented normalized coface data of a finite family. -/
noncomputable abbrev normalizedAugmentedCofaceModule (𝒰 : P.Family) :
    𝒰.normalizedCofaceModule.Augmented where
  augmentationObject := P.sections 𝒰.ambient
  ε := ModuleCat.ofHom 𝒰.normalizedAugmentation
  ε_comp := 𝒰.normalizedAugmentation_comp

/-- The augmented normalized Čech complex of a finite family. -/
noncomputable abbrev normalizedCechComplex (𝒰 : P.Family) :
    CochainComplex (ModuleCat R) ℕ :=
  𝒰.normalizedAugmentedCofaceModule.complex

@[simp]
theorem normalizedCechComplex_X_zero (𝒰 : P.Family) :
    𝒰.normalizedCechComplex.X 0 = P.sections 𝒰.ambient :=
  rfl

/-- Degree zero of the augmented normalized Čech complex is the module on the ambient domain. -/
noncomputable def normalizedCechComplexDegreeZeroIso (𝒰 : P.Family) :
    𝒰.normalizedCechComplex.X 0 ≅ P.sections 𝒰.ambient :=
  Iso.refl _

end Presheaf.Family

end Rigid.Cech
