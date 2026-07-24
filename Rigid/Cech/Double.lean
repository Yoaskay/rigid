import Rigid.Cech.Normalized

set_option linter.style.header false

/-!
# Double normalized Čech cochains

This file constructs the two commuting systems of coface maps attached to a pair of finite
families.  These are the entries and the horizontal/vertical arrows of the double Čech complex
used in the refinement comparison theorem.
-/

open CategoryTheory

universe u v w

namespace Rigid.Cech

variable {R : Type u} [Ring R]
variable {P : Presheaf.{u, v, w} R}

namespace Presheaf.Family

/-- Bidegree `(p,q)` normalized cochains for two finite families over the same ambient domain. -/
abbrev DoubleCochains (𝒰 𝒱 : P.Family) (p q : ℕ) :=
  ∀ (σ : 𝒰.StrictTuple p) (τ : 𝒱.StrictTuple q),
    P.sections (P.inter (𝒰.tupleInter p σ) (𝒱.tupleInter q τ))

/-- Inclusion of a double intersection after deleting one horizontal index. -/
theorem doubleInter_subset_horizontalDelete (𝒰 𝒱 : P.Family) {p q : ℕ}
    (i : Fin (p + 2)) (σ : 𝒰.StrictTuple (p + 1)) (τ : 𝒱.StrictTuple q) :
    P.subset
      (P.inter (𝒰.tupleInter (p + 1) σ) (𝒱.tupleInter q τ))
      (P.inter (𝒰.tupleInter p (𝒰.strictDelete i σ)) (𝒱.tupleInter q τ)) := by
  apply P.subset_inter
  · exact P.subset_trans (P.inter_subset_left _ _)
      (𝒰.tupleInter_subset_strictDelete i σ)
  · exact P.inter_subset_right _ _

/-- Inclusion of a double intersection after deleting one vertical index. -/
theorem doubleInter_subset_verticalDelete (𝒰 𝒱 : P.Family) {p q : ℕ}
    (j : Fin (q + 2)) (σ : 𝒰.StrictTuple p) (τ : 𝒱.StrictTuple (q + 1)) :
    P.subset
      (P.inter (𝒰.tupleInter p σ) (𝒱.tupleInter (q + 1) τ))
      (P.inter (𝒰.tupleInter p σ) (𝒱.tupleInter q (𝒱.strictDelete j τ))) := by
  apply P.subset_inter
  · exact P.inter_subset_left _ _
  · exact P.subset_trans (P.inter_subset_right _ _)
      (𝒱.tupleInter_subset_strictDelete j τ)

/-- A horizontal coface in the normalized double Čech object. -/
def horizontalCoface (𝒰 𝒱 : P.Family) (p q : ℕ) (i : Fin (p + 2)) :
    DoubleCochains 𝒰 𝒱 p q →ₗ[R] DoubleCochains 𝒰 𝒱 (p + 1) q where
  toFun s σ τ :=
    P.restriction (doubleInter_subset_horizontalDelete 𝒰 𝒱 i σ τ)
      (s (𝒰.strictDelete i σ) τ)
  map_add' _ _ := by
    ext σ τ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ τ
    exact map_smul _ _ _

/-- A vertical coface in the normalized double Čech object. -/
def verticalCoface (𝒰 𝒱 : P.Family) (p q : ℕ) (j : Fin (q + 2)) :
    DoubleCochains 𝒰 𝒱 p q →ₗ[R] DoubleCochains 𝒰 𝒱 p (q + 1) where
  toFun s σ τ :=
    P.restriction (doubleInter_subset_verticalDelete 𝒰 𝒱 j σ τ)
      (s σ (𝒱.strictDelete j τ))
  map_add' _ _ := by
    ext σ τ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ τ
    exact map_smul _ _ _

/-- Horizontal cofaces satisfy the cosimplicial identity. -/
theorem horizontalCoface_comp_horizontalCoface (𝒰 𝒱 : P.Family) (p q : ℕ)
    (i j : Fin (p + 2)) (hij : i ≤ j) :
    ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p q i) ≫
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 (p + 1) q j.succ) =
      ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p q j) ≫
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 (p + 1) q i.castSucc) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    P.restriction _
        (P.restriction _
          (s (𝒰.strictDelete i (𝒰.strictDelete j.succ σ)) τ)) =
      P.restriction _
        (P.restriction _
          (s (𝒰.strictDelete j (𝒰.strictDelete i.castSucc σ)) τ))
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
      (fun θ : Fin (p + 1) ↪o Fin (p + 1 + 1 + 1) ↦
        P.restriction
          (P.subset_inter
            (P.subset_trans (P.inter_subset_left _ _)
              (𝒰.tupleInter_subset_precomp (p := p) (q := p + 1 + 1) σ θ))
            (P.inter_subset_right _ _))
          (s (θ.comp σ) τ)) hθ using 1 <;>
    simp only [strictDelete, OrderEmbedding.coe_comp, Function.comp_def] <;>
    congr 1

/-- Vertical cofaces satisfy the cosimplicial identity. -/
theorem verticalCoface_comp_verticalCoface (𝒰 𝒱 : P.Family) (p q : ℕ)
    (i j : Fin (q + 2)) (hij : i ≤ j) :
    ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p q i) ≫
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p (q + 1) j.succ) =
      ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p q j) ≫
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p (q + 1) i.castSucc) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    P.restriction _
        (P.restriction _
          (s σ (𝒱.strictDelete i (𝒱.strictDelete j.succ τ)))) =
      P.restriction _
        (P.restriction _
          (s σ (𝒱.strictDelete j (𝒱.strictDelete i.castSucc τ))))
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
      (fun θ : Fin (q + 1) ↪o Fin (q + 1 + 1 + 1) ↦
        P.restriction
          (P.subset_inter
            (P.inter_subset_left _ _)
            (P.subset_trans (P.inter_subset_right _ _)
              (𝒱.tupleInter_subset_precomp (p := q) (q := q + 1 + 1) τ θ)))
          (s σ (θ.comp τ))) hθ using 1 <;>
    simp only [strictDelete, OrderEmbedding.coe_comp, Function.comp_def] <;>
    congr 1

/-- Horizontal and vertical cofaces commute. -/
theorem horizontalCoface_comp_verticalCoface (𝒰 𝒱 : P.Family) (p q : ℕ)
    (i : Fin (p + 2)) (j : Fin (q + 2)) :
    ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p q i) ≫
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 (p + 1) q j) =
      ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p q j) ≫
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p (q + 1) i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    P.restriction _
        (P.restriction _ (s (𝒰.strictDelete i σ) (𝒱.strictDelete j τ))) =
      P.restriction _
        (P.restriction _ (s (𝒰.strictDelete i σ) (𝒱.strictDelete j τ)))
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

/-- Augment the horizontal direction by cochains of the vertical family. -/
def horizontalAugmentation (𝒰 𝒱 : P.Family) (q : ℕ) :
    𝒱.NormalizedCochains q →ₗ[R] DoubleCochains 𝒰 𝒱 0 q where
  toFun s σ τ :=
    P.restriction (P.inter_subset_right
      (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ)) (s τ)
  map_add' _ _ := by
    ext σ τ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ τ
    exact map_smul _ _ _

/-- Augment the vertical direction by cochains of the horizontal family. -/
def verticalAugmentation (𝒰 𝒱 : P.Family) (p : ℕ) :
    𝒰.NormalizedCochains p →ₗ[R] DoubleCochains 𝒰 𝒱 p 0 where
  toFun s σ τ :=
    P.restriction (P.inter_subset_left
      (𝒰.tupleInter p σ) (𝒱.tupleInter 0 τ)) (s σ)
  map_add' _ _ := by
    ext σ τ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ τ
    exact map_smul _ _ _

/-- Horizontal augmentation commutes with vertical cofaces. -/
theorem horizontalAugmentation_comp_verticalCoface
    (𝒰 𝒱 : P.Family) (q : ℕ) (j : Fin (q + 2)) :
    ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q) ≫
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 0 q j) =
      ModuleCat.ofHom (𝒱.normalizedCoface q j) ≫
        ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 (q + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    P.restriction _ (P.restriction _ (s (𝒱.strictDelete j τ))) =
      P.restriction _ (P.restriction _ (s (𝒱.strictDelete j τ)))
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

/-- Vertical augmentation commutes with horizontal cofaces. -/
theorem verticalAugmentation_comp_horizontalCoface
    (𝒰 𝒱 : P.Family) (p : ℕ) (i : Fin (p + 2)) :
    ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p) ≫
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p 0 i) =
      ModuleCat.ofHom (𝒰.normalizedCoface p i) ≫
        ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 (p + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    P.restriction _ (P.restriction _ (s (𝒰.strictDelete i σ))) =
      P.restriction _ (P.restriction _ (s (𝒰.strictDelete i σ)))
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

/-- The two degree-zero horizontal cofaces agree after horizontal augmentation. -/
theorem horizontalAugmentation_comp (𝒰 𝒱 : P.Family) (q : ℕ) :
    ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q) ≫
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 0 q 0) =
      ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q) ≫
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 0 q 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    P.restriction _ (P.restriction _ (s τ)) =
      P.restriction _ (P.restriction _ (s τ))
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

/-- The two degree-zero vertical cofaces agree after vertical augmentation. -/
theorem verticalAugmentation_comp (𝒰 𝒱 : P.Family) (p : ℕ) :
    ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p) ≫
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p 0 0) =
      ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p) ≫
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p 0 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ τ
  change
    P.restriction _ (P.restriction _ (s σ)) =
      P.restriction _ (P.restriction _ (s σ))
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

/-- The horizontal coface module in a fixed vertical degree. -/
noncomputable abbrev horizontalCofaceModule (𝒰 𝒱 : P.Family) (q : ℕ) :
    CofaceModule R where
  X p := ModuleCat.of R (DoubleCochains 𝒰 𝒱 p q)
  δ p i := ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p q i)
  δ_comp_δ := fun p i j hij ↦
    horizontalCoface_comp_horizontalCoface 𝒰 𝒱 p q i j hij

/-- The vertical coface module in a fixed horizontal degree. -/
noncomputable abbrev verticalCofaceModule (𝒰 𝒱 : P.Family) (p : ℕ) :
    CofaceModule R where
  X q := ModuleCat.of R (DoubleCochains 𝒰 𝒱 p q)
  δ q j := ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p q j)
  δ_comp_δ := fun q i j hij ↦
    verticalCoface_comp_verticalCoface 𝒰 𝒱 p q i j hij

/-- A horizontal row of the double Čech object, augmented by vertical cochains. -/
noncomputable abbrev horizontalAugmentedCofaceModule
    (𝒰 𝒱 : P.Family) (q : ℕ) :
    (horizontalCofaceModule 𝒰 𝒱 q).Augmented where
  augmentationObject := ModuleCat.of R (𝒱.NormalizedCochains q)
  ε := ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q)
  ε_comp := horizontalAugmentation_comp 𝒰 𝒱 q

/-- A vertical column of the double Čech object, augmented by horizontal cochains. -/
noncomputable abbrev verticalAugmentedCofaceModule
    (𝒰 𝒱 : P.Family) (p : ℕ) :
    (verticalCofaceModule 𝒰 𝒱 p).Augmented where
  augmentationObject := ModuleCat.of R (𝒰.NormalizedCochains p)
  ε := ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p)
  ε_comp := verticalAugmentation_comp 𝒰 𝒱 p

/-- Horizontal augmentation commutes with the vertical alternating differential. -/
theorem horizontalAugmentation_comp_verticalDifferential
    (𝒰 𝒱 : P.Family) (q : ℕ) :
    ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q) ≫
        (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
          ModuleCat.ofHom (verticalCoface 𝒰 𝒱 0 q j)) =
      (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
          ModuleCat.ofHom (𝒱.normalizedCoface q j)) ≫
        ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 (q + 1)) := by
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact horizontalAugmentation_comp_verticalCoface 𝒰 𝒱 q j

/-- Vertical augmentation commutes with the horizontal alternating differential. -/
theorem verticalAugmentation_comp_horizontalDifferential
    (𝒰 𝒱 : P.Family) (p : ℕ) :
    ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p) ≫
        (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p 0 i)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ModuleCat.ofHom (𝒰.normalizedCoface p i)) ≫
        ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 (p + 1)) := by
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact verticalAugmentation_comp_horizontalCoface 𝒰 𝒱 p i

/-- The map from vertical Čech cochains into horizontal degree zero of the double complex. -/
noncomputable def horizontalAugmentationHom (𝒰 𝒱 : P.Family) :
    𝒱.normalizedCofaceModule.complex ⟶
      (verticalCofaceModule 𝒰 𝒱 0).complex :=
  CochainComplex.ofHom
    (fun q ↦ ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q))
    (fun q ↦ by
      simpa only [CofaceModule.complex, CochainComplex.of_d,
        CofaceModule.differential] using
          horizontalAugmentation_comp_verticalDifferential 𝒰 𝒱 q)

/-- The map from horizontal Čech cochains into vertical degree zero of the double complex. -/
noncomputable def verticalAugmentationHom (𝒰 𝒱 : P.Family) :
    𝒰.normalizedCofaceModule.complex ⟶
      (horizontalCofaceModule 𝒰 𝒱 0).complex :=
  CochainComplex.ofHom
    (fun p ↦ ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p))
    (fun p ↦ by
      simpa only [CofaceModule.complex, CochainComplex.of_d,
        CofaceModule.differential] using
          verticalAugmentation_comp_horizontalDifferential 𝒰 𝒱 p)

/-- The horizontal and vertical alternating differentials commute. -/
theorem horizontalDifferential_comp_verticalDifferential
    (𝒰 𝒱 : P.Family) (p q : ℕ) :
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p q i)) ≫
      (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 (p + 1) q j)) =
    (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p q j)) ≫
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 p (q + 1) i)) := by
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 1
  exact horizontalCoface_comp_verticalCoface 𝒰 𝒱 p q i j

/-- The horizontal differential, regarded as a morphism between the vertical complexes. -/
noncomputable def horizontalDifferential (𝒰 𝒱 : P.Family) (p : ℕ) :
    (verticalCofaceModule 𝒰 𝒱 p).complex ⟶
      (verticalCofaceModule 𝒰 𝒱 (p + 1)).complex :=
  CochainComplex.ofHom
    (fun q ↦ (horizontalCofaceModule 𝒰 𝒱 q).differential p)
    (fun q ↦ by
      simpa only [CofaceModule.complex, CochainComplex.of_d,
        CofaceModule.differential] using
          horizontalDifferential_comp_verticalDifferential 𝒰 𝒱 p q)

/-- The normalized double Čech bicomplex of two finite families. -/
noncomputable def doubleComplex (𝒰 𝒱 : P.Family) :
    CochainComplex (CochainComplex (ModuleCat R) ℕ) ℕ :=
  CochainComplex.of
    (fun p ↦ (verticalCofaceModule 𝒰 𝒱 p).complex)
    (horizontalDifferential 𝒰 𝒱)
    (fun p ↦ by
      apply HomologicalComplex.Hom.ext
      apply funext
      intro q
      change
        (horizontalCofaceModule 𝒰 𝒱 q).differential p ≫
            (horizontalCofaceModule 𝒰 𝒱 q).differential (p + 1) = 0
      exact (horizontalCofaceModule 𝒰 𝒱 q).differential_comp p)

/-- The horizontal augmentation followed by the first horizontal differential is zero. -/
theorem horizontalAugmentationHom_comp_horizontalDifferential
    (𝒰 𝒱 : P.Family) :
    horizontalAugmentationHom 𝒰 𝒱 ≫ horizontalDifferential 𝒰 𝒱 0 = 0 := by
  apply HomologicalComplex.Hom.ext
  apply funext
  intro q
  change
    ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q) ≫
        (horizontalCofaceModule 𝒰 𝒱 q).differential 0 = 0
  rw [CofaceModule.differential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_zsmul, one_zsmul]
  change
    ModuleCat.ofHom (horizontalAugmentation 𝒰 𝒱 q) ≫
        (ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 0 q 0) +
          -ModuleCat.ofHom (horizontalCoface 𝒰 𝒱 0 q 1)) = 0
  rw [Preadditive.comp_add, Preadditive.comp_neg,
    horizontalAugmentation_comp 𝒰 𝒱 q, add_neg_cancel]

/-- Terms of the double Čech complex augmented in the horizontal direction. -/
noncomputable def horizontalAugmentedTerms (𝒰 𝒱 : P.Family) :
    ℕ → CochainComplex (ModuleCat R) ℕ
  | 0 => 𝒱.normalizedCofaceModule.complex
  | p + 1 => (verticalCofaceModule 𝒰 𝒱 p).complex

/-- Differential of the double Čech complex augmented in the horizontal direction. -/
noncomputable def horizontalAugmentedDifferential (𝒰 𝒱 : P.Family) :
    ∀ p, horizontalAugmentedTerms 𝒰 𝒱 p ⟶
      horizontalAugmentedTerms 𝒰 𝒱 (p + 1)
  | 0 => horizontalAugmentationHom 𝒰 𝒱
  | p + 1 => horizontalDifferential 𝒰 𝒱 p

/-- The horizontally augmented normalized double Čech bicomplex. -/
noncomputable def horizontalAugmentedDoubleComplex (𝒰 𝒱 : P.Family) :
    CochainComplex (CochainComplex (ModuleCat R) ℕ) ℕ :=
  CochainComplex.of
    (horizontalAugmentedTerms 𝒰 𝒱)
    (horizontalAugmentedDifferential 𝒰 𝒱)
    (fun p ↦ by
      cases p with
      | zero =>
          exact horizontalAugmentationHom_comp_horizontalDifferential 𝒰 𝒱
      | succ p =>
          apply HomologicalComplex.Hom.ext
          apply funext
          intro q
          change
            (horizontalCofaceModule 𝒰 𝒱 q).differential p ≫
                (horizontalCofaceModule 𝒰 𝒱 q).differential (p + 1) = 0
          exact (horizontalCofaceModule 𝒰 𝒱 q).differential_comp p)

/-- The vertical differential, regarded as a morphism between horizontal complexes. -/
noncomputable def verticalDifferential (𝒰 𝒱 : P.Family) (q : ℕ) :
    (horizontalCofaceModule 𝒰 𝒱 q).complex ⟶
      (horizontalCofaceModule 𝒰 𝒱 (q + 1)).complex :=
  CochainComplex.ofHom
    (fun p ↦ (verticalCofaceModule 𝒰 𝒱 p).differential q)
    (fun p ↦ by
      simpa only [CofaceModule.complex, CochainComplex.of_d,
        CofaceModule.differential] using
          (horizontalDifferential_comp_verticalDifferential 𝒰 𝒱 p q).symm)

/-- The vertical augmentation followed by the first vertical differential is zero. -/
theorem verticalAugmentationHom_comp_verticalDifferential
    (𝒰 𝒱 : P.Family) :
    verticalAugmentationHom 𝒰 𝒱 ≫ verticalDifferential 𝒰 𝒱 0 = 0 := by
  apply HomologicalComplex.Hom.ext
  apply funext
  intro p
  change
    ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p) ≫
        (verticalCofaceModule 𝒰 𝒱 p).differential 0 = 0
  rw [CofaceModule.differential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_zsmul, one_zsmul]
  change
    ModuleCat.ofHom (verticalAugmentation 𝒰 𝒱 p) ≫
        (ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p 0 0) +
          -ModuleCat.ofHom (verticalCoface 𝒰 𝒱 p 0 1)) = 0
  rw [Preadditive.comp_add, Preadditive.comp_neg,
    verticalAugmentation_comp 𝒰 𝒱 p, add_neg_cancel]

/-- Terms of the double Čech complex augmented in the vertical direction. -/
noncomputable def verticalAugmentedTerms (𝒰 𝒱 : P.Family) :
    ℕ → CochainComplex (ModuleCat R) ℕ
  | 0 => 𝒰.normalizedCofaceModule.complex
  | q + 1 => (horizontalCofaceModule 𝒰 𝒱 q).complex

/-- Differential of the double Čech complex augmented in the vertical direction. -/
noncomputable def verticalAugmentedDifferential (𝒰 𝒱 : P.Family) :
    ∀ q, verticalAugmentedTerms 𝒰 𝒱 q ⟶
      verticalAugmentedTerms 𝒰 𝒱 (q + 1)
  | 0 => verticalAugmentationHom 𝒰 𝒱
  | q + 1 => verticalDifferential 𝒰 𝒱 q

/-- The vertically augmented normalized double Čech bicomplex. -/
noncomputable def verticalAugmentedDoubleComplex (𝒰 𝒱 : P.Family) :
    CochainComplex (CochainComplex (ModuleCat R) ℕ) ℕ :=
  CochainComplex.of
    (verticalAugmentedTerms 𝒰 𝒱)
    (verticalAugmentedDifferential 𝒰 𝒱)
    (fun q ↦ by
      cases q with
      | zero =>
          exact verticalAugmentationHom_comp_verticalDifferential 𝒰 𝒱
      | succ q =>
          apply HomologicalComplex.Hom.ext
          apply funext
          intro p
          change
            (verticalCofaceModule 𝒰 𝒱 p).differential q ≫
                (verticalCofaceModule 𝒰 𝒱 p).differential (q + 1) = 0
          exact (verticalCofaceModule 𝒰 𝒱 p).differential_comp q)

end Presheaf.Family

end Rigid.Cech
