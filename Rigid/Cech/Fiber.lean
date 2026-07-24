import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Rigid.Cech.Double

set_option linter.style.header false

/-!
# Fibers of the normalized double Čech complex

A vertical column is the product, over horizontal tuples, of augmented Čech complexes on the
corresponding fixed intersections.  This file makes those fiber complexes explicit and proves
that a product of acyclic fibers is acyclic.
-/

open CategoryTheory

universe u v w

namespace Rigid.Cech

variable {K : Type u} [Field K]
variable {P : Presheaf.{u, v, w} K}

namespace Presheaf.Family

/-- The one-member family consisting of a fixed domain. -/
noncomputable abbrev singletonFamily (W : P.Domain) : P.Family where
  ambient := W
  card := 1
  domain _ := W
  subset _ := P.subset_refl W

/-- The unique normalized zero-tuple in the one-member family. -/
def singletonStrictTuple (W : P.Domain) :
    (singletonFamily (P := P) W).StrictTuple 0 :=
  OrderEmbedding.id _

/-- Vertical cochains with one horizontal tuple fixed. -/
abbrev VerticalFiberCochains (𝒰 𝒱 : P.Family) {p : ℕ}
    (σ : 𝒰.StrictTuple p) (q : ℕ) :=
  ∀ τ : 𝒱.StrictTuple q,
    P.sections (P.inter (𝒰.tupleInter p σ) (𝒱.tupleInter q τ))

/-- A vertical coface with the horizontal tuple fixed. -/
def verticalFiberCoface (𝒰 𝒱 : P.Family) {p : ℕ}
    (σ : 𝒰.StrictTuple p) (q : ℕ) (j : Fin (q + 2)) :
    VerticalFiberCochains 𝒰 𝒱 σ q →ₗ[K]
      VerticalFiberCochains 𝒰 𝒱 σ (q + 1) where
  toFun s τ :=
    P.restriction (doubleInter_subset_verticalDelete 𝒰 𝒱 j σ τ)
      (s (𝒱.strictDelete j τ))
  map_add' _ _ := by
    funext τ
    exact map_add _ _ _
  map_smul' _ _ := by
    funext τ
    exact map_smul _ _ _

theorem verticalFiberCoface_comp (𝒰 𝒱 : P.Family) {p : ℕ}
    (σ : 𝒰.StrictTuple p) (q : ℕ)
    (i j : Fin (q + 2)) (hij : i ≤ j) :
    ModuleCat.ofHom (verticalFiberCoface 𝒰 𝒱 σ q i) ≫
        ModuleCat.ofHom (verticalFiberCoface 𝒰 𝒱 σ (q + 1) j.succ) =
      ModuleCat.ofHom (verticalFiberCoface 𝒰 𝒱 σ q j) ≫
        ModuleCat.ofHom (verticalFiberCoface 𝒰 𝒱 σ (q + 1) i.castSucc) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext τ
  change
    P.restriction _
        (P.restriction _
          (s (𝒱.strictDelete i (𝒱.strictDelete j.succ τ)))) =
      P.restriction _
        (P.restriction _
          (s (𝒱.strictDelete j (𝒱.strictDelete i.castSucc τ))))
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
          (s (θ.comp τ))) hθ using 1 <;>
    simp only [strictDelete, OrderEmbedding.coe_comp, Function.comp_def] <;>
    congr 1

noncomputable abbrev verticalFiberCofaceModule
    (𝒰 𝒱 : P.Family) {p : ℕ} (σ : 𝒰.StrictTuple p) :
    CofaceModule K where
  X q := ModuleCat.of K (VerticalFiberCochains 𝒰 𝒱 σ q)
  δ q j := ModuleCat.ofHom (verticalFiberCoface 𝒰 𝒱 σ q j)
  δ_comp_δ := verticalFiberCoface_comp 𝒰 𝒱 σ

/-- Fiberwise vertical augmentation. -/
def verticalFiberAugmentation (𝒰 𝒱 : P.Family) {p : ℕ}
    (σ : 𝒰.StrictTuple p) :
    P.sections (𝒰.tupleInter p σ) →ₗ[K]
      VerticalFiberCochains 𝒰 𝒱 σ 0 where
  toFun s τ :=
    P.restriction
      (P.inter_subset_left (𝒰.tupleInter p σ) (𝒱.tupleInter 0 τ)) s
  map_add' _ _ := by
    funext τ
    exact map_add _ _ _
  map_smul' _ _ := by
    funext τ
    exact map_smul _ _ _

theorem verticalFiberAugmentation_comp (𝒰 𝒱 : P.Family) {p : ℕ}
    (σ : 𝒰.StrictTuple p) :
    ModuleCat.ofHom (verticalFiberAugmentation 𝒰 𝒱 σ) ≫
        ModuleCat.ofHom (verticalFiberCoface 𝒰 𝒱 σ 0 0) =
      ModuleCat.ofHom (verticalFiberAugmentation 𝒰 𝒱 σ) ≫
        ModuleCat.ofHom (verticalFiberCoface 𝒰 𝒱 σ 0 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext τ
  change P.restriction _ (P.restriction _ s) =
    P.restriction _ (P.restriction _ s)
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

noncomputable abbrev verticalFiberAugmentedCofaceModule
    (𝒰 𝒱 : P.Family) {p : ℕ} (σ : 𝒰.StrictTuple p) :
    (verticalFiberCofaceModule 𝒰 𝒱 σ).Augmented where
  augmentationObject := P.sections (𝒰.tupleInter p σ)
  ε := ModuleCat.ofHom (verticalFiberAugmentation 𝒰 𝒱 σ)
  ε_comp := verticalFiberAugmentation_comp 𝒰 𝒱 σ

/-- The normalized coface module obtained by restricting a family to a fixed domain. -/
noncomputable abbrev fixedDomainCofaceModule
    (W : P.Domain) (𝒱 : P.Family) :
    CofaceModule K :=
  verticalFiberCofaceModule
    (singletonFamily (P := P) W) 𝒱 (singletonStrictTuple (P := P) W)

/-- The augmented normalized Čech fiber obtained by restricting a family to a fixed domain. -/
noncomputable abbrev fixedDomainAugmentedCofaceModule
    (W : P.Domain) (𝒱 : P.Family) :
    (fixedDomainCofaceModule (P := P) W 𝒱).Augmented :=
  verticalFiberAugmentedCofaceModule
    (singletonFamily (P := P) W) 𝒱 (singletonStrictTuple (P := P) W)

theorem verticalDifferential_apply_fiber
    (𝒰 𝒱 : P.Family) (p q : ℕ)
    (x : DoubleCochains 𝒰 𝒱 p q) (σ : 𝒰.StrictTuple p)
    (τ : 𝒱.StrictTuple (q + 1)) :
    ((verticalCofaceModule 𝒰 𝒱 p).differential q).hom x σ τ =
      ((verticalFiberCofaceModule 𝒰 𝒱 σ).differential q).hom
        (fun τ ↦ x σ τ) τ := by
  rw [CofaceModule.differential, CofaceModule.differential]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom,
    LinearMap.sum_apply, Finset.sum_apply]
  rfl

/-- A vertical column is acyclic if every fixed-horizontal-tuple fiber is acyclic. -/
theorem verticalAugmentedCofaceModule_acyclic_of_fibers
    (𝒰 𝒱 : P.Family) (p : ℕ)
    (hfiber : ∀ σ : 𝒰.StrictTuple p,
      (verticalFiberAugmentedCofaceModule 𝒰 𝒱 σ).complex.Acyclic) :
    (verticalAugmentedCofaceModule 𝒰 𝒱 p).complex.Acyclic := by
  intro n
  rcases n with _ | _ | n
  · rw [(verticalAugmentedCofaceModule 𝒰 𝒱 p).complex.exactAt_iff'
      0 0 1 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ x : 𝒰.NormalizedCochains p,
      verticalAugmentation 𝒰 𝒱 p x = 0 →
        ∃ y : 𝒰.NormalizedCochains p, 0 = x
    intro x hx
    refine ⟨0, ?_⟩
    funext σ
    have hs := hfiber σ 0
    rw [(verticalFiberAugmentedCofaceModule 𝒰 𝒱 σ).complex.exactAt_iff'
      0 0 1 (by simp) (by simp)] at hs
    rw [ShortComplex.moduleCat_exact_iff] at hs
    change ∀ z : P.sections (𝒰.tupleInter p σ),
      verticalFiberAugmentation 𝒰 𝒱 σ z = 0 →
        ∃ y : P.sections (𝒰.tupleInter p σ), 0 = z at hs
    have hxσ : verticalFiberAugmentation 𝒰 𝒱 σ (x σ) = 0 := by
      funext τ
      exact congrFun (congrFun hx σ) τ
    obtain ⟨_, hzero⟩ := hs (x σ) hxσ
    exact hzero
  · rw [(verticalAugmentedCofaceModule 𝒰 𝒱 p).complex.exactAt_iff'
      0 1 2 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ x : DoubleCochains 𝒰 𝒱 p 0,
      ((verticalCofaceModule 𝒰 𝒱 p).differential 0).hom x = 0 →
        ∃ y : 𝒰.NormalizedCochains p,
          verticalAugmentation 𝒰 𝒱 p y = x
    intro x hx
    have hexists : ∀ σ : 𝒰.StrictTuple p,
        ∃ y : P.sections (𝒰.tupleInter p σ),
          verticalFiberAugmentation 𝒰 𝒱 σ y = fun τ ↦ x σ τ := by
      intro σ
      have hs := hfiber σ 1
      rw [(verticalFiberAugmentedCofaceModule 𝒰 𝒱 σ).complex.exactAt_iff'
        0 1 2 (by simp) (by simp)] at hs
      rw [ShortComplex.moduleCat_exact_iff] at hs
      change ∀ z : VerticalFiberCochains 𝒰 𝒱 σ 0,
        ((verticalFiberCofaceModule 𝒰 𝒱 σ).differential 0).hom z = 0 →
          ∃ y : P.sections (𝒰.tupleInter p σ),
            verticalFiberAugmentation 𝒰 𝒱 σ y = z at hs
      apply hs (fun τ ↦ x σ τ)
      funext τ
      rw [← verticalDifferential_apply_fiber 𝒰 𝒱 p 0 x σ τ]
      exact congrFun (congrFun hx σ) τ
    choose y hy using hexists
    exact ⟨y, by funext σ τ; exact congrFun (hy σ) τ⟩
  · rw [(verticalAugmentedCofaceModule 𝒰 𝒱 p).complex.exactAt_iff'
      (n + 1) ((n + 1) + 1) (((n + 1) + 1) + 1) (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
      HomologicalComplex.shortComplexFunctor'_obj_g, CochainComplex.of_d]
    dsimp only [CofaceModule.Augmented.terms,
      CofaceModule.Augmented.differential]
    change ∀ x : DoubleCochains 𝒰 𝒱 p (n + 1),
      ((verticalCofaceModule 𝒰 𝒱 p).differential (n + 1)).hom x = 0 →
        ∃ y : DoubleCochains 𝒰 𝒱 p n,
          ((verticalCofaceModule 𝒰 𝒱 p).differential n).hom y = x
    intro x hx
    have hexists : ∀ σ : 𝒰.StrictTuple p,
        ∃ y : VerticalFiberCochains 𝒰 𝒱 σ n,
          ((verticalFiberCofaceModule 𝒰 𝒱 σ).differential n).hom y =
            fun τ ↦ x σ τ := by
      intro σ
      have hs := hfiber σ (n + 2)
      rw [(verticalFiberAugmentedCofaceModule 𝒰 𝒱 σ).complex.exactAt_iff'
        (n + 1) ((n + 1) + 1) (((n + 1) + 1) + 1)
        (by simp) (by simp)] at hs
      rw [ShortComplex.moduleCat_exact_iff] at hs
      simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g, CochainComplex.of_d] at hs
      dsimp only [CofaceModule.Augmented.terms,
        CofaceModule.Augmented.differential] at hs
      change ∀ z : VerticalFiberCochains 𝒰 𝒱 σ (n + 1),
        ((verticalFiberCofaceModule 𝒰 𝒱 σ).differential (n + 1)).hom z = 0 →
          ∃ y : VerticalFiberCochains 𝒰 𝒱 σ n,
            ((verticalFiberCofaceModule 𝒰 𝒱 σ).differential n).hom y = z at hs
      apply hs (fun τ ↦ x σ τ)
      funext τ
      rw [← verticalDifferential_apply_fiber 𝒰 𝒱 p (n + 1) x σ τ]
      exact congrFun (congrFun hx σ) τ
    choose y hy using hexists
    exact ⟨fun σ τ ↦ y σ τ, by
      funext σ τ
      rw [verticalDifferential_apply_fiber 𝒰 𝒱 p n
        (fun σ τ ↦ y σ τ) σ τ]
      exact congrFun (hy σ) τ⟩

end Presheaf.Family

end Rigid.Cech
