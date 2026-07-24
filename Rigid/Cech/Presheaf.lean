import Rigid.Cech.Coface

set_option linter.style.header false

/-!
# Finite Čech complexes of a presheaf

This file constructs the augmented Čech complex of a finite family in a category of domains with
finite intersections.  We use all ordered tuples (including repetitions); this is the standard
unnormalized Čech complex.  The construction is deliberately independent of rigid geometry so the
same refinement and comparison arguments can be reused for restricted covers.
-/

open CategoryTheory

open scoped BigOperators

universe u v w

namespace Rigid.Cech

variable (R : Type u) [Ring R]

/-- The part of a contravariant module-valued presheaf needed to form finite Čech complexes.

`subset V U` means that `V` is a subdomain of `U`.  Antisymmetry is intentionally not required:
two rational data may cut out the same point set without being equal as bundled data. -/
structure Presheaf where
  Domain : Type v
  subset : Domain → Domain → Prop
  subset_refl (U : Domain) : subset U U
  subset_trans {U V W : Domain} : subset W V → subset V U → subset W U
  inter : Domain → Domain → Domain
  inter_subset_left (U V : Domain) : subset (inter U V) U
  inter_subset_right (U V : Domain) : subset (inter U V) V
  subset_inter {U V W : Domain} : subset W U → subset W V → subset W (inter U V)
  sections : Domain → ModuleCat.{w} R
  restriction {U V : Domain} : subset V U → sections U →ₗ[R] sections V
  restriction_id (U : Domain) :
    restriction (subset_refl U) = LinearMap.id
  restriction_comp {U V W : Domain} (hVU : subset V U) (hWV : subset W V) :
    (restriction hWV).comp (restriction hVU) =
      restriction (subset_trans hWV hVU)

namespace Presheaf

variable {R}

/-- A finite family of subdomains of an ambient domain.  The covering condition is not needed to
form the complex and is therefore kept by the geometric layer. -/
structure Family (P : Presheaf R) where
  ambient : P.Domain
  card : ℕ
  domain : Fin card → P.Domain
  subset : ∀ i, P.subset (domain i) ambient

variable {P : Presheaf R}

namespace Family

/-- The intersection indexed by a nonempty ordered tuple. -/
def tupleInter (𝒰 : P.Family) :
    ∀ n : ℕ, (Fin (n + 1) → Fin 𝒰.card) → P.Domain
  | 0, σ => 𝒰.domain (σ 0)
  | n + 1, σ =>
      P.inter
        (tupleInter 𝒰 n (fun i ↦ σ i.castSucc))
        (𝒰.domain (σ (Fin.last (n + 1))))

/-- A tuple intersection is contained in each domain occurring in the tuple. -/
theorem tupleInter_subset_domain (𝒰 : P.Family) (n : ℕ)
    (σ : Fin (n + 1) → Fin 𝒰.card) (i : Fin (n + 1)) :
    P.subset (𝒰.tupleInter n σ) (𝒰.domain (σ i)) := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact P.subset_refl _
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact P.inter_subset_right _ _
      · exact P.subset_trans (P.inter_subset_left _ _) (ih _ j)

/-- A domain contained in every member of a tuple is contained in their intersection. -/
theorem subset_tupleInter (𝒰 : P.Family) {W : P.Domain} (n : ℕ)
    (σ : Fin (n + 1) → Fin 𝒰.card)
    (h : ∀ i, P.subset W (𝒰.domain (σ i))) :
    P.subset W (𝒰.tupleInter n σ) := by
  induction n with
  | zero =>
      simpa only [tupleInter] using h 0
  | succ n ih =>
      apply P.subset_inter
      · apply ih
        intro i
        exact h i.castSucc
      · exact h (Fin.last (n + 1))

/-- Intersecting all entries of a tuple gives a subdomain of the intersection indexed by any
precomposition of that tuple. -/
theorem tupleInter_subset_precomp (𝒰 : P.Family) {p q : ℕ}
    (σ : Fin (q + 1) → Fin 𝒰.card) (θ : Fin (p + 1) → Fin (q + 1)) :
    P.subset (𝒰.tupleInter q σ) (𝒰.tupleInter p (σ ∘ θ)) := by
  apply 𝒰.subset_tupleInter
  intro i
  exact 𝒰.tupleInter_subset_domain q σ (θ i)

/-- Degree-`n` unnormalized Čech cochains. -/
abbrev Cochains (𝒰 : P.Family) (n : ℕ) :=
  ∀ σ : Fin (n + 1) → Fin 𝒰.card, P.sections (𝒰.tupleInter n σ)

/-- Delete one entry from a tuple. -/
def delete (𝒰 : P.Family) {n : ℕ} (i : Fin (n + 2))
    (σ : Fin (n + 2) → Fin 𝒰.card) : Fin (n + 1) → Fin 𝒰.card :=
  σ ∘ i.succAbove

/-- One Čech coface map: delete an index and restrict to the full intersection. -/
def coface (𝒰 : P.Family) (n : ℕ) (i : Fin (n + 2)) :
    𝒰.Cochains n →ₗ[R] 𝒰.Cochains (n + 1) where
  toFun s σ :=
    P.restriction (𝒰.tupleInter_subset_precomp σ i.succAbove) (s (𝒰.delete i σ))
  map_add' _ _ := by
    ext σ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ
    exact map_smul _ _ _

private theorem delete_delete {n : ℕ} (𝒰 : P.Family)
    (i j : Fin (n + 2)) (hij : i ≤ j)
    (σ : Fin (n + 3) → Fin 𝒰.card) :
    𝒰.delete i (𝒰.delete j.succ σ) =
      𝒰.delete j (𝒰.delete i.castSucc σ) := by
  funext k
  change σ (j.succ.succAbove (i.succAbove k)) =
    σ (i.castSucc.succAbove (j.succAbove k))
  congr 1
  simpa only [SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply] using
    SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_δ hij) k

/-- The Čech coface maps satisfy the cosimplicial identity. -/
theorem coface_comp_coface (𝒰 : P.Family) (n : ℕ)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    ModuleCat.ofHom (𝒰.coface n i) ≫ ModuleCat.ofHom (𝒰.coface (n + 1) j.succ) =
      ModuleCat.ofHom (𝒰.coface n j) ≫
        ModuleCat.ofHom (𝒰.coface (n + 1) i.castSucc) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ
  change
    P.restriction _ (P.restriction _ (s (𝒰.delete i (𝒰.delete j.succ σ)))) =
      P.restriction _ (P.restriction _ (s (𝒰.delete j (𝒰.delete i.castSucc σ))))
  change
    ((P.restriction _).comp (P.restriction _)) (s _) =
      ((P.restriction _).comp (P.restriction _)) (s _)
  rw [P.restriction_comp, P.restriction_comp]
  have hθ :
      (fun k ↦ j.succ.succAbove (i.succAbove k)) =
        fun k ↦ i.castSucc.succAbove (j.succAbove k) := by
    funext k
    simpa only [SimplexCategory.δ, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      Fin.succAboveOrderEmb_apply] using
      SimplexCategory.congr_toOrderHom_apply
        (SimplexCategory.δ_comp_δ hij) k
  convert congrArg
      (fun θ : Fin (n + 1) → Fin (n + 1 + 1 + 1) ↦
        P.restriction
          (𝒰.tupleInter_subset_precomp (p := n) (q := n + 1 + 1) σ θ)
          (s (σ ∘ θ))) hθ using 1 <;>
    simp only [delete, Function.comp_def] <;>
    congr 1

/-- The coface module underlying a finite Čech complex. -/
noncomputable def cofaceModule (𝒰 : P.Family) : CofaceModule R where
  X n := ModuleCat.of R (𝒰.Cochains n)
  δ n i := ModuleCat.ofHom (𝒰.coface n i)
  δ_comp_δ := 𝒰.coface_comp_coface

/-- Restriction from the ambient domain to degree-zero Čech cochains. -/
def augmentation (𝒰 : P.Family) :
    P.sections 𝒰.ambient →ₗ[R] 𝒰.Cochains 0 where
  toFun s σ := P.restriction (𝒰.subset (σ 0)) s
  map_add' _ _ := by
    ext σ
    exact map_add _ _ _
  map_smul' _ _ := by
    ext σ
    exact map_smul _ _ _

/-- The augmentation followed by the two degree-zero cofaces agrees. -/
theorem augmentation_comp (𝒰 : P.Family) :
    ModuleCat.ofHom 𝒰.augmentation ≫
        ModuleCat.ofHom (𝒰.coface 0 0) =
      ModuleCat.ofHom 𝒰.augmentation ≫
        ModuleCat.ofHom (𝒰.coface 0 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext σ
  change (𝒰.coface 0 0) (𝒰.augmentation s) σ =
    (𝒰.coface 0 1) (𝒰.augmentation s) σ
  simp only [coface, augmentation, delete, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  change
    ((P.restriction _).comp (P.restriction _)) s =
      ((P.restriction _).comp (P.restriction _)) s
  rw [P.restriction_comp, P.restriction_comp]

/-- The augmented coface data of a finite family. -/
noncomputable def augmentedCofaceModule (𝒰 : P.Family) :
    𝒰.cofaceModule.Augmented where
  augmentationObject := P.sections 𝒰.ambient
  ε := ModuleCat.ofHom 𝒰.augmentation
  ε_comp := 𝒰.augmentation_comp

/-- The augmented unnormalized Čech complex of a finite family. -/
noncomputable def augmentedCechComplex (𝒰 : P.Family) :
    CochainComplex (ModuleCat R) ℕ :=
  𝒰.augmentedCofaceModule.complex

@[simp]
theorem augmentedCechComplex_X_zero (𝒰 : P.Family) :
    𝒰.augmentedCechComplex.X 0 = P.sections 𝒰.ambient :=
  rfl

/-- Degree zero of the augmented Čech complex is the module on the ambient domain. -/
noncomputable def augmentedCechComplexDegreeZeroIso (𝒰 : P.Family) :
    𝒰.augmentedCechComplex.X 0 ≅ P.sections 𝒰.ambient :=
  Iso.refl _

end Family

end Presheaf

end Rigid.Cech
