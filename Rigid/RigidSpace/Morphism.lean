import Mathlib.CategoryTheory.Sites.CoverPreserving
import Rigid.RigidSpace.GRingedSpace

set_option linter.style.header false

/-!
# Morphisms of G-ringed spaces

A continuous map carries an inverse-image functor on admissible opens together with mathlib's
`Functor.IsContinuous` site condition.  A morphism of G-ringed spaces adds a morphism from the
target structure sheaf to the continuous pushforward of the source structure sheaf.  Its maps on
stalks are then constructed from the universal property of the neighbourhood colimit.
-/

open CategoryTheory
open CategoryTheory.Limits

universe pX oX pY oY pZ oZ k a v

namespace Rigid

namespace AdmissibleSite

/-- Point-set and inverse-image data for a map of admissible sites. The inverse-image functor
is primitive so identities and composites agree definitionally with the corresponding functor
operations. -/
structure MapData (X : AdmissibleSite.{pX, oX}) (Y : AdmissibleSite.{pY, oY}) where
  toFun : X.Point → Y.Point
  preimageFunctor : Y.Open ⥤ X.Open
  carrier_preimage :
    ∀ U, X.carrier (preimageFunctor.obj U) = toFun ⁻¹' Y.carrier U

namespace MapData

variable {X : AdmissibleSite.{pX, oX}} {Y : AdmissibleSite.{pY, oY}}

/-- Inverse image on admissible opens. -/
abbrev preimage (f : MapData X Y) (U : Y.Open) : X.Open :=
  f.preimageFunctor.obj U

/-- Inverse image is monotone because it is functorial on inclusion categories. -/
theorem monotone_preimage (f : MapData X Y) : Monotone f.preimage :=
  fun _ _ h ↦ leOfHom (f.preimageFunctor.map (homOfLE h))

@[ext]
theorem ext (f g : MapData X Y) (hfun : f.toFun = g.toFun)
    (hpreimage : f.preimageFunctor = g.preimageFunctor) : f = g := by
  cases f
  cases g
  cases hfun
  cases hpreimage
  rfl

/-- The identity map data. -/
abbrev id (X : AdmissibleSite.{pX, oX}) : MapData X X where
  toFun := _root_.id
  preimageFunctor := 𝟭 X.Open
  carrier_preimage := fun _ ↦ rfl

/-- Composition of point-set and inverse-image data. -/
abbrev comp {Z : AdmissibleSite.{pZ, oZ}} (f : MapData X Y) (g : MapData Y Z) : MapData X Z where
  toFun := g.toFun ∘ f.toFun
  preimageFunctor := g.preimageFunctor ⋙ f.preimageFunctor
  carrier_preimage U := by
    change X.carrier (f.preimage (g.preimage U)) =
      (g.toFun ∘ f.toFun) ⁻¹' Z.carrier U
    rw [f.carrier_preimage, g.carrier_preimage]
    rfl

end MapData

/-- A continuous map of admissible sites. -/
structure Hom (X : AdmissibleSite.{pX, oX}) (Y : AdmissibleSite.{pY, oY})
    extends MapData X Y where
  continuous :
    Functor.IsContinuous toMapData.preimageFunctor Y.topology X.topology

namespace Hom

variable {X : AdmissibleSite.{pX, oX}} {Y : AdmissibleSite.{pY, oY}}

@[ext]
theorem ext (f g : Hom X Y) (h : f.toMapData = g.toMapData) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity continuous map of an admissible site. -/
abbrev id (X : AdmissibleSite.{pX, oX}) : Hom X X where
  toMapData := MapData.id X
  continuous := by infer_instance

/-- Composition of continuous maps of admissible sites. -/
abbrev comp {Z : AdmissibleSite.{pZ, oZ}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toMapData := MapData.comp f.toMapData g.toMapData
  continuous := by
    letI := f.continuous
    letI := g.continuous
    exact Functor.isContinuous_comp g.toMapData.preimageFunctor
      f.toMapData.preimageFunctor Z.topology Y.topology X.topology

/-- The mathlib continuous pushforward along the inverse-image functor on opens. -/
noncomputable def pushforwardSheaf (f : Hom X Y) {A : Type a} [Category.{v} A]
    (F : Sheaf X.topology A) : Sheaf Y.topology A := by
  letI := f.continuous
  exact (f.toMapData.preimageFunctor.sheafPushforwardContinuous
    A Y.topology X.topology).obj F

end Hom

end AdmissibleSite

variable (K : Type k) [CommRing K]

namespace GRingedSpace

variable {X Y : GRingedSpace.{k} K}

/-- A morphism of G-ringed spaces: a continuous map of sites and a morphism of structure
sheaves. -/
structure Hom (X Y : GRingedSpace.{k} K) where
  base : AdmissibleSite.Hom X.toAdmissibleSite Y.toAdmissibleSite
  pullback :
    Y.structureSheaf.obj ⟶
      base.toMapData.preimageFunctor.op ⋙ X.structureSheaf.obj

namespace Hom

@[ext]
theorem ext (f g : Hom K X Y) (hbase : f.base = g.base)
    (hpullback : HEq f.pullback g.pullback) : f = g := by
  cases f
  cases g
  cases hbase
  cases hpullback
  rfl

/-- The identity morphism of a G-ringed space. -/
abbrev id (X : GRingedSpace.{k} K) : Hom K X X where
  base := AdmissibleSite.Hom.id X.toAdmissibleSite
  pullback := 𝟙 X.structureSheaf.obj

/-- Composition of morphisms of G-ringed spaces. -/
abbrev comp {Z : GRingedSpace.{k} K} (f : Hom K X Y) (g : Hom K Y Z) : Hom K X Z where
  base := AdmissibleSite.Hom.comp f.base g.base
  pullback :=
    g.pullback ≫
      Functor.whiskerLeft g.base.toMapData.preimageFunctor.op f.pullback ≫
        (Functor.associator g.base.toMapData.preimageFunctor.op
          f.base.toMapData.preimageFunctor.op X.structureSheaf.obj).inv ≫
        Functor.whiskerRight
          (Functor.opComp g.base.toMapData.preimageFunctor
            f.base.toMapData.preimageFunctor).inv
          X.structureSheaf.obj

@[simp]
theorem comp_base_toFun {Z : GRingedSpace.{k} K} (f : Hom K X Y) (g : Hom K Y Z)
    (x : X.toAdmissibleSite.Point) :
    (comp K f g).base.toMapData.toFun x =
      g.base.toMapData.toFun (f.base.toMapData.toFun x) :=
  rfl

variable (f : Hom K X Y)

/-- The pullback natural transformation bundled as a morphism of sheaves. -/
noncomputable def pullbackSheafHom :
    Y.structureSheaf ⟶
      f.base.pushforwardSheaf (A := CommAlgCat.{k} K) X.structureSheaf :=
  ObjectProperty.homMk f.pullback

/-- Inverse image sends a neighbourhood of `f(x)` to a neighbourhood of `x`. -/
@[reducible]
def preimageNeighborhood (x : X.toAdmissibleSite.Point)
    (U : Neighborhood K Y (f.base.toMapData.toFun x)) :
    Neighborhood K X x where
  obj := f.base.toMapData.preimage U.obj
  mem := by
    rw [f.base.toMapData.carrier_preimage]
    exact U.mem

/-- Pullback of sections on one admissible open. -/
noncomputable def pullbackApp (U : Y.toAdmissibleSite.Open) :
    Sections K Y U →ₐ[K] Sections K X (f.base.toMapData.preimage U) :=
  (f.pullback.app (Opposite.op U)).hom

/-- The cocone from target neighbourhood sections to the source stalk. -/
noncomputable def stalkCocone (x : X.toAdmissibleSite.Point) :
    Cocone (stalkDiagram K Y (f.base.toMapData.toFun x)) where
  pt := stalkObj K X x
  ι :=
    { app := fun U ↦
        f.pullback.app (Opposite.op U.obj) ≫
          colimit.ι (stalkDiagram K X x) (preimageNeighborhood K f x U)
      naturality := by
        intro U V h
        let h' : preimageNeighborhood K f x U ⟶ preimageNeighborhood K f x V :=
          homOfLE (f.base.toMapData.monotone_preimage (leOfHom h))
        simp only [Functor.const_obj_map]
        change
          Y.structureSheaf.obj.map
                (homOfLE (show V.obj ≤ U.obj from leOfHom h)).op ≫
              f.pullback.app (Opposite.op V.obj) ≫
                colimit.ι (stalkDiagram K X x) (preimageNeighborhood K f x V) =
            f.pullback.app (Opposite.op U.obj) ≫
              colimit.ι (stalkDiagram K X x) (preimageNeighborhood K f x U)
        rw [← Category.assoc]
        rw [f.pullback.naturality]
        rw [Category.assoc]
        have hmap :
            (f.base.toMapData.preimageFunctor.op ⋙ X.structureSheaf.obj).map
                (homOfLE (show V.obj ≤ U.obj from leOfHom h)).op =
              (stalkDiagram K X x).map h' := rfl
        rw [hmap]
        exact congrArg
          (fun q ↦ f.pullback.app (Opposite.op U.obj) ≫ q)
          (colimit.w (stalkDiagram K X x) h') }

/-- The induced map on stalks, obtained from the colimit universal property. -/
noncomputable def stalkMap (x : X.toAdmissibleSite.Point) :
    stalkObj K Y (f.base.toMapData.toFun x) ⟶ stalkObj K X x :=
  colimit.desc (stalkDiagram K Y (f.base.toMapData.toFun x)) (stalkCocone K f x)

/-- The induced stalk map carries the germ of a section to the germ of its pullback. -/
@[simp]
theorem germ_stalkMap {U : Y.toAdmissibleSite.Open} {x : X.toAdmissibleSite.Point}
    (hx : f.base.toMapData.toFun x ∈ Y.toAdmissibleSite.carrier U) :
    (stalkMap K f x).hom.comp (germ K Y hx) =
      (germ K X (by
        rw [f.base.toMapData.carrier_preimage]
        exact hx)).comp (pullbackApp K f U) := by
  exact congrArg CommAlgCat.Hom.hom
    (colimit.ι_desc (stalkCocone K f x) ⟨U, hx⟩)

@[simp]
theorem stalkMap_id (X : GRingedSpace.{k} K) (x : X.toAdmissibleSite.Point) :
    stalkMap K (id K X) x = 𝟙 (stalkObj K X x) := by
  dsimp only [stalkMap, id, AdmissibleSite.Hom.id, AdmissibleSite.MapData.id]
  apply colimit.hom_ext
  intro U
  rw [colimit.ι_desc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem stalkMap_comp {Z : GRingedSpace.{k} K} (f : Hom K X Y) (g : Hom K Y Z)
    (x : X.toAdmissibleSite.Point) :
    stalkMap K (comp K f g) x =
      stalkMap K g (f.base.toMapData.toFun x) ≫ stalkMap K f x := by
  apply colimit.hom_ext
  intro U
  apply CommAlgCat.hom_ext
  have hZ : g.base.toMapData.toFun (f.base.toMapData.toFun x) ∈
      Z.toAdmissibleSite.carrier U.obj := by
    exact U.mem
  have hY : f.base.toMapData.toFun x ∈
      Y.toAdmissibleSite.carrier (g.base.toMapData.preimage U.obj) := by
    rw [g.base.toMapData.carrier_preimage]
    exact hZ
  change (stalkMap K (comp K f g) x).hom.comp (germ K Z hZ) =
    (stalkMap K f x).hom.comp
      ((stalkMap K g (f.base.toMapData.toFun x)).hom.comp (germ K Z hZ))
  rw [germ_stalkMap]
  rw [germ_stalkMap]
  change (germ K X _).comp (pullbackApp K (comp K f g) U.obj) =
    ((stalkMap K f x).hom.comp (germ K Y hY)).comp (pullbackApp K g U.obj)
  rw [germ_stalkMap]
  simp [pullbackApp, comp]
  rfl

end Hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : Category (GRingedSpace.{k} K) where
  Hom := GRingedSpace.Hom K
  id := GRingedSpace.Hom.id K
  comp := GRingedSpace.Hom.comp K
  id_comp f := by
    apply GRingedSpace.Hom.ext
    · rfl
    · apply heq_of_eq
      apply NatTrans.ext
      funext U
      simp [GRingedSpace.Hom.comp, GRingedSpace.Hom.id]
  comp_id f := by
    apply GRingedSpace.Hom.ext
    · rfl
    · apply heq_of_eq
      apply NatTrans.ext
      funext U
      simp [GRingedSpace.Hom.comp, GRingedSpace.Hom.id]
  assoc f g h := by
    apply GRingedSpace.Hom.ext
    · rfl
    · apply heq_of_eq
      apply NatTrans.ext
      funext U
      simp [GRingedSpace.Hom.comp, Category.assoc]

end GRingedSpace

namespace LocallyGRingedSpace

variable {X Y : LocallyGRingedSpace.{k} K}

/-- A morphism of G-locally ringed spaces is a G-ringed-space morphism whose canonically induced
maps on stalks are local. -/
structure Hom (X Y : LocallyGRingedSpace.{k} K) where
  toGRingedSpaceHom : GRingedSpace.Hom K X.toGRingedSpace Y.toGRingedSpace
  local_stalk :
    ∀ x : X.toAdmissibleSite.Point,
      IsLocalHom (GRingedSpace.Hom.stalkMap K toGRingedSpaceHom x).hom

namespace Hom

@[ext]
theorem ext (f g : Hom K X Y)
    (h : f.toGRingedSpaceHom = g.toGRingedSpaceHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity morphism of a G-locally ringed space. -/
abbrev id (X : LocallyGRingedSpace.{k} K) : Hom K X X where
  toGRingedSpaceHom := GRingedSpace.Hom.id K X.toGRingedSpace
  local_stalk _ := by
    sorry

/-- Composition of morphisms of G-locally ringed spaces. -/
abbrev comp {Z : LocallyGRingedSpace.{k} K} (f : Hom K X Y) (g : Hom K Y Z) :
    Hom K X Z where
  toGRingedSpaceHom :=
    GRingedSpace.Hom.comp K f.toGRingedSpaceHom g.toGRingedSpaceHom
  local_stalk x := by
    rw [GRingedSpace.Hom.stalkMap_comp]
    change IsLocalHom
      ((GRingedSpace.Hom.stalkMap K f.toGRingedSpaceHom x).hom.comp
        (GRingedSpace.Hom.stalkMap K g.toGRingedSpaceHom
          (f.toGRingedSpaceHom.base.toMapData.toFun x)).hom)
    letI : IsLocalHom (GRingedSpace.Hom.stalkMap K f.toGRingedSpaceHom x).hom :=
      f.local_stalk x
    letI : IsLocalHom (GRingedSpace.Hom.stalkMap K g.toGRingedSpaceHom
        (f.toGRingedSpaceHom.base.toMapData.toFun x)).hom :=
      g.local_stalk (f.toGRingedSpaceHom.base.toMapData.toFun x)
    refine ⟨?_⟩
    intro a ha
    exact IsLocalHom.map_nonunit
      (f := (GRingedSpace.Hom.stalkMap K g.toGRingedSpaceHom
        (f.toGRingedSpaceHom.base.toMapData.toFun x)).hom) a
      (IsLocalHom.map_nonunit
        (f := (GRingedSpace.Hom.stalkMap K f.toGRingedSpaceHom x).hom) _ ha)

end Hom

instance : Category (LocallyGRingedSpace.{k} K) where
  Hom := LocallyGRingedSpace.Hom K
  id := LocallyGRingedSpace.Hom.id K
  comp := LocallyGRingedSpace.Hom.comp K
  id_comp f := by
    apply LocallyGRingedSpace.Hom.ext
    exact @Category.id_comp (GRingedSpace.{k} K) _ _ _ f.toGRingedSpaceHom
  comp_id f := by
    apply LocallyGRingedSpace.Hom.ext
    exact @Category.comp_id (GRingedSpace.{k} K) _ _ _ f.toGRingedSpaceHom
  assoc f g h := by
    apply LocallyGRingedSpace.Hom.ext
    exact @Category.assoc (GRingedSpace.{k} K) _ _ _ _ _
      f.toGRingedSpaceHom g.toGRingedSpaceHom h.toGRingedSpaceHom

end LocallyGRingedSpace

end Rigid
