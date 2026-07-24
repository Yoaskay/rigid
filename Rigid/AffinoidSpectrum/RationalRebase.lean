import Rigid.AffinoidSpectrum.RationalCover
import Rigid.AffinoidSpectrum.RationalPresheaf
import Mathlib.RingTheory.Ideal.Maps

set_option linter.style.header false

/-!
# Rebasing rational domains to a rational subdomain

If `V` is a rational subdomain of an affinoid algebra `A` and `U` is another rational subdomain,
the defining datum of `V` can be mapped to `U.Sections`.  For `V ⊆ U`, its carrier is then the
pullback of `V` to the spectrum of `U.Sections`.  Consequently, every rational cover of `U`
becomes a rational cover of the whole spectrum of `U.Sections`.

This is the geometric rebasing step used in BGR 8.2.2 before applying the Laurent-cover argument
over the affinoid algebra of a member of a cover.
-/

universe u v w

namespace Rigid

/-- A unital ring homomorphism carries rational data to rational data. -/
theorem IsRationalDatum.map
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    {n : ℕ} {g : R} {f : Fin n → R}
    (h : IsRationalDatum g f) (φ : R →+* S) :
    IsRationalDatum (φ g) (fun i ↦ φ (f i)) := by
  rw [IsRationalDatum] at h ⊢
  have hmap :
      Ideal.map φ (Ideal.span (Set.insert g (Set.range f))) = ⊤ := by
    rw [h, Ideal.map_top]
  rw [Ideal.map_span] at hmap
  have himage :
      φ '' Set.insert g (Set.range f) =
        Set.insert (φ g) (Set.range fun i ↦ φ (f i)) := by
    ext x
    constructor
    · rintro ⟨a, (rfl | ⟨i, rfl⟩), rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨g, Set.mem_insert _ _, rfl⟩
      · exact ⟨f i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩
  rwa [himage] at hmap

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain

/-- A rational datum on `A`, mapped to the section algebra of a rational subdomain `U`. -/
noncomputable def rebase (U V : AffinoidRationalSubdomain K A) :
    AffinoidRationalSubdomain K U.Sections where
  n := V.n
  g := RationalLocalization.baseMap K A U.n U.g U.f V.g
  f i := RationalLocalization.baseMap K A U.n U.g U.f (V.f i)
  isRational := V.isRational.map
    (RationalLocalization.baseMap K A U.n U.g U.f).toRingHom

@[simp]
theorem mem_rebase_carrier_iff (U V : AffinoidRationalSubdomain K A)
    (y : BerkovichSpectrumOver K U.Sections) :
    y ∈ (rebase K A U V).carrier ↔
      ambientPoint K A U y ∈ V.carrier := by
  rfl

/-- Rebasing preserves inclusions of rational subdomains. -/
theorem rebase_carrier_subset
    (U : AffinoidRationalSubdomain K A)
    {V W : AffinoidRationalSubdomain K A} (hWV : W.carrier ⊆ V.carrier) :
    (rebase K A U W).carrier ⊆ (rebase K A U V).carrier := by
  intro y hy
  exact (mem_rebase_carrier_iff K A U V y).2
    (hWV ((mem_rebase_carrier_iff K A U W y).1 hy))

/-- A rational cover of `U`, regarded as a cover of the whole spectrum of `U.Sections`. -/
noncomputable abbrev Cover.rebase
    {U : AffinoidRationalSubdomain K A} (𝒱 : Cover K A U) :
    Cover K U.Sections (whole K U.Sections) where
  m := 𝒱.m
  domain i := AffinoidRationalSubdomain.rebase K A U (𝒱.domain i)
  subset := fun _ ↦ by
    rw [carrier_whole]
    exact Set.subset_univ _
  covers := by
    rw [carrier_whole]
    symm
    apply Set.eq_univ_of_forall
    intro y
    have hyU : ambientPoint K A U y ∈ U.carrier :=
      ambientPoint_mem_carrier K A U y
    rw [𝒱.covers] at hyU
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyU
    exact Set.mem_iUnion.mpr
      ⟨i, (mem_rebase_carrier_iff K A U (𝒱.domain i) y).2 hi⟩

section Sections

variable (hA : IsAffinoidAlgebra K A)

include hA in
/-- The section algebra of a rational subdomain of an affinoid algebra is affinoid. -/
theorem isAffinoidAlgebra_sections (U : AffinoidRationalSubdomain K A) :
    IsAffinoidAlgebra K U.Sections := by
  let π : ContinuousAlgHom K
      (TateAlgebra K (Fin hA.presentation.n)) A :=
    { toAlgHom := hA.presentation.toAlgHom
      cont := continuous_tateAlgebra_to_affinoid K hA
        (topology_eq_affinoidTopology_of_presentation K A
          hA.presentation.n hA.presentation.ideal hA.presentation.equiv)
        hA.presentation.toAlgHom }
  exact isAffinoidAlgebra_rationalLocalization_of_surjective
    K A hA.presentation.n π hA.presentation.toAlgHom_surjective
      U.n U.g U.f

/-- The iterated rational localization obtained by rebasing `V` to `U.Sections` maps to the
original section algebra of `V`. -/
noncomputable def rebaseToSections
    {U V : AffinoidRationalSubdomain K A} (hVU : V.carrier ⊆ U.carrier) :
    (rebase K A U V).Sections →A[K] V.Sections :=
  RationalLocalization.lift K U.Sections V.n
    (RationalLocalization.baseMap K A U.n U.g U.f V.g)
    (fun i ↦ RationalLocalization.baseMap K A U.n U.g U.f (V.f i))
    (restriction K A hA hVU)
    (RationalLocalization.coordinate K A V.n V.g V.f)
    (RationalLocalization.isPowerBounded_coordinate K A V.n V.g V.f)
    (fun i ↦ by
      have hrest := restriction_comp_baseMap K A hA hVU
      have hg := congrArg (fun φ : ContinuousAlgHom K A V.Sections ↦ φ V.g) hrest
      have hf := congrArg (fun φ : ContinuousAlgHom K A V.Sections ↦ φ (V.f i)) hrest
      calc
        restriction K A hA hVU
              (RationalLocalization.baseMap K A U.n U.g U.f V.g) *
            RationalLocalization.coordinate K A V.n V.g V.f i =
          RationalLocalization.baseMap K A V.n V.g V.f V.g *
            RationalLocalization.coordinate K A V.n V.g V.f i := by
              rw [show restriction K A hA hVU
                (RationalLocalization.baseMap K A U.n U.g U.f V.g) =
                  RationalLocalization.baseMap K A V.n V.g V.f V.g by
                    simpa only [ContinuousAlgHom.comp_apply] using hg]
        _ = RationalLocalization.baseMap K A V.n V.g V.f (V.f i) :=
          RationalLocalization.baseMap_denominator_mul_coordinate K A V.n V.g V.f i
        _ = restriction K A hA hVU
              (RationalLocalization.baseMap K A U.n U.g U.f (V.f i)) := by
                simpa only [ContinuousAlgHom.comp_apply] using hf.symm)

@[simp]
theorem rebaseToSections_comp_baseMap
    {U V : AffinoidRationalSubdomain K A} (hVU : V.carrier ⊆ U.carrier) :
    (rebaseToSections K A hA hVU).comp
        (RationalLocalization.baseMap K U.Sections
          (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f) =
      restriction K A hA hVU :=
  RationalLocalization.lift_comp_baseMap K U.Sections V.n
    (RationalLocalization.baseMap K A U.n U.g U.f V.g)
    (fun i ↦ RationalLocalization.baseMap K A U.n U.g U.f (V.f i))
    (restriction K A hA hVU)
    (RationalLocalization.coordinate K A V.n V.g V.f)
    (RationalLocalization.isPowerBounded_coordinate K A V.n V.g V.f) _

/-- Map the original section algebra of `V` to the iterated localization over `U.Sections`. -/
noncomputable def sectionsToRebase
    {U V : AffinoidRationalSubdomain K A} :
    V.Sections →A[K] (rebase K A U V).Sections :=
  let baseU := RationalLocalization.baseMap K A U.n U.g U.f
  let baseR := RationalLocalization.baseMap K U.Sections
    (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
  RationalLocalization.lift K A V.n V.g V.f
    (baseR.comp baseU)
    (RationalLocalization.coordinate K U.Sections
      (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f)
    (RationalLocalization.isPowerBounded_coordinate K U.Sections
      (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f)
    (fun i ↦ by
      change
        RationalLocalization.baseMap K U.Sections
              (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
              (RationalLocalization.baseMap K A U.n U.g U.f V.g) *
            RationalLocalization.coordinate K U.Sections
              (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f i =
          RationalLocalization.baseMap K U.Sections
            (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
            (RationalLocalization.baseMap K A U.n U.g U.f (V.f i))
      exact RationalLocalization.baseMap_denominator_mul_coordinate K U.Sections
        (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f i)

@[simp]
theorem sectionsToRebase_comp_baseMap
    {U V : AffinoidRationalSubdomain K A} :
    (sectionsToRebase K A (U := U) (V := V)).comp
        (RationalLocalization.baseMap K A V.n V.g V.f) =
      (RationalLocalization.baseMap K U.Sections
        (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f).comp
          (RationalLocalization.baseMap K A U.n U.g U.f) :=
  RationalLocalization.lift_comp_baseMap K A V.n V.g V.f
    ((RationalLocalization.baseMap K U.Sections
      (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f).comp
        (RationalLocalization.baseMap K A U.n U.g U.f))
    (RationalLocalization.coordinate K U.Sections
      (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f)
    (RationalLocalization.isPowerBounded_coordinate K U.Sections
      (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f)
    (fun i ↦ by
      change
        RationalLocalization.baseMap K U.Sections
              (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
              (RationalLocalization.baseMap K A U.n U.g U.f V.g) *
            RationalLocalization.coordinate K U.Sections
              (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f i =
          RationalLocalization.baseMap K U.Sections
            (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
            (RationalLocalization.baseMap K A U.n U.g U.f (V.f i))
      exact RationalLocalization.baseMap_denominator_mul_coordinate K U.Sections
        (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f i)

@[simp]
theorem sectionsToRebase_comp_restriction
    {U V : AffinoidRationalSubdomain K A} (hVU : V.carrier ⊆ U.carrier) :
    (sectionsToRebase K A (U := U) (V := V)).comp
        (restriction K A hA hVU) =
      RationalLocalization.baseMap K U.Sections
        (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f := by
  let baseU := RationalLocalization.baseMap K A U.n U.g U.f
  let baseR := RationalLocalization.baseMap K U.Sections
    (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
  let φ := (sectionsToRebase K A (U := U) (V := V)).comp
    (restriction K A hA hVU)
  have hbase : φ.comp baseU = baseR.comp baseU := by
    dsimp only [φ]
    rw [ContinuousAlgHom.comp_assoc, restriction_comp_baseMap,
      sectionsToRebase_comp_baseMap]
  apply RationalLocalization.hom_ext_of_isUnit K A φ baseR
  · have hg := congrArg (fun q : ContinuousAlgHom K A _ ↦ q U.g) hbase
    change IsUnit (φ (baseU U.g))
    rw [show φ (baseU U.g) = baseR (baseU U.g) by
      simpa only [ContinuousAlgHom.comp_apply] using hg]
    exact
      (RationalLocalization.isUnit_baseMap_denominator K A
        U.n U.g U.f U.isRational).map baseR.toRingHom
  · exact hbase

@[simp]
theorem rebaseToSections_comp_sectionsToRebase
    {U V : AffinoidRationalSubdomain K A} (hVU : V.carrier ⊆ U.carrier) :
    (rebaseToSections K A hA hVU).comp
        (sectionsToRebase K A (U := U) (V := V)) =
      ContinuousAlgHom.id K V.Sections := by
  let baseU := RationalLocalization.baseMap K A U.n U.g U.f
  let baseV := RationalLocalization.baseMap K A V.n V.g V.f
  let baseR := RationalLocalization.baseMap K U.Sections
    (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
  let φ := (rebaseToSections K A hA hVU).comp
    (sectionsToRebase K A (U := U) (V := V))
  have hbase : φ.comp baseV = (ContinuousAlgHom.id K V.Sections).comp baseV := by
    dsimp only [φ]
    calc
      ((rebaseToSections K A hA hVU).comp
          (sectionsToRebase K A (U := U) (V := V))).comp baseV =
          (rebaseToSections K A hA hVU).comp
            ((sectionsToRebase K A (U := U) (V := V)).comp baseV) := by
              rw [ContinuousAlgHom.comp_assoc]
      _ = (rebaseToSections K A hA hVU).comp (baseR.comp baseU) := by
            rw [sectionsToRebase_comp_baseMap]
      _ = ((rebaseToSections K A hA hVU).comp baseR).comp baseU := by
            rw [ContinuousAlgHom.comp_assoc]
      _ = (restriction K A hA hVU).comp baseU := by
            rw [rebaseToSections_comp_baseMap]
      _ = baseV := restriction_comp_baseMap K A hA hVU
      _ = (ContinuousAlgHom.id K V.Sections).comp baseV := by
            rw [ContinuousAlgHom.id_comp]
  apply RationalLocalization.hom_ext_of_isUnit K A φ
    (ContinuousAlgHom.id K V.Sections)
  · have hg := congrArg (fun q : ContinuousAlgHom K A V.Sections ↦ q V.g) hbase
    change IsUnit (φ (baseV V.g))
    rw [show φ (baseV V.g) = baseV V.g by
      simpa only [ContinuousAlgHom.comp_apply, ContinuousAlgHom.id_apply] using hg]
    exact RationalLocalization.isUnit_baseMap_denominator K A
      V.n V.g V.f V.isRational
  · exact hbase

@[simp]
theorem sectionsToRebase_comp_rebaseToSections
    {U V : AffinoidRationalSubdomain K A} (hVU : V.carrier ⊆ U.carrier) :
    (sectionsToRebase K A (U := U) (V := V)).comp
        (rebaseToSections K A hA hVU) =
      ContinuousAlgHom.id K (rebase K A U V).Sections := by
  let baseR := RationalLocalization.baseMap K U.Sections
    (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
  let φ := (sectionsToRebase K A (U := U) (V := V)).comp
    (rebaseToSections K A hA hVU)
  have hbase :
      φ.comp baseR =
        (ContinuousAlgHom.id K (rebase K A U V).Sections).comp baseR := by
    dsimp only [φ]
    calc
      ((sectionsToRebase K A (U := U) (V := V)).comp
          (rebaseToSections K A hA hVU)).comp baseR =
          (sectionsToRebase K A (U := U) (V := V)).comp
            ((rebaseToSections K A hA hVU).comp baseR) := by
              rw [ContinuousAlgHom.comp_assoc]
      _ = (sectionsToRebase K A (U := U) (V := V)).comp
          (restriction K A hA hVU) := by
            rw [rebaseToSections_comp_baseMap]
      _ = baseR := sectionsToRebase_comp_restriction K A hA hVU
      _ = (ContinuousAlgHom.id K (rebase K A U V).Sections).comp baseR := by
            rw [ContinuousAlgHom.id_comp]
  apply RationalLocalization.hom_ext_of_isUnit K U.Sections φ
    (ContinuousAlgHom.id K (rebase K A U V).Sections)
  · have hg := congrArg
      (fun q : ContinuousAlgHom K U.Sections (rebase K A U V).Sections ↦
        q (rebase K A U V).g) hbase
    change IsUnit (φ (baseR (rebase K A U V).g))
    rw [show φ (baseR (rebase K A U V).g) =
        baseR (rebase K A U V).g by
      simpa only [ContinuousAlgHom.comp_apply, ContinuousAlgHom.id_apply] using hg]
    exact RationalLocalization.isUnit_baseMap_denominator K U.Sections
      (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
      (rebase K A U V).isRational
  · exact hbase

/-- Rebasing a rational subdomain inside `U` does not change its section module. -/
noncomputable def rebaseSectionsLinearEquiv
    {U V : AffinoidRationalSubdomain K A} (hVU : V.carrier ⊆ U.carrier) :
    (rebase K A U V).Sections ≃ₗ[K] V.Sections where
  toFun := rebaseToSections K A hA hVU
  invFun := sectionsToRebase K A
  left_inv x :=
    congrArg
      (fun φ : ContinuousAlgHom K (rebase K A U V).Sections
          (rebase K A U V).Sections ↦ φ x)
      (sectionsToRebase_comp_rebaseToSections K A hA hVU)
  right_inv x :=
    congrArg
      (fun φ : ContinuousAlgHom K V.Sections V.Sections ↦ φ x)
      (rebaseToSections_comp_sectionsToRebase K A hA hVU)
  map_add' x y := map_add (rebaseToSections K A hA hVU) x y
  map_smul' c x := map_smul (rebaseToSections K A hA hVU) c x

/-- The equivalence between rebased and original sections commutes with restriction. -/
theorem rebaseToSections_natural
    {U V W : AffinoidRationalSubdomain K A}
    (hVU : V.carrier ⊆ U.carrier) (hWV : W.carrier ⊆ V.carrier) :
    (restriction K A hA hWV).comp (rebaseToSections K A hA hVU) =
      (rebaseToSections K A hA (hWV.trans hVU)).comp
        (restriction K U.Sections (isAffinoidAlgebra_sections K A hA U)
          (rebase_carrier_subset K A U hWV)) := by
  let baseV := RationalLocalization.baseMap K U.Sections
    (rebase K A U V).n (rebase K A U V).g (rebase K A U V).f
  let φ := (restriction K A hA hWV).comp (rebaseToSections K A hA hVU)
  let ψ := (rebaseToSections K A hA (hWV.trans hVU)).comp
    (restriction K U.Sections (isAffinoidAlgebra_sections K A hA U)
      (rebase_carrier_subset K A U hWV))
  have hbase : φ.comp baseV = ψ.comp baseV := by
    dsimp only [φ, ψ]
    calc
      ((restriction K A hA hWV).comp
          (rebaseToSections K A hA hVU)).comp baseV =
          (restriction K A hA hWV).comp
            ((rebaseToSections K A hA hVU).comp baseV) := by
              rw [ContinuousAlgHom.comp_assoc]
      _ = (restriction K A hA hWV).comp
          (restriction K A hA hVU) := by
            rw [rebaseToSections_comp_baseMap]
      _ = restriction K A hA (hWV.trans hVU) :=
            restriction_comp K A hA hVU hWV
      _ = (rebaseToSections K A hA (hWV.trans hVU)).comp
          (RationalLocalization.baseMap K U.Sections
            (rebase K A U W).n (rebase K A U W).g
            (rebase K A U W).f) := by
            rw [rebaseToSections_comp_baseMap]
      _ = (rebaseToSections K A hA (hWV.trans hVU)).comp
          ((restriction K U.Sections
              (isAffinoidAlgebra_sections K A hA U)
              (rebase_carrier_subset K A U hWV)).comp baseV) := by
            rw [restriction_comp_baseMap]
      _ = ((rebaseToSections K A hA (hWV.trans hVU)).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U)
            (rebase_carrier_subset K A U hWV))).comp baseV := by
            rw [ContinuousAlgHom.comp_assoc]
  apply RationalLocalization.hom_ext_of_isUnit K U.Sections φ ψ
  · have hg := congrArg
      (fun q : ContinuousAlgHom K U.Sections W.Sections ↦
        q (rebase K A U V).g) hbase
    change IsUnit (φ (baseV (rebase K A U V).g))
    rw [show φ (baseV (rebase K A U V).g) =
        ψ (baseV (rebase K A U V).g) by
      simpa only [ContinuousAlgHom.comp_apply] using hg]
    change IsUnit
      (rebaseToSections K A hA (hWV.trans hVU)
        (restriction K U.Sections
          (isAffinoidAlgebra_sections K A hA U)
          (rebase_carrier_subset K A U hWV)
          (baseV (rebase K A U V).g)))
    exact
      ((RationalLocalization.isUnit_baseMap_denominator K U.Sections
        (rebase K A U V).n (rebase K A U V).g
        (rebase K A U V).f (rebase K A U V).isRational).map
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U)
            (rebase_carrier_subset K A U hWV)).toRingHom).map
        (rebaseToSections K A hA (hWV.trans hVU)).toRingHom
  · exact hbase

/-- Naturality after replacing rebased rational data by any equal-carrier data.  This is the
form used for tuple intersections, whose iterated intersection datum need not literally be the
rebase of the corresponding original datum. -/
theorem rebaseToSections_natural_of_carrier_eq
    {U V W : AffinoidRationalSubdomain K A}
    (hVU : V.carrier ⊆ U.carrier) (hWV : W.carrier ⊆ V.carrier)
    {V' W' : AffinoidRationalSubdomain K U.Sections}
    (hV' : V'.carrier = (rebase K A U V).carrier)
    (hW' : W'.carrier = (rebase K A U W).carrier)
    (hW'V' : W'.carrier ⊆ V'.carrier) :
    (restriction K A hA hWV).comp
        ((rebaseToSections K A hA hVU).comp
          (restriction K U.Sections (isAffinoidAlgebra_sections K A hA U) hV'.ge)) =
      ((rebaseToSections K A hA (hWV.trans hVU)).comp
          (restriction K U.Sections (isAffinoidAlgebra_sections K A hA U) hW'.ge)).comp
        (restriction K U.Sections (isAffinoidAlgebra_sections K A hA U) hW'V') := by
  let hrebased := rebase_carrier_subset K A U hWV
  calc
    (restriction K A hA hWV).comp
        ((rebaseToSections K A hA hVU).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hV'.ge)) =
      ((restriction K A hA hWV).comp
        (rebaseToSections K A hA hVU)).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hV'.ge) := by
        rw [ContinuousAlgHom.comp_assoc]
    _ = ((rebaseToSections K A hA (hWV.trans hVU)).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hrebased)).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hV'.ge) := by
        rw [rebaseToSections_natural K A hA hVU hWV]
    _ = (rebaseToSections K A hA (hWV.trans hVU)).comp
        ((restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hrebased).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hV'.ge)) := by
        rw [ContinuousAlgHom.comp_assoc]
    _ = (rebaseToSections K A hA (hWV.trans hVU)).comp
        (restriction K U.Sections
          (isAffinoidAlgebra_sections K A hA U)
          (hW'.ge.trans hW'V')) := by
        rw [restriction_comp]
    _ = (rebaseToSections K A hA (hWV.trans hVU)).comp
        ((restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hW'.ge).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hW'V')) := by
        rw [restriction_comp]
    _ = ((rebaseToSections K A hA (hWV.trans hVU)).comp
          (restriction K U.Sections
            (isAffinoidAlgebra_sections K A hA U) hW'.ge)).comp
        (restriction K U.Sections
          (isAffinoidAlgebra_sections K A hA U) hW'V') := by
        rw [ContinuousAlgHom.comp_assoc]

end Sections

end AffinoidRationalSubdomain

end Rigid
