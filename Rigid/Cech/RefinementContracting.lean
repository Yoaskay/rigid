import Mathlib.Data.Fin.Parity
import Mathlib.Algebra.BigOperators.Fin
import Rigid.Cech.Contracting
import Rigid.Cech.Double
import Rigid.Cech.DoubleTranspose
import Rigid.Cech.Refinement
import Rigid.Cech.StrictTuple

set_option linter.style.header false

/-!
# Contractible rows in the normalized double Čech complex

If a fixed domain `W` is contained in one member of a finite family, the normalized Čech
complex of the intersections with `W` is contractible.  This file constructs the contraction
in the product form needed for rows of the double Čech complex.  The distinguished member may
depend on the vertical tuple.
-/

universe u v w

namespace Rigid.Cech

variable {K : Type u} [Field K]
variable {P : Presheaf.{u, v, w} K}

namespace Presheaf.Family

variable (𝒰 𝒱 : P.Family) (q : ℕ)
variable (owner : 𝒱.StrictTuple q → Fin 𝒰.card)

private theorem restriction_roundtrip_of_strictTuple_eq {n : ℕ}
    (W D : P.Domain) (ρ σ : 𝒰.StrictTuple n) (hρσ : ρ = σ)
    (hin : P.subset D (P.inter (𝒰.tupleInter n ρ) W))
    (hout : P.subset (P.inter (𝒰.tupleInter n σ) W) D)
    (s : ∀ θ : 𝒰.StrictTuple n,
      P.sections (P.inter (𝒰.tupleInter n θ) W)) :
    P.restriction hout (P.restriction hin (s ρ)) = s σ := by
  subst ρ
  rw [← LinearMap.comp_apply, P.restriction_comp]
  simpa only [LinearMap.id_apply] using congrArg
    (fun f : P.sections (P.inter (𝒰.tupleInter n σ) W) →ₗ[K]
        P.sections (P.inter (𝒰.tupleInter n σ) W) ↦ f (s σ))
    (P.restriction_id (P.inter (𝒰.tupleInter n σ) W))

private theorem restriction_paths_eq_of_strictTuple_eq {n : ℕ}
    (W D₁ D₂ E : P.Domain) (ρ₁ ρ₂ : 𝒰.StrictTuple n) (hρ : ρ₁ = ρ₂)
    (hin₁ : P.subset D₁ (P.inter (𝒰.tupleInter n ρ₁) W))
    (hout₁ : P.subset E D₁)
    (hin₂ : P.subset D₂ (P.inter (𝒰.tupleInter n ρ₂) W))
    (hout₂ : P.subset E D₂)
    (s : ∀ θ : 𝒰.StrictTuple n,
      P.sections (P.inter (𝒰.tupleInter n θ) W)) :
    P.restriction hout₁ (P.restriction hin₁ (s ρ₁)) =
      P.restriction hout₂ (P.restriction hin₂ (s ρ₂)) := by
  subst ρ₁
  rw [← LinearMap.comp_apply, P.restriction_comp,
    ← LinearMap.comp_apply, P.restriction_comp]

private theorem neg_one_pow_cross (n : ℕ) (k : Fin (n + 2)) (j : Fin (n + 1)) :
    (-1 : ℤ) ^ ((j : ℕ) + (j.predAbove k : ℕ)) =
      -(-1 : ℤ) ^ ((k : ℕ) + (k.succAbove j : ℕ)) := by
  have hsign := Fin.neg_one_pow_succAbove_add_predAbove (R := ℤ) k j
  rw [pow_add, pow_add] at hsign ⊢
  have hleft :
      (-1 : ℤ) ^ (k.succAbove j : ℕ) *
          (-1 : ℤ) ^ (k.succAbove j : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (k.succAbove j : ℕ)).neg_one_pow]
  have hright :
      (-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (j : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (j : ℕ)).neg_one_pow]
  calc
    (-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (j.predAbove k : ℕ) =
        ((-1 : ℤ) ^ (k.succAbove j : ℕ) *
          (-1 : ℤ) ^ (k.succAbove j : ℕ)) *
            ((-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (j.predAbove k : ℕ)) := by
              rw [hleft, one_mul]
    _ = ((-1 : ℤ) ^ (k.succAbove j : ℕ) *
          (-1 : ℤ) ^ (j.predAbove k : ℕ)) *
        ((-1 : ℤ) ^ (k.succAbove j : ℕ) *
          (-1 : ℤ) ^ (j : ℕ)) := by ring
    _ = (-((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (j : ℕ))) *
        ((-1 : ℤ) ^ (k.succAbove j : ℕ) *
          (-1 : ℤ) ^ (j : ℕ)) := by rw [hsign]
    _ = -(((-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (j : ℕ)) *
        ((-1 : ℤ) ^ (k : ℕ) *
          (-1 : ℤ) ^ (k.succAbove j : ℕ))) := by ring
    _ = -((-1 : ℤ) ^ (k : ℕ) *
        (-1 : ℤ) ^ (k.succAbove j : ℕ)) := by rw [hright, one_mul]

/-- Inserting the distinguished member does not change an intersection with the vertical
tuple: the old double intersection is contained in the new one. -/
theorem doubleInter_subset_horizontalInsert {n : ℕ}
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ)))
    (σ : 𝒰.StrictTuple n) (τ : 𝒱.StrictTuple q)
    (hi : owner τ ∉ 𝒰.strictSupport σ) :
    P.subset
      (P.inter (𝒰.tupleInter n σ) (𝒱.tupleInter q τ))
      (P.inter
        (𝒰.tupleInter (n + 1) (𝒰.strictInsert σ (owner τ) hi))
        (𝒱.tupleInter q τ)) := by
  apply P.subset_inter
  · apply 𝒰.subset_tupleInter
    intro a
    let k := 𝒰.strictInsertPosition σ (owner τ) hi
    refine Fin.succAboveCases k ?_ (fun j ↦ ?_) a
    · rw [𝒰.strictInsert_apply_position]
      exact P.subset_trans (P.inter_subset_right _ _) (howner τ)
    · have hinsert := congrFun (𝒰.strictInsert_coe σ (owner τ) hi)
        (k.succAbove j)
      rw [Fin.insertNth_apply_succAbove] at hinsert
      rw [hinsert]
      exact P.subset_trans (P.inter_subset_left _ _)
        (𝒰.tupleInter_subset_domain n σ j)
  · exact P.inter_subset_right _ _

/-- The vertical tuple itself is contained in the double intersection with its distinguished
horizontal singleton. -/
theorem verticalTuple_subset_horizontalSingleton
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ)))
    (τ : 𝒱.StrictTuple q) :
    P.subset (𝒱.tupleInter q τ)
      (P.inter
        (𝒰.tupleInter 0 (𝒰.strictSingleton (owner τ)))
        (𝒱.tupleInter q τ)) := by
  apply P.subset_inter
  · simpa only [tupleInter, strictSingleton_apply] using howner τ
  · exact P.subset_refl _

/-- Evaluation at the distinguished horizontal singleton contracts degree zero to the
horizontal augmentation object. -/
noncomputable def horizontalContractZero
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ))) :
    DoubleCochains 𝒰 𝒱 0 q →ₗ[K] 𝒱.NormalizedCochains q where
  toFun s τ :=
    P.restriction (verticalTuple_subset_horizontalSingleton
      𝒰 𝒱 q owner howner τ) (s (𝒰.strictSingleton (owner τ)) τ)
  map_add' _ _ := by
    funext τ
    exact map_add _ _ _
  map_smul' _ _ := by
    funext τ
    exact map_smul _ _ _

/-- Insert the distinguished horizontal member, with the standard alternating sign. -/
noncomputable def horizontalContract
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ)))
    (n : ℕ) :
    DoubleCochains 𝒰 𝒱 (n + 1) q →ₗ[K] DoubleCochains 𝒰 𝒱 n q where
  toFun s σ τ :=
    if hi : owner τ ∈ 𝒰.strictSupport σ then
      0
    else
      (-1 : ℤ) ^ (𝒰.strictInsertPosition σ (owner τ) hi : ℕ) •
        P.restriction
          (doubleInter_subset_horizontalInsert
            𝒰 𝒱 q owner howner σ τ hi)
          (s (𝒰.strictInsert σ (owner τ) hi) τ)
  map_add' x y := by
    funext σ τ
    by_cases hi : owner τ ∈ 𝒰.strictSupport σ
    · have hi' := (𝒰.mem_strictSupport_iff σ (owner τ)).1 hi
      simp only [mem_strictSupport_iff, hi', ↓reduceDIte, Pi.add_apply, zero_add]
    · have hi' := not_congr (𝒰.mem_strictSupport_iff σ (owner τ)) |>.mp hi
      simp only [mem_strictSupport_iff, hi', ↓reduceDIte, Pi.add_apply, map_add, smul_add]
  map_smul' a x := by
    funext σ τ
    by_cases hi : owner τ ∈ 𝒰.strictSupport σ
    · have hi' := (𝒰.mem_strictSupport_iff σ (owner τ)).1 hi
      simp only [mem_strictSupport_iff, hi', ↓reduceDIte, Pi.smul_apply, smul_zero]
    · have hi' := not_congr (𝒰.mem_strictSupport_iff σ (owner τ)) |>.mp hi
      simp only [mem_strictSupport_iff, hi', ↓reduceDIte, Pi.smul_apply, map_smul,
        RingHom.id_apply]
      rw [smul_comm]

@[simp]
theorem horizontalContractZero_horizontalAugmentation
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ)))
    (x : 𝒱.NormalizedCochains q) :
    horizontalContractZero 𝒰 𝒱 q owner howner
        (horizontalAugmentation 𝒰 𝒱 q x) = x := by
  funext τ
  change P.restriction _
    (P.restriction (P.inter_subset_right
      (𝒰.tupleInter 0 (𝒰.strictSingleton (owner τ)))
      (𝒱.tupleInter q τ)) (x τ)) = x τ
  rw [← LinearMap.comp_apply, P.restriction_comp]
  simpa only [LinearMap.id_apply] using congrArg
    (fun f : P.sections (𝒱.tupleInter q τ) →ₗ[K]
        P.sections (𝒱.tupleInter q τ) ↦ f (x τ))
    (P.restriction_id (𝒱.tupleInter q τ))

/-- If the distinguished index is already present, the `d h` part of the homotopy identity is
the identity and the `h d` part vanishes. -/
theorem horizontalContracting_degree_succ_of_mem
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ)))
    (n : ℕ) (x : DoubleCochains 𝒰 𝒱 (n + 1) q)
    (σ : 𝒰.StrictTuple (n + 1)) (τ : 𝒱.StrictTuple q)
    (hmem : owner τ ∈ 𝒰.strictSupport σ) :
    ((horizontalCofaceModule 𝒰 𝒱 q).differential n).hom
          (horizontalContract 𝒰 𝒱 q owner howner n x) σ τ +
        horizontalContract 𝒰 𝒱 q owner howner (n + 1)
          (((horizontalCofaceModule 𝒰 𝒱 q).differential (n + 1)).hom x) σ τ =
      x σ τ := by
  have hrange := (𝒰.mem_strictSupport_iff σ (owner τ)).1 hmem
  have hhd :
      horizontalContract 𝒰 𝒱 q owner howner (n + 1)
          (((horizontalCofaceModule 𝒰 𝒱 q).differential (n + 1)).hom x) σ τ =
        0 := by
    change
      (if hi : owner τ ∈ 𝒰.strictSupport σ then 0 else
        (-1 : ℤ) ^ (𝒰.strictInsertPosition σ (owner τ) hi : ℕ) •
          P.restriction
            (doubleInter_subset_horizontalInsert
              𝒰 𝒱 q owner howner σ τ hi)
            _) = 0
    exact dif_pos hmem
  rw [hhd, add_zero]
  obtain ⟨k, hk⟩ := hrange
  rw [CofaceModule.differential]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom,
    LinearMap.sum_apply, Finset.sum_apply]
  change
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      P.restriction (doubleInter_subset_horizontalDelete 𝒰 𝒱 j σ τ)
        (horizontalContract 𝒰 𝒱 q owner howner n x
          (𝒰.strictDelete j σ) τ)) = x σ τ
  rw [Finset.sum_eq_single k]
  · change
      (-1 : ℤ) ^ (k : ℕ) •
          P.restriction _
            (horizontalContract 𝒰 𝒱 q owner howner n x
              (𝒰.strictDelete k σ) τ) =
        x σ τ
    have hnot :
        owner τ ∉ 𝒰.strictSupport (𝒰.strictDelete k σ) := by
      rw [← hk]
      exact 𝒰.not_mem_strictSupport_strictDelete σ k
    change
      (-1 : ℤ) ^ (k : ℕ) • P.restriction _
        (if hi : owner τ ∈ 𝒰.strictSupport (𝒰.strictDelete k σ) then 0 else
          (-1 : ℤ) ^
              (𝒰.strictInsertPosition (𝒰.strictDelete k σ) (owner τ) hi : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalInsert 𝒰 𝒱 q owner howner
                (𝒰.strictDelete k σ) τ hi)
              (x (𝒰.strictInsert (𝒰.strictDelete k σ) (owner τ) hi) τ)) =
        x σ τ
    rw [dif_neg hnot]
    have hinsert :
        𝒰.strictInsert (𝒰.strictDelete k σ) (owner τ) hnot = σ := by
      exact 𝒰.strictInsert_strictDelete_of_eq σ k (owner τ) hnot hk
    have hposition :
        𝒰.strictInsertPosition (𝒰.strictDelete k σ) (owner τ) hnot = k := by
      exact 𝒰.strictInsertPosition_strictDelete_of_eq σ k (owner τ) hnot hk
    rw [hposition, map_zsmul, ← mul_zsmul, ← pow_add,
      (Even.add_self (k : ℕ)).neg_one_pow, one_zsmul]
    exact restriction_roundtrip_of_strictTuple_eq 𝒰
      (𝒱.tupleInter q τ)
      (P.inter (𝒰.tupleInter n (𝒰.strictDelete k σ))
        (𝒱.tupleInter q τ))
      (𝒰.strictInsert (𝒰.strictDelete k σ) (owner τ) hnot) σ hinsert
      (doubleInter_subset_horizontalInsert 𝒰 𝒱 q owner howner
        (𝒰.strictDelete k σ) τ hnot)
      (doubleInter_subset_horizontalDelete 𝒰 𝒱 k σ τ)
      (fun θ ↦ x θ τ)
  · intro j _ hjk
    have hownerDelete :
        owner τ ∈ 𝒰.strictSupport (𝒰.strictDelete j σ) := by
      rw [𝒰.mem_strictSupport_iff]
      rcases Fin.eq_self_or_eq_succAbove j k with h | ⟨l, h⟩
      · exact (hjk h.symm).elim
      · exact ⟨l, by
          change σ (j.succAbove l) = owner τ
          rw [← h]
          exact hk⟩
    have hownerDelete' :
        owner τ ∈ Set.range (𝒰.strictDelete j σ) :=
      (𝒰.mem_strictSupport_iff (𝒰.strictDelete j σ) (owner τ)).1
        hownerDelete
    change
      (-1 : ℤ) ^ (j : ℕ) •
          P.restriction _
            (horizontalContract 𝒰 𝒱 q owner howner n x
              (𝒰.strictDelete j σ) τ) = 0
    change
      (-1 : ℤ) ^ (j : ℕ) • P.restriction _
        (if hi : owner τ ∈ 𝒰.strictSupport (𝒰.strictDelete j σ) then 0 else
          (-1 : ℤ) ^
              (𝒰.strictInsertPosition (𝒰.strictDelete j σ) (owner τ) hi : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalInsert 𝒰 𝒱 q owner howner
                (𝒰.strictDelete j σ) τ hi)
              (x (𝒰.strictInsert (𝒰.strictDelete j σ) (owner τ) hi) τ)) = 0
    rw [dif_pos hownerDelete, map_zero, smul_zero]
  · simp

/-- If the distinguished index is absent, the inserted-face term is the identity and all
remaining terms cancel in pairs. -/
theorem horizontalContracting_degree_succ_of_not_mem
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ)))
    (n : ℕ) (x : DoubleCochains 𝒰 𝒱 (n + 1) q)
    (σ : 𝒰.StrictTuple (n + 1)) (τ : 𝒱.StrictTuple q)
    (hnot : owner τ ∉ 𝒰.strictSupport σ) :
    ((horizontalCofaceModule 𝒰 𝒱 q).differential n).hom
          (horizontalContract 𝒰 𝒱 q owner howner n x) σ τ +
        horizontalContract 𝒰 𝒱 q owner howner (n + 1)
          (((horizontalCofaceModule 𝒰 𝒱 q).differential (n + 1)).hom x) σ τ =
      x σ τ := by
  let k := 𝒰.strictInsertPosition σ (owner τ) hnot
  let ρ := 𝒰.strictInsert σ (owner τ) hnot
  let Aterm : Fin (n + 2) →
      P.sections
        (P.inter (𝒰.tupleInter (n + 1) σ) (𝒱.tupleInter q τ)) :=
    fun j ↦
      (-1 : ℤ) ^ (j : ℕ) •
        P.restriction
          (doubleInter_subset_horizontalDelete 𝒰 𝒱 j σ τ)
          (horizontalContract 𝒰 𝒱 q owner howner n x
            (𝒰.strictDelete j σ) τ)
  let Bterm : Fin (n + 2) →
      P.sections
        (P.inter (𝒰.tupleInter (n + 1) σ) (𝒱.tupleInter q τ)) :=
    fun j ↦
      (-1 : ℤ) ^ (k : ℕ) •
        P.restriction
          (doubleInter_subset_horizontalInsert
            𝒰 𝒱 q owner howner σ τ hnot)
          ((-1 : ℤ) ^ (k.succAbove j : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalDelete
                𝒰 𝒱 (k.succAbove j) ρ τ)
              (x (𝒰.strictDelete (k.succAbove j) ρ) τ))
  have hdelete : 𝒰.strictDelete k ρ = σ := by
    exact 𝒰.strictDelete_strictInsert σ (owner τ) hnot
  have hidentity :
      (-1 : ℤ) ^ (k : ℕ) •
          P.restriction
            (doubleInter_subset_horizontalInsert
              𝒰 𝒱 q owner howner σ τ hnot)
            ((-1 : ℤ) ^ (k : ℕ) •
              P.restriction
                (doubleInter_subset_horizontalDelete 𝒰 𝒱 k ρ τ)
                (x (𝒰.strictDelete k ρ) τ)) =
        x σ τ := by
    rw [map_zsmul, ← mul_zsmul, ← pow_add,
      (Even.add_self (k : ℕ)).neg_one_pow, one_zsmul]
    exact restriction_roundtrip_of_strictTuple_eq 𝒰
      (𝒱.tupleInter q τ)
      (P.inter (𝒰.tupleInter (n + 2) ρ) (𝒱.tupleInter q τ))
      (𝒰.strictDelete k ρ) σ hdelete
      (doubleInter_subset_horizontalDelete 𝒰 𝒱 k ρ τ)
      (doubleInter_subset_horizontalInsert
        𝒰 𝒱 q owner howner σ τ hnot)
      (fun θ ↦ x θ τ)
  have hcancel (j : Fin (n + 2)) : Aterm j + Bterm j = 0 := by
    have hnotDelete :
        owner τ ∉ 𝒰.strictSupport (𝒰.strictDelete j σ) :=
      𝒰.not_mem_strictSupport_strictDelete_of_not_mem σ (owner τ) hnot j
    have hposition :
        𝒰.strictInsertPosition (𝒰.strictDelete j σ) (owner τ) hnotDelete =
          j.predAbove k := by
      exact 𝒰.strictInsertPosition_after_strictDelete σ (owner τ) hnot j
    have htuple :
        𝒰.strictInsert (𝒰.strictDelete j σ) (owner τ) hnotDelete =
          𝒰.strictDelete (k.succAbove j) ρ := by
      exact (𝒰.strictDelete_strictInsert_eq_insert
        σ (owner τ) hnot j).symm
    have hpath :
        P.restriction
            (doubleInter_subset_horizontalDelete 𝒰 𝒱 j σ τ)
            (P.restriction
              (doubleInter_subset_horizontalInsert 𝒰 𝒱 q owner howner
                (𝒰.strictDelete j σ) τ hnotDelete)
              (x (𝒰.strictInsert (𝒰.strictDelete j σ)
                (owner τ) hnotDelete) τ)) =
          P.restriction
            (doubleInter_subset_horizontalInsert
              𝒰 𝒱 q owner howner σ τ hnot)
            (P.restriction
              (doubleInter_subset_horizontalDelete
                𝒰 𝒱 (k.succAbove j) ρ τ)
              (x (𝒰.strictDelete (k.succAbove j) ρ) τ)) := by
      exact restriction_paths_eq_of_strictTuple_eq 𝒰
        (𝒱.tupleInter q τ)
        (P.inter (𝒰.tupleInter n (𝒰.strictDelete j σ))
          (𝒱.tupleInter q τ))
        (P.inter (𝒰.tupleInter (n + 2) ρ)
          (𝒱.tupleInter q τ))
        (P.inter (𝒰.tupleInter (n + 1) σ)
          (𝒱.tupleInter q τ))
        (𝒰.strictInsert (𝒰.strictDelete j σ) (owner τ) hnotDelete)
        (𝒰.strictDelete (k.succAbove j) ρ) htuple
        (doubleInter_subset_horizontalInsert 𝒰 𝒱 q owner howner
          (𝒰.strictDelete j σ) τ hnotDelete)
        (doubleInter_subset_horizontalDelete 𝒰 𝒱 j σ τ)
        (doubleInter_subset_horizontalDelete
          𝒰 𝒱 (k.succAbove j) ρ τ)
        (doubleInter_subset_horizontalInsert
          𝒰 𝒱 q owner howner σ τ hnot)
        (fun θ ↦ x θ τ)
    have hsign := neg_one_pow_cross (n + 1) k j
    dsimp only [Aterm, Bterm]
    change
      (-1 : ℤ) ^ (j : ℕ) •
          P.restriction _
            (horizontalContract 𝒰 𝒱 q owner howner n x
              (𝒰.strictDelete j σ) τ) +
        (-1 : ℤ) ^ (k : ℕ) •
          P.restriction _
            ((-1 : ℤ) ^ (k.succAbove j : ℕ) •
              P.restriction _ (x (𝒰.strictDelete (k.succAbove j) ρ) τ)) = 0
    change
      (-1 : ℤ) ^ (j : ℕ) •
          P.restriction _
            (if hi : owner τ ∈
                𝒰.strictSupport (𝒰.strictDelete j σ) then 0 else
              (-1 : ℤ) ^
                  (𝒰.strictInsertPosition
                    (𝒰.strictDelete j σ) (owner τ) hi : ℕ) •
                P.restriction
                  (doubleInter_subset_horizontalInsert 𝒰 𝒱 q owner howner
                    (𝒰.strictDelete j σ) τ hi)
                  (x (𝒰.strictInsert (𝒰.strictDelete j σ)
                    (owner τ) hi) τ)) +
        (-1 : ℤ) ^ (k : ℕ) •
          P.restriction _
            ((-1 : ℤ) ^ (k.succAbove j : ℕ) •
              P.restriction _ (x (𝒰.strictDelete (k.succAbove j) ρ) τ)) = 0
    rw [dif_neg hnotDelete, map_zsmul, map_zsmul,
      ← mul_zsmul, ← mul_zsmul, ← pow_add, ← pow_add, hposition]
    rw [hsign, neg_zsmul, hpath, neg_add_cancel]
  have hfirst :
      ((horizontalCofaceModule 𝒰 𝒱 q).differential n).hom
          (horizontalContract 𝒰 𝒱 q owner howner n x) σ τ =
        ∑ j : Fin (n + 2), Aterm j := by
    rw [CofaceModule.differential]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom,
      LinearMap.sum_apply, Finset.sum_apply]
    rfl
  have hsecond :
      ((horizontalCofaceModule 𝒰 𝒱 q).differential (n + 1)).hom x ρ τ =
        ∑ l : Fin (n + 3), (-1 : ℤ) ^ (l : ℕ) •
          P.restriction
            (doubleInter_subset_horizontalDelete 𝒰 𝒱 l ρ τ)
            (x (𝒰.strictDelete l ρ) τ) := by
    rw [CofaceModule.differential]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom,
      LinearMap.sum_apply, Finset.sum_apply]
    rfl
  rw [hfirst]
  change
    (∑ j : Fin (n + 2), Aterm j) +
      (if hi : owner τ ∈ 𝒰.strictSupport σ then 0 else
        (-1 : ℤ) ^ (𝒰.strictInsertPosition σ (owner τ) hi : ℕ) •
          P.restriction
            (doubleInter_subset_horizontalInsert 𝒰 𝒱 q owner howner σ τ hi)
            (((horizontalCofaceModule 𝒰 𝒱 q).differential (n + 1)).hom
              x ρ τ)) =
      x σ τ
  rw [dif_neg hnot]
  rw [hsecond]
  rw [Fin.sum_univ_succAbove _ k, map_add, map_sum,
    smul_add, Finset.smul_sum]
  change (∑ j : Fin (n + 2), Aterm j) +
      ((-1 : ℤ) ^ (k : ℕ) •
        P.restriction
          (doubleInter_subset_horizontalInsert
            𝒰 𝒱 q owner howner σ τ hnot)
          ((-1 : ℤ) ^ (k : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalDelete 𝒰 𝒱 k ρ τ)
              (x (𝒰.strictDelete k ρ) τ)) +
        ∑ j : Fin (n + 2), Bterm j) =
      x σ τ
  rw [hidentity]
  have hsum :
      (∑ j : Fin (n + 2), Aterm j) + ∑ j : Fin (n + 2), Bterm j = 0 := by
    rw [← Finset.sum_add_distrib]
    simp only [hcancel, Finset.sum_const_zero]
  calc
    (∑ j : Fin (n + 2), Aterm j) +
          (x σ τ + ∑ j : Fin (n + 2), Bterm j) =
        x σ τ +
          ((∑ j : Fin (n + 2), Aterm j) + ∑ j : Fin (n + 2), Bterm j) := by
            abel
    _ = x σ τ + 0 := congrArg (x σ τ + ·) hsum
    _ = x σ τ := add_zero _

/-- The augmentation and the degree-zero differential satisfy the contracting identity. -/
theorem horizontalContracting_degree_zero
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ)))
    (x : DoubleCochains 𝒰 𝒱 0 q)
    (σ : 𝒰.StrictTuple 0) (τ : 𝒱.StrictTuple q) :
    horizontalAugmentation 𝒰 𝒱 q
          (horizontalContractZero 𝒰 𝒱 q owner howner x) σ τ +
        horizontalContract 𝒰 𝒱 q owner howner 0
          (((horizontalCofaceModule 𝒰 𝒱 q).differential 0).hom x) σ τ =
      x σ τ := by
  by_cases hmem : owner τ ∈ 𝒰.strictSupport σ
  · have hrange := (𝒰.mem_strictSupport_iff σ (owner τ)).1 hmem
    obtain ⟨j, hj⟩ := hrange
    have hvalue : σ 0 = owner τ := by
      simpa only [Fin.eq_zero j] using hj
    have hsingleton : 𝒰.strictSingleton (owner τ) = σ := by
      ext a
      rw [𝒰.strictSingleton_apply, Fin.eq_zero a, hvalue]
    have hcontract :
        horizontalContract 𝒰 𝒱 q owner howner 0
            (((horizontalCofaceModule 𝒰 𝒱 q).differential 0).hom x) σ τ =
          0 := by
      change
        (if hi : owner τ ∈ 𝒰.strictSupport σ then 0 else
          (-1 : ℤ) ^
              (𝒰.strictInsertPosition σ (owner τ) hi : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalInsert
                𝒰 𝒱 q owner howner σ τ hi) _) = 0
      exact dif_pos hmem
    rw [hcontract, add_zero]
    exact restriction_roundtrip_of_strictTuple_eq 𝒰
      (𝒱.tupleInter q τ) (𝒱.tupleInter q τ)
      (𝒰.strictSingleton (owner τ)) σ hsingleton
      (verticalTuple_subset_horizontalSingleton
        𝒰 𝒱 q owner howner τ)
      (P.inter_subset_right (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ))
      (fun θ ↦ x θ τ)
  · let k := 𝒰.strictInsertPosition σ (owner τ) hmem
    let ρ := 𝒰.strictInsert σ (owner τ) hmem
    let l := k.succAbove (0 : Fin 1)
    have hdelete : 𝒰.strictDelete k ρ = σ :=
      𝒰.strictDelete_strictInsert σ (owner τ) hmem
    have hidentity :
        (-1 : ℤ) ^ (k : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalInsert
                𝒰 𝒱 q owner howner σ τ hmem)
              ((-1 : ℤ) ^ (k : ℕ) •
                P.restriction
                  (doubleInter_subset_horizontalDelete 𝒰 𝒱 k ρ τ)
                  (x (𝒰.strictDelete k ρ) τ)) =
          x σ τ := by
      rw [map_zsmul, ← mul_zsmul, ← pow_add,
        (Even.add_self (k : ℕ)).neg_one_pow, one_zsmul]
      exact restriction_roundtrip_of_strictTuple_eq 𝒰
        (𝒱.tupleInter q τ)
        (P.inter (𝒰.tupleInter 1 ρ) (𝒱.tupleInter q τ))
        (𝒰.strictDelete k ρ) σ hdelete
        (doubleInter_subset_horizontalDelete 𝒰 𝒱 k ρ τ)
        (doubleInter_subset_horizontalInsert
          𝒰 𝒱 q owner howner σ τ hmem)
        (fun θ ↦ x θ τ)
    have hsingletonDelete :
        𝒰.strictSingleton (owner τ) = 𝒰.strictDelete l ρ := by
      ext a
      rw [Fin.eq_zero a, 𝒰.strictSingleton_apply]
      have hindex : l.succAbove (0 : Fin 1) = k := by
        simpa only [Fin.eq_zero ((0 : Fin 1).predAbove k)] using
          Fin.succAbove_succAbove_predAbove k (0 : Fin 1)
      exact congrArg Fin.val (by
        change owner τ = ρ (l.succAbove 0)
        rw [hindex]
        exact (𝒰.strictInsert_apply_position σ (owner τ) hmem).symm)
    have hpath :
        P.restriction
            (P.inter_subset_right (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ))
            (P.restriction
              (verticalTuple_subset_horizontalSingleton
                𝒰 𝒱 q owner howner τ)
              (x (𝒰.strictSingleton (owner τ)) τ)) =
          P.restriction
            (doubleInter_subset_horizontalInsert
              𝒰 𝒱 q owner howner σ τ hmem)
            (P.restriction
              (doubleInter_subset_horizontalDelete 𝒰 𝒱 l ρ τ)
              (x (𝒰.strictDelete l ρ) τ)) := by
      exact restriction_paths_eq_of_strictTuple_eq 𝒰
        (𝒱.tupleInter q τ)
        (𝒱.tupleInter q τ)
        (P.inter (𝒰.tupleInter 1 ρ) (𝒱.tupleInter q τ))
        (P.inter (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ))
        (𝒰.strictSingleton (owner τ)) (𝒰.strictDelete l ρ)
        hsingletonDelete
        (verticalTuple_subset_horizontalSingleton
          𝒰 𝒱 q owner howner τ)
        (P.inter_subset_right (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ))
        (doubleInter_subset_horizontalDelete 𝒰 𝒱 l ρ τ)
        (doubleInter_subset_horizontalInsert
          𝒰 𝒱 q owner howner σ τ hmem)
        (fun θ ↦ x θ τ)
    have hsign :
        (-1 : ℤ) ^ ((k : ℕ) + (l : ℕ)) = -1 := by
      have hcross := neg_one_pow_cross 0 k (0 : Fin 1)
      simp only [Fin.val_zero, zero_add,
        Fin.eq_zero ((0 : Fin 1).predAbove k), pow_zero] at hcross
      dsimp only [l]
      have hneg := congrArg Neg.neg hcross
      simpa only [neg_neg] using hneg.symm
    have hother :
        (-1 : ℤ) ^ (k : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalInsert
                𝒰 𝒱 q owner howner σ τ hmem)
              ((-1 : ℤ) ^ (l : ℕ) •
                P.restriction
                  (doubleInter_subset_horizontalDelete 𝒰 𝒱 l ρ τ)
                  (x (𝒰.strictDelete l ρ) τ)) =
          -P.restriction
            (P.inter_subset_right (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ))
            (P.restriction
              (verticalTuple_subset_horizontalSingleton
                𝒰 𝒱 q owner howner τ)
              (x (𝒰.strictSingleton (owner τ)) τ)) := by
      rw [map_zsmul, ← mul_zsmul, ← pow_add, hsign, neg_one_zsmul,
        ← hpath]
    have hdifferential :
        ((horizontalCofaceModule 𝒰 𝒱 q).differential 0).hom x ρ τ =
          ∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalDelete 𝒰 𝒱 a ρ τ)
              (x (𝒰.strictDelete a ρ) τ) := by
      rw [CofaceModule.differential]
      simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom,
        LinearMap.sum_apply, Finset.sum_apply]
      rfl
    change
      P.restriction
          (P.inter_subset_right (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ))
          (P.restriction
            (verticalTuple_subset_horizontalSingleton
              𝒰 𝒱 q owner howner τ)
            (x (𝒰.strictSingleton (owner τ)) τ)) +
        (if hi : owner τ ∈ 𝒰.strictSupport σ then 0 else
          (-1 : ℤ) ^ (𝒰.strictInsertPosition σ (owner τ) hi : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalInsert
                𝒰 𝒱 q owner howner σ τ hi)
              (((horizontalCofaceModule 𝒰 𝒱 q).differential 0).hom x ρ τ)) =
        x σ τ
    rw [dif_neg hmem, hdifferential, Fin.sum_univ_succAbove _ k,
      map_add, smul_add, Fin.sum_univ_one]
    change
      P.restriction
          (P.inter_subset_right (𝒰.tupleInter 0 σ) (𝒱.tupleInter q τ))
          (P.restriction
            (verticalTuple_subset_horizontalSingleton
              𝒰 𝒱 q owner howner τ)
            (x (𝒰.strictSingleton (owner τ)) τ)) +
        ((-1 : ℤ) ^ (k : ℕ) •
          P.restriction
            (doubleInter_subset_horizontalInsert
              𝒰 𝒱 q owner howner σ τ hmem)
            ((-1 : ℤ) ^ (k : ℕ) •
              P.restriction
                (doubleInter_subset_horizontalDelete 𝒰 𝒱 k ρ τ)
                (x (𝒰.strictDelete k ρ) τ)) +
          (-1 : ℤ) ^ (k : ℕ) •
            P.restriction
              (doubleInter_subset_horizontalInsert
                𝒰 𝒱 q owner howner σ τ hmem)
              ((-1 : ℤ) ^ (l : ℕ) •
                P.restriction
                  (doubleInter_subset_horizontalDelete 𝒰 𝒱 l ρ τ)
                  (x (𝒰.strictDelete l ρ) τ))) =
        x σ τ
    rw [hidentity, hother]
    abel

/-- The explicit contraction of a horizontal row whose vertical intersections have chosen
containing horizontal members. -/
noncomputable def horizontalContractingHomotopy
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ))) :
    (horizontalAugmentedCofaceModule 𝒰 𝒱 q).ContractingHomotopy where
  h₀ := horizontalContractZero 𝒰 𝒱 q owner howner
  h n := horizontalContract 𝒰 𝒱 q owner howner n
  h₀_augmentation x :=
    horizontalContractZero_horizontalAugmentation
      𝒰 𝒱 q owner howner x
  degree_zero x := by
    funext σ τ
    exact horizontalContracting_degree_zero
      𝒰 𝒱 q owner howner x σ τ
  degree_succ n x := by
    funext σ τ
    by_cases hmem : owner τ ∈ 𝒰.strictSupport σ
    · exact horizontalContracting_degree_succ_of_mem
        𝒰 𝒱 q owner howner n x σ τ hmem
    · exact horizontalContracting_degree_succ_of_not_mem
        𝒰 𝒱 q owner howner n x σ τ hmem

/-- A horizontal row with a chosen member containing every vertical tuple intersection is
acyclic. -/
theorem horizontalAugmentedCofaceModule_acyclic_of_owner
    (howner : ∀ τ : 𝒱.StrictTuple q,
      P.subset (𝒱.tupleInter q τ) (𝒰.domain (owner τ))) :
    (horizontalAugmentedCofaceModule 𝒰 𝒱 q).complex.Acyclic :=
  (horizontalContractingHomotopy 𝒰 𝒱 q owner howner).acyclic

namespace Refinement

variable {𝒰 𝒱 : P.Family}

/-- A refinement supplies a containing coarse member for every strict tuple of the finer
family, by using its first entry. -/
noncomputable def tupleOwner (r : Refinement 𝒱 𝒰) (q : ℕ) :
    𝒱.StrictTuple q → Fin 𝒰.card :=
  fun τ ↦ r.index (τ 0)

theorem tupleInter_subset_tupleOwner (r : Refinement 𝒱 𝒰) (q : ℕ)
    (τ : 𝒱.StrictTuple q) :
    P.subset (𝒱.tupleInter q τ) (𝒰.domain (r.tupleOwner q τ)) :=
  P.subset_trans (𝒱.tupleInter_subset_domain q τ 0) (r.subset (τ 0))

/-- Every horizontal restricted row associated with a refinement is contractible. -/
theorem horizontalAugmentedCofaceModule_acyclic
    (r : Refinement 𝒱 𝒰) (q : ℕ) :
    (horizontalAugmentedCofaceModule 𝒰 𝒱 q).complex.Acyclic :=
  horizontalAugmentedCofaceModule_acyclic_of_owner
    𝒰 𝒱 q (r.tupleOwner q) (r.tupleInter_subset_tupleOwner q)

/-- If the horizontal family refines the vertical family, every vertical restricted column is
contractible. -/
theorem verticalAugmentedCofaceModule_acyclic
    (r : Refinement 𝒰 𝒱) (p : ℕ) :
    (verticalAugmentedCofaceModule 𝒰 𝒱 p).complex.Acyclic := by
  have hhorizontal :
      (horizontalAugmentedCofaceModule 𝒱 𝒰 p).complex.Acyclic :=
    r.horizontalAugmentedCofaceModule_acyclic p
  intro n
  exact (hhorizontal n).of_iso
    (verticalAugmentedCofaceModuleIso 𝒰 𝒱 p).symm

end Refinement

end Presheaf.Family

end Rigid.Cech
