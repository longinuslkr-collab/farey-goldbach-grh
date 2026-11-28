import FareyGoldbach.ChenCRTPrimitive
import FareyGoldbach.ChenAPConductorWeights

/-! # Expanding the two progression characters by their conductors -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem chenAP_conductor_packet_le (P : Finset (ℕ×ℕ)) {r d m n : ℕ}
    [NeZero r] [NeZero d] [NeZero m] [NeZero n]
    (hm : m∣r) (hn : n∣d) (hmn : m.Coprime n) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.conductor=m),
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ => ψ.conductor=n),
        ‖∑ x ∈ P, χ ((x.1*x.2:ℕ):ZMod r) * ψ ((x.1*x.2:ℕ):ZMod d)‖) ≤
      chenMaskedPrimitiveMass P (m*n) ((r/m)*(d/n)) := by
  classical
  rw [chenConductorFiber_eq_image hm,chenConductorFiber_eq_image hn]
  rw [sum_image (fun _ _ _ _ h => DirichletCharacter.changeLevel_injective hm h)]
  simp_rw [sum_image (fun _ _ _ _ h => DirichletCharacter.changeLevel_injective hn h)]
  let A := (univ : Finset (DirichletCharacter ℂ m)).filter (fun χ => χ.IsPrimitive)
  let B := (univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ.IsPrimitive)
  let f (p : DirichletCharacter ℂ m × DirichletCharacter ℂ n) := chenCRTChar p.1 p.2
  let V (ξ : DirichletCharacter ℂ (m*n)) :=
    ‖∑ x ∈ P, chenMaskedChar ξ ((r/m)*(d/n)) x.1 * chenMaskedChar ξ ((r/m)*(d/n)) x.2‖
  have he (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) :
      ‖∑ x ∈ P, χ.changeLevel hm ((x.1*x.2:ℕ):ZMod r) * ψ.changeLevel hn ((x.1*x.2:ℕ):ZMod d)‖ =
        V (chenCRTChar χ ψ) := by
    apply congrArg norm
    apply sum_congr rfl
    intro x _
    simp only [Nat.cast_mul,map_mul]
    rw [show χ.changeLevel hm (x.1:ZMod r)*χ.changeLevel hm (x.2:ZMod r)*
        (ψ.changeLevel hn (x.1:ZMod d)*ψ.changeLevel hn (x.2:ZMod d)) =
        (χ.changeLevel hm (x.1:ZMod r)*ψ.changeLevel hn (x.1:ZMod d))*
        (χ.changeLevel hm (x.2:ZMod r)*ψ.changeLevel hn (x.2:ZMod d)) by ring,
      chenCRTChar_changeLevel_mask,chenCRTChar_changeLevel_mask]
  simp_rw [he]
  calc
    _ = ∑ p∈A ×ˢ B, V (f p) := (sum_product (s:=A) (t:=B) (fun p => V (f p))).symm
    _ = ∑ ξ∈(A ×ˢ B).image f, V ξ := (sum_image (fun _ _ _ _ h => chenCRTChar_injective hmn h)).symm
    _ ≤ _ := by
      rw [chenMaskedPrimitiveMass_of_pos]
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => norm_nonneg _)
      intro ξ hξ
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hξ
      have hAB := mem_product.mp hp
      exact mem_filter.mpr ⟨mem_univ _,chenCRTChar_isPrimitive hmn
        (mem_filter.mp hAB.1).2 (mem_filter.mp hAB.2).2⟩

/-- Split the character at `r` by all of its conductors, and the nonprincipal
character at the coprime level `d` by its conductors greater than one. -/
theorem chenAP_twisted_conductor_sum_le (P : Finset (ℕ×ℕ)) {r d : ℕ}
    [NeZero r] [NeZero d] (hrd : r.Coprime d) :
    (∑ χ : DirichletCharacter ℂ r,
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ => ψ≠1),
        ‖∑ x ∈ P, χ ((x.1*x.2:ℕ):ZMod r) * ψ ((x.1*x.2:ℕ):ZMod d)‖) ≤
      ∑ m ∈ r.divisors, ∑ n ∈ d.divisors.filter (fun n => 1<n),
        chenMaskedPrimitiveMass P (m*n) ((r/m)*(d/n)) := by
  classical
  let E := (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ => ψ≠1)
  let T := d.divisors.filter (fun n => 1<n)
  let V (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ d) :=
    ‖∑ x∈P, χ ((x.1*x.2:ℕ):ZMod r)*ψ ((x.1*x.2:ℕ):ZMod d)‖
  have hχ (χ : DirichletCharacter ℂ r) (_ : χ∈(univ:Finset _)) : χ.conductor∈r.divisors :=
    Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,NeZero.ne _⟩
  have hψ (ψ : DirichletCharacter ℂ d) (hψ : ψ∈E) : ψ.conductor∈T := by
    have hne := mt (DirichletCharacter.eq_one_iff_conductor_eq_one (χ:=ψ)).mpr (mem_filter.mp hψ).2
    have hpos := Nat.pos_of_ne_zero ψ.conductor_ne_zero
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨ψ.conductor_dvd_level,NeZero.ne _⟩,by omega⟩
  have hf (n : ℕ) (hn : n∈T) :
      E.filter (fun ψ => ψ.conductor=n) =
      (univ : Finset (DirichletCharacter ℂ d)).filter (fun ψ => ψ.conductor=n) := by
    ext ψ
    simp only [E,mem_filter,mem_univ,true_and]
    refine ⟨And.right, fun he => ⟨?_,he⟩⟩
    intro h
    have h1 := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ:=ψ)).mp h
    have h2 := (mem_filter.mp hn).2
    omega
  change (∑ χ : DirichletCharacter ℂ r,∑ ψ∈E,V χ ψ) ≤ _
  rw [←sum_fiberwise_of_maps_to hχ]
  refine sum_le_sum fun m hm => ?_
  have hm' := (Nat.mem_divisors.mp hm).1
  let : NeZero m := ⟨by intro h; exact NeZero.ne r (Nat.eq_zero_of_zero_dvd (h ▸ hm'))⟩
  calc
    _ = ∑ χ∈(univ : Finset _).filter (fun χ : DirichletCharacter ℂ r => χ.conductor=m),
        ∑ n∈T, ∑ ψ∈E.filter (fun ψ => ψ.conductor=n), V χ ψ :=
      sum_congr rfl fun χ _ => (sum_fiberwise_of_maps_to hψ (V χ)).symm
    _ = _ := Finset.sum_comm
    _ ≤ _ := by
      refine sum_le_sum fun n hn => ?_
      have hn' := (Nat.mem_divisors.mp (mem_filter.mp hn).1).1
      have hnpos := (mem_filter.mp hn).2
      let : NeZero n := ⟨by omega⟩
      simp_rw [hf n hn]
      exact chenAP_conductor_packet_le P hm' hn' ((hrd.of_dvd_left hm').of_dvd_right hn')

/-- The cofactor and fixed-level primitive conductor appear independently in
the final masked first moment. -/
theorem chenAP_masked_conductor_reindex (P : Finset (ℕ×ℕ)) (r N D : ℕ) :
    (∑ d ∈ (Ico 1 D).filter (fun d => d.Coprime (r*N)),
      (∑ m ∈ r.divisors, ∑ q ∈ d.divisors.filter (fun q => 1<q),
        chenMaskedPrimitiveMass P (m*q) ((r/m)*(d/q))) / (d.totient:ℝ)) ≤
    ∑ m ∈ r.divisors, ∑ k ∈ Ico 1 D, (1/(k.totient:ℝ)) *
      ∑ q ∈ (Ico 2 D).filter (fun q => m.Coprime q),
        chenMaskedPrimitiveMass P (m*q) ((r/m)*k)/(q.totient:ℝ) :=
  chenAP_conductor_reindex r N D
    (fun m q k => chenMaskedPrimitiveMass P (m*q) ((r/m)*k))
    (fun m q k => chenMaskedPrimitiveMass_nonneg P (m*q) ((r/m)*k))

end FareyGoldbach
