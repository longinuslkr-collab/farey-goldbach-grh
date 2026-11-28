import FareyGoldbach.ChenElementaryError

/-! # Chen's switching inequality for prescribed residue classes -/

open Finset
open scoped Classical

namespace FareyGoldbach

/-- A complement `m` is retained when the prime `N-m` has residue `b`. -/
def chenAPA (N r b : ℕ) : Finset ℕ := (chenA N).filter (fun m => (N-m)%r=b%r)

/-- A switched element is `p=N-u*v*w`. The residue argument indexes the triple product. -/
noncomputable def chenAPUnrestrictedB (N r b z y : ℕ) : Finset ℕ :=
  (chenUnrestrictedB N z y).filter (fun p => (N-p)%r=b%r)

noncomputable def chenAPRepresentations (N r b₁ b₂ : ℕ) : Finset ℕ :=
  (chenRepresentations N).filter (fun p => p%r=b₁%r ∧ (N-p)%r=b₂%r)

noncomputable def chenAPCount (N r b : ℕ) : ℕ :=
  ((chenAPA N r b).filter IsAlmostPrimeTwo).card

theorem chenAP_reflect_residue_iff {N r b₁ b₂ a : ℕ} (ha : a≤N)
    (hadm : N%r=(b₁+b₂)%r) : (N-a)%r=b₂%r ↔ a%r=b₁%r := by
  have hsum : a+(N-a) ≡ b₁+b₂ [MOD r] := by rwa [Nat.add_sub_of_le ha]
  exact ⟨fun hb => (show N-a ≡ b₂ [MOD r] from hb).add_right_cancel hsum,
    fun hb => (show a ≡ b₁ [MOD r] from hb).add_left_cancel hsum⟩

/-- When residues are compatible, filtering on the product class `b₂` is
equivalent to filtering the actual switched element on its prime class `b₁`. -/
theorem chenAPUnrestrictedB_eq_prime_class {N r b₁ b₂ z y : ℕ}
    (hadm : N%r=(b₁+b₂)%r) :
    chenAPUnrestrictedB N r b₂ z y =
      (chenUnrestrictedB N z y).filter (fun p => p%r=b₁%r) := by
  ext p
  simp only [chenAPUnrestrictedB,mem_filter]
  refine and_congr_right fun hp => ?_
  have hb := mem_range.mp (mem_filter.mp hp).1
  exact chenAP_reflect_residue_iff (by omega) hadm

theorem chenAPCount_eq_representations_card {N r b₁ b₂ : ℕ}
    (hadm : N%r=(b₁+b₂)%r) :
    chenAPCount N r b₁=(chenAPRepresentations N r b₁ b₂).card := by
  unfold chenAPCount
  apply Finset.card_bij' (fun m _ => N-m) (fun p _ => N-p)
  · intro m hm
    obtain ⟨hA,halmost⟩ := mem_filter.mp hm
    obtain ⟨hA,hb⟩ := mem_filter.mp hA
    obtain ⟨hmem,hprime⟩ := mem_filter.mp hA
    have hmN : m≤N := by simpa using mem_range.mp hmem
    have he := Nat.sub_sub_self hmN
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hprime,by simpa only [he] using halmost⟩,
      hb,(chenAP_reflect_residue_iff (Nat.sub_le N m) hadm).2 hb⟩
  · intro p hp
    obtain ⟨hR,hp₁,_⟩ := mem_filter.mp hp
    obtain ⟨hmem,hprime,halmost⟩ := mem_filter.mp hR
    have hpN : p≤N := by simpa using mem_range.mp hmem
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_range.mpr (by omega),by simpa only [Nat.sub_sub_self hpN] using hprime⟩,
        by simpa only [Nat.sub_sub_self hpN] using hp₁⟩,halmost⟩
  · intro m hm
    have hh := mem_range.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hm).1).1).1
    exact Nat.sub_sub_self (by omega)
  · intro p hp
    exact Nat.sub_sub_self (by simpa using mem_range.mp (mem_filter.mp (mem_filter.mp hp).1).1)

theorem chenAPA_coprime {N r b₁ b₂ a : ℕ}
    (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r)
    (ha : a∈chenAPA N r b₁) : a.Coprime r := by
  obtain ⟨hA,hp⟩ := mem_filter.mp ha
  have haN : a≤N := by simpa using mem_range.mp (mem_filter.mp hA).1
  have ha₂ : a ≡ b₂ [MOD r] := by
    have hh := (chenAP_reflect_residue_iff (Nat.sub_le N a) hadm).2 hp
    change a%r=b₂%r
    simpa only [Nat.sub_sub_self haN] using hh
  refine Nat.coprime_of_dvd fun q hprime hqa hqr => ?_
  have hb : q∣b₂ := Nat.modEq_zero_iff_dvd.mp
    ((Nat.ModEq.of_dvd hqr ha₂).symm.trans (Nat.modEq_zero_iff_dvd.mpr hqa))
  exact (Nat.not_coprime_of_dvd_of_dvd hprime.one_lt hb hqr) hb₂

/-- On this carrier, excluding primes dividing the progression modulus leaves
exactly the same roughness condition. -/
theorem chenAPA_rough_mul_iff {N r b₁ b₂ z a : ℕ}
    (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r) (ha : a∈chenAPA N r b₁) :
    chenRough (r*N) z a ↔ chenRough N z a := by
  have hcop := chenAPA_coprime hb₂ hadm ha
  constructor
  · intro hrough q hq hp hqN hqa
    apply hrough q hq hp _ hqa
    intro hden
    rcases hp.dvd_mul.mp hden with hqr | hqN'
    · exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hqa hqr) hcop
    · exact hqN hqN'
  · exact fun h q hq hp hqN => h q hq hp (fun hd => hqN (hd.trans (Nat.dvd_mul_left N r)))

private theorem chenAP_mem_global_sift {N r b₁ b₂ z a : ℕ}
    (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r)
    (ha : a∈chenSifted (r*N) z (chenAPA N r b₁)) : a∈chenSifted N z (chenA N) := by
  obtain ⟨hA,hrough⟩ := mem_filter.mp ha
  exact mem_filter.mpr ⟨(mem_filter.mp hA).1,(chenAPA_rough_mul_iff hb₂ hadm hA).1 hrough⟩

theorem chenAP_switching_twice {N r b₁ b₂ z y : ℕ}
    (hy : N<(y+1)^3) (hy₃ : 3≤y) (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r) :
    2*(chenSifted (r*N) z (chenAPA N r b₁)).card ≤ 2*chenAPCount N r b₁ +
      (∑ q∈chenMediumPrimes z y, (chenSifted (r*N) z (chenDivisible (chenAPA N r b₁) q)).card) +
      (chenSifted (r*N) y (chenAPUnrestrictedB N r b₂ z y)).card + 2*(chenBadSet N z y).card := by
  let A := chenSifted (r*N) z (chenAPA N r b₁)
  let S := chenSifted N y (chenB N z y)
  have hsum := Finset.sum_le_sum (s:=A) (fun a ha =>
    two_charges (z:=z) hy hy₃ (chenAP_mem_global_sift hb₂ hadm (a:=a) ha))
  simp only [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib,←Finset.mul_sum,
    Finset.sum_boole,Nat.cast_id] at hsum
  have hg : (A.filter (fun a => IsAlmostPrimeTwo a)).card≤chenAPCount N r b₁ :=
    card_le_card (fun _ ha => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp ha).1).1,(mem_filter.mp ha).2⟩)
  have hb : (A.filter (·∈chenBadSet N z y)).card≤(chenBadSet N z y).card :=
    card_le_card (fun _ ha => (mem_filter.mp ha).2)
  have hAN {m : ℕ} (hm : m∈A) : m≤N := by
    simpa using mem_range.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hm).1).1).1
  have hs : (A.filter (fun m => N-m∈S)).card≤
      (chenSifted (r*N) y (chenAPUnrestrictedB N r b₂ z y)).card := by
    apply card_le_card_of_injOn (fun m => N-m)
    · intro m hm
      obtain ⟨ham,hsm⟩ := mem_filter.mp hm
      obtain ⟨hsg,hr⟩ := mem_filter.mp hsm
      have hres := (mem_filter.mp (mem_filter.mp ham).1).2
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨chenB_subset_unrestricted N z y hsg,
        (chenAP_reflect_residue_iff (Nat.sub_le N m) hadm).2 hres⟩,?_⟩
      exact fun q hq hp hqN => hr q hq hp (fun hh => hqN (hh.trans (Nat.dvd_mul_left N r)))
    · intro a ha b hb' he
      have haN := hAN (mem_filter.mp ha).1
      have hbN := hAN (mem_filter.mp hb').1
      change N-a=N-b at he
      omega
  have hi := chen_sifted_incident_sum (r*N) z y (chenAPA N r b₁)
  dsimp only [A,S] at *
  omega

/-- Finite AP switching at the two integer cutoffs, with the explicit global loss. -/
theorem chenAP_switching_inequality_floor_explicit {N r b₁ b₂ : ℕ} (hN : 2^24≤N)
    (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r) :
    let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    ((chenSifted (r*N) z (chenAPA N r b₁)).card:ℝ) -
      (1/2:ℝ)*(∑ q∈chenMediumPrimes z y, ((chenSifted (r*N) z (chenDivisible (chenAPA N r b₁) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted (r*N) y (chenAPUnrestrictedB N r b₂ z y)).card:ℝ) -
      (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) ≤ (chenAPCount N r b₁:ℝ) := by
  obtain ⟨hy,hy₃⟩ := floor_cutoff_cube hN
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  have hs := chenAP_switching_twice (z:=z) hy hy₃ hb₂ hadm
  have hreal : (2:ℝ)*(chenSifted (r*N) z (chenAPA N r b₁)).card ≤ 2*(chenAPCount N r b₁:ℝ) +
      (∑ q∈chenMediumPrimes z y, ((chenSifted (r*N) z (chenDivisible (chenAPA N r b₁) q)).card:ℝ)) +
      (chenSifted (r*N) y (chenAPUnrestrictedB N r b₂ z y)).card + 2*((chenBadSet N z y).card:ℝ) := by
    exact_mod_cast hs
  have he := chenElementaryError_le hN
  change ((chenBadSet N z y).card:ℝ)≤_ at he
  dsimp only
  dsimp only [z,y] at hreal he
  linarith only [hreal,he]

end FareyGoldbach
