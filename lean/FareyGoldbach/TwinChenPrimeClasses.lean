import FareyGoldbach.TwinChenDistributionInterfaces
import FareyGoldbach.ChenAPPrimeReduction

/-! # Reduced residue classes for the shifted-prime carrier -/

open Finset
open scoped Classical

namespace FareyGoldbach

/-- A nonnegative representative of −2 at every positive modulus. -/
def twinNegTwo (d : ℕ) : ℕ := 2*d-2

theorem twin_dvd_add_two_iff {p d : ℕ} (hd : 0<d) :
    d∣p+2 ↔ p ≡ twinNegTwo d [MOD d] := by
  have h : twinNegTwo d+2 = 2*d := by unfold twinNegTwo; omega
  have hz : twinNegTwo d+2 ≡ 0 [MOD d] := by rw [h]; exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left ..)
  exact ⟨fun hp => Nat.ModEq.add_right_cancel' 2 ((Nat.modEq_zero_iff_dvd.mpr hp).trans hz.symm),
    fun hp => Nat.modEq_zero_iff_dvd.mp ((hp.add_right 2).trans hz)⟩

theorem twinNegTwo_coprime {d : ℕ} (hd : 0<d) (hc : d.Coprime 2) :
    (twinNegTwo d).Coprime d := by
  apply Nat.coprime_of_dvd
  intro q hq hqa hqd
  have h := Nat.dvd_sub (hqd.trans (dvd_mul_left d 2)) hqa
  have he : 2*d-twinNegTwo d=2 := by unfold twinNegTwo; omega
  rw [he] at h
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqd h) hc

theorem twinChenAPA_card_eq_prime_class (X r b : ℕ) :
    (twinChenAPA X r b).card=(X.primesLE.filter fun p => p%r=b%r).card := by
  exact card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)

theorem twinChenAPA_divisible_card {X r b d : ℕ} (hd : 0<d) :
    (chenDivisible (twinChenAPA X r b) d).card =
      (X.primesLE.filter fun p => p%r=b%r ∧ p%d=twinNegTwo d%d).card := by
  have he : chenDivisible (twinChenAPA X r b) d =
      (X.primesLE.filter fun p => p%r=b%r ∧ p%d=twinNegTwo d%d).image (fun p => p+2) := by
    ext m
    constructor
    · intro hm
      obtain ⟨ha,hdiv⟩ := mem_filter.mp hm
      obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
      obtain ⟨hp,hr⟩ := mem_filter.mp hp
      exact mem_image.mpr ⟨p,mem_filter.mpr ⟨hp,hr,(twin_dvd_add_two_iff hd).mp hdiv⟩,rfl⟩
    · intro hm
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hm
      obtain ⟨hp,hr,hdiv⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_image.mpr ⟨p,mem_filter.mpr ⟨hp,hr⟩,rfl⟩,
        (twin_dvd_add_two_iff hd).mpr hdiv⟩
  rw [he,Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]

private theorem reduced_of_congr {m a b : ℕ} (h : a ≡ b [MOD m]) (hb : b.Coprime m) :
    a.Coprime m := by
  refine Nat.coprime_of_dvd fun q hq hqa hqm => ?_
  have hqb := Nat.modEq_zero_iff_dvd.mp
    ((Nat.ModEq.of_dvd hqm h).symm.trans (Nat.modEq_zero_iff_dvd.mpr hqa))
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqb hqm) hb

theorem twinChenAPA_divisible_card_crt {X r b d : ℕ} (hd : 0<d) (hb : b.Coprime r)
    (hc : d.Coprime (2*r)) : ∃ u : ℕ, u.Coprime (r*d) ∧
      (chenDivisible (twinChenAPA X r b) d).card=(X.primesLE.filter fun p => p%(r*d)=u%(r*d)).card := by
  have hrd := (hc.coprime_dvd_right (dvd_mul_left r 2)).symm
  have hd₂ := hc.coprime_dvd_right (dvd_mul_right 2 r)
  let u := Nat.chineseRemainder hrd b (twinNegTwo d)
  refine ⟨u,(reduced_of_congr u.2.1 hb).mul_right (reduced_of_congr u.2.2 (twinNegTwo_coprime hd hd₂)),?_⟩
  rw [twinChenAPA_divisible_card hd]
  congr 1
  ext p
  simp only [mem_filter]
  refine and_congr_right fun _ => ?_
  change (p ≡ b [MOD r] ∧ p ≡ twinNegTwo d [MOD d]) ↔ p ≡ u.val [MOD r*d]
  rw [←Nat.modEq_and_modEq_iff_modEq_mul hrd]
  exact ⟨fun ⟨h₁,h₂⟩ => ⟨h₁.trans u.2.1.symm,h₂.trans u.2.2.symm⟩,
    fun ⟨h₁,h₂⟩ => ⟨h₁.trans u.2.1,h₂.trans u.2.2⟩⟩

/-- Extending a prime-class count by three integers changes it by at most three. -/
theorem twin_prime_class_shift (X d a : ℕ) :
    |((X.primesLE.filter fun p => p%d=a%d).card:ℝ) -
      (((X+3).primesLE.filter fun p => p%d=a%d).card:ℝ)| ≤ 3 := by
  let A := X.primesLE.filter fun p => p%d=a%d
  let B := (X+3).primesLE.filter fun p => p%d=a%d
  have hAB : A⊆B := by
    intro p hp
    obtain ⟨hp,ha⟩ := mem_filter.mp hp
    obtain ⟨hX,hp⟩ := Nat.mem_primesLE.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,hp⟩,ha⟩
  have hsub : B \ A ⊆ Ioc X (X+3) := by
    intro p hp
    obtain ⟨hp,hn⟩ := mem_sdiff.mp hp
    obtain ⟨hp,ha⟩ := mem_filter.mp hp
    obtain ⟨hX,hp⟩ := Nat.mem_primesLE.mp hp
    refine mem_Ioc.mpr ⟨lt_of_not_ge (fun hh => hn (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hh,hp⟩,ha⟩)),hX⟩
  have hh := card_le_card hsub
  rw [card_sdiff_of_subset hAB,Nat.card_Ioc] at hh
  have h₁ := card_le_card hAB
  change |(A.card:ℝ)-(B.card:ℝ)|≤3
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h₁)),neg_sub,sub_le_iff_le_add]
  exact_mod_cast (show B.card≤3+A.card by omega)

theorem twinChenPrimeError_le_of_classes {X r b d : ℕ} {E : ℝ} (hr : 0<r) (hd : 0<d)
    (hb : b.Coprime r) (hc : d.Coprime (2*r))
    (hclasses : ∀ e u : ℕ, 0<e → e≤r*d → u.Coprime e →
      |((X.primesLE.filter fun p => p%e=u%e).card:ℝ)-((X+3).primeCounting:ℝ)/e.totient|≤E) :
    |twinChenPrimeError X r b d|≤2*E := by
  obtain ⟨u,hu,he⟩ := twinChenAPA_divisible_card_crt (X:=X) hd hb hc
  have hrd := (hc.coprime_dvd_right (dvd_mul_left r 2)).symm
  have hφ : (1:ℝ)≤d.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hd)
  have h₁ := hclasses (r*d) u (Nat.mul_pos hr hd) le_rfl hu
  have h₂ := hclasses r b hr (Nat.le_mul_of_pos_right r hd) hb
  rw [←he,Nat.totient_mul hrd,Nat.cast_mul,←div_div] at h₁
  rw [←twinChenAPA_card_eq_prime_class] at h₂
  have hdiv : |(((X+3).primeCounting:ℝ)/r.totient)/d.totient -
      ((twinChenAPA X r b).card:ℝ)/d.totient|≤E := by
    rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ)≤d.totient by positivity),abs_sub_comm]
    exact (div_le_self (abs_nonneg _) hφ).trans h₂
  unfold twinChenPrimeError chenAPError
  exact (abs_sub_le _ ((((X+3).primeCounting:ℝ)/r.totient)/d.totient) _).trans
    ((add_le_add h₁ hdiv).trans_eq (by ring))

end FareyGoldbach
