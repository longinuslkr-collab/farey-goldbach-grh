import FareyGoldbach.ChenAPDistributionInterfaces
import FareyGoldbach.ChenPrimeAPDistributionOfGRH

/-! # Finite CRT and medium-prime reductions for the prime progression -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem ap_prime_reflection (N r b d : ℕ) :
    (chenDivisible (chenAPA N r b) d).card =
      (N.primesLE.filter (fun p => p%r=b%r ∧ p%d=N%d)).card := by
  apply Finset.card_bij' (fun m _ => N-m) (fun p _ => N-p)
  · intro m hm
    obtain ⟨ha,hd⟩ := mem_filter.mp hm
    obtain ⟨ha,hb⟩ := mem_filter.mp ha
    obtain ⟨hh,hp⟩ := mem_filter.mp ha
    have hmN : m≤N := by simpa using mem_range.mp hh
    refine mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.sub_le ..,hp⟩,hb,?_⟩
    apply (Nat.modEq_iff_dvd' (Nat.sub_le N m)).mpr
    rwa [Nat.sub_sub_self hmN]
  · intro p hp
    obtain ⟨hp,hr,hd⟩ := mem_filter.mp hp
    obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩,?_⟩,
      (Nat.modEq_iff_dvd' hle).mp hd⟩ <;> rwa [Nat.sub_sub_self hle]
  · intro m hm
    have hh := mem_range.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hm).1).1).1
    exact Nat.sub_sub_self (by omega)
  · intro p hp
    exact Nat.sub_sub_self (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1

theorem chenAPA_card_eq_prime_class (N r b : ℕ) :
    (chenAPA N r b).card=(N.primesLE.filter (fun p => p%r=b%r)).card := by
  simpa [chenDivisible,Nat.mod_one] using ap_prime_reflection N r b 1

private theorem coprime_of_congr {n a b : ℕ} (hab : a ≡ b [MOD n]) (hb : b.Coprime n) :
    a.Coprime n := by
  refine Nat.coprime_of_dvd fun q hprime hqa hqn => ?_
  have hqb : q∣b := Nat.modEq_zero_iff_dvd.mp
    ((Nat.ModEq.of_dvd hqn hab).symm.trans (Nat.modEq_zero_iff_dvd.mpr hqa))
  exact (Nat.not_coprime_of_dvd_of_dvd hprime.one_lt hqb hqn) hb

theorem chenAPA_divisible_card_crt {N r b d : ℕ} (hrd : r.Coprime d)
    (hb : b.Coprime r) (hdN : d.Coprime N) :
    ∃ u : ℕ, u.Coprime (r*d) ∧ (chenDivisible (chenAPA N r b) d).card =
      (N.primesLE.filter (fun p => p%(r*d)=u%(r*d))).card := by
  let u := Nat.chineseRemainder hrd b N
  refine ⟨u,(coprime_of_congr u.2.1 hb).mul_right (coprime_of_congr u.2.2 hdN.symm),?_⟩
  rw [ap_prime_reflection]
  congr 1
  ext p
  simp only [mem_filter]
  refine and_congr_right fun _ => ?_
  change (p ≡ b [MOD r] ∧ p ≡ N [MOD d]) ↔ p ≡ u.val [MOD r*d]
  rw [←Nat.modEq_and_modEq_iff_modEq_mul hrd]
  exact ⟨fun ⟨h₁,h₂⟩ => ⟨h₁.trans u.2.1.symm,h₂.trans u.2.2.symm⟩,
    fun ⟨h₁,h₂⟩ => ⟨h₁.trans u.2.1,h₂.trans u.2.2⟩⟩

/-- Both main terms use the same prime count. Total variation is at most two
single-progression discrepancies because the second one is divided by φ(d). -/
theorem chenAPPrimeError_le_of_prime_classes {N r b d : ℕ} {E : ℝ}
    (hr : 0<r) (hd : 0<d) (hb : b.Coprime r) (hc : d.Coprime (r*N))
    (hB : ∀ e u : ℕ, 0<e → e≤r*d → u.Coprime e →
      |((N.primesLE.filter (fun p => p%e=u%e)).card:ℝ)-(N.primeCounting:ℝ)/(e.totient:ℝ)|≤E) :
    |chenAPPrimeError N r b d|≤2*E := by
  have hrD := hc.coprime_dvd_right (Nat.dvd_mul_right r N)
  have hN := hc.coprime_dvd_right (Nat.dvd_mul_left N r)
  obtain ⟨u,hu,he⟩ := chenAPA_divisible_card_crt hrD.symm hb hN
  have hφ : (1:ℝ)≤d.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hd)
  have h₁ := hB (r*d) u (Nat.mul_pos hr hd) le_rfl hu
  have h₂ := hB r b hr (Nat.le_mul_of_pos_right r hd) hb
  rw [←he, Nat.totient_mul hrD.symm,Nat.cast_mul,←div_div] at h₁
  rw [←chenAPA_card_eq_prime_class] at h₂
  have hh : |((N.primeCounting:ℝ)/r.totient)/d.totient -
      ((chenAPA N r b).card:ℝ)/d.totient|≤E := by
    rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ)≤d.totient by positivity),abs_sub_comm]
    exact (div_le_self (abs_nonneg _) hφ).trans h₂
  unfold chenAPPrimeError chenAPError
  exact (abs_sub_le _ (((N.primeCounting:ℝ)/(r.totient:ℝ))/(d.totient:ℝ)) _).trans
    ((add_le_add h₁ hh).trans_eq (by ring))

private theorem prime_omitted_small {N r b₁ b₂ q d : ℕ} (hp : q.Prime) (hdiv : q∣r*N)
    (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r) :
    |chenAPError (chenDivisible (chenAPA N r b₁) q) (chenCarrierMediumMass (r*N) (chenAPA N r b₁) q) d|≤1 := by
  let A := chenDivisible (chenDivisible (chenAPA N r b₁) q) d
  have hs : A⊆{N-q} := by
    intro m hm
    obtain ⟨hm,_⟩ := mem_filter.mp hm
    obtain ⟨ha,hq⟩ := mem_filter.mp hm
    rcases hp.dvd_mul.mp hdiv with hqr | hqN
    · exact ((Nat.not_coprime_of_dvd_of_dvd hp.one_lt hq hqr) (chenAPA_coprime hb₂ hadm ha)).elim
    · obtain ⟨hN,hp'⟩ := mem_filter.mp (mem_filter.mp ha).1
      have hmN : m≤N := by simpa using mem_range.mp hN
      have he := (hp'.dvd_iff_eq hp.ne_one).mp (Nat.dvd_sub hqN hq)
      exact mem_singleton.mpr (by omega)
  have hh : A.card≤1 := (card_le_card hs).trans_eq (card_singleton _)
  simpa [A,chenAPError,chenCarrierMediumMass,hdiv] using (Nat.cast_le (α:=ℝ)).mpr hh

theorem chenAPPrimeDistribution_finite {N D r b₁ b₂ : ℕ} {E : ℝ}
    (hN : 2≤N) (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r)
    (hE : 1≤E) (hAP : ∀ d : ℕ, 0<d → d≤D →
        d.Coprime (r*N) → |chenAPPrimeError N r b₁ d|≤E) :
    chenReducedError (r*N) D (chenAPPrimeError N r b₁)≤D*E ∧
      chenAPMediumError N r b₁ D≤D*E*(1+Real.log N) := by
  have h₀ := zero_le_one.trans hE
  refine ⟨sum_filtered_Ico_abs_le _ _ h₀ _ ?_,?_⟩
  · intro d hd
    obtain ⟨hI,hc⟩ := mem_filter.mp hd
    exact hAP d (mem_Ico.mp hI).1 (mem_Ico.mp hI).2.le hc
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let A := chenAPA N r b₁
  have hrow (q : ℕ) (hq : q∈chenMediumPrimes z y) :
      (∑ d∈(Ico 1 (D/q)).filter (fun d => d∣chenSiftingProduct (r*N) z),
        |chenAPError (chenDivisible A q) (chenCarrierMediumMass (r*N) A q) d|)≤(D:ℝ)*E*(1/(q:ℝ)) := by
    have hp := (mem_filter.mp hq).2
    apply (sum_filtered_Ico_abs_le _ _ h₀ _ ?_).trans
    · have hf : ((D/q:ℕ):ℝ)≤(D:ℝ)/(q:ℝ) := Nat.cast_div_le
      exact (mul_le_mul_of_nonneg_right hf h₀).trans_eq (by ring)
    intro d hd
    obtain ⟨hi,hdP⟩ := mem_filter.mp hd
    by_cases hqd : q∣r*N
    · exact (prime_omitted_small hp hqd hb₂ hadm).trans hE
    have hc := chenMedium_coprime_modulus hq hdP
    have he : chenAPError (chenDivisible A q) (chenCarrierMediumMass (r*N) A q) d =
        chenAPPrimeError N r b₁ (q*d) := by
      simp only [chenAPPrimeError,chenAPError,chenCarrierMediumMass,ite_eq_right hqd,
        chenDivisible_twice hc,Nat.totient_mul hc,Nat.cast_mul,div_div,A]
    rw [he]
    exact hAP _ (Nat.mul_pos hp.pos (mem_Ico.mp hi).1)
      ((Nat.mul_le_mul_left _ (mem_Ico.mp hi).2.le).trans (Nat.mul_div_le ..))
      ((hp.coprime_iff_not_dvd.mpr hqd).mul_left ((chenSiftingProduct_coprime (r*N) z).coprime_dvd_left hdP))
  have hsub : chenMediumPrimes z y⊆Icc 1 N := by
    intro q hq
    obtain ⟨hi,hp⟩ := mem_filter.mp hq
    exact mem_Icc.mpr ⟨hp.pos,(mem_Ico.mp hi).2.le.trans
      (chenPowerLevel_le_self (a:=1/3) (by norm_num) (by omega))⟩
  apply (sum_le_sum hrow).trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (harmonic_le_one_add_log (by omega))) (by positivity)

end FareyGoldbach
