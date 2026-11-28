import FareyGoldbach.TwinChenPrimeClasses

/-! # Injective reduction of the medium-prime errors for shifted primes -/

open Finset
open scoped Classical

namespace FareyGoldbach

theorem twin_lower_cutoff_ge_three {N : ℕ} (hN : 3^8≤N) : 3≤chenLowerCutoff N := by
  apply Nat.le_floor
  have h₃ : (3:ℝ)=((3:ℝ)^8)^(1/8:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    norm_num
  exact h₃.le.trans (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num))

theorem twinChenMediumError_le_reducedError {X r b D : ℕ} (hz : 3≤chenLowerCutoff (X+3))
    (hb : (b+2).Coprime r) :
    twinChenMediumError X r b D ≤ chenReducedError (2*r) D (twinChenPrimeError X r b) := by
  let z := chenLowerCutoff (X+3)
  let y := chenUpperCutoff (X+3)
  let P := chenMediumPrimes z y
  let I (q : ℕ) := (Finset.Ico 1 (D/q)).filter (fun d => d∣chenSiftingProduct (2*r) z)
  let S := P.sigma I
  let T := S.filter (fun p => ¬p.1∣2*r)
  let f (p : Σ _q : ℕ, ℕ) := p.1*p.2
  let A := twinChenAPA X r b
  let g (p : Σ _q : ℕ, ℕ) := |chenAPError (chenDivisible A p.1) (chenCarrierMediumMass (2*r) A p.1) p.2|
  have memI {q d : ℕ} (h : d∈I q) : 1≤d ∧ d<D/q ∧ d∣chenSiftingProduct (2*r) z :=
    ⟨(mem_Ico.mp (mem_filter.mp h).1).1,(mem_Ico.mp (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
  have prime {q : ℕ} (hq : q∈P) : q.Prime := (mem_filter.mp hq).2
  have hzero (p : Σ _q : ℕ, ℕ) (hs : p∈S) (hbad : p.1∣2*r) : g p=0 := by
    obtain ⟨hq,_⟩ := mem_sigma.mp hs
    have h3 : 3≤p.1 := hz.trans (mem_Ico.mp (mem_filter.mp hq).1).1
    have hqr : p.1∣r := ((prime hq).dvd_mul.mp hbad).resolve_left (fun hh => by
      have := Nat.le_of_dvd (by decide : 0<2) hh
      omega)
    have hnone : chenDivisible A p.1=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hm,hqm⟩ := mem_filter.mp hm
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hm
      have hvb : v ≡ b [MOD r] := (mem_filter.mp hv).2
      have hqb : p.1∣b+2 := Nat.modEq_zero_iff_dvd.mp
        ((Nat.ModEq.of_dvd hqr (hvb.add_right 2)).symm.trans (Nat.modEq_zero_iff_dvd.mpr hqm))
      exact (Nat.not_coprime_of_dvd_of_dvd (prime hq).one_lt hqb hqr) hb
    simp only [g,chenAPError,hnone,chenCarrierMediumMass,ite_eq_left hbad]
    simp [chenDivisible]
  have hinj : Set.InjOn f T := by
    rintro ⟨q,d⟩ h₁ ⟨q',d'⟩ h₂ he
    obtain ⟨hq,hd⟩ := mem_sigma.mp (mem_filter.mp h₁).1
    obtain ⟨hq',hd'⟩ := mem_sigma.mp (mem_filter.mp h₂).1
    change q*d=q'*d' at he
    have hnq := (prime hq).coprime_iff_not_dvd.mp (chenMedium_coprime_modulus hq (memI hd').2.2)
    have hqq : q=q' := by
      have h := (prime hq).dvd_mul.mp (show q∣q'*d' by rw [←he]; exact dvd_mul_right ..)
      exact ((prime hq').dvd_iff_eq (prime hq).ne_one).mp (h.resolve_right hnq) |>.symm
    subst q'
    obtain rfl := Nat.eq_of_mul_eq_mul_left (prime hq).pos he
    rfl
  calc
    twinChenMediumError X r b D = ∑ p∈S, g p := by
      change (∑ q∈P, ∑ d∈I q, g ⟨q,d⟩)=_
      rw [←Finset.sum_sigma P I g]
    _ = ∑ p∈T, g p := by
      apply (Finset.sum_subset (by exact filter_subset ..) ?_).symm
      intro p hp hn
      exact hzero p hp (by simpa [T,hp] using hn)
    _ = ∑ p∈T, |twinChenPrimeError X r b (f p)| := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hs,hn⟩ := mem_filter.mp hp
      obtain ⟨hq,hd⟩ := mem_sigma.mp hs
      have hc := chenMedium_coprime_modulus hq (memI hd).2.2
      simp only [g,f,twinChenPrimeError,chenAPError,chenCarrierMediumMass,ite_eq_right hn,
        chenDivisible_twice hc,Nat.totient_mul hc,Nat.cast_mul,div_div,A]
    _ = ∑ d∈T.image f, |twinChenPrimeError X r b d| := by
      rw [sum_image (fun _ h _ h' he => hinj h h' he)]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
      intro a ha
      obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
      obtain ⟨hs,hn⟩ := mem_filter.mp hp
      obtain ⟨hq,hd⟩ := mem_sigma.mp hs
      obtain ⟨hd₁,hdD,hdP⟩ := memI hd
      apply mem_filter.mpr
      refine ⟨mem_Ico.mpr ⟨Nat.mul_pos (prime hq).pos hd₁,?_⟩,?_⟩
      · exact (Nat.mul_lt_mul_of_pos_left hdD (prime hq).pos).trans_le (Nat.mul_div_le ..)
      · exact ((prime hq).coprime_iff_not_dvd.mpr hn).mul_left
          ((chenSiftingProduct_coprime (2*r) z).coprime_dvd_left hdP)

end FareyGoldbach
