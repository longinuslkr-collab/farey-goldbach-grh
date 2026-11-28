import FareyGoldbach.TwinChenCarriers

/-! # Finite switching for the shifted-prime sequence -/

open Finset
open scoped Classical

namespace FareyGoldbach

/-- The squarefree combinatorial part of switching at any finite carrier.
Only the ordered triple alternative calls the switching implication. -/
theorem chen_two_charges_of_squarefree {M z y a : ℕ} {W : Prop} [Decidable W]
    (hy : M<(y+1)^3) (hy₃ : 3≤y) (ha₂ : 2≤a) (haM : a≤M)
    (hsq : Squarefree a) (hrf : ∀ q∈a.primeFactors, z≤q)
    (hsw : ∀ u v w : ℕ, u.Prime → v.Prime → w.Prime → z≤u → u<y → y≤v →
      v≤w → a=u*v*w → W) :
    2 ≤ 2*(if IsAlmostPrimeTwo a then 1 else 0) +
      ((chenMediumPrimes z y).filter (·∣a)).card + (if W then 1 else 0) := by
  by_cases hg : IsAlmostPrimeTwo a
  · rw [ite_eq_left hg]; omega
  have hmed {q : ℕ} (hq : q∈a.primeFactors) (h : q<y) : q∈(chenMediumPrimes z y).filter (·∣a) :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨hrf q hq,h⟩,Nat.prime_of_mem_primeFactors hq⟩,
      Nat.dvd_of_mem_primeFactors hq⟩
  rcases chen_squarefree_dichotomy hy hy₃ ha₂ haM hsq hrf with h|h|h
  · exact (hg ((isAlmostPrimeTwo_iff_primeFactorsList_length_le_two (by omega)).2 h)).elim
  · obtain ⟨u,hu,v,hv,hne,huy,hvy⟩ := h
    have h₂ : 2≤((chenMediumPrimes z y).filter (·∣a)).card :=
      Finset.Nontrivial.two_le_card ⟨u,hmed hu huy,v,hmed hv hvy,hne⟩
    omega
  · obtain ⟨u,v,w,hu,hv,hw,hzu,huy,hyv,hvw,he⟩ := h
    have hd : u∣a := ⟨v*w,by rw [he]; ac_rfl⟩
    have h₁ := Finset.card_pos.mpr ⟨u,hmed (Nat.mem_primeFactors.mpr ⟨hu,hd,by omega⟩) huy⟩
    rw [ite_eq_left (hsw u v w hu hv hw hzu huy hyv hvw he)]
    omega

private def twinSquareExceptions (M z : ℕ) : Finset ℕ :=
  (Ico z (M+1)).biUnion (fun d => (Ioc 0 M).filter (d^2∣·))

private def twinExceptions (M z y : ℕ) : Finset ℕ :=
  twinSquareExceptions M z ∪ (range y).image (fun p => p+2)

private theorem twinExceptions_card {M : ℕ} (hM : 2^24≤M) :
    ((twinExceptions M (chenLowerCutoff M) (chenUpperCutoff M)).card:ℝ) ≤
      2*(M:ℝ)^(7/8:ℝ)+(M:ℝ)^(1/3:ℝ) := by
  let z := chenLowerCutoff M
  let y := chenUpperCutoff M
  let t := (M:ℝ)^(1/8:ℝ)
  have hs : (twinSquareExceptions M z).card ≤ ∑ d∈Ico z (M+1), M/d^2 :=
    card_biUnion_le.trans (sum_le_sum fun d _ => (Nat.Ioc_filter_dvd_card_eq_div M (d^2)).le)
  have hc : (twinExceptions M z y).card≤(∑ d∈Ico z (M+1), M/d^2)+y := by
    apply (card_union_le ..).trans
    exact Nat.add_le_add hs (card_image_le.trans (by simp))
  have hp : (0:ℝ)<M := Nat.cast_pos.mpr (by omega)
  have ht : 4≤t := by
    have ht' : t^8=(M:ℝ) := by
      dsimp only [t]
      rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]; norm_num
    by_contra! hl
    have ht₀ : 0≤t := Real.rpow_nonneg hp.le _
    have h₄ := pow_lt_pow_left₀ hl ht₀ (by decide : 8≠0)
    have hlM : (2:ℝ)^24≤M := by exact_mod_cast hM
    linarith only [h₄,ht',hlM]
  have hzf : t<(z:ℝ)+1 := Nat.lt_floor_add_one t
  have hz : 2≤z := Nat.le_floor (by change (2:ℝ)≤t; linarith only [ht])
  have hz₀ : 0<(z:ℝ)-1 := by
    have h : (2:ℝ)≤z := by exact_mod_cast hz
    linarith only [h]
  have hr : (M:ℝ)/((z:ℝ)-1)≤2*(M:ℝ)^(7/8:ℝ) := by
    apply (div_le_iff₀ hz₀).mpr
    have ht' : t≤2*((z:ℝ)-1) := by linarith only [ht,hzf]
    have hm : (M:ℝ)^(7/8:ℝ)*t=(M:ℝ) := by
      dsimp only [t]
      rw [←Real.rpow_add hp,show (7/8+1/8:ℝ)=1 by norm_num,Real.rpow_one]
    have hh := mul_le_mul_of_nonneg_left ht' (Real.rpow_nonneg hp.le (7/8:ℝ))
    linarith only [hh,hm]
  have hy : (y:ℝ)≤(M:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have hreal := Nat.cast_le (α:=ℝ) |>.mpr hc
  simp only [Nat.cast_add,Nat.cast_sum] at hreal
  exact hreal.trans (add_le_add ((chen_square_quotient_sum_bound M z hz).trans hr) hy)

private theorem sifted_prime {K y p : ℕ} (hp : p.Prime) (hpy : y≤p) : chenRough K y p := by
  intro q hq hqp _ hd
  have hlt := mem_range.mp hq
  have he := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hd
  omega

private theorem shifted_coprime {p r b : ℕ} (hp : p.Prime) (hp₃ : 3≤p)
    (hr : p%r=b%r) (hb : (b+2).Coprime r) : (p+2).Coprime (2*r) := by
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · apply Nat.coprime_two_right.mpr
    obtain ⟨k,hk⟩ := hp.odd_iff.mpr (by omega)
    exact ⟨k+1,by omega⟩
  · have hmod := (show p≡b [MOD r] from hr).add_right 2
    change (p+2).gcd r=1
    exact hmod.gcd_eq.trans hb

private theorem twin_two_charges {X r b z y m : ℕ} (hb : (b+2).Coprime r)
    (hy : X+3<(y+1)^3) (hy₃ : 3≤y) (hm : m∈chenSifted (2*r) z (twinChenAPA X r b)) :
    2≤2*(if IsAlmostPrimeTwo m then 1 else 0) + ((chenMediumPrimes z y).filter (·∣m)).card +
      (if m-2∈chenSifted (2*r) y (twinChenAPUnrestrictedB (X+3) r b z y) then 1 else 0) +
      2*(if m∈twinExceptions (X+3) z y then 1 else 0) := by
  obtain ⟨hA,hrough⟩ := mem_filter.mp hm
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hA
  obtain ⟨hp,hres⟩ := mem_filter.mp hp
  obtain ⟨hpX,hp⟩ := Nat.mem_primesLE.mp hp
  by_cases he : p+2∈twinExceptions (X+3) z y
  · rw [ite_eq_left he]; omega
  have hpy : y≤p := by
    by_contra! h
    exact he (mem_union.mpr (Or.inr (mem_image.mpr ⟨p,mem_range.mpr h,rfl⟩)))
  have hf := chenRough_primeFactors hrough (shifted_coprime hp (hy₃.trans hpy) hres hb)
  have hsq : Squarefree (p+2) := by
    by_contra h
    rw [Nat.squarefree_iff_prime_squarefree] at h
    push Not at h
    obtain ⟨q,hq,hd⟩ := h
    have hqm : q∣p+2 := dvd_trans (dvd_mul_right q q) hd
    have hqz := hf q (Nat.mem_primeFactors.mpr ⟨hq,hqm,by omega⟩)
    have hqM := Nat.le_of_dvd (by omega : 0<p+2) hqm
    apply he
    exact mem_union.mpr (Or.inl (mem_biUnion.mpr ⟨q,mem_Ico.mpr ⟨hqz,by omega⟩,
      mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,by simpa only [sq] using hd⟩⟩))
  rw [ite_eq_right he,mul_zero,add_zero]
  apply chen_two_charges_of_squarefree hy hy₃ (by omega) (by omega) hsq hf
  intro u v w hu hv hw hzu huy hyv hvw hprod
  have hlt : u*v*w<X+3 := by omega
  have htr := mem_chenSwitchTriples.mpr ⟨hu,hv,hw,hzu,huy,hyv,hvw,hlt⟩
  have hpair : (u*v,w)∈chenSwitchPairs (X+3) z y :=
    mem_image.mpr ⟨(u,v,w),htr,rfl⟩
  have hdiff : u*v*w-2=p := by omega
  have hpr := (show p ≡ b [MOD r] from hres).add_right 2
  change (p+2)-2∈_
  rw [Nat.add_sub_cancel]
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_image.mpr ⟨(u*v,w),hpair,hdiff⟩,hpr⟩,sifted_prime hp hpy⟩

theorem twinChen_switching_inequality {X r b : ℕ} (hM : 2^24≤X+3) (hb : (b+2).Coprime r) :
    let M := X+3
    let z := chenLowerCutoff M
    let y := chenUpperCutoff M
    ((chenSifted (2*r) z (twinChenAPA X r b)).card:ℝ) -
      (1/2:ℝ)*(∑ q∈chenMediumPrimes z y,
        ((chenSifted (2*r) z (chenDivisible (twinChenAPA X r b) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted (2*r) y (twinChenAPUnrestrictedB M r b z y)).card:ℝ) -
      (2*(M:ℝ)^(7/8:ℝ)+(M:ℝ)^(1/3:ℝ)) ≤ ((twinChenRepresentations X r b).card:ℝ) := by
  let M := X+3
  let z := chenLowerCutoff M
  let y := chenUpperCutoff M
  let A := chenSifted (2*r) z (twinChenAPA X r b)
  let B := chenSifted (2*r) y (twinChenAPUnrestrictedB M r b z y)
  let E := twinExceptions M z y
  obtain ⟨hy,hy₃⟩ := floor_cutoff_cube hM
  have hs := sum_le_sum (s:=A) (fun a ha => twin_two_charges (z:=z) hb hy hy₃ (m:=a) ha)
  simp only [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib,←Finset.mul_sum,
    Finset.sum_boole,Nat.cast_id] at hs
  have hge {a : ℕ} (ha : a∈A) : 2≤a := by
    obtain ⟨p,_,rfl⟩ := mem_image.mp (mem_filter.mp ha).1
    omega
  have hinj : Set.InjOn (fun a : ℕ => a-2) A := by
    intro a ha a' ha' he
    have h := hge ha
    have h' := hge ha'
    change a-2=a'-2 at he
    omega
  have hgood : (A.filter (fun a => IsAlmostPrimeTwo a)).card≤(twinChenRepresentations X r b).card := by
    apply card_le_card_of_injOn (fun a => a-2) _ (hinj.mono (filter_subset ..))
    intro a ha
    obtain ⟨ha,hg⟩ := mem_filter.mp ha
    obtain ⟨p,hp,rfl⟩ := mem_image.mp (mem_filter.mp ha).1
    obtain ⟨hp,hres⟩ := mem_filter.mp hp
    change p+2-2∈twinChenRepresentations X r b
    rw [Nat.add_sub_cancel]
    exact mem_filter.mpr ⟨hp,hres,hg⟩
  have hsw : (A.filter (fun a => a-2∈B)).card≤B.card :=
    card_le_card_of_injOn (fun a => a-2) (fun _ ha => (mem_filter.mp ha).2) (hinj.mono (filter_subset ..))
  have he : (A.filter (·∈E)).card≤E.card := card_le_card (fun _ ha => (mem_filter.mp ha).2)
  have hi := chen_sifted_incident_sum (2*r) z y (twinChenAPA X r b)
  have hnat : 2*A.card ≤ 2*(twinChenRepresentations X r b).card+
      (∑ q∈chenMediumPrimes z y,(chenSifted (2*r) z (chenDivisible (twinChenAPA X r b) q)).card)+
      B.card+2*E.card := by
    dsimp only [A,B,E,M,y,z] at *
    omega
  have hreal := Nat.cast_le (α:=ℝ) |>.mpr hnat
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum] at hreal
  have helem := twinExceptions_card hM
  change (E.card:ℝ)≤_ at helem
  dsimp only
  change (A.card:ℝ)-1/2*(_ : ℝ)-1/2*(B.card:ℝ)-_≤_
  linarith only [hreal,helem]

end FareyGoldbach
