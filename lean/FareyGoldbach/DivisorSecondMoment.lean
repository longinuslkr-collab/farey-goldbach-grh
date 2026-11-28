import FareyGoldbach.PrimeSums

/-! # Second moment of the ordinary divisor count -/

open Finset

namespace FareyGoldbach

private def divisorPairTriple (t : ℕ×ℕ) : ℕ×ℕ×ℕ :=
  let g := t.1.gcd t.2
  (g,t.1/g,t.2/g)

private theorem prod_divisorPairTriple {d e : ℕ} (hd : 0<d) :
    let t := divisorPairTriple (d,e)
    t.1*t.2.1*t.2.2=d.lcm e := by
  let g := d.gcd e
  have hg : 0<g := Nat.gcd_pos_of_pos_left e hd
  have hgd : g*(d/g)=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have hge : g*(e/g)=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  change g*(d/g)*(e/g)=d.lcm e
  rw [hgd]
  apply Nat.eq_of_mul_eq_mul_left hg
  calc g*(d*(e/g))=d*(g*(e/g)) := by ring
       _ = d*e := by rw [hge]
       _ = _ := (Nat.gcd_mul_lcm ..).symm

private theorem divisorPairTriple_injective : Function.Injective divisorPairTriple := by
  rintro ⟨d,e⟩ ⟨d',e'⟩ h
  let undo (v : ℕ×ℕ×ℕ) := (v.1*v.2.1,v.1*v.2.2)
  have hu (d e : ℕ) : undo (divisorPairTriple (d,e))=(d,e) := by
    change (d.gcd e*(d/d.gcd e), d.gcd e*(e/d.gcd e))=_
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left ..),Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)]
  simpa only [hu] using congrArg undo h

/-- The second moment counts pairs of divisors; dividing each pair by its gcd
embeds it into the ordered triples whose product divides the original integer. -/
theorem sum_divisors_card_sq_le {M : ℕ} (hM : 1≤M) :
    (∑ n∈Finset.Icc 1 M, (n.divisors.card:ℝ)^2) ≤ (M:ℝ)*(1+Real.log (M:ℝ))^3 := by
  let I := Finset.Icc 1 M
  let T := I ×ˢ (I ×ˢ I)
  let prod (v : ℕ×ℕ×ℕ) := v.1*v.2.1*v.2.2
  have htriple (n : ℕ) (hn : n∈I) :
      (n.divisors.card:ℝ)^2 ≤ ∑ v∈T, (if prod v∣n then 1 else 0 : ℝ) := by
    obtain ⟨hn0,hnM⟩ := mem_Icc.mp hn
    let V := T.filter (fun v => prod v∣n)
    have hmap : ((n.divisors ×ˢ n.divisors : Finset _) : Set (ℕ×ℕ)).MapsTo divisorPairTriple V := by
      rintro ⟨d,e⟩ h
      obtain ⟨hd,he⟩ := mem_product.mp h
      have hd' := Nat.pos_of_mem_divisors hd
      have he' := Nat.pos_of_mem_divisors he
      obtain ⟨hdn,_⟩ := Nat.mem_divisors.mp hd
      obtain ⟨hen,_⟩ := Nat.mem_divisors.mp he
      let g := d.gcd e
      have hg : 0<g := Nat.gcd_pos_of_pos_left _ hd'
      have hgd : g≤d := Nat.le_of_dvd hd' (Nat.gcd_dvd_left ..)
      have hge : g≤e := Nat.le_of_dvd he' (Nat.gcd_dvd_right ..)
      have hdm := (Nat.le_of_dvd hn0 hdn).trans hnM
      have hem := (Nat.le_of_dvd hn0 hen).trans hnM
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hg,hgd.trans hdm⟩,
        mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos hgd hg,(Nat.div_le_self ..).trans hdm⟩,
          mem_Icc.mpr ⟨Nat.div_pos hge hg,(Nat.div_le_self ..).trans hem⟩⟩⟩,?_⟩
      change (divisorPairTriple (d,e)).1*(divisorPairTriple (d,e)).2.1*
        (divisorPairTriple (d,e)).2.2∣n
      rw [prod_divisorPairTriple hd']
      exact Nat.lcm_dvd hdn hen
    have h := Nat.cast_le (α:=ℝ).mpr
      (card_le_card_of_injOn _ hmap divisorPairTriple_injective.injOn)
    simpa [V,Finset.sum_ite,pow_two] using h
  let f (t : ℕ) := (1:ℝ)/(t:ℝ)
  have hmult (v : ℕ×ℕ×ℕ) : (∑ n∈I, if prod v∣n then (1:ℝ) else 0) ≤
      (M:ℝ)*(f v.1*f v.2.1*f v.2.2) := by
    have hI : I=Finset.Ioc 0 M := by ext n; simp [I]; omega
    rw [hI,Finset.sum_ite]
    simp only [sum_const,nsmul_eq_mul,mul_one,mul_zero,add_zero]
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    calc _ ≤ (M:ℝ)/((prod v:ℕ):ℝ) := Nat.cast_div_le
         _ = _ := by simp only [prod,f,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]; ring
  have hfpos : 0≤∑ u∈I,f u := Finset.sum_nonneg fun _ _ => by dsimp [f]; positivity
  calc _ ≤ ∑ n∈I, ∑ v∈T, if prod v∣n then (1:ℝ) else 0 := Finset.sum_le_sum htriple
       _ = ∑ v∈T, ∑ n∈I, if prod v∣n then (1:ℝ) else 0 := Finset.sum_comm
       _ ≤ ∑ v∈T,(M:ℝ)*(f v.1*f v.2.1*f v.2.2) := Finset.sum_le_sum fun v _ => hmult v
       _ = (M:ℝ)*(∑ u∈I,f u)^3 := by
         rw [←Finset.mul_sum]
         apply congrArg
         simp only [T,Finset.sum_product,←Finset.mul_sum]
         simp only [←Finset.sum_mul]
         simp only [←Finset.mul_sum,←Finset.sum_mul]
         ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfpos (harmonic_le_one_add_log hM) 3)
         (Nat.cast_nonneg _)

end FareyGoldbach
