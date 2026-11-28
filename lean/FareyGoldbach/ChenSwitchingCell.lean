import FareyGoldbach.ChenSwitchingTriples
import FareyGoldbach.ChenSwitchingKernel
import FareyGoldbach.ChenSwitchingScales
import FareyGoldbach.ChenSwitchingMassMathlib

/-! # Counting the largest prime in a fixed outer switching cell -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

def chenSwitchFirstFiber (N z y u : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  (chenSwitchTriples N z y).filter (fun t => t.1=u)

theorem chenSwitchTriples_card_eq_sum (N z y : ℕ) :
    (chenSwitchTriples N z y).card =
      ∑ u∈chenMediumPrimes z y, (chenSwitchFirstFiber N z y u).card := by
  apply Finset.card_eq_sum_card_fiberwise
  rintro ⟨u,v,w⟩ ht
  obtain ⟨hu,_,_,hz,hy,_⟩ := mem_chenSwitchTriples.mp ht
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hz,hy⟩,hu⟩

private theorem fiber_card_le {N z y u : ℕ} {V : Finset ℕ}
    (hV : ∀ v w : ℕ, (u,v,w)∈chenSwitchTriples N z y → v∈V) :
    (chenSwitchFirstFiber N z y u).card ≤ ∑ v∈V, (N/(u*v)).primeCounting := by
  let F := chenSwitchFirstFiber N z y u
  have hmap : (F:Set (ℕ×ℕ×ℕ)).MapsTo (fun t => t.2.1) V := by
    rintro ⟨p,v,w⟩ ht
    have hmem : (p,v,w)∈chenSwitchTriples N z y ∧ p=u := mem_filter.mp ht
    exact hV v w (hmem.2 ▸ hmem.1)
  calc _ = ∑ v∈V, (F.filter fun t => t.2.1=v).card := card_eq_sum_card_fiberwise hmap
    _ ≤ _ := by
      apply sum_le_sum
      intro v _
      rw [← Nat.primesLE_card_eq_primeCounting]
      apply Finset.card_le_card_of_injOn (fun t : ℕ×ℕ×ℕ => t.2.2)
      · rintro ⟨p,q,w⟩ ht
        have hq' : (p,q,w)∈F ∧ q=v := mem_filter.mp ht
        have hp' : (p,q,w)∈chenSwitchTriples N z y ∧ p=u := mem_filter.mp hq'.1
        obtain ⟨hp,hq,hw,_,_,_,_,hlt⟩ := mem_chenSwitchTriples.mp hp'.1
        rw [←hp'.2,←hq'.2]
        exact Nat.mem_primesLE.mpr ⟨(Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos hq.pos)).mpr
          (by simpa only [mul_comm w] using hlt.le),hw⟩
      · rintro ⟨p,q,w⟩ h₁ ⟨p',q',w'⟩ h₂ he
        obtain ⟨h₁,hq⟩ := mem_filter.mp h₁
        obtain ⟨h₂,hq'⟩ := mem_filter.mp h₂
        have hp := (mem_filter.mp h₁).2
        have hp' := (mem_filter.mp h₂).2
        change p=u at hp
        change p'=u at hp'
        change q=v at hq
        change q'=v at hq'
        change w=w' at he
        simp [hp,hp',hq,hq',he]

/-- Uniform PNT upper estimate at a real endpoint. -/
private theorem real_pnt_upper
    (hPNT : Tendsto (fun n : ℕ => (n.primeCounting:ℝ)/((n:ℝ)/Real.log n)) atTop (𝓝 1))
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop, ((⌊x⌋₊).primeCounting:ℝ) ≤ (1+δ)*(x/Real.log x) := by
  have hf : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have h := hf.eventually (hPNT.eventually_lt_const (lt_add_of_pos_right 1 hδ))
  filter_upwards [h,hf.eventually_ge_atTop 4] with x hx hn
  let n := ⌊x⌋₊
  have hn4 : (4:ℝ)≤n := by exact_mod_cast hn
  have hx₀ : 0≤x := by
    by_contra! h'
    have h0 := Nat.floor_of_nonpos h'.le
    omega
  have hnx : (n:ℝ)≤x := Nat.floor_le hx₀
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hlx : 0<Real.log x := Real.log_pos (by linarith)
  have he : Real.exp 1 ≤ (n:ℝ) := by linarith only [Real.exp_one_lt_d9,hn4]
  have hmono := Real.log_div_self_antitoneOn he (he.trans hnx) hnx
  have hinv := one_div_le_one_div_of_le (div_pos hlx (by linarith : 0<x)) hmono
  rw [one_div_div,one_div_div] at hinv
  apply ((div_lt_iff₀ (div_pos (by linarith) hln)).mp hx).le.trans
  exact mul_le_mul_of_nonneg_left hinv (by linarith)

noncomputable def chenSwitchCap (a h : ℝ) : ℝ := (1-a)/2+h

/-- The lower floor on the first prime and the ordering of the other two put
the middle prime in one fixed power band. -/
private theorem cell_second_band {a h : ℝ} (ha : 1/8≤a) (ha' : a≤1/3)
    (hh : 0<h) (hh' : h≤1/24) :
    ∀ᶠ N : ℕ in atTop, ∀ {u v w : ℕ}, chenPowerLevel a N≤u →
      (u,v,w)∈chenSwitchTriples N (chenLowerCutoff N) (chenUpperCutoff N) →
      v∈chenMediumPrimes (chenUpperCutoff N) (chenPowerLevel (chenSwitchCap a h) N) := by
  let s := (1-a+h)/2
  have h₁ := eventually_rpow_add_one_le_powerLevel (a:=a-h) (b:=a) (by linarith) (by linarith)
  have h₂ := eventually_rpow_add_one_le_powerLevel (a:=s) (b:=chenSwitchCap a h)
    (by dsimp [s]; linarith) (by dsimp [s,chenSwitchCap]; linarith)
  filter_upwards [h₁,h₂,eventually_ge_atTop (2:ℕ)] with N h₁ h₂ hn
  intro u v w hu ht
  obtain ⟨hpu,hpv,_,_,_,hv,hvw,hm⟩ := mem_chenSwitchTriples.mp ht
  refine mem_filter.mpr ⟨mem_Ico.mpr ⟨hv,?_⟩,hpv⟩
  have hn' : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hu' : (N:ℝ)^(a-h)≤u := by linarith only [h₁,Nat.cast_le (α:=ℝ).mpr hu]
  have hw' : (v:ℝ)≤w := Nat.cast_le.mpr hvw
  have hm' : (u:ℝ)*v*w<N := by exact_mod_cast hm
  have hvs : (v:ℝ)<(N:ℝ)^s := by
    by_contra! hs
    have hprod := mul_le_mul (mul_le_mul hu' hs (Real.rpow_nonneg hn'.le _) (by positivity))
      (hs.trans hw') (Real.rpow_nonneg hn'.le _) (by positivity)
    rw [←Real.rpow_add hn',←Real.rpow_add hn',show a-h+s+s=1 by dsimp [s]; ring,
      Real.rpow_one] at hprod
    linarith only [hprod,hm']
  exact Nat.cast_lt (α:=ℝ).mp (by linarith only [h₂,hvs])

private theorem prime_band_tag {N p : ℕ} {a b : ℝ} (hn : 2≤N)
    (hp : p∈chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N)) :
    (p:ℝ)≤(N:ℝ)^b ∧ Real.log (p:ℝ)/Real.log (N:ℝ)≤b := by
  obtain ⟨hI,hpr⟩ := mem_filter.mp hp
  have hnr : (1:ℝ)<N := by exact_mod_cast hn
  have hpos := zero_lt_one.trans hnr
  have h := (Nat.cast_le (α:=ℝ).mpr (mem_Ico.mp hI).2.le).trans
    (Nat.floor_le (Real.rpow_nonneg hpos.le b))
  have hl := Real.log_le_log (Nat.cast_pos (α:=ℝ).mpr hpr.pos) h
  rw [Real.log_rpow hpos] at hl
  exact ⟨h,(div_le_iff₀ (Real.log_pos hnr)).mpr hl⟩

noncomputable def chenSwitchCellCount (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ u∈chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N),
    ((chenSwitchFirstFiber N (chenLowerCutoff N) (chenUpperCutoff N) u).card:ℝ)

/-- Uniform PNT on the largest prime, keeping the logarithm of the middle
prime inside its reciprocal sum. -/
theorem chenSwitchCellCount_eventually_le
    (hPNT : Tendsto (fun n : ℕ => (n.primeCounting:ℝ)/((n:ℝ)/Real.log n)) atTop (𝓝 1))
    {a b h δ : ℝ} (ha : 1/8≤a) (hab : a≤b) (hb : b≤1/3) (hh : 0<h)
    (hh' : h≤1/24) (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop, chenSwitchCellCount N a b ≤
      (1+δ)*((N:ℝ)/Real.log N)*chenSwitchBandMass N a b *
      chenSwitchBandKernel N (1/3) (chenSwitchCap a h) (1-b) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (real_pnt_upper hPNT hδ)
  have hx := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/6)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop M
  filter_upwards [hx,cell_second_band ha (hab.trans hb) hh hh',eventually_ge_atTop (2:ℕ)] with N hx hsecond hn
  let U := chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N)
  let V := chenMediumPrimes (chenUpperCutoff N) (chenPowerLevel (chenSwitchCap a h) N)
  let L := Real.log (N:ℝ)
  let W := (1+δ)*((N:ℝ)/L)
  let f (v : ℕ) := (1/(v:ℝ))*(1/(1-b-Real.log (v:ℝ)/L))
  have hn' : (1:ℝ)<N := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans hn'
  have hL : 0<L := Real.log_pos hn'
  have hcap : chenSwitchCap a h≤1/2 := by dsimp [chenSwitchCap]; linarith
  have hθ : chenSwitchCap a h<1-b := by linarith
  have hpair (u : ℕ) (hu : u∈U) (v : ℕ) (hv : v∈V) :
      ((N/(u*v)).primeCounting:ℝ) ≤ (W*(1/(u:ℝ)))*f v := by
    let x := (N:ℝ)/((u:ℝ)*v)
    obtain ⟨huN,hut⟩ := prime_band_tag hn hu
    obtain ⟨hvN,hvt⟩ := prime_band_tag hn (a:=1/3) hv
    have hu' : (0:ℝ)<u := Nat.cast_pos.mpr (mem_filter.mp hu).2.pos
    have hv' : (0:ℝ)<v := Nat.cast_pos.mpr (mem_filter.mp hv).2.pos
    have hNpow : (N:ℝ)^(1/6:ℝ)≤x := by
      apply (le_div_iff₀ (mul_pos hu' hv')).mpr
      calc _ ≤ (N:ℝ)^(1/6:ℝ)*((N:ℝ)^(1/3:ℝ)*(N:ℝ)^(1/2:ℝ)) := by
                 exact mul_le_mul_of_nonneg_left (mul_le_mul
                   (huN.trans (Real.rpow_le_rpow_of_exponent_le hn'.le hb))
                   (hvN.trans (Real.rpow_le_rpow_of_exponent_le hn'.le hcap)) hv'.le (by positivity)) (by positivity)
           _ = _ := by rw [←Real.rpow_add hn₀,←Real.rpow_add hn₀]; norm_num
    have hpx := hM x (le_trans hx hNpow)
    have hfloor : ⌊x⌋₊=N/(u*v) := by
      change ⌊(N:ℝ)/((u:ℝ)*v)⌋₊=_
      rw [←Nat.cast_mul,Nat.floor_div_natCast,Nat.floor_natCast]
    rw [hfloor] at hpx
    have hlog : Real.log x=L-Real.log (u:ℝ)-Real.log (v:ℝ) := by
      dsimp only [x,L]
      rw [Real.log_div hn₀.ne' (mul_ne_zero hu'.ne' hv'.ne'),Real.log_mul hu'.ne' hv'.ne']
      ring
    have hd : 0<1-b-Real.log (v:ℝ)/L := by linarith only [hvt,hθ]
    have hut' := (div_le_iff₀ hL).mp hut
    have hden : L*(1-b-Real.log (v:ℝ)/L)≤Real.log x := by
      rw [hlog,show L*(1-b-Real.log (v:ℝ)/L)=L-b*L-Real.log (v:ℝ) by field_simp]
      linarith only [hut']
    apply hpx.trans
    calc _ ≤ (1+δ)*(x/(L*(1-b-Real.log (v:ℝ)/L))) := by
               apply mul_le_mul_of_nonneg_left _ (by linarith)
               exact div_le_div_of_nonneg_left (by dsimp [x]; positivity) (mul_pos hL hd) hden
         _ = _ := by dsimp [W,x,f]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have hF (u : ℕ) (hu : u∈U) :
      ((chenSwitchFirstFiber N (chenLowerCutoff N) (chenUpperCutoff N) u).card:ℝ) ≤
      (W*(1/(u:ℝ)))*(∑ v∈V, f v) := by
    rw [Finset.mul_sum]
    have h := fiber_card_le (u:=u) (V:=V) (fun v w ht =>
      hsecond (mem_Ico.mp (mem_filter.mp hu).1).1 ht)
    have h' := Nat.cast_le (α:=ℝ).mpr h
    push_cast only [Nat.cast_sum] at h'
    exact h'.trans (Finset.sum_le_sum (hpair u hu))
  apply (Finset.sum_le_sum hF).trans_eq
  change (∑ u∈U, W*(1/(u:ℝ))*(∑ v∈V,f v))=W*(∑ u∈U,1/(u:ℝ))*(∑ v∈V,f v)
  rw [←Finset.sum_mul,←Finset.mul_sum]

end FareyGoldbach
