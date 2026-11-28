import FareyGoldbach.ChenSwitchingCell
import FareyGoldbach.ChenTheoremUnconditional

/-! # Prime counts on fixed logarithmic boxes for quarter-cutoff switching -/

open Filter Finset MeasureTheory Set
open scoped Topology Classical

namespace FareyGoldbach

private theorem fiber_card_le {N u : ℕ} {T : Finset (ℕ × ℕ × ℕ)} {V : Finset ℕ}
    (hT : ∀ {p q w : ℕ}, (p,q,w) ∈ T → p.Prime ∧ q.Prime ∧ w.Prime ∧ p*q*w < N)
    (hV : ∀ v w : ℕ, (u,v,w) ∈ T → v∈V) :
    (T.filter (fun t => t.1=u)).card ≤ ∑ v∈V, (N/(u*v)).primeCounting := by
  let F := T.filter (fun t => t.1=u)
  have hmap : (F:Set (ℕ×ℕ×ℕ)).MapsTo (fun t => t.2.1) V := by
    rintro ⟨p,v,w⟩ ht
    have hmem : (p,v,w)∈T ∧ p=u := mem_filter.mp ht
    exact hV v w (hmem.2 ▸ hmem.1)
  calc _ = ∑ v∈V, (F.filter fun t => t.2.1=v).card := card_eq_sum_card_fiberwise hmap
    _ ≤ _ := by
      apply sum_le_sum
      intro v _
      rw [← Nat.primesLE_card_eq_primeCounting]
      apply Finset.card_le_card_of_injOn (fun t : ℕ×ℕ×ℕ => t.2.2)
      · rintro ⟨p,q,w⟩ ht
        have hq' : (p,q,w)∈F ∧ q=v := mem_filter.mp ht
        have hp' : (p,q,w)∈T ∧ p=u := mem_filter.mp hq'.1
        obtain ⟨hp,hq,hw,hlt⟩ := hT hp'.1
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

private theorem cell_second_band {a h : ℝ} (ha : 1/8≤a) (ha' : a≤1/3)
    (hh : 0<h) (hh' : h≤1/24) :
    ∀ᶠ N : ℕ in atTop, ∀ {u v w : ℕ}, chenPowerLevel a N≤u →
      v≤w → u*v*w<N → v<chenPowerLevel (chenSwitchCap a h) N := by
  let s := (1-a+h)/2
  have h₁ := eventually_rpow_add_one_le_powerLevel (a:=a-h) (b:=a) (by linarith) (by linarith)
  have h₂ := eventually_rpow_add_one_le_powerLevel (a:=s) (b:=chenSwitchCap a h)
    (by dsimp [s]; linarith) (by dsimp [s,chenSwitchCap]; linarith)
  filter_upwards [h₁,h₂,eventually_ge_atTop (2:ℕ)] with N h₁ h₂ hn
  intro u v w hu hvw hm
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

/-- The portion of an ordered triple carrier in a fixed first-prime band. -/
noncomputable def chenQuarterTripleCellCount (N : ℕ) (T : Finset (ℕ × ℕ × ℕ)) (a b : ℝ) : ℝ :=
  ∑ u∈chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N),
    ((T.filter (fun t => t.1=u)).card:ℝ)

/-- Uniform PNT on the largest prime, keeping the logarithm of the middle
prime inside its reciprocal sum. -/
theorem chenQuarterTripleCellCount_eventually_le
    (T : ℕ → Finset (ℕ × ℕ × ℕ))
    (hT : ∀ {N u v w : ℕ}, (u,v,w) ∈ T N →
      u.Prime ∧ v.Prime ∧ w.Prime ∧ v ≤ w ∧ u*v*w < N)
    {a b c h δ : ℝ}
    (hc : ∀ {N u v w : ℕ}, (u,v,w) ∈ T N → chenPowerLevel a N ≤ u → chenPowerLevel c N ≤ v) (ha : 1/8≤a) (hab : a≤b) (hb : b≤1/3) (hh : 0<h)
    (hh' : h≤1/24) (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop, chenQuarterTripleCellCount N (T N) a b ≤
      (1+δ)*((N:ℝ)/Real.log N)*chenSwitchBandMass N a b *
      chenSwitchBandKernel N c (chenSwitchCap a h) (1-b) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (real_pnt_upper primeCounting_ratio_unconditional hδ)
  have hx := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/6)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop M
  filter_upwards [hx,cell_second_band ha (hab.trans hb) hh hh',eventually_ge_atTop (2:ℕ)] with N hx hsecond hn
  let U := chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N)
  let V := chenMediumPrimes (chenPowerLevel c N) (chenPowerLevel (chenSwitchCap a h) N)
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
    obtain ⟨hvN,hvt⟩ := prime_band_tag hn (a:=c) hv
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
      (((T N).filter (fun t => t.1=u)).card:ℝ) ≤
      (W*(1/(u:ℝ)))*(∑ v∈V, f v) := by
    rw [Finset.mul_sum]
    have h := fiber_card_le (u:=u) (T:=T N) (V:=V)
      (fun ht => let ⟨hu,hv,hw,_,hprod⟩ := hT ht; ⟨hu,hv,hw,hprod⟩)
      (fun v w ht => by
        have hau := (mem_Ico.mp (mem_filter.mp hu).1).1
        obtain ⟨_,hv,_,hvw,hprod⟩ := hT ht
        exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hc ht hau, hsecond hau hvw hprod⟩,hv⟩)
    have h' := Nat.cast_le (α:=ℝ).mpr h
    push_cast only [Nat.cast_sum] at h'
    exact h'.trans (Finset.sum_le_sum (hpair u hu))
  apply (Finset.sum_le_sum hF).trans_eq
  change (∑ u∈U, W*(1/(u:ℝ))*(∑ v∈V,f v))=W*(∑ u∈U,1/(u:ℝ))*(∑ v∈V,f v)
  rw [←Finset.sum_mul,←Finset.mul_sum]

/-- The mass coefficient for a first-prime band and its upper second-prime envelope. -/
noncomputable def chenQuarterTripleCellCoeff (a b c h : ℝ) : ℝ :=
  let θ := 1 - b
  let d := chenSwitchCap a h
  (Real.log b - Real.log a) * (Real.log ((d/(θ-d))/(c/(θ-c))) / θ)

theorem chenQuarterTripleCellCoeff_eventually_le
    (T : ℕ → Finset (ℕ × ℕ × ℕ))
    (hT : ∀ {N u v w : ℕ}, (u,v,w) ∈ T N →
      u.Prime ∧ v.Prime ∧ w.Prime ∧ v ≤ w ∧ u*v*w < N)
    {a b c h ε : ℝ}
    (hc : ∀ {N u v w : ℕ}, (u,v,w) ∈ T N → chenPowerLevel a N ≤ u → chenPowerLevel c N ≤ v)
    (ha : 1/8 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3) (hh : 0 < h) (hh' : h ≤ 1/24)
    (hc₀ : 0 < c) (hcd : c < chenSwitchCap a h) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, chenQuarterTripleCellCount N (T N) a b ≤
      (chenQuarterTripleCellCoeff a b c h + ε) * ((N:ℝ)/Real.log N) := by
  let θ := 1-b
  let d := chenSwitchCap a h
  let A := Real.log b - Real.log a
  let B := Real.log ((d/(θ-d))/(c/(θ-c))) / θ
  have ha₀ : 0 < a := by linarith
  have hdθ : d < θ := by dsimp [d, θ, chenSwitchCap]; linarith
  have hθ₀ : 0 < θ := by dsimp [θ]; linarith
  have hA₀ : 0 ≤ A := sub_nonneg.mpr (Real.log_le_log ha₀ hab)
  have hB₀ : 0 ≤ B := by
    have hx : 0 < c / (θ-c) := div_pos hc₀ (by linarith)
    have hy : c / (θ-c) ≤ d / (θ-d) := by
      apply div_le_div₀ (show 0≤d by linarith) hcd.le (by linarith) (by linarith)
    exact div_nonneg (Real.log_nonneg ((le_div_iff₀ hx).mpr (by simpa using hy))) hθ₀.le
  let E (t : ℝ) := (1+t)*(A+t)*(B+t)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have htend : Tendsto E (𝓝 0) (𝓝 (A*B)) := by
    simpa only [E, add_zero, zero_add, one_mul] using
      (show Tendsto E (𝓝 0) (𝓝 (E 0)) from hE.continuousAt)
  have hseq : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n, hn⟩ := ((htend.comp hseq).eventually_lt_const
    (lt_add_of_pos_right (A*B) hε)).exists
  let τ : ℝ := 1/((n:ℝ)+1)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  change E τ < A*B + ε at hn
  have hBand := (chenSwitchBandMass_tendsto ha₀ hab).eventually_lt_const (lt_add_of_pos_right A hτ)
  have hKernel := chenSwitchBandKernel_eventually_le hc₀ hcd hdθ hτ
  rw [chen_prime_band_kernel_integral_eq hc₀ hcd.le hdθ] at hKernel
  have hKernel' : ∀ᶠ N : ℕ in atTop, chenSwitchBandKernel N c d θ ≤ B+τ := by
    filter_upwards [hKernel] with N hk
    convert hk using 1
    dsimp only [B]
    ring
  filter_upwards [chenQuarterTripleCellCount_eventually_le T hT hc ha hab hb hh hh' hτ,
    hBand, hKernel', eventually_ge_atTop (2:ℕ)] with N hcell hband hkernel hN
  have hR : 0≤(N:ℝ)/Real.log N := div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg
    (Nat.one_le_cast.mpr (by omega)))
  have hband₀ : 0≤chenSwitchBandMass N a b := by unfold chenSwitchBandMass; positivity
  have hτ₀ : 0≤1+τ := by linarith
  calc
    _ ≤ (1+τ)*((N:ℝ)/Real.log N)*chenSwitchBandMass N a b * chenSwitchBandKernel N c d θ := hcell
    _ ≤ (1+τ)*((N:ℝ)/Real.log N)*chenSwitchBandMass N a b * (B+τ) :=
      mul_le_mul_of_nonneg_left hkernel (mul_nonneg (mul_nonneg hτ₀ hR) hband₀)
    _ ≤ (1+τ)*((N:ℝ)/Real.log N)*(A+τ)*(B+τ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hband.le (mul_nonneg hτ₀ hR))
        (add_nonneg hB₀ hτ.le)
    _ = E τ * ((N:ℝ)/Real.log N) := by dsimp only [E]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hR

private theorem sum_prime_bands {F : ℕ→ℕ} (hF : Monotone F) (g : ℕ→ℝ) (K : ℕ) :
    ∑ i∈range K, ∑ u∈chenMediumPrimes (F i) (F (i+1)), g u =
      ∑ u∈chenMediumPrimes (F 0) (F K),g u := by
  simp_rw [chenMediumPrimes,Finset.sum_filter]
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ,ih,sum_Ico_consecutive _ (hF (Nat.zero_le K)) (hF (Nat.le_succ K))]

/-- A finite grid of disjoint first-prime bands bounds a triple carrier. -/
theorem chenQuarterTripleMass_eventually_le_of_grid
    (T : ℕ → Finset (ℕ × ℕ × ℕ)) {g c : ℕ → ℝ} {K : ℕ} {h C ε : ℝ}
    (hT : ∀ {N u v w : ℕ}, (u,v,w) ∈ T N →
      u.Prime ∧ v.Prime ∧ w.Prime ∧ v ≤ w ∧ u*v*w < N)
    (hfirst : ∀ᶠ N : ℕ in atTop, ∀ t ∈ T N, chenPowerLevel (g 0) N ≤ t.1 ∧
      t.1 < chenPowerLevel (g K) N)
    (hgrid : Monotone g) (h₀ : 1/8 ≤ g 0) (hK : g K ≤ 1/3)
    (hc : ∀ i<K, ∀ {N u v w : ℕ}, (u,v,w) ∈ T N →
      chenPowerLevel (g i) N ≤ u → chenPowerLevel (c i) N ≤ v)
    (hc₀ : ∀ i<K, 0 < c i) (hc' : ∀ i<K, c i < chenSwitchCap (g i) h)
    (hh : 0 < h) (hh' : h ≤ 1/24) (hε : 0 < ε)
    (hCoeff : (∑ i∈range K, chenQuarterTripleCellCoeff (g i) (g (i+1)) (c i) h) ≤ C) :
    ∀ᶠ N : ℕ in atTop, ((T N).card:ℝ) ≤ (C+ε)*((N:ℝ)/Real.log N) := by
  let δ : ℝ := ε/((K:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcell : ∀ᶠ N : ℕ in atTop, ∀ i ∈ range K, chenQuarterTripleCellCount N (T N) (g i) (g (i+1)) ≤
      (chenQuarterTripleCellCoeff (g i) (g (i+1)) (c i) h + δ) * ((N:ℝ)/Real.log N) := by
    apply (Finset.eventually_all _).mpr
    intro i hi
    have hi' := mem_range.mp hi
    exact chenQuarterTripleCellCoeff_eventually_le T hT (hc i hi') (h₀.trans (hgrid (Nat.zero_le i)))
      (hgrid (Nat.le_succ i)) ((hgrid (Nat.succ_le_of_lt hi')).trans hK) hh hh'
      (hc₀ i hi') (hc' i hi') hδ
  filter_upwards [hcell,hfirst,eventually_ge_atTop (2:ℕ)] with N hcell hfirst hN
  let F := fun i : ℕ => chenPowerLevel (g i) N
  have hF : Monotone F := fun _ _ hij => Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (by omega)) (hgrid hij))
  have hMap : (T N : Set (ℕ × ℕ × ℕ)).MapsTo (fun t => t.1) (chenMediumPrimes (F 0) (F K)) := by
    rintro ⟨u,v,w⟩ ht
    have h₁ := hfirst (u,v,w) ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr h₁,(hT ht).1⟩
  have hcard : (T N).card = ∑ u∈chenMediumPrimes (F 0) (F K),
      ((T N).filter (fun t => t.1=u)).card :=
    Finset.card_eq_sum_card_fiberwise hMap
  have hcard' := congrArg (fun n : ℕ => (n:ℝ)) hcard
  push_cast at hcard'
  rw [←sum_prime_bands hF (fun u => (((T N).filter (fun t => t.1=u)).card:ℝ)) K] at hcard'
  have hR : 0≤(N:ℝ)/Real.log N := div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg
    (Nat.one_le_cast.mpr (by omega)))
  have hδK : (K:ℝ)*δ ≤ ε := by
    have hden : 0 < (K:ℝ)+1 := by positivity
    simpa only [δ,mul_div_assoc] using
      (div_le_iff₀ hden).mpr (show (K:ℝ)*ε≤ε*((K:ℝ)+1) by nlinarith only [hε])
  calc
    _ = ∑ i∈range K, chenQuarterTripleCellCount N (T N) (g i) (g (i+1)) := hcard'
    _ ≤ ∑ i∈range K, (chenQuarterTripleCellCoeff (g i) (g (i+1)) (c i) h + δ) *
        ((N:ℝ)/Real.log N) := Finset.sum_le_sum hcell
    _ = ((∑ i∈range K, chenQuarterTripleCellCoeff (g i) (g (i+1)) (c i) h)+(K:ℝ)*δ) *
        ((N:ℝ)/Real.log N) := by
      rw [←Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add hCoeff hδK) hR

end FareyGoldbach
