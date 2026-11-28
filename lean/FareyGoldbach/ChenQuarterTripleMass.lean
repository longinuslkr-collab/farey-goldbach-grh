import FareyGoldbach.ChenQuarterSwitching
import FareyGoldbach.ChenQuarterMassCells
import FareyGoldbach.ChenQuarterMassCertificate

/-! # Mass bounds for the two three-prime quarter switching sequences -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private noncomputable def countTriples (N : ℕ) (P : ℕ → ℕ → Prop) : Finset (ℕ × ℕ × ℕ) :=
  (N.primesLE ×ˢ (N.primesLE ×ˢ N.primesLE)).filter
    (fun t => t.1<t.2.1 ∧ t.2.1<t.2.2 ∧ t.1*t.2.1*t.2.2<N ∧ P t.1 t.2.1)

private theorem mem_countTriples {N u v w : ℕ} {P : ℕ → ℕ → Prop} :
    (u,v,w)∈countTriples N P ↔
      u.Prime ∧ v.Prime ∧ w.Prime ∧ u<v ∧ v<w ∧ u*v*w<N ∧ P u v := by
  constructor
  · intro h
    obtain ⟨h,huv,hvw,hprod,hP⟩ := Finset.mem_filter.mp h
    obtain ⟨hu,hvw'⟩ := Finset.mem_product.mp h
    obtain ⟨hv,hw⟩ := Finset.mem_product.mp hvw'
    exact ⟨(Nat.mem_primesLE.mp hu).2,(Nat.mem_primesLE.mp hv).2,
      (Nat.mem_primesLE.mp hw).2,huv,hvw,hprod,hP⟩
  · rintro ⟨hu,hv,hw,huv,hvw,hprod,hP⟩
    have hpos : 0<u*v*w := Nat.mul_pos (Nat.mul_pos hu.pos hv.pos) hw.pos
    have huN : u≤N := (Nat.le_of_dvd hpos (show u ∣ u*v*w from ⟨v*w, by ac_rfl⟩)).trans hprod.le
    have hvN : v≤N := (Nat.le_of_dvd hpos (show v ∣ u*v*w from ⟨u*w, by ac_rfl⟩)).trans hprod.le
    have hwN : w≤N := (Nat.le_of_dvd hpos (show w ∣ u*v*w from ⟨u*v, by ac_rfl⟩)).trans hprod.le
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Nat.mem_primesLE.mpr ⟨huN,hu⟩,Finset.mem_product.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hvN,hv⟩,Nat.mem_primesLE.mpr ⟨hwN,hw⟩⟩⟩,huv,hvw,hprod,hP⟩

private theorem countTriples_constraints {N u v w : ℕ} {P : ℕ → ℕ → Prop}
    (ht : (u,v,w)∈countTriples N P) : u.Prime ∧ v.Prime ∧ w.Prime ∧ v≤w ∧ u*v*w<N := by
  obtain ⟨hu,hv,hw,_,hvw,hprod,_⟩ := mem_countTriples.mp ht
  exact ⟨hu,hv,hw,hvw.le,hprod⟩

private theorem card_B30_le (N y : ℕ) :
    (chenQuarterB30 N y).card ≤ (countTriples N (fun u _ => y≤u)).card := by
  have hsub : chenQuarterB30 N y ⊆
      (countTriples N (fun u _ => y≤u)).image (fun t => N-t.1*t.2.1*t.2.2) := by
    intro b hb
    obtain ⟨_,u,v,w,hu,hv,hw,hy,huv,hvw,hprod,hb⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_image.mpr ⟨(u,v,w),mem_countTriples.mpr
      ⟨hu,hv,hw,huv,hvw,hprod,hy⟩,hb.symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

private theorem card_B31_le (N z y : ℕ) :
    (chenQuarterB31 N z y).card ≤ (countTriples N (fun u v => z≤u ∧ u<y ∧ y≤v)).card := by
  have hsub : chenQuarterB31 N z y ⊆
      (countTriples N (fun u v => z≤u ∧ u<y ∧ y≤v)).image (fun t => N-t.1*t.2.1*t.2.2) := by
    intro b hb
    obtain ⟨_,u,v,w,hu,hv,hw,hz,hy,hyv,hvw,hprod,hb⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_image.mpr ⟨(u,v,w),mem_countTriples.mpr
      ⟨hu,hv,hw,hy.trans_le hyv,hvw,hprod,hz,hy,hyv⟩,hb.symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

private theorem first_third_lt {N u v w : ℕ} (hN : 2^24≤N)
    (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (huv : u<v) (hvw : v<w) (hprod : u*v*w<N) :
    u < chenPowerLevel (1/3) N := by
  let y := chenUpperCutoff N
  obtain ⟨hcube,hy₃⟩ := floor_cutoff_cube hN
  change u<y
  by_contra! hyu
  obtain ⟨a,ha⟩ := hu.odd_iff.mpr (by omega)
  obtain ⟨b,hb⟩ := hv.odd_iff.mpr (by omega)
  obtain ⟨c,hc⟩ := hw.odd_iff.mpr (by omega)
  have hv' : y+2≤v := by omega
  have hw' : y+4≤w := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul hyu hv') hw'
  have hp : (y+1)^3≤y*(y+2)*(y+4) := by
    exact_mod_cast (show ((y:ℤ)+1)^3≤(y:ℤ)*((y:ℤ)+2)*((y:ℤ)+4) by
      have H : (3:ℤ)≤y := by exact_mod_cast hy₃
      nlinarith only [H,sq_nonneg (y:ℤ)])
  exact (not_lt_of_ge ((hp.trans hmul).trans hprod.le)) hcube

private theorem grid_mono {A B : ℚ} (hAB : A≤B) :
    Monotone (fun i : ℕ => (chenQuarterGrid A B i:ℝ)) := by
  intro i j hij
  have hab : (A:ℝ)≤B := by exact_mod_cast hAB
  have hij' : (i:ℝ)≤j := by exact_mod_cast hij
  unfold chenQuarterGrid
  push_cast
  nlinarith only [mul_nonneg (sub_nonneg.mpr hij') (sub_nonneg.mpr hab)]

private theorem grid_zero (A B : ℚ) : (chenQuarterGrid A B 0:ℝ) = A := by
  simp [chenQuarterGrid]

private theorem grid_end (A B : ℚ) : (chenQuarterGrid A B 128:ℝ) = B := by
  unfold chenQuarterGrid
  push_cast
  ring

private theorem sum_cellCoeff_le_rounded {A B : ℚ} (hAB : A≤B)
    (ha : (1/8:ℝ)≤A) (hb : (B:ℝ)≤1/3) (c : ℚ → ℚ)
    (hc₀ : ∀ i<128, (0:ℝ)<(c (chenQuarterGrid A B i):ℝ))
    (hc : ∀ i<128, (c (chenQuarterGrid A B i):ℝ)<
      chenSwitchCap (chenQuarterGrid A B i:ℝ) (1/100000)) :
    (∑ i∈range 128, chenQuarterTripleCellCoeff (chenQuarterGrid A B i:ℝ)
      (chenQuarterGrid A B (i+1):ℝ) (c (chenQuarterGrid A B i):ℝ) (1/100000)) ≤
      ((∑ i∈range 128, chenQuarterBoxUpperRounded A B c i : ℕ):ℝ)/1000000 := by
  have hm := grid_mono hAB
  calc
    _ ≤ ∑ i∈range 128, (chenQuarterBoxUpperRounded A B c i:ℝ)/1000000 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have ha' : (0:ℝ)<(chenQuarterGrid A B i:ℝ) :=
        (show (0:ℝ)<A by linarith).trans_le ((grid_zero A B) ▸ hm (Nat.zero_le i))
      have hbK : (chenQuarterGrid A B 128:ℝ)≤1/3 := by rwa [grid_end]
      have hb' : (chenQuarterGrid A B (i+1):ℝ)≤1/3 := (hm (Nat.succ_le_of_lt hi')).trans hbK
      exact chen_quarter_box_coeff_le_rounded A B c i ha' (hm (Nat.le_succ i)) hb' (hc₀ i hi') (hc i hi')
    _ = _ := by rw [←Finset.sum_div,←Nat.cast_sum]

/-- Uniform mass bound for the ordered triple carrier with all factors above the quarter cutoff. -/
theorem chen_quarter_B30_mass :
    ∀ᶠ N : ℕ in atTop, ((chenQuarterB30 N (chenPowerLevel (1/4) N)).card:ℝ) ≤
      (149:ℝ)/1000*((N:ℝ)/Real.log N) := by
  let y := chenPowerLevel (1/4)
  let T (N : ℕ) := countTriples N (fun u _ => y N≤u)
  let g (i : ℕ) : ℝ := chenQuarterGrid (1/4) (1/3) i
  let h : ℝ := 1/100000
  have hg : Monotone g := grid_mono (by norm_num)
  have hg₀ : g 0=1/4 := by dsimp [g]; rw [grid_zero]; norm_num
  have hgK : g 128=1/3 := by dsimp [g]; rw [grid_end]; norm_num
  have hc₀ (i : ℕ) : 0<g i := by linarith only [hg (Nat.zero_le i),hg₀]
  have hcap (i : ℕ) (hi : i<128) : g i<chenSwitchCap (g i) h := by
    have hle := hg hi.le
    dsimp [chenSwitchCap,h]
    linarith only [hle,hgK]
  have hFirst : ∀ᶠ N : ℕ in atTop, ∀ t ∈ T N,
      chenPowerLevel (g 0) N≤t.1 ∧ t.1<chenPowerLevel (g 128) N := by
    filter_upwards [eventually_ge_atTop (2^24:ℕ)] with N hN
    rintro ⟨u,v,w⟩ ht
    obtain ⟨hu,hv,hw,huv,hvw,hprod,hy⟩ := mem_countTriples.mp ht
    rw [hg₀,hgK]
    exact ⟨hy,first_third_lt hN hu hv hw huv hvw hprod⟩
  have hCoeff := sum_cellCoeff_le_rounded (A:=1/4) (B:=1/3) (by norm_num) (by norm_num)
    (by norm_num) id (fun i _ => hc₀ i) hcap
  rw [chen_quarter_box_sum_30] at hCoeff
  have hMass := chenQuarterTripleMass_eventually_le_of_grid T (g:=g) (c:=g)
    (K:=128) (h:=h) (C:=(148754:ℝ)/1000000) (ε:=1/5000)
    countTriples_constraints hFirst hg (by rw [hg₀]; norm_num) hgK.le
    (fun _ _ {N u v w} ht hu => hu.trans (mem_countTriples.mp ht).2.2.2.1.le)
    (fun i _ => hc₀ i) hcap (by dsimp [h]; norm_num) (by dsimp [h]; norm_num) (by norm_num) hCoeff
  filter_upwards [hMass,eventually_ge_atTop (2:ℕ)] with N hMass hN
  have hR : 0≤(N:ℝ)/Real.log N := div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg
    (Nat.one_le_cast.mpr (by omega)))
  exact (Nat.cast_le.mpr (card_B30_le N (y N))).trans
    (hMass.trans (mul_le_mul_of_nonneg_right (by norm_num) hR))

/-- Uniform mass bound for ordered triples with one prime between the two cutoffs. -/
theorem chen_quarter_B31_mass_four_twentyfifths :
    ∀ᶠ N : ℕ in atTop,
      ((chenQuarterB31 N (chenPowerLevel (4/25) N) (chenPowerLevel (1/4) N)).card:ℝ) ≤
        (441:ℝ)/1000*((N:ℝ)/Real.log N) := by
  let y := chenPowerLevel (1/4)
  let z := chenPowerLevel (4/25)
  let T (N : ℕ) := countTriples N (fun u v => z N≤u ∧ u<y N ∧ y N≤v)
  let g (i : ℕ) : ℝ := chenQuarterGrid (4/25) (1/4) i
  let h : ℝ := 1/100000
  have hg : Monotone g := grid_mono (by norm_num)
  have hg₀ : g 0=4/25 := by dsimp [g]; rw [grid_zero]; norm_num
  have hgK : g 128=1/4 := by dsimp [g]; rw [grid_end]; norm_num
  have hcap (i : ℕ) (hi : i<128) : (1/4:ℝ)<chenSwitchCap (g i) h := by
    have hle := hg hi.le
    dsimp [chenSwitchCap,h]
    linarith only [hle,hgK]
  have hFirst : ∀ᶠ N : ℕ in atTop, ∀ t ∈ T N,
      chenPowerLevel (g 0) N≤t.1 ∧ t.1<chenPowerLevel (g 128) N := by
    filter_upwards with N
    rintro ⟨u,v,w⟩ ht
    obtain ⟨_,_,_,_,_,_,hz,hy,_⟩ := mem_countTriples.mp ht
    rw [hg₀,hgK]
    exact ⟨hz,hy⟩
  have hCoeff := sum_cellCoeff_le_rounded (A:=4/25) (B:=1/4) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => 1/4) (fun _ _ => by norm_num) (fun i hi => by
      simpa only [g,h,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hcap i hi)
  rw [chen_quarter_box_sum_31] at hCoeff
  have hCoeff' : (∑ i ∈ range 128, chenQuarterTripleCellCoeff (g i) (g (i+1)) (1/4) h)
      ≤ (439737:ℝ)/1000000 := by
    simpa only [g,h,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Nat.cast_ofNat] using hCoeff
  have hMass := chenQuarterTripleMass_eventually_le_of_grid T (g:=g) (c:=fun _ => 1/4)
    (K:=128) (h:=h) (C:=(439737:ℝ)/1000000) (ε:=1/1000)
    countTriples_constraints hFirst hg (by rw [hg₀]; norm_num) (by rw [hgK]; norm_num)
    (fun _ _ {N u v w} ht _ => (mem_countTriples.mp ht).2.2.2.2.2.2.2.2)
    (fun _ _ => by norm_num) hcap (by dsimp [h]; norm_num) (by dsimp [h]; norm_num) (by norm_num) hCoeff'
  filter_upwards [hMass,eventually_ge_atTop (2:ℕ)] with N hMass hN
  have hR : 0≤(N:ℝ)/Real.log N := div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg
    (Nat.one_le_cast.mpr (by omega)))
  exact (Nat.cast_le.mpr (card_B31_le N (z N) (y N))).trans
    (hMass.trans (mul_le_mul_of_nonneg_right (by norm_num) hR))

end FareyGoldbach
