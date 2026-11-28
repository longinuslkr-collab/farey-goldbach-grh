import FareyGoldbach.ChenQuarterSwitching
import FareyGoldbach.ChenSwitchingKernel

/-! # A rational box certificate for the four-prime switching mass -/

namespace FareyGoldbach

open Filter Finset
open scoped Classical Topology

private noncomputable def gridU (i : ℕ) : ℝ := 4/25+(i:ℝ)*(3/200)
private noncomputable def gridV (j : ℕ) : ℝ := 1/4+(j:ℝ)*(61/10000)
private noncomputable def gridW (i j : ℕ) : ℝ := (1-gridU i-gridV j)/2+1/5000

private noncomputable def quarter41Grid : Finset (ℕ × ℕ) :=
  (range 6 ×ˢ range 5).filter (fun k ↦ gridU k.1+3*gridV k.2≤2501/2500)

private noncomputable def quarterBand (N : ℕ) (a b : ℝ) : Finset ℕ :=
  chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N)

private noncomputable def quarter41Patch (N : ℕ) (a b c d e : ℝ) : Finset ℕ :=
  ((quarterBand N a b ×ˢ quarterBand N c d) ×ˢ quarterBand N c e).biUnion fun k ↦
    let m := k.1.1*k.1.2*k.2
    if k.2≤N/m then (N/m).primesLE.image (fun t ↦ N-m*t) else ∅

private theorem adjacent_cutoff {f : ℕ → ℕ} {p k : ℕ} (hl : f 0≤p) (hu : p<f k) :
    ∃ i<k, f i≤p ∧ p<f (i+1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : p<f k
    · obtain ⟨i,hi,hlo,hhi⟩ := ih h
      exact ⟨i,by omega,hlo,hhi⟩
    · exact ⟨k,by omega,by omega,hu⟩

private theorem floor_exponent_mono {N : ℕ} {a b : ℝ} (hN : 1≤N) (hab : a≤b) :
    chenPowerLevel a N≤chenPowerLevel b N :=
  Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) hab)

/-- A prime tuple meeting the left endpoints belongs to an active cell.
The upper endpoint for the third prime has explicit room for flooring. -/
private theorem quarter41_box_geometry {a c : ℝ}
    (ha : 1/10000<a) (hc : 1/10000<c) (hac : a+c≤3/4) :
    ∀ᶠ N : ℕ in atTop, ∀ {u v w t : ℕ}, chenPowerLevel a N≤u →
      chenPowerLevel c N≤v → v≤w → w≤t → u*v*w*t<N →
      a+3*c≤2501/2500 ∧ w<chenPowerLevel ((1-a-c)/2+1/5000) N := by
  let h : ℝ := 1/10000
  let s : ℝ := (1-a-c)/2+h
  have ha' : 0≤a-h := by dsimp [h]; linarith
  have hc' : 0≤c-h := by dsimp [h]; linarith
  have hs : 0≤s := by dsimp [s,h]; linarith
  have hu := eventually_rpow_add_one_le_powerLevel ha' (show a-h<a by dsimp [h]; linarith)
  have hv := eventually_rpow_add_one_le_powerLevel hc' (show c-h<c by dsimp [h]; linarith)
  have hw := eventually_rpow_add_one_le_powerLevel hs
    (show s<(1-a-c)/2+1/5000 by dsimp [s,h]; linarith)
  filter_upwards [hu,hv,hw,eventually_ge_atTop (2:ℕ)] with N hu hv hw hN
  intro u v w t hau hcv hvw hwt hprod
  have hN' : (1:ℝ)≤N := Nat.one_le_cast.mpr (by omega)
  have hN₀ : (0:ℝ)<N := zero_lt_one.trans_le hN'
  have hu' : (N:ℝ)^(a-h)≤u := by linarith only [hu,Nat.cast_le (α:=ℝ).mpr hau]
  have hv' : (N:ℝ)^(c-h)≤v := by linarith only [hv,Nat.cast_le (α:=ℝ).mpr hcv]
  have hvw' : (v:ℝ)≤w := Nat.cast_le.mpr hvw
  have hwt' : (w:ℝ)≤t := Nat.cast_le.mpr hwt
  have hprod' : (u:ℝ)*v*w*t<N := by exact_mod_cast hprod
  have hmul : (N:ℝ)^(a-h+(c-h)+(c-h)+(c-h)) ≤ (u:ℝ)*v*w*t := by
    rw [Real.rpow_add hN₀,Real.rpow_add hN₀,Real.rpow_add hN₀]
    gcongr
    · exact hv'.trans hvw'
    · exact hv'.trans (hvw'.trans hwt')
  have hactive : a+3*c≤2501/2500 := by
    by_contra! ha₃
    have hep : (1:ℝ)≤a-h+(c-h)+(c-h)+(c-h) := by dsimp [h]; linarith
    have hNpow := Real.rpow_le_rpow_of_exponent_le hN' hep
    rw [Real.rpow_one] at hNpow
    exact (lt_irrefl (N:ℝ)) ((hNpow.trans hmul).trans_lt hprod')
  have hws : (w:ℝ)<(N:ℝ)^s := by
    by_contra! hh
    have hmul' : (N:ℝ)^(a-h+(c-h)+s+s) ≤ (u:ℝ)*v*w*t := by
      rw [Real.rpow_add hN₀,Real.rpow_add hN₀,Real.rpow_add hN₀]
      gcongr
      exact hh.trans hwt'
    rw [show a-h+(c-h)+s+s=1 by dsimp [s]; ring,Real.rpow_one] at hmul'
    exact (lt_irrefl (N:ℝ)) (hmul'.trans_lt hprod')
  exact ⟨hactive,Nat.cast_lt (α:=ℝ).mp (by linarith only [hw,hws])⟩

private theorem quarter41_grid_geometry :
    ∀ᶠ N : ℕ in atTop, chenQuarterB41 N (chenPowerLevel (4/25) N) (chenPowerLevel (1/4) N) ⊆
      quarter41Grid.biUnion (fun k ↦ quarter41Patch N (gridU k.1) (gridU (k.1+1))
        (gridV k.2) (gridV (k.2+1)) (gridW k.1 k.2)) := by
  have hlocal : ∀ᶠ N : ℕ in atTop, ∀ k∈(range 6 ×ˢ range 5 : Finset (ℕ × ℕ)),
      ∀ {u v w t : ℕ}, chenPowerLevel (gridU k.1) N≤u → chenPowerLevel (gridV k.2) N≤v →
        v≤w → w≤t → u*v*w*t<N →
        gridU k.1+3*gridV k.2≤2501/2500 ∧ w<chenPowerLevel (gridW k.1 k.2) N := by
    apply (Finset.eventually_all _).mpr
    intro k hk
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hk
    have hi' : (k.1:ℝ)<6 := Nat.cast_lt.mpr (Finset.mem_range.mp hi)
    have hj' : (k.2:ℝ)<5 := Nat.cast_lt.mpr (Finset.mem_range.mp hj)
    exact quarter41_box_geometry (by dsimp [gridU]; linarith [Nat.cast_nonneg (α:=ℝ) k.1])
      (by dsimp [gridV]; linarith [Nat.cast_nonneg (α:=ℝ) k.2])
      (by dsimp [gridU,gridV]; linarith)
  have hglobal := quarter41_box_geometry (a:=4/25) (c:=1401/5000)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hlocal,hglobal,eventually_ge_atTop (1:ℕ)] with N hlocal hglobal hN
  intro b hb
  obtain ⟨_,u,v,w,t,hu,hv,hw,ht,hzu,huy,hyv,hvw,hwt,hprod,hb⟩ := Finset.mem_filter.mp hb
  have hvCap : v<chenPowerLevel (gridV 5) N := by
    have hv' : v<chenPowerLevel (1401/5000) N := by
      by_contra! hcontra
      have h := (hglobal hzu hcontra hvw.le hwt.le hprod).1
      norm_num at h
    exact hv'.trans_le (floor_exponent_mono hN (by norm_num [gridV]))
  obtain ⟨i,hi,hiu,hub⟩ := adjacent_cutoff (k:=6) (f:=fun i ↦ chenPowerLevel (gridU i) N)
    (by simpa [gridU] using hzu) (by convert huy using 1; norm_num [gridU])
  obtain ⟨j,hj,hjv,hvb⟩ := adjacent_cutoff (k:=5) (f:=fun j ↦ chenPowerLevel (gridV j) N)
    (by simpa [gridV] using hyv) hvCap
  have hgrid : (i,j)∈(range 6 ×ˢ range 5 : Finset (ℕ × ℕ)) :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi,Finset.mem_range.mpr hj⟩
  obtain ⟨hactive,hwCap⟩ := hlocal (i,j) hgrid hiu hjv hvw.le hwt.le hprod
  have hd : 0<u*v*w := Nat.mul_pos (Nat.mul_pos hu.pos hv.pos) hw.pos
  have htD : t≤N/(u*v*w) := (Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm t] using hprod.le)
  refine Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨hgrid,hactive⟩,?_⟩
  refine Finset.mem_biUnion.mpr ⟨((u,v),w),Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hiu,hub⟩,hu⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hjv,hvb⟩,hv⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hjv.trans hvw.le,hwCap⟩,hw⟩⟩,?_⟩
  simp only [ite_eq_left (hwt.le.trans htD)]
  exact Finset.mem_image.mpr ⟨t,Nat.mem_primesLE.mpr ⟨htD,ht⟩,hb.symm⟩

private theorem quarter41_pnt :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 0<d → chenPowerLevel (1/4) N≤N/d →
      ((N/d).primeCounting:ℝ)≤(401/100)*((N:ℝ)/Real.log N)*(1/(d:ℝ)) := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp
    (primeCounting_ratio_unconditional.eventually_lt_const (show (1:ℝ)<1001/1000 by norm_num))
  have hquarter := chenPowerLevel_tendsto_atTop (show (0:ℝ)<1/4 by norm_num)
  have hmargin := eventually_rpow_add_one_le_powerLevel (a:=2499/10000) (b:=1/4)
    (by norm_num) (by norm_num)
  filter_upwards [hquarter.eventually_ge_atTop (max Q 2),hmargin,eventually_ge_atTop (2:ℕ)]
    with N hquart hmargin hN
  intro d hd hdiv
  let n := N/d
  have hnQ : Q≤n := (le_max_left _ _).trans (hquart.trans hdiv)
  have hn₂ : 2≤n := (le_max_right _ _).trans (hquart.trans hdiv)
  have hn₁ : (1:ℝ)<n := Nat.one_lt_cast.mpr hn₂
  have hN₁ : (1:ℝ)<N := Nat.one_lt_cast.mpr hN
  have hn' : (0:ℝ)<n := zero_lt_one.trans hn₁
  have hln := Real.log_pos hn₁
  have hlN := Real.log_pos hN₁
  have hpnt := (div_lt_iff₀ (div_pos hn' hln)).mp (hQ n hnQ)
  have hlog : (2499/10000:ℝ)*Real.log N≤Real.log n := by
    rw [←Real.log_rpow (zero_lt_one.trans hN₁)]
    exact Real.log_le_log (by positivity)
      (by linarith only [hmargin,Nat.cast_le (α:=ℝ).mpr hdiv])
  have hd' : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hnN : (n:ℝ)≤(N:ℝ)/d := (le_div_iff₀ hd').mpr (by exact_mod_cast Nat.div_mul_le_self N d)
  have hpos : 0<(2499/10000:ℝ)*Real.log N := mul_pos (by norm_num) hlN
  calc
    _ ≤ (1001/1000)*((n:ℝ)/Real.log n) := hpnt.le
    _ ≤ (1001/1000)*(((N:ℝ)/d)/Real.log n) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnN hln.le) (by norm_num)
    _ ≤ (1001/1000)*(((N:ℝ)/d)/((2499/10000:ℝ)*Real.log N)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hpos hlog) (by norm_num)
    _ = ((1001/1000)/(2499/10000):ℝ)*(((N:ℝ)/Real.log N)*(1/(d:ℝ))) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

private theorem quarter41_patch_card {N : ℕ} {a b c d e : ℝ} (hN : 1≤N) (hc : 1/4≤c)
    (hpnt : ∀ m : ℕ, 0<m → chenPowerLevel (1/4) N≤N/m →
      ((N/m).primeCounting:ℝ)≤(401/100)*((N:ℝ)/Real.log N)*(1/(m:ℝ))) :
    ((quarter41Patch N a b c d e).card:ℝ) ≤ (401/100)*((N:ℝ)/Real.log N)*
      (chenSwitchBandMass N a b*chenSwitchBandMass N c d*chenSwitchBandMass N c e) := by
  let U := quarterBand N a b
  let V := quarterBand N c d
  let W := quarterBand N c e
  let C : ℝ := (401/100)*((N:ℝ)/Real.log N)
  let f (k : (ℕ × ℕ) × ℕ) : Finset ℕ :=
    let m := k.1.1*k.1.2*k.2
    if k.2≤N/m then (N/m).primesLE.image (fun t ↦ N-m*t) else ∅
  have hf (k : (ℕ × ℕ) × ℕ) (hk : k∈((U ×ˢ V) ×ˢ W)) :
      ((f k).card:ℝ) ≤ C*(1/(k.1.1:ℝ))*(1/(k.1.2:ℝ))*(1/(k.2:ℝ)) := by
    obtain ⟨⟨u,v⟩,w⟩ := k
    obtain ⟨huv,hw⟩ := Finset.mem_product.mp hk
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
    let m := u*v*w
    have hc₀ : 0≤C := by
      unfold C
      exact mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (Nat.one_le_cast.mpr hN)))
    change ((if w≤N/m then (N/m).primesLE.image (fun t ↦ N-m*t) else ∅).card:ℝ) ≤ _
    split_ifs with h
    · have hmd : 0<m := Nat.mul_pos (Nat.mul_pos (Finset.mem_filter.mp hu).2.pos
        (Finset.mem_filter.mp hv).2.pos) (Finset.mem_filter.mp hw).2.pos
      have hyw := (floor_exponent_mono hN hc).trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).1
      have hcard : (((N/m).primesLE.image (fun t ↦ N-m*t)).card:ℝ)≤((N/m).primeCounting:ℝ) := by
        rw [←Nat.primesLE_card_eq_primeCounting]
        exact Nat.cast_le.mpr Finset.card_image_le
      refine hcard.trans ((hpnt m hmd (hyw.trans h)).trans_eq ?_)
      simp only [m,Nat.cast_mul,one_div,mul_inv_rev]
      ring
    · simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have hcard := Nat.cast_le (α:=ℝ).mpr (Finset.card_biUnion_le (s:=((U ×ˢ V) ×ˢ W)) (t:=f))
  rw [Nat.cast_sum] at hcard
  refine hcard.trans ((Finset.sum_le_sum hf).trans_eq ?_)
  change (∑ k∈((U ×ˢ V) ×ˢ W), C*(1/(k.1.1:ℝ))*(1/(k.1.2:ℝ))*(1/(k.2:ℝ))) =
    C*((∑ u∈U, 1/(u:ℝ))*(∑ v∈V, 1/(v:ℝ))*(∑ w∈W, 1/(w:ℝ)))
  simp only [Finset.sum_product,←Finset.mul_sum,←Finset.sum_mul]
  ring

private noncomputable def quarter41Kernel (a b : ℝ) : ℝ := Real.log b-Real.log a

private theorem quarter41_kernel_bound {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    0≤quarter41Kernel a b ∧ quarter41Kernel a b≤(b-a)/a := by
  unfold quarter41Kernel
  have hb := ha.trans_le hab
  refine ⟨sub_nonneg.mpr (Real.log_le_log ha hab),?_⟩
  rw [←Real.log_div hb.ne' ha.ne']
  exact (Real.log_le_sub_one_of_pos (div_pos hb ha)).trans_eq
    (by rw [sub_div,div_self ha.ne'])

private theorem quarter41_certificate :
    (401/100:ℝ)*(∑ k∈quarter41Grid, ((gridU (k.1+1)-gridU k.1)/gridU k.1)*
      ((gridV (k.2+1)-gridV k.2)/gridV k.2)*((gridW k.1 k.2-gridV k.2)/gridV k.2))<3/250 := by
  norm_num [quarter41Grid,gridU,gridV,gridW,Finset.sum_filter,Finset.sum_product,Finset.sum_range_succ]

/-- The unconditional four-prime count is small relative to the prime mass.
The certificate uses thirty candidate boxes, of which twenty meet the product bound. -/
theorem chen_quarter_B41_mass :
    ∀ᶠ N : ℕ in atTop,
      ((chenQuarterB41 N (chenPowerLevel (4/25) N) (chenPowerLevel (1/4) N)).card:ℝ)
        ≤ (3/250)*((N:ℝ)/Real.log N) := by
  let cut (k : ℕ × ℕ) := (gridU k.1,gridU (k.1+1),gridV k.2,gridV (k.2+1),gridW k.1 k.2)
  let B (N : ℕ) (k : ℕ × ℕ) := quarter41Patch N (cut k).1 (cut k).2.1
    (cut k).2.2.1 (cut k).2.2.2.1 (cut k).2.2.2.2
  let H (N : ℕ) (k : ℕ × ℕ) := chenSwitchBandMass N (gridU k.1) (gridU (k.1+1))*
    chenSwitchBandMass N (gridV k.2) (gridV (k.2+1))*chenSwitchBandMass N (gridV k.2) (gridW k.1 k.2)
  let G (k : ℕ × ℕ) := quarter41Kernel (gridU k.1) (gridU (k.1+1))*
    quarter41Kernel (gridV k.2) (gridV (k.2+1))*quarter41Kernel (gridV k.2) (gridW k.1 k.2)
  have hr (k : ℕ × ℕ) : 0<gridU k.1 ∧ gridU k.1≤gridU (k.1+1) ∧
      1/4≤gridV k.2 ∧ gridV k.2≤gridV (k.2+1) := by
    have h₁ := Nat.cast_nonneg (α:=ℝ) k.1
    have h₂ := Nat.cast_nonneg (α:=ℝ) k.2
    dsimp [gridU,gridV]
    push_cast
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hw (k : ℕ × ℕ) (hk : k∈quarter41Grid) : gridV k.2≤gridW k.1 k.2 := by
    have h := (Finset.mem_filter.mp hk).2
    change gridU k.1+3*gridV k.2≤2501/2500 at h
    dsimp [gridW]
    linarith
  have ht : Tendsto (fun N ↦ (401/100)*(∑ k∈quarter41Grid,H N k)) atTop
      (𝓝 ((401/100)*(∑ k∈quarter41Grid,G k))) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro k hk
    obtain ⟨hu,hU,hv,hV⟩ := hr k
    exact ((chenSwitchBandMass_tendsto hu hU).mul
      (chenSwitchBandMass_tendsto (by linarith) hV)).mul
      (chenSwitchBandMass_tendsto (by linarith) (hw k hk))
  have hG : (401/100)*(∑ k∈quarter41Grid,G k)<3/250 := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by norm_num))
      quarter41_certificate
    intro k hk
    obtain ⟨hu,hU,hv,hV⟩ := hr k
    obtain ⟨hu₀,hu₁⟩ := quarter41_kernel_bound hu hU
    obtain ⟨hv₀,hv₁⟩ := quarter41_kernel_bound (show 0<gridV k.2 by linarith) hV
    obtain ⟨hw₀,hw₁⟩ := quarter41_kernel_bound (show 0<gridV k.2 by linarith) (hw k hk)
    exact mul_le_mul (mul_le_mul hu₁ hv₁ hv₀ (hu₀.trans hu₁)) hw₁ hw₀
      (mul_nonneg (hu₀.trans hu₁) (hv₀.trans hv₁))
  filter_upwards [quarter41_grid_geometry,quarter41_pnt,ht.eventually_lt_const hG,eventually_ge_atTop (2:ℕ)]
    with N hcover hpnt hmass hN
  have hsum (k : ℕ × ℕ) : ((B N k).card:ℝ) ≤ (401/100)*((N:ℝ)/Real.log N)*(H N k) :=
    quarter41_patch_card (by omega) (hr k).2.2.1 hpnt
  have hcard := Nat.cast_le (α:=ℝ).mpr ((Finset.card_le_card hcover).trans Finset.card_biUnion_le)
  rw [Nat.cast_sum] at hcard
  have hscale : 0≤(N:ℝ)/Real.log N :=
    div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (Nat.one_le_cast.mpr (by omega)))
  calc
    _ ≤ ∑ k∈quarter41Grid, ((B N k).card:ℝ) := hcard
    _ ≤ ∑ k∈quarter41Grid, (401/100)*((N:ℝ)/Real.log N)*(H N k) :=
      Finset.sum_le_sum (fun k _ ↦ hsum k)
    _ = ((401/100)*(∑ k∈quarter41Grid,H N k))*((N:ℝ)/Real.log N) := by rw [←Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass.le hscale

end FareyGoldbach
