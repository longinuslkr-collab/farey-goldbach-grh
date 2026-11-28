import FareyGoldbach.ChenIntervalSwitching
import FareyGoldbach.ChenQuarterSwitching
import FareyGoldbach.ChenTheoremUnconditional

/-! # Distribution of the three quarter-cutoff switched carriers -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private inductive QuarterPattern where
  | threeAbove
  | threeMixed
  | fourMixed

private def quarterPrefix (k : QuarterPattern) (z y m : ℕ) : Prop :=
  match k with
  | .threeAbove => ∃ u v, m.primeFactorsList = [u,v] ∧ y≤u ∧ u<v
  | .threeMixed => ∃ u v, m.primeFactorsList = [u,v] ∧ z≤u ∧ u<y ∧ y≤v
  | .fourMixed => ∃ u v w, m.primeFactorsList = [u,v,w] ∧ z≤u ∧ u<y ∧ y≤v ∧ v<w

private def quarterLast (m : ℕ) : ℕ := m.primeFactorsList.getLastD 0

private def quarterLo (m : ℕ) : ℕ := quarterLast m + 2

private theorem factors_of_sorted_primes {n : ℕ} {l : List ℕ}
    (hs : l.Pairwise (·≤·)) (hp : ∀ q∈l, Nat.Prime q) (hn : l.prod = n) :
    n.primeFactorsList = l :=
  (List.Perm.eq_of_pairwise' hs (Nat.primeFactorsList_sorted n).pairwise
    (Nat.primeFactorsList_unique hn hp)).symm

private theorem factors_pair {u v : ℕ} (hu : u.Prime) (hv : v.Prime) (huv : u≤v) :
    (u*v).primeFactorsList = [u,v] := by
  apply factors_of_sorted_primes (by simp [huv]) _ (by simp)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl <;> assumption

private theorem factors_triple {u v w : ℕ} (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (huv : u≤v) (hvw : v≤w) : (u*v*w).primeFactorsList = [u,v,w] := by
  apply factors_of_sorted_primes (by simp [huv,hvw,huv.trans hvw]) _ (by simp [mul_assoc])
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl <;> assumption

private theorem odd_prime_gap {v w : ℕ} (hv : v.Prime) (hw : w.Prime)
    (hv₀ : 3≤v) (hvw : v<w) : v+2≤w := by
  obtain ⟨a,ha⟩ := hv.odd_of_ne_two (by omega)
  obtain ⟨b,hb⟩ := hw.odd_of_ne_two (by omega)
  omega

private theorem quarterPrefix_data {k : QuarterPattern} {z y m : ℕ}
    (hzy : z≤y) (ha : quarterPrefix k z y m) :
    2*y≤m ∧ y≤quarterLast m ∧
      (∀ p ∈ m.primeFactorsList, z≤p ∧ p≤quarterLast m) := by
  cases k with
  | threeAbove =>
    obtain ⟨u,v,hl,hu,hv⟩ := ha
    have hm₀ : m≠0 := by
      intro he
      simp [he] at hl
    have huP := Nat.prime_of_mem_primeFactorsList (show u ∈ m.primeFactorsList by simp [hl])
    have hprod := Nat.prod_primeFactorsList hm₀
    rw [hl] at hprod
    simp only [List.prod_cons,List.prod_nil,mul_one] at hprod
    refine ⟨(Nat.mul_le_mul huP.two_le (hu.trans hv.le)).trans_eq hprod, ?_, ?_⟩
    · simpa [quarterLast,hl] using hu.trans hv.le
    · intro p hp
      simp only [hl,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> simp [quarterLast,hl] <;> omega
  | threeMixed =>
    obtain ⟨u,v,hl,hu,huv,hv⟩ := ha
    have hm₀ : m≠0 := by
      intro he
      simp [he] at hl
    have huP := Nat.prime_of_mem_primeFactorsList (show u ∈ m.primeFactorsList by simp [hl])
    have hprod := Nat.prod_primeFactorsList hm₀
    rw [hl] at hprod
    simp only [List.prod_cons,List.prod_nil,mul_one] at hprod
    refine ⟨(Nat.mul_le_mul huP.two_le hv).trans_eq hprod, ?_, ?_⟩
    · simpa [quarterLast,hl] using hv
    · intro p hp
      simp only [hl,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> simp [quarterLast,hl] <;> omega
  | fourMixed =>
    obtain ⟨u,v,w,hl,hu,huv,hv,hvw⟩ := ha
    have hm₀ : m≠0 := by
      intro he
      simp [he] at hl
    have huP := Nat.prime_of_mem_primeFactorsList (show u ∈ m.primeFactorsList by simp [hl])
    have hvP := Nat.prime_of_mem_primeFactorsList (show v ∈ m.primeFactorsList by simp [hl])
    have hwP := Nat.prime_of_mem_primeFactorsList (show w ∈ m.primeFactorsList by simp [hl])
    have hprod := Nat.prod_primeFactorsList hm₀
    rw [hl] at hprod
    simp only [List.prod_cons,List.prod_nil,mul_one] at hprod
    have hh := Nat.mul_le_mul (Nat.mul_le_mul huP.two_le hv) (show 1≤w from hwP.pos)
    rw [mul_one,mul_assoc] at hh
    refine ⟨hh.trans_eq hprod, ?_, ?_⟩
    · simpa [quarterLast,hl] using hv.trans hvw.le
    · intro p hp
      simp only [hl,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl <;> simp [quarterLast,hl] <;> omega

private theorem quarterPair_rough {N z y : ℕ} {k : QuarterPattern} (hzy : z≤y)
    (x : ℕ×ℕ) (hx : x ∈ chenIntervalSwitchPairs N (quarterPrefix k z y) quarterLo)
    (p : ℕ) (hp : p.Prime) (hd : p ∣ x.1*x.2) : z≤p := by
  obtain ⟨hm,ha,hw,hlo,_⟩ := mem_chenIntervalSwitchPairs.mp hx
  obtain ⟨_,hy,hband⟩ := quarterPrefix_data hzy ha
  rcases hp.dvd_mul.mp hd with hd|hd
  · exact (hband _ ((Nat.mem_primeFactorsList hm.ne').mpr ⟨hp,hd⟩)).1
  · rw [(Nat.prime_dvd_prime_iff_eq hp hw).mp hd]
    exact hzy.trans (hy.trans ((Nat.le_add_right _ _).trans hlo))

private theorem quarterPair_injOn {N z y : ℕ} {k : QuarterPattern} (hzy : z≤y) :
    Set.InjOn (fun x : ℕ×ℕ ↦ x.1*x.2) (chenIntervalSwitchPairs N (quarterPrefix k z y) quarterLo) := by
  have hmax (x : ℕ×ℕ) (hx : x ∈ chenIntervalSwitchPairs N (quarterPrefix k z y) quarterLo) :
      x.2 ∈ (x.1*x.2).primeFactorsList ∧ (∀ p ∈ (x.1*x.2).primeFactorsList, p≤x.2) := by
    obtain ⟨hm,ha,hw,hlo,_⟩ := mem_chenIntervalSwitchPairs.mp hx
    have hband := (quarterPrefix_data hzy ha).2.2
    have hx₀ : x.1*x.2≠0 := (Nat.mul_pos hm hw.pos).ne'
    refine ⟨(Nat.mem_primeFactorsList hx₀).mpr ⟨hw,dvd_mul_left ..⟩, ?_⟩
    intro p hp
    obtain ⟨hpP, hd⟩ := (Nat.mem_primeFactorsList hx₀).mp hp
    rcases hpP.dvd_mul.mp hd with hd|hd
    · exact ((hband _ ((Nat.mem_primeFactorsList hm.ne').mpr ⟨hpP,hd⟩)).2).trans
        ((Nat.le_add_right _ _).trans hlo)
    · exact ((Nat.prime_dvd_prime_iff_eq hpP hw).mp hd).le
  rintro ⟨m,w⟩ hx ⟨m',w'⟩ hy he
  obtain ⟨hw, hW⟩ := hmax _ hx
  obtain ⟨hw', hW'⟩ := hmax _ hy
  change m*w = m'*w' at he
  have h₁ : w≤w' := hW' w (he ▸ hw)
  have h₂ : w'≤w := hW w' (he.symm ▸ hw')
  have hwEq := Nat.le_antisymm h₁ h₂
  subst w'
  have hmEq := Nat.eq_of_mul_eq_mul_right (mem_chenIntervalSwitchPairs.mp hx).2.2.1.pos he
  subst m'
  rfl

private theorem quarter30_eq_interval (N z y : ℕ) (hy : 3≤y) :
    chenQuarterB30 N y = chenIntervalSwitchCarrier N (quarterPrefix .threeAbove z y) quarterLo := by
  ext b
  constructor
  · intro hb
    obtain ⟨_,u,v,w,hu,hv,hw,hyu,huv,hvw,hN,rfl⟩ := Finset.mem_filter.mp hb
    have hl := factors_pair hu hv huv.le
    have hwlo : quarterLo (u*v)≤w := by
      simpa [quarterLo,quarterLast,hl] using odd_prime_gap hv hw (hy.trans (hyu.trans huv.le)) hvw
    exact Finset.mem_image.mpr ⟨(u*v,w),mem_chenIntervalSwitchPairs.mpr
      ⟨Nat.mul_pos hu.pos hv.pos, ⟨u,v,hl,hyu,huv⟩, hw, hwlo, hN⟩,rfl⟩
  · intro hb
    obtain ⟨⟨m,w⟩,hp,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hm,ha,hw,hlo,hN⟩ := mem_chenIntervalSwitchPairs.mp hp
    obtain ⟨u,v,hl,hyu,huv⟩ := ha
    have he : u*v=m := by
      have hprod := Nat.prod_primeFactorsList hm.ne'
      simpa [hl] using hprod
    have hu := Nat.prime_of_mem_primeFactorsList (show u∈m.primeFactorsList by simp [hl])
    have hv := Nat.prime_of_mem_primeFactorsList (show v∈m.primeFactorsList by simp [hl])
    have hvw : v<w := by
      simp [quarterLo,quarterLast,hl] at hlo
      omega
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le ..)),u,v,w,hu,hv,hw,hyu,huv,hvw,
      by simpa only [he] using hN,by simp [he]⟩

private theorem quarter31_eq_interval (N z y : ℕ) (hy : 3≤y) :
    chenQuarterB31 N z y = chenIntervalSwitchCarrier N (quarterPrefix .threeMixed z y) quarterLo := by
  ext b
  constructor
  · intro hb
    obtain ⟨_,u,v,w,hu,hv,hw,hzu,huy,hyv,hvw,hN,rfl⟩ := Finset.mem_filter.mp hb
    have hl := factors_pair hu hv (huy.le.trans hyv)
    have hwlo : quarterLo (u*v)≤w := by
      simpa [quarterLo,quarterLast,hl] using odd_prime_gap hv hw (hy.trans hyv) hvw
    exact Finset.mem_image.mpr ⟨(u*v,w),mem_chenIntervalSwitchPairs.mpr
      ⟨Nat.mul_pos hu.pos hv.pos, ⟨u,v,hl,hzu,huy,hyv⟩, hw, hwlo,hN⟩,rfl⟩
  · intro hb
    obtain ⟨⟨m,w⟩,hp,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hm,ha,hw,hlo,hN⟩ := mem_chenIntervalSwitchPairs.mp hp
    obtain ⟨u,v,hl,hzu,huy,hyv⟩ := ha
    have he : u*v=m := by
      have hprod := Nat.prod_primeFactorsList hm.ne'
      simpa [hl] using hprod
    have hu := Nat.prime_of_mem_primeFactorsList (show u∈m.primeFactorsList by simp [hl])
    have hv := Nat.prime_of_mem_primeFactorsList (show v∈m.primeFactorsList by simp [hl])
    have hvw : v<w := by
      simp [quarterLo,quarterLast,hl] at hlo
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le ..)),
      u,v,w,hu,hv,hw,hzu,huy,hyv,hvw,by simpa only [he] using hN,by simp [he]⟩

private theorem quarter41_eq_interval (N z y : ℕ) (hy : 3≤y) :
    chenQuarterB41 N z y = chenIntervalSwitchCarrier N (quarterPrefix .fourMixed z y) quarterLo := by
  ext b
  constructor
  · intro hb
    obtain ⟨_,u,v,w,t,hu,hv,hw,ht,hzu,huy,hyv,hvw,hwt,hN,rfl⟩ := Finset.mem_filter.mp hb
    have hl := factors_triple hu hv hw (huy.le.trans hyv) hvw.le
    have htlo : quarterLo (u*v*w)≤t := by
      simpa [quarterLo,quarterLast,hl] using odd_prime_gap hw ht (hy.trans (hyv.trans hvw.le)) hwt
    exact Finset.mem_image.mpr ⟨(u*v*w,t),mem_chenIntervalSwitchPairs.mpr
      ⟨Nat.mul_pos (Nat.mul_pos hu.pos hv.pos) hw.pos, ⟨u,v,w,hl,hzu,huy,hyv,hvw⟩, ht,htlo,hN⟩,rfl⟩
  · intro hb
    obtain ⟨⟨m,t⟩,hp,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hm,ha,ht,hlo,hN⟩ := mem_chenIntervalSwitchPairs.mp hp
    obtain ⟨u,v,w,hl,hzu,huy,hyv,hvw⟩ := ha
    have he : u*v*w=m := by
      have hprod := Nat.prod_primeFactorsList hm.ne'
      simpa [hl,mul_assoc] using hprod
    have hu := Nat.prime_of_mem_primeFactorsList (show u∈m.primeFactorsList by simp [hl])
    have hv := Nat.prime_of_mem_primeFactorsList (show v∈m.primeFactorsList by simp [hl])
    have hw := Nat.prime_of_mem_primeFactorsList (show w∈m.primeFactorsList by simp [hl])
    have hwt : w<t := by
      simp [quarterLo,quarterLast,hl] at hlo
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le ..)),
      u,v,w,t,hu,hv,hw,ht,hzu,huy,hyv,hvw,hwt,by simpa only [he] using hN,by simp [he]⟩

/-- The three reflected carriers have unconditional reduced progression discrepancy
of little-o size at any fixed sieve level below one half. -/
theorem chen_quarter_reduced_errors_unconditional {a θ : ℝ} (ha : 1/16<a) (ha' : a≤1/4)
    (hθ : 0<θ) (hhalf : θ<1/2) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      let z := chenPowerLevel a N
      let y := chenPowerLevel (1/4) N
      let D := chenPowerLevel θ N
      chenReducedError N D (chenAPError (chenQuarterB30 N y) (chenQuarterB30 N y).card) ≤ ε*chenLogScale N ∧
      chenReducedError N D (chenAPError (chenQuarterB31 N z y) (chenQuarterB31 N z y).card) ≤ ε*chenLogScale N ∧
      chenReducedError N D (chenAPError (chenQuarterB41 N z y) (chenQuarterB41 N z y).card) ≤ ε*chenLogScale N := by
  have h := chen_intervalSwitch_reduced_error_of_smallConductor smallConductorPrimeTwists_unconditional hθ hhalf ε hε
  have hy₃ := (chenPowerLevel_tendsto_atTop (a:=1/4) (by norm_num)).eventually_ge_atTop 3
  have hz := eventually_rpow_add_one_le_powerLevel (a:=1/16) (b:=a) (by norm_num) ha
  filter_upwards [h,hy₃,hz,eventually_ge_atTop (1:ℕ)] with N h hy₃ hz hN
  let z := chenPowerLevel a N
  let y := chenPowerLevel (1/4) N
  have hzy : z≤y := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) ha')
  have hyfloor : (N:ℝ)^(1/4:ℝ)<(y:ℝ)+1 := Nat.lt_floor_add_one _
  have hk (k : QuarterPattern) := h z (quarterPrefix k z y) quarterLo (by linarith only [hz])
    (fun m hm ↦ by have := (quarterPrefix_data hzy hm).1; omega)
    (fun m hm ↦ by
      have hm' : (2:ℝ)*(y:ℝ)≤m := by exact_mod_cast (quarterPrefix_data hzy hm).1
      have hy' : (3:ℝ)≤y := by exact_mod_cast hy₃
      linarith only [hyfloor,hm',hy'])
    (fun m hm ↦ by
      have hm' : (y:ℝ)≤quarterLast m := Nat.cast_le.mpr (quarterPrefix_data hzy hm).2.1
      unfold quarterLo
      push_cast
      linarith only [hyfloor,hm'])
    (quarterPair_injOn hzy) (quarterPair_rough hzy)
  exact ⟨by simpa only [← quarter30_eq_interval N z y hy₃] using hk .threeAbove,
    by simpa only [← quarter31_eq_interval N z y hy₃] using hk .threeMixed,
    by simpa only [← quarter41_eq_interval N z y hy₃] using hk .fourMixed⟩

end FareyGoldbach
