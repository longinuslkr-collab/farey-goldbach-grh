import FareyGoldbach.ChenSwitchingCell
import FareyGoldbach.ChenSwitchingGrid
import FareyGoldbach.SharpPrimeCount

/-! # Mass of the unrestricted three-prime switching sequence -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private theorem sum_prime_bands {F : ℕ→ℕ} (hF : Monotone F) (g : ℕ→ℝ) (K : ℕ) :
    ∑ i∈range K, ∑ u∈chenMediumPrimes (F i) (F (i+1)), g u =
      ∑ u∈chenMediumPrimes (F 0) (F K),g u := by
  simp_rw [chenMediumPrimes,Finset.sum_filter]
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ,ih,sum_Ico_consecutive _ (hF (Nat.zero_le K)) (hF (Nat.le_succ K))]

private theorem grid_count_eq {K N : ℕ} (hk : 0<K) (hn : 1≤N) :
    (∑ i∈range K, chenSwitchCellCount N (chenSwitchGrid K i) (chenSwitchGrid K (i+1))) =
      ((chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ) := by
  obtain ⟨hz,he,hm,_⟩ := chenSwitchGrid_properties hk
  let F (i : ℕ) := chenPowerLevel (chenSwitchGrid K i) N
  have hF : Monotone F := fun i j hij => Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le
    (Nat.one_le_cast.mpr hn) (hm.monotone hij))
  rw [chenUnrestrictedB_card_eq_triples,chenSwitchTriples_card_eq_sum,Nat.cast_sum]
  simpa only [F,hz,he,chenSwitchCellCount,chenPowerLevel,chenLowerCutoff,chenUpperCutoff] using (sum_prime_bands hF
    (fun u => ((chenSwitchFirstFiber N (chenLowerCutoff N) (chenUpperCutoff N) u).card:ℝ)) K)

/-- All three primes range freely over the original carrier. The sole
prime-counting hypothesis is the ordinary PNT. -/
theorem chen_switching_mass_of_pnt
    (hPNT : Tendsto (fun n : ℕ => (n.primeCounting:ℝ)/((n:ℝ)/Real.log n)) atTop (𝓝 1))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ((chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ) ≤
      (chenSwitchIntegral+ε)*((N:ℝ)/Real.log (N:ℝ)) := by
  obtain ⟨K,hK,hsmall,hquad⟩ := chenSwitchGrid_upper (show 0<ε/3 by positivity)
  obtain ⟨hg₀,hgK,hmono,_⟩ := chenSwitchGrid_properties hK
  let g := chenSwitchGrid K
  let s := chenSwitchStep K
  let M (i : ℕ) := Real.log (g (i+1))-Real.log (g i)
  let C (i : ℕ) := chenSwitchCellCoeff (g i) (g (i+1)) s
  let S := ∑ i∈range K,M i*C i
  have hs : 0<s := by dsimp [s,chenSwitchStep]; positivity
  have hbounds {i : ℕ} (hi : i<K) : 1/8≤g i ∧ g i≤g (i+1) ∧ g (i+1)≤1/3 :=
    ⟨hg₀ ▸ hmono.monotone (Nat.zero_le i),hmono.monotone (Nat.le_succ i),hgK ▸ hmono.monotone hi⟩
  let E (t : ℝ) := (1+t)*∑ i∈range K,M i*(C i+t)
  have hcont : Continuous E := by dsimp [E]; fun_prop
  have hE : Tendsto E (𝓝 (0:ℝ)) (𝓝 S) := by
    have h := (show Tendsto E (𝓝 0) (𝓝 (E 0)) from hcont.continuousAt)
    simpa only [E,add_zero,one_mul,S] using h
  have htend : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n,hn⟩ := ((hE.comp htend).eventually_lt_const (by
    change S<chenSwitchIntegral+ε/2
    change S≤_ at hquad
    linarith only [hquad,hε])).exists
  let t := (1:ℝ)/((n:ℝ)+1)
  have ht : 0<t := by dsimp [t]; positivity
  change E t<chenSwitchIntegral+ε/2 at hn
  let A (N i : ℕ) := chenSwitchBandMass N (g i) (g (i+1))
  have hA : Tendsto (fun N => (1+t)*∑ i∈range K,A N i*(C i+t)) atTop (𝓝 (E t)) := by
    apply Tendsto.const_mul
    exact tendsto_finsetSum _ fun i hi =>
      (chenSwitchBandMass_tendsto (show 0<g i by linarith only [(hbounds (mem_range.mp hi)).1])
        (hbounds (mem_range.mp hi)).2.1).mul_const _
  have hmajor : ∀ᶠ N : ℕ in atTop, ∀ i∈range K, chenSwitchCellCount N (g i) (g (i+1)) ≤
      ((N:ℝ)/Real.log N)*((1+t)*(A N i*(C i+t))) := by
    apply (Finset.eventually_all _).mpr
    intro i hi
    obtain ⟨h₁,h₂,h₃⟩ := hbounds (mem_range.mp hi)
    have hcap : (1/3:ℝ)<chenSwitchCap (g i) s := by dsimp [chenSwitchCap]; linarith
    have hθ : chenSwitchCap (g i) s<1-g (i+1) := by dsimp [chenSwitchCap]; linarith
    have hinner := chenSwitchBandKernel_eventually_le (by norm_num) hcap hθ ht
    rw [show (∫ u in (1/3:ℝ)..chenSwitchCap (g i) s,2/(u*(1-g (i+1)-u)))/2=C i from
      chenSwitchCellCoeff_integral h₁ h₂ h₃ hs hsmall] at hinner
    filter_upwards [chenSwitchCellCount_eventually_le hPNT h₁ h₂ h₃ hs hsmall ht,hinner,
      eventually_ge_atTop (2:ℕ)] with N hc hinner hN
    have hpos : (0:ℝ)≤(N:ℝ)/Real.log N := div_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (Nat.one_le_cast.mpr (by omega)))
    have hMass : 0≤A N i := by dsimp [A,chenSwitchBandMass]; positivity
    exact hc.trans ((mul_le_mul_of_nonneg_left hinner
      (mul_nonneg (mul_nonneg (by linarith) hpos) hMass)).trans_eq (by dsimp only [A]; ring))
  filter_upwards [hmajor,hA.eventually_lt_const (show E t<chenSwitchIntegral+ε by linarith),
    eventually_ge_atTop (2:ℕ)] with N hN hE hn
  rw [←grid_count_eq hK (by omega : 1≤N)]
  have hL : 0≤(N:ℝ)/Real.log N := div_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (Nat.one_le_cast.mpr (by omega)))
  apply (Finset.sum_le_sum hN).trans
  rw [←Finset.mul_sum,←Finset.mul_sum,mul_comm (chenSwitchIntegral+ε)]
  exact mul_le_mul_of_nonneg_left hE.le hL

theorem chen_switching_mass_of_dirichletGRH (hGRH : DirichletGRH) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ((chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ) ≤
      (chenSwitchIntegral+ε)*((N:ℝ)/Real.log (N:ℝ)) :=
  chen_switching_mass_of_pnt (primeCounting_ratio_of_dirichletGRH hGRH) ε hε

end FareyGoldbach
