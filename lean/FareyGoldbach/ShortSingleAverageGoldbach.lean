import FareyGoldbach.ShortPrimeResidualEnergy
import FareyGoldbach.ShortSingleAverageMixed
import FareyGoldbach.ShortSingleMixedCap
import FareyGoldbach.ShortProductWindow

/-! # Singly averaged Goldbach exceptions in a translated interval -/

open Filter
open scoped BigOperators Topology Classical

namespace FareyGoldbach

private noncomputable def shortSingleModel (r b Y Q : ℕ) (hY : 1≤Y) : BoundedPeriodicFunction :=
  ⟨shortContModel r b Y Q,shortContModel_measurable hY r b Q,
    shortContModel_norm_bounded hY r b Q,shortContModel_periodic r b Y Q⟩

private theorem pair_energy_sum {ι : Type*} (s : Finset ι) (E F G : ι → ℝ) (T Z : ℝ)
    (hp : ∀ i ∈ s, E i*T^2 ≤ 2*(F i+G i))
    (hg : ∀ i ∈ s, G i ≤ Z) :
    (∑ i ∈ s, E i)*T^2 ≤ 2*((∑ i ∈ s, F i)+(s.card:ℝ)*Z) := by
  rw [Finset.sum_mul]
  calc _ ≤ ∑ i ∈ s, 2*(F i+Z) := Finset.sum_le_sum fun i hi => (hp i hi).trans
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl (F i)) (hg i hi)) (by norm_num))
       _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]

set_option maxHeartbeats 1200000 in
/-- The localized error on the averaged prime and the full-circle error on the
fixed prime enter separately. -/
theorem shortSingleAvgBound_of_window_energies
    (hf : ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (_hr : 0<r) (b₁ : ReducedClass r),
      2≤X → r≤X → 1≤Δ → Δ≤X → 2^72≤Δ/r → shortSingleBase X r ≤ (X:ℝ)/r →
      let Y := X+Δ; let Q := routeAQ Δ r
      let S := fun b => smoothedPrimeSum r b Y
      let R := fun b x => S b x-shortContModel r b Y Q x
      let T := (1:ℝ)/262144*((r:ℝ)/r.totient)^2*((Y:ℝ)/r)
      (∑ b ∈ coprimeClasses r, productWindowEnergy (R b) (S b₁.1) (X/r-2) (Δ/r+3))/(r.totient:ℝ) ≤
        C*T^2*shortDoubleAvgAnalyticCap X Δ r)
    (hm : ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (_hr : 0<r) (b₁ b₂ : ReducedClass r),
      2≤X → r≤X → 1≤Δ → Δ≤X → 2^72≤Δ/r → shortSingleBase X r ≤ (X:ℝ)/r →
      let Y := X+Δ; let Q := routeAQ Δ r
      let T := (1:ℝ)/262144*((r:ℝ)/r.totient)^2*((Y:ℝ)/r)
      (∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b₁.1 Y x-shortContModel r b₁.1 Y Q x‖^2*
          ‖shortContModel r b₂.1 Y Q x‖^2) ≤ C*T^2*shortSingleMixedCap X Δ r) : ShortSingleAvgBound := by
  obtain ⟨C,hC,hfirst⟩ := hf
  obtain ⟨D,hD,hmixed⟩ := hm
  apply shortSingleAvgBound_of_active
  refine ⟨2*(C+D),by positivity,fun {X Δ r} hr b hX hrX hΔ hΔX hbig hbase => ?_⟩
  let Y := X+Δ
  let Q := routeAQ Δ r
  let m := X/r-2
  let K := Δ/r+3
  have hY : 1≤Y := by dsimp [Y]; omega
  let S := fun c => shortPrimeFunction r c Y
  let M := fun c => shortSingleModel r c Y Q hY
  let R := fun c => shortDifference (S c) (M c)
  let T := (1:ℝ)/262144*((r:ℝ)/r.totient)^2*((Y:ℝ)/r)
  let s := coprimeClasses r
  let A := shortDoubleAvgAnalyticCap X Δ r
  let V := shortSingleMixedCap X Δ r
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hy : (0:ℝ)<Y := Nat.cast_pos.mpr hY
  have hT : 0<T := by dsimp [T]; positivity
  have hU : 0≤A := by have hL := one_le_log_two_mul hX; dsimp [A,shortDoubleAvgAnalyticCap]; positivity
  have hV : 0≤V := shortSingleMixedCap_nonneg hX
  have hpc (c : ReducedClass r) (k : ℕ) (hk : k ∈ shortBadFrequencies (shortProgressions hr b c) X Δ) :
      T ≤ (shortPC (M b.1) (M c.1) k).re := short_model_bad_freq_lower hr hX hrX hΔ hΔX hbig b c hk
  have hpair (c : ReducedClass r) : ((shortIntervalExceptions (shortProgressions hr b c) X Δ).card:ℝ)*T^2 ≤
      2*(productWindowEnergy (R c.1) (S b.1) m K + productWindowEnergy (R b.1) (M c.1) m K) :=
    shortCountPair (shortProgressions hr b c) hrX hΔX (M b.1) (M c.1) hT.le (hpc c)
  have hE₁ := hfirst hr b hX hrX hΔ hΔX hbig hbase
  change (∑ c ∈ s, productWindowEnergy (R c) (S b.1) m K)/(r.totient:ℝ) ≤ C*T^2*A at hE₁
  have hE₂ (c : ReducedClass r) : productWindowEnergy (R b.1) (M c.1) m K ≤ D*T^2*V := by
    have hh := productWindowEnergy_le_integral (R b.1) (M c.1) m K
    simp_rw [norm_mul,mul_pow] at hh
    exact hh.trans (hmixed hr b c hX hrX hΔ hΔX hbig hbase)
  have hsum : (∑ c ∈ s.attach, ((shortIntervalExceptions (shortProgressions hr b c) X Δ).card:ℝ))*T^2 ≤
      2*((∑ c ∈ s, productWindowEnergy (R c) (S b.1) m K)+(r.totient:ℝ)*(D*T^2*V)) := by
    have hh := pair_energy_sum s.attach
      (fun c => ((shortIntervalExceptions (shortProgressions hr b c) X Δ).card:ℝ))
      (fun c => productWindowEnergy (R c.1) (S b.1) m K)
      (fun c => productWindowEnergy (R b.1) (M c.1) m K)
      T (D*T^2*V) (fun c _ => hpair c) (fun c _ => hE₂ c)
    rw [Finset.sum_attach s (fun c => productWindowEnergy (R c) (S b.1) m K),
      Finset.card_attach,show s.card=r.totient from card_coprimeClasses r] at hh
    exact hh
  have hnorm := (div_le_iff₀ ht).mp hE₁
  apply le_of_mul_le_mul_right _ (pow_pos hT 2)
  change (1/(r.totient:ℝ)*_)*T^2 ≤ (2*(C+D)*(A+V))*T^2
  rw [mul_assoc,one_div,←div_eq_inv_mul,div_le_iff₀ ht]
  refine hsum.trans ?_
  nlinarith only [hnorm,mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg T)) hV) ht.le,
    mul_nonneg (mul_nonneg (mul_nonneg hD.le (sq_nonneg T)) hU) ht.le]

/-- Normalize and optimize the three fourth-moment estimates supplied by the mixed integral. -/
theorem short_single_mixed_energy_of_bounds
    (h₁ : ∃ C : ℝ, 0<C ∧ ∀ {r b₁ b₂ Y Q : ℕ}, 0<r → b₁<r → Nat.Coprime b₁ r →
      b₂<r → r≤Y → 2≤Y → 0<Q → Q≤Y → (r:ℝ)≤4*((Y:ℝ)/r) → ∀ D : ℕ, 1≤D →
      let κ := (r:ℝ)/r.totient; let H := (Y:ℝ)/r; let L := Real.log (2*(Y:ℝ))
      (∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b₁ Y x-shortContModel r b₁ Y Q x‖^2*‖shortContModel r b₂ Y Q x‖^2) ≤
        C*(κ^2*(Y:ℝ)*H*L^2*Real.log (2*(D:ℝ))+κ^4*H^3/(D:ℝ)))
    (h₂ : ∃ C : ℝ, 0<C ∧ ∀ {r b₁ b₂ Y Q : ℕ}, 0<r → b₁<r → Nat.Coprime b₁ r →
      b₂<r → r≤Y → 2≤Y → 0<Q → Q≤Y → 2^72≤Y →
      let κ := (r:ℝ)/r.totient; let H := (Y:ℝ)/r; let L := Real.log (2*(Y:ℝ))
      let I := ∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b₁ Y x-shortContModel r b₁ Y Q x‖^2*‖shortContModel r b₂ Y Q x‖^2
      I ≤ C*(κ^2*(Y:ℝ)*H*L^2*Real.log (2*(Q:ℝ))) ∧ I ≤ C*(κ*(Y:ℝ)*H*L^3)) :
    ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (_hr : 0<r) (b₁ b₂ : ReducedClass r),
      2≤X → r≤X → 1≤Δ → Δ≤X → 2^72≤Δ/r → shortSingleBase X r ≤ (X:ℝ)/r →
      let Y := X+Δ; let Q := routeAQ Δ r
      let T := (1:ℝ)/262144*((r:ℝ)/r.totient)^2*((Y:ℝ)/r)
      (∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b₁.1 Y x-shortContModel r b₁.1 Y Q x‖^2*
          ‖shortContModel r b₂.1 Y Q x‖^2) ≤ C*T^2*shortSingleMixedCap X Δ r := by
  obtain ⟨C,hC,hcut⟩ := h₁
  obtain ⟨D,hD,hall⟩ := h₂
  refine ⟨8*(262144:ℝ)^2*(C+D),by positivity,fun {X Δ r} hr b c hX hrX hΔ hΔX hbig hbase => ?_⟩
  let Y := X+Δ
  let Q := routeAQ Δ r
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hY2 : 2≤Y := by dsimp [Y]; omega
  have hrY : r≤Y := by dsimp [Y]; omega
  have hΔY : Δ≤Y := by dsimp [Y]; omega
  have hh := routeAQ_bounds hr (le_trans (by norm_num : 2^26≤2^72) hbig)
  have hQ : 0<Q := by change 0<routeAQ Δ r; omega
  have hQY : Q≤Y := hh.2.2.2.trans hΔY
  have hYL : 2^72≤Y := hbig.trans ((Nat.div_le_self _ _).trans hΔY)
  have hr4 : (r:ℝ)≤4*((Y:ℝ)/r) := by
    have hh := (edge_basics hr hX hrX).1
    change (r:ℝ)≤4*shortSingleBase X r at hh
    have hy := div_le_div_of_nonneg_right (show (X:ℝ)≤Y by exact_mod_cast (show X≤Y by dsimp [Y]; omega)) hr'.le
    linarith only [hh,hbase,hy]
  have hQf : Q≤Δ/r := le_trans (Nat.div_le_self _ _) (Nat.sqrt_le_self _)
  have hQK : (Q:ℝ)≤(Δ:ℝ)/r := (Nat.cast_le.mpr hQf).trans ((le_div_iff₀ hr').2 (by exact_mod_cast Nat.div_mul_le_self Δ r))
  have hc := hall (b₂:=c.1) hr (mem_coprimeClasses.mp b.2).1 (mem_coprimeClasses.mp b.2).2 (mem_coprimeClasses.mp c.2).1 hrY hY2 hQ hQY hYL
  have he := hcut (b₂:=c.1) hr (mem_coprimeClasses.mp b.2).1 (mem_coprimeClasses.mp b.2).2 (mem_coprimeClasses.mp c.2).1 hrY hY2 hQ hQY hr4
  have hL := one_le_log_two_mul hY2
  have hth : 0<(r.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hLQ : 0≤Real.log (2*(Q:ℝ)) := Real.log_nonneg (by have hh1 : (1:ℝ)≤Q := Nat.one_le_cast.mpr hQ; linarith)
  apply short_mixed_cap_optimize hr hX hΔX (show 0<C+D by positivity) hQ hQK
  · intro j hj
    have hlogj : 0≤Real.log (2*(j:ℝ)) := Real.log_nonneg (by have hhj : (1:ℝ)≤j := Nat.one_le_cast.mpr hj; linarith)
    exact (he j hj).trans (mul_le_mul_of_nonneg_right (by linarith : C≤C+D) (by positivity))
  · exact hc.1.trans (mul_le_mul_of_nonneg_right (by linarith : D≤C+D) (by positivity))
  · exact hc.2.trans (mul_le_mul_of_nonneg_right (by linarith : D≤C+D) (by positivity))

/-- An absolute bound for every translated interval and every fixed first residue class. -/
theorem short_single_average_of_dirichletGRH (hGRH : DirichletGRH) : ShortSingleAvgBound := by
  obtain ⟨C,hC,hf⟩ := short_single_prime_residual_energy hGRH
  exact shortSingleAvgBound_of_window_energies
    ⟨C,hC,fun {X Δ r} hr b => hf (r:=r) (X:=X) (Δ:=Δ) hr b⟩
    (short_single_mixed_energy_of_bounds (short_fixed_mixed_integral_fourth_bound hGRH)
      (short_fixed_mixed_integral_all_bounds hGRH))

theorem short_single_average_long_window_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (hr : 0<r) (b₁ : ReducedClass r), 2≤X → r≤Δ → Δ≤X →
      shortSingleAvgExceptions X Δ r hr b₁ ≤ C*min ((Δ:ℝ)/r) (shortSingleAvgAnalyticCap X Δ r) :=
  shortSingleAvgBound_long_window (short_single_average_of_dirichletGRH hGRH)

/-- Density one when the analytic exceptional-count bound is little-oh of the number of periods. -/
theorem short_single_average_density_one_of_dirichletGRH (hGRH : DirichletGRH)
    (X Δ r : ℕ→ℕ) (hr : ∀ n,0<r n) (b₁ : ∀ n, ReducedClass (r n)) (hX : ∀ n,2≤X n)
    (hrX : ∀ n,r n≤X n) (hΔ : ∀ n,1≤Δ n) (hΔX : ∀ n,Δ n≤X n)
    (hP : Tendsto (fun n => shortSingleAvgAnalyticCap (X n) (Δ n) (r n)/((Δ n:ℝ)/r n)) atTop (𝓝 0)) :
    Tendsto (fun n => shortSingleAvgExceptions (X n) (Δ n) (r n) (hr n) (b₁ n)/((Δ n:ℝ)/r n)) atTop (𝓝 0) :=
  shortSingleAvgDensity_of_bound (short_single_average_of_dirichletGRH hGRH) X Δ r hr b₁ hX hrX hΔ hΔX hP

/-- It suffices that Δ/(r(φ(r)/r)⁴L⁶ + (φ(r)/r)³r²L³) tends to infinity. -/
theorem short_single_average_density_one_of_sufficient_parameter (hGRH : DirichletGRH)
    (X Δ r : ℕ→ℕ) (hr : ∀ n,0<r n) (b₁ : ∀ n, ReducedClass (r n)) (hX : ∀ n,2≤X n)
    (hrX : ∀ n,r n≤X n) (hΔ : ∀ n,1≤Δ n) (hΔX : ∀ n,Δ n≤X n)
    (hP : Tendsto (fun n => shortSingleSufficientParameter (X n) (Δ n) (r n)) atTop atTop) :
    Tendsto (fun n => shortSingleAvgExceptions (X n) (Δ n) (r n) (hr n) (b₁ n)/((Δ n:ℝ)/r n)) atTop (𝓝 0) :=
  short_single_average_density_one_of_dirichletGRH hGRH X Δ r hr b₁ hX hrX hΔ hΔX
    (shortSingleAvgParameter_suffices X Δ r hr hX hΔ hP)

end FareyGoldbach





