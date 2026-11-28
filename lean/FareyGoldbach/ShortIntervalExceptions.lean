import FareyGoldbach.DoubleAverageGoldbach

/-! # Exception counts in translated intervals -/

open scoped BigOperators Classical Topology
open Filter

namespace FareyGoldbach

/-- Even admissible exceptions in `(X, X+Δ]`. -/
noncomputable def shortIntervalExceptions (P : Progressions) (X Δ : ℕ) : Finset ℕ :=
  (exceptions P (X+Δ)).filter fun n => X < n

/-- The Fourier frequencies corresponding to the exceptional integers. -/
noncomputable def shortBadFrequencies (P : Progressions) (X Δ : ℕ) : Finset ℕ :=
  (shortIntervalExceptions P X Δ).image (fun n => (n-(P.b₁+P.b₂))/P.r)

theorem shortIntervalExceptions_mem {P : Progressions} {X Δ n : ℕ} (hn : n ∈ shortIntervalExceptions P X Δ) :
    X < n ∧ n ≤ X+Δ ∧ Even n ∧ n % P.r = (P.b₁ + P.b₂) % P.r ∧ (primeRepresentations P n).card = 0 := by
  have h := Finset.mem_filter.mp hn
  have he := Finset.mem_filter.mp h.1
  exact ⟨h.2,(Finset.mem_Icc.mp he.1).2,he.2⟩

theorem shortBadFrequencies_recover (P : Progressions) {X Δ n : ℕ} (hrX : P.r ≤ X)
    (hn : n ∈ shortIntervalExceptions P X Δ) : P.r*((n-(P.b₁+P.b₂))/P.r)+P.b₁+P.b₂=n := by
  obtain ⟨hlo,_,_,hm,_⟩ := shortIntervalExceptions_mem hn
  have hle : P.b₁+P.b₂ ≤ n := by
    by_contra! h
    have hd : P.r ∣ (P.b₁+P.b₂)-n := (Nat.modEq_iff_dvd' h.le).mp hm
    have hs := Nat.le_of_dvd (Nat.sub_pos_of_lt h) hd
    have h₁ := P.b₁_lt; have h₂ := P.b₂_lt; omega
  have hd := (Nat.modEq_iff_dvd' hle).mp hm.symm
  rw [Nat.mul_div_cancel' hd]; omega

theorem shortBadFrequencies_card (P : Progressions) {X Δ : ℕ} (hrX : P.r ≤ X) :
    (shortBadFrequencies P X Δ).card = (shortIntervalExceptions P X Δ).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have h₁ := shortBadFrequencies_recover P hrX ha
  have h₂ := shortBadFrequencies_recover P hrX hb
  dsimp only at he; rw [he] at h₁; omega

/-- Every fixed residue pair uses one common integer frequency window. -/
theorem shortBadFrequencies_subset_window (P : Progressions) {X Δ : ℕ} (hrX : P.r ≤ X) :
    shortBadFrequencies P X Δ ⊆ Finset.Icc (X/P.r-2) (X/P.r-2 + (Δ/P.r+3)) := by
  intro k hk
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hk
  have hrec := shortBadFrequencies_recover P hrX hn
  rw [he] at hrec
  obtain ⟨hlo,hhi,_⟩ := shortIntervalExceptions_mem hn
  have h₁ := P.b₁_lt; have h₂ := P.b₂_lt
  have hx : X < (k+2)*P.r := by nlinarith only [hrec,hlo,h₁,h₂]
  have hklo := (Nat.div_lt_iff_lt_mul P.r_pos).2 hx
  have hab : X+Δ < (X/P.r+Δ/P.r+2)*P.r := by
    nlinarith only [Nat.div_add_mod X P.r,Nat.div_add_mod Δ P.r,Nat.mod_lt X P.r_pos,Nat.mod_lt Δ P.r_pos]
  have hfloor := (Nat.div_lt_iff_lt_mul P.r_pos).2 hab
  have hkhi : k ≤ (X+Δ)/P.r := (Nat.le_div_iff_mul_le P.r_pos).2 (by nlinarith only [hrec,hhi])
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

/-- Coercing to the subtype ensures that the residue bounds and coprimality proofs
    used to construct `Progressions` are available in each summand. -/
def shortProgressions {r : ℕ} (hr : 0 < r) (b₁ b₂ : {b // b ∈ coprimeClasses r}) : Progressions :=
  ⟨r,hr,b₁.1,b₂.1,(mem_coprimeClasses.mp b₁.2).1,(mem_coprimeClasses.mp b₂.2).1,
    (mem_coprimeClasses.mp b₁.2).2,(mem_coprimeClasses.mp b₂.2).2⟩

noncomputable def shortDoubleAvgExceptions (X Δ r : ℕ) (hr : 0 < r) : ℝ :=
  (1 / (r.totient:ℝ)^2) * ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
    ((shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ).card : ℝ)

/-- The map `n ↦ ⌊(n-X)/r⌋` is injective on one congruence class in the window. -/
theorem shortIntervalExceptions_card_le (P : Progressions) (X Δ : ℕ) :
    (shortIntervalExceptions P X Δ).card ≤ Δ/P.r+1 := by
  let s := shortIntervalExceptions P X Δ
  let f := fun n : ℕ => (n-X)/P.r
  have hinj : Set.InjOn f s := by
    intro n hn m hm he
    obtain ⟨h₁,_,_,hnm,_⟩ := shortIntervalExceptions_mem hn
    obtain ⟨h₂,_,_,hmm,_⟩ := shortIntervalExceptions_mem hm
    have hcon : n ≡ m [MOD P.r] := hnm.trans hmm.symm
    have hshift := Nat.ModEq.add_right_cancel' X (a := n-X) (b := m-X)
      (by simpa [Nat.sub_add_cancel h₁.le,Nat.sub_add_cancel h₂.le] using hcon)
    change (n-X)%P.r = (m-X)%P.r at hshift
    change (n-X)/P.r = (m-X)/P.r at he
    have ha := Nat.div_add_mod (n-X) P.r; have hb := Nat.div_add_mod (m-X) P.r
    rw [he,hshift] at ha; omega
  have hsub : s.image f ⊆ Finset.range (Δ/P.r+1) := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have hhi := (shortIntervalExceptions_mem hn).2.1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n-X ≤ Δ)))
  rw [← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_card hsub).trans (by simp)

/-- Fixing `b₁`, distinct values of `b₂` select disjoint congruence classes of `n`. -/
theorem short_fixed_first_sum_le {r : ℕ} (hr : 0 < r) (b₁ : {b // b ∈ coprimeClasses r}) (X Δ : ℕ) :
    (∑ b₂ ∈ (coprimeClasses r).attach, (shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ).card) ≤ Δ := by
  classical
  let s := (coprimeClasses r).attach
  let E := fun b₂ : {b // b ∈ coprimeClasses r} => shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ
  have hdis : (s : Set _).PairwiseDisjoint E := by
    intro b hb c hc hbc
    refine Finset.disjoint_left.mpr fun n hn hm => hbc ?_
    have hn' := (shortIntervalExceptions_mem hn).2.2.2.1
    have hm' := (shortIntervalExceptions_mem hm).2.2.2.1
    have he := Nat.ModEq.add_left_cancel' b₁.1 (a := b.1) (b := c.1) (n := r) (hn'.symm.trans hm')
    apply Subtype.ext
    simpa [Nat.ModEq,Nat.mod_eq_of_lt (mem_coprimeClasses.mp b.2).1,
      Nat.mod_eq_of_lt (mem_coprimeClasses.mp c.2).1] using he
  have hsub : s.biUnion E ⊆ Finset.Ioc X (X+Δ) := by
    intro n hn
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hn
    have h := shortIntervalExceptions_mem hb
    exact Finset.mem_Ioc.mpr ⟨h.1,h.2.1⟩
  change (∑ b ∈ s, (E b).card) ≤ Δ
  rw [← Finset.card_biUnion hdis]
  exact (Finset.card_le_card hsub).trans (by simp)

theorem shortDoubleAvgExceptions_trivial {X Δ r : ℕ} (hr : 0 < r) :
    shortDoubleAvgExceptions X Δ r hr ≤ min ((Δ:ℝ)/r+1) (((r:ℝ)/r.totient)*((Δ:ℝ)/r)) := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hcard : ((coprimeClasses r).attach.card:ℝ) = r.totient := by rw [Finset.card_attach,card_coprimeClasses]
  have havg : 0 ≤ 1 / (r.totient:ℝ)^2 := by positivity
  unfold shortDoubleAvgExceptions
  apply le_min
  · have per (b₁ b₂ : {b // b ∈ coprimeClasses r}) :
        ((shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ).card:ℝ) ≤ (Δ:ℝ)/r+1 := by
      have hd : ((Δ/r:ℕ):ℝ) ≤ (Δ:ℝ)/r := by
        rw [le_div_iff₀ hr']; exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Δ r)
      have h := shortIntervalExceptions_card_le (shortProgressions hr b₁ b₂) X Δ
      change _ ≤ Δ/r+1 at h
      have h' : ((shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ).card:ℝ) ≤ ((Δ/r:ℕ):ℝ)+1 := by exact_mod_cast h
      linarith
    calc _ ≤ 1/(r.totient:ℝ)^2 * ∑ _b₁ ∈ (coprimeClasses r).attach, ∑ _b₂ ∈ (coprimeClasses r).attach, ((Δ:ℝ)/r+1) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => per i j) havg
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,hcard]; field_simp
  · have per (b₁ : {b // b ∈ coprimeClasses r}) :
        (∑ b₂ ∈ (coprimeClasses r).attach, ((shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ).card:ℝ)) ≤ Δ := by
      exact_mod_cast short_fixed_first_sum_le hr b₁ X Δ
    calc _ ≤ 1/(r.totient:ℝ)^2 * ∑ _b₁ ∈ (coprimeClasses r).attach, (Δ:ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => per i) havg
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,hcard]; field_simp

noncomputable def shortDoubleAvgAnalyticCap (X Δ r : ℕ) : ℝ :=
  ((r.totient:ℝ)/r)^2 * Real.sqrt ((Δ:ℝ)/r) * Real.log (2*(X:ℝ))^3

noncomputable def shortDoubleAvgBudget (X Δ r : ℕ) : ℝ :=
  min (min ((Δ:ℝ)/r+1) (((r:ℝ)/r.totient)*((Δ:ℝ)/r))) (shortDoubleAvgAnalyticCap X Δ r)

def ShortDoubleAvgBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {X Δ r : ℕ} (hr : 0 < r), 2 ≤ X → r ≤ X → 1 ≤ Δ → Δ ≤ X →
    shortDoubleAvgExceptions X Δ r hr ≤ C * shortDoubleAvgBudget X Δ r

/-- Complete an estimate that is available above an absolute activity threshold. -/
theorem shortDoubleAvgBound_of_large_cap (T : ℕ)
    (input : ∃ C : ℝ, 0 < C ∧ ∀ {X Δ r : ℕ} (hr : 0 < r), 2 ≤ X → r ≤ X → 1 ≤ Δ → Δ ≤ X →
      T ≤ Δ/r → shortDoubleAvgExceptions X Δ r hr ≤ C * shortDoubleAvgAnalyticCap X Δ r) : ShortDoubleAvgBound := by
  obtain ⟨C,hC,hcap⟩ := input
  let c := C + 8*((T:ℝ)+1) + 1
  have hc : 1 ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) T]
  refine ⟨c,by linarith,fun {X Δ r} hr hX hrX hΔ hΔX => ?_⟩
  let k := (Δ:ℝ)/r
  let L := Real.log (2*(X:ℝ))
  let a := (r.totient:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let U := min (k+1) (κ*k)
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hk : 0<k := div_pos (Nat.cast_pos.mpr hΔ) hr'
  have hL : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (one_le_log_two_mul hX)
  have hκ : 0<κ := div_pos hr' hφ
  have ha : 0<a := div_pos hφ hr'
  have hA : 0 ≤ shortDoubleAvgAnalyticCap X Δ r := by change 0 ≤ a^2*Real.sqrt k*L^3; positivity
  have hU : 0 ≤ U := le_min (by positivity) (by positivity)
  have htr := shortDoubleAvgExceptions_trivial (X := X) (Δ := Δ) hr
  change _ ≤ U at htr
  have htr' := htr.trans (show U ≤ c*U by nlinarith only [mul_le_mul_of_nonneg_right hc hU])
  change _ ≤ c * min U (shortDoubleAvgAnalyticCap X Δ r)
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ c)]
  refine le_min htr' ?_
  by_cases hlarge : T ≤ Δ/r
  · exact (hcap hr hX hrX hΔ hΔX hlarge).trans (mul_le_mul_of_nonneg_right (by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) T] : C ≤ c) hA)
  · have hn := (Nat.div_lt_iff_lt_mul hr).mp (lt_of_not_ge hlarge)
    have hkT : k ≤ T := (div_le_iff₀ hr').2 (by exact_mod_cast hn.le)
    have hrt : Real.sqrt k ≤ (T:ℝ)+1 := by
      apply (Real.sqrt_le_left (by positivity : 0 ≤ (T:ℝ)+1)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) T,sq_nonneg (T:ℝ)]
    have hκL : κ ≤ 2*L := (div_totient_le_two_log hr).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity : (0:ℝ)<2*(r:ℝ))
        (by have : (r:ℝ) ≤ X := Nat.cast_le.mpr hrX; linarith : 2*(r:ℝ) ≤ 2*(X:ℝ))) (by norm_num))
    have hinv : a*κ=1 := by dsimp [a,κ]; field_simp
    have hpow := pow_le_pow_left₀ hκ.le hκL 3
    have hκfin : κ ≤ 8*(a^2*L^3) := by
      have he : a^2*κ^3 = κ := by calc _ = (a*κ)^2*κ := by ring
                                         _ = _ := by rw [hinv]; ring
      nlinarith only [mul_le_mul_of_nonneg_left hpow (sq_nonneg a), he]
    have hmono := mul_le_mul hκfin hrt (Real.sqrt_nonneg k) (by positivity)
    have hfinal := mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg k)
    have he : κ * Real.sqrt k * Real.sqrt k = κ*k := by rw [mul_assoc,←sq,Real.sq_sqrt hk.le]
    rw [he] at hfinal
    refine (htr.trans (min_le_right ..)).trans ?_
    calc κ*k ≤ 8*((T:ℝ)+1)*shortDoubleAvgAnalyticCap X Δ r := by
          change κ*k ≤ 8*((T:ℝ)+1)*(a^2*Real.sqrt k*L^3); nlinarith only [hfinal]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [c]; linarith) hA

/-- On a window containing at least one full period, the additive endpoint error is absorbed by its length. -/
theorem shortDoubleAvgBound_long_window (h : ShortDoubleAvgBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X Δ r : ℕ} (hr : 0<r), 2≤X → r≤Δ → Δ≤X →
      shortDoubleAvgExceptions X Δ r hr ≤ C * min ((Δ:ℝ)/r) (shortDoubleAvgAnalyticCap X Δ r) := by
  obtain ⟨C,hC,hbound⟩ := h
  refine ⟨C+2,by linarith,fun {X Δ r} hr hX hrΔ hΔX => ?_⟩
  have hK : 1 ≤ (Δ:ℝ)/r := (one_le_div (Nat.cast_pos.mpr hr)).2 (Nat.cast_le.mpr hrΔ)
  have htr := (shortDoubleAvgExceptions_trivial (X := X) (Δ := Δ) hr).trans (min_le_left ..)
  have htr' : shortDoubleAvgExceptions X Δ r hr ≤ (C+2)*((Δ:ℝ)/r) := by
    nlinarith only [htr,hK,mul_nonneg hC.le (show 0 ≤ (Δ:ℝ)/r by positivity)]
  have hb := hbound hr hX (hrΔ.trans hΔX) (hr.trans_le hrΔ) hΔX
  have hA : 0 ≤ shortDoubleAvgAnalyticCap X Δ r := by
    have hL := one_le_log_two_mul hX; dsimp [shortDoubleAvgAnalyticCap]; positivity
  have hcap := (hb.trans (mul_le_mul_of_nonneg_left (min_le_right ..) hC.le)).trans
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+2) hA)
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ C+2)]; exact le_min htr' hcap

noncomputable def shortDoubleAvgParameter (X Δ r : ℕ) : ℝ :=
  ((r:ℝ)/r.totient)^4 * ((Δ:ℝ)/r) / Real.log (2*(X:ℝ))^6

private theorem shortDoubleAvg_normalized_term {X Δ r : ℕ} (hr : 0 < r) (hX : 2 ≤ X) (hΔ : 0 < Δ) :
    (((r.totient : ℝ) / r) ^ 2 * Real.sqrt ((Δ : ℝ) / r) * Real.log (2 * (X : ℝ)) ^ 3) /
      ((Δ : ℝ) / r) = (Real.sqrt (shortDoubleAvgParameter X Δ r))⁻¹ := by
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have ht : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hX' : (0 : ℝ) < Δ := Nat.cast_pos.mpr hΔ
  let H : ℝ := (Δ : ℝ) / r
  let L := Real.log (2 * (X : ℝ))
  let κ : ℝ := (r : ℝ) / r.totient
  let a : ℝ := (r.totient : ℝ) / r
  have hH : 0 < H := div_pos hX' hr'
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * X))
  have hκ : 0 < κ := div_pos hr' ht
  have haκ : a * κ = 1 := by dsimp [a, κ]; field_simp
  have hs : Real.sqrt (shortDoubleAvgParameter X Δ r) = κ ^ 2 * Real.sqrt H / L ^ 3 := by
    change Real.sqrt (κ ^ 4 * H / L ^ 6) = _
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    have hκ4 : κ ^ 4 = (κ ^ 2) ^ 2 := by ring
    have hL6 : L ^ 6 = (L ^ 3) ^ 2 := by ring
    rw [hκ4, hL6, Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  have hs' : 0 < Real.sqrt (shortDoubleAvgParameter X Δ r) := by rw [hs]; positivity
  change (a ^ 2 * Real.sqrt H * L ^ 3) / H = _
  rw [← one_div]
  symm
  apply (div_eq_iff hs'.ne').2
  symm
  rw [hs]
  calc a ^ 2 * Real.sqrt H * L ^ 3 / H * (κ ^ 2 * Real.sqrt H / L ^ 3) =
      (a * κ) ^ 2 * (Real.sqrt H) ^ 2 / H := by field_simp
    _ = 1 := by rw [haκ, Real.sq_sqrt hH.le]; simp [hH.ne']


/-- The exceptional count divided by the number of periods tends to zero uniformly
    along any sequence for which `κ⁴(Δ/r)/log⁶(2X)` tends to infinity. -/
theorem shortDoubleAvgDensity_of_bound (h : ShortDoubleAvgBound)
    (X Δ r : ℕ → ℕ) (hr : ∀ n,0<r n) (hX : ∀ n,2≤X n) (hrX : ∀ n,r n≤X n)
    (hΔ : ∀ n,1≤Δ n) (hΔX : ∀ n,Δ n≤X n)
    (hP : Tendsto (fun n => shortDoubleAvgParameter (X n) (Δ n) (r n)) atTop atTop) :
    Tendsto (fun n => shortDoubleAvgExceptions (X n) (Δ n) (r n) (hr n) / ((Δ n:ℝ)/r n)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := h
  have hs : Tendsto (fun n => (Real.sqrt (shortDoubleAvgParameter (X n) (Δ n) (r n)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hP)
  have hsC : Tendsto (fun n => C*(Real.sqrt (shortDoubleAvgParameter (X n) (Δ n) (r n)))⁻¹) atTop (𝓝 0) := by
    simpa using hs.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsC
    (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_)
  · intro n; unfold shortDoubleAvgExceptions; positivity
  · intro n
    have he := (hbound (hr n) (hX n) (hrX n) (hΔ n) (hΔX n)).trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) hC.le)
    refine (div_le_div_of_nonneg_right he (by positivity)).trans_eq ?_
    rw [mul_div_assoc,shortDoubleAvgAnalyticCap,shortDoubleAvg_normalized_term (hr n) (hX n) (hΔ n)]

end FareyGoldbach


