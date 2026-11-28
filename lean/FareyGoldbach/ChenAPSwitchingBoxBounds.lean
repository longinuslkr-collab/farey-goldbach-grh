import FareyGoldbach.ChenLargeConductor
import FareyGoldbach.ChenSwitchingAssembly
import FareyGoldbach.ChenAPSmallConductor

/-! # Bounds for the masked primitive character sums on switching boxes -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem norm_div_large {N z y i K a D R : ℕ} (ha : 0<a) (hN : 1≤N)
    (hy : (N:ℝ)^(1/4:ℝ)+1≤(y:ℝ)) (hD : D≤N) (hR : 1≤R) :
    (∑ q∈Finset.Ioc R D, chenPrimitiveNorm (a*q) (chenSwitchBoxSum N z y i K)/(q:ℝ)) ≤
      100000*(chenSwitchLog N)^2*((N:ℝ)/R+Real.sqrt (a:ℝ)*(N:ℝ)^(7/8:ℝ)+
        (a:ℝ)*(D:ℝ)*Real.sqrt N) := by
  by_cases hne : (chenSwitchBoxPairs N z y i).Nonempty
  · obtain ⟨hW,hWN,hMW,hM,hWpow⟩ := chenSwitchBox_ranges hy hN hne
    have heq (q : ℕ) : (chenSwitchBoxSum N z y i K : DirichletCharacter ℂ q → ℂ) =
        fun χ => ∑ m∈Finset.Icc 1 (chenSwitchBoxM i), chenSwitchBoxA z y i K m*χ (m:ZMod q)*
          ∑ w∈Finset.Icc (chenSwitchBoxLo m) (chenSwitchBoxHi N i m),
            chenSwitchBoxB K w*χ (w:ZMod q) := rfl
    simp_rw [heq]
    exact chen_large_conductor_interval_multiple_bound
      a (chenSwitchBoxM i) (chenSwitchBoxW N i) D R N ha
      (chenSwitchBoxA z y i K) (chenSwitchBoxB K) chenSwitchBoxLo (chenSwitchBoxHi N i)
      hN hW hWN hD hR hMW hM hWpow
      (fun m _ => chenSwitchBoxA_norm_le z y i K m) (fun w _ => chenSwitchBoxB_norm_le K w)
      (fun m _ => chenSwitchBoxLo_pos m) (fun m _ => chenSwitchBoxHi_le N i m)
  · have hz0 (q : ℕ) : chenPrimitiveNorm (a*q) (chenSwitchBoxSum N z y i K)=0 := by
      unfold chenPrimitiveNorm
      split_ifs <;> simp [chenSwitchBoxSum_eq_zero_of_empty
        (Finset.not_nonempty_iff_eq_empty.mp hne)]
    simp_rw [hz0,zero_div,Finset.sum_const_zero]
    positivity

/-- At level (a q), averaging over primitive characters and dividing by
the shell index (q) costs at most the factor (a). -/
private theorem norm_div_small {a q : ℕ} (F : DirichletCharacter ℂ (a*q) → ℂ) (ha : 0<a) (hq : 2≤q)
    {T : ℝ} (hT : 0≤T)
    (h : ∀ χ : DirichletCharacter ℂ (a*q), χ.IsPrimitive →
      ‖F χ‖≤T) :
    chenPrimitiveNorm (a*q) (F)/(q:ℝ)≤(a:ℝ)*T := by
  have hp := Nat.mul_pos ha (show 0<q by omega)
  let _ : NeZero (a*q) := ⟨hp.ne'⟩
  have ht := mul_le_mul_of_nonneg_left (chenPrimitiveNorm_div_le_of_bound _ hT h)
    (Nat.cast_nonneg (α:=ℝ) a)
  convert ht using 1
  have hq' : (q:ℝ)≠0 := by positivity
  have ha' : (a:ℝ)≠0 := by positivity
  push_cast
  field_simp

/-- Split a conductor first moment into the bounded range and large-sieve range. -/
theorem chen_ap_box_conductors_of_bounds {N a D R : ℕ} (F : ∀ q : ℕ, DirichletCharacter ℂ q → ℂ)
    {B : ℝ} (hB : 0≤B) (ha : 0<a)
    (hsmall : ∀ q : ℕ, 2≤q → q<D → q≤R →
      ∀ χ : DirichletCharacter ℂ (a*q), χ.IsPrimitive → ‖F (a*q) χ‖≤B)
    (hlarge : (∑ q∈Finset.Ioc R D,chenPrimitiveNorm (a*q) (F (a*q))/(q:ℝ))≤
      100000*(chenSwitchLog N)^2*((N:ℝ)/R+
        Real.sqrt (a:ℝ)*(N:ℝ)^(7/8:ℝ)+(a:ℝ)*(D:ℝ)*Real.sqrt N)) :
    (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
      chenPrimitiveNorm (a*q) (F (a*q))/(q:ℝ)) ≤
        (R:ℝ)*a*B+100000*(chenSwitchLog N)^2*((N:ℝ)/R+
          Real.sqrt (a:ℝ)*(N:ℝ)^(7/8:ℝ)+(a:ℝ)*(D:ℝ)*Real.sqrt N) := by
  let S := (Finset.Ico 2 D).filter (fun q => a.Coprime q)
  let E (q : ℕ) := chenPrimitiveNorm (a*q) (F (a*q))/(q:ℝ)
  have hE (q : ℕ) : 0≤E q := div_nonneg (chenPrimitiveNorm_nonneg ..) (Nat.cast_nonneg _)
  change (∑ q∈S,E q)≤_
  rw [← Finset.sum_filter_add_sum_filter_not S (·≤R)]
  apply add_le_add
  · calc
      _ ≤ ∑ _q∈S.filter (·≤R),(a:ℝ)*B := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hS,hqR⟩ := Finset.mem_filter.mp hq
        obtain ⟨hq₂,hqD⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hS).1
        exact norm_div_small (F (a*q)) ha hq₂ hB (hsmall q hq₂ hqD hqR)
      _ ≤ ∑ _q∈Finset.Icc 2 R,(a:ℝ)*B := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro q hq
        obtain ⟨hS,hqR⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hS).1).1,hqR⟩
      _ ≤ _ := by
        rw [Finset.sum_const,nsmul_eq_mul,mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Nat.card_Icc]
        exact_mod_cast (show R+1-2≤R by omega)
  · refine (Finset.sum_le_sum_of_subset_of_nonneg (t:=Finset.Ioc R D) ?_
        (fun q _ _ => hE q)).trans hlarge
    intro q hq
    obtain ⟨hS,hqR⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hqR,(Finset.mem_Ico.mp (Finset.mem_filter.mp hS).1).2.le⟩

/-- Sum over the conductors permitted by the AP character expansion, using
the sharp prime twist below the cutoff and the multiple large sieve above it. -/
theorem chen_ap_switch_box_conductors_le {N z y i K a D R : ℕ} {B : ℝ} (hB : 0≤B)
    (hN : 1≤N) (hy : (N:ℝ)^(1/4:ℝ)+1≤(y:ℝ)) (ha : 0<a) (hD : D≤N) (hR : 1≤R)
    (hsmall : ∀ q : ℕ, 2≤q → q<D → q≤R →
      ∀ χ : DirichletCharacter ℂ (a*q), χ.IsPrimitive →
        ‖chenSwitchBoxSum N z y i K χ‖≤B) :
    (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
      chenPrimitiveNorm (a*q) (chenSwitchBoxSum N z y i K)/(q:ℝ)) ≤
        (R:ℝ)*a*B+100000*(chenSwitchLog N)^2*((N:ℝ)/R+
          Real.sqrt (a:ℝ)*(N:ℝ)^(7/8:ℝ)+(a:ℝ)*(D:ℝ)*Real.sqrt N) :=
  chen_ap_box_conductors_of_bounds (fun _ => chenSwitchBoxSum N z y i K)
    hB ha hsmall (norm_div_large ha hN hy hD hR)

/-- Convert a character sum decomposed into boxes to the free-conductor normalization. -/
theorem chen_ap_masked_mass_le_of_sum_boxes {a q : ℕ} (ha : 0<a) (hq : 0<q)
    (hc : a.Coprime q) (P : Finset (ℕ×ℕ)) (K : ℕ)
    (I : Finset ℕ) (F : ℕ → DirichletCharacter ℂ (a*q) → ℂ)
    (hdecomp : ∀ χ : DirichletCharacter ℂ (a*q),
      (∑ x∈P,chenMaskedChar χ K x.1*chenMaskedChar χ K x.2) = ∑ i∈I,F i χ) :
    chenMaskedPrimitiveMass P (a*q) K/(q.totient:ℝ) ≤
      ∑ i∈I,chenPrimitiveNorm (a*q) (F i)/(q:ℝ) := by
  let _ : NeZero (a*q) := ⟨(Nat.mul_pos ha hq).ne'⟩
  have hφ : (0:ℝ)<q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hφa : (0:ℝ)<a.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr ha)
  have ha' : (a:ℝ)≠0 := by positivity
  have hq' : (q:ℝ)≠0 := by positivity
  have hboxes : chenMaskedPrimitiveMass P (a*q) K/((a*q).totient:ℝ) ≤
      ∑ i∈I,chenPrimitiveNorm (a*q) (F i)/(↑(a*q):ℝ) := by
    let S := (Finset.univ : Finset (DirichletCharacter ℂ (a*q))).filter (·.IsPrimitive)
    rw [chenMaskedPrimitiveMass_of_pos]
    simp_rw [hdecomp]
    calc
      _ ≤ (∑ χ∈S,∑ i∈I,‖F i χ‖)/((a*q).totient:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun χ _ => norm_sum_le _ _)
      _ = _ := by
        rw [Finset.sum_comm (s:=S)]
        simp only [Finset.sum_div,chenPrimitiveNorm_div_eq_avg,S]
  let T := chenMaskedPrimitiveMass P (a*q) K
  calc
    _ = (a.totient:ℝ)*(T/((a*q).totient:ℝ)) := by
      rw [Nat.totient_mul hc,Nat.cast_mul]
      field_simp
      rfl
    _ ≤ (a.totient:ℝ)*(∑ i∈I,
        chenPrimitiveNorm (a*q) (F i)/(↑(a*q):ℝ)) :=
      mul_le_mul_of_nonneg_left hboxes hφa.le
    _ ≤ (a:ℝ)*(∑ i∈I,
        chenPrimitiveNorm (a*q) (F i)/(↑(a*q):ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.totient_le a))
        (Finset.sum_nonneg fun _ _ => div_nonneg (chenPrimitiveNorm_nonneg ..) (by positivity))
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      field_simp

/-- Converting from the coprime conductor average to the average indexed
by its free factor does not lose an additional factor of the modulus. -/
theorem chen_ap_masked_mass_le_boxes {a q : ℕ} (ha : 0<a) (hq : 0<q)
    (hc : a.Coprime q) (N z y K : ℕ) :
    chenMaskedPrimitiveMass (chenSwitchPairs N z y) (a*q) K/(q.totient:ℝ) ≤
      ∑ i∈Finset.range (N.log2+1), chenPrimitiveNorm (a*q) (chenSwitchBoxSum N z y i K)/(q:ℝ) :=
  chen_ap_masked_mass_le_of_sum_boxes ha hq hc _ _ (Finset.range (N.log2+1))
    (fun i => chenSwitchBoxSum N z y i K) (chenSwitch_masked_sum_eq_sum_boxes N z y K)

end FareyGoldbach
