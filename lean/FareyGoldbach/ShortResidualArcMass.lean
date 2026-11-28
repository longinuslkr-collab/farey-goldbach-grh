import FareyGoldbach.ShortAveragedRemainder
import FareyGoldbach.ContinuousShortModel
import FareyGoldbach.ShortCellMass
import FareyGoldbach.ShortFareyGeometry

/-! # Averaged residual mass on arbitrary short arcs -/

open MeasureTheory Set
open scoped Classical BigOperators

namespace FareyGoldbach

private theorem shortLocalMain_eq {r b Y : ℕ} (hr : 0 < r) (hY : 2 ≤ Y)
    (c : RatCenter) (hb : b < r) (hbr : Nat.Coprime b r) [NeZero (r*c.q)] (β : ℝ) :
    shortLocalMain r b Y c.a c.q β = modelCoeff r b c * shortContKernel r b Y β := by
  have hr' : (r:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have ht : (r.totient:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
  have hq : (c.q.totient:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr c.q_pos).ne'
  unfold shortLocalMain shortContKernel modelCoeff
  rw [← shortContinuousMain_eq_mellin (by omega : 1 ≤ Y)]
  by_cases hc : Nat.Coprime c.q r
  · rw [ite_eq_left hc, charCoeff_one_coprime hr c.q_pos hb c.coprime hbr hc]
    push_cast
    field_simp
  · have hg : 1 < Nat.gcd r c.q := by
      have hp := Nat.gcd_pos_of_pos_left c.q hr
      have hn : Nat.gcd r c.q ≠ 1 := fun h => hc (by rwa [Nat.Coprime, Nat.gcd_comm])
      omega
    rw [ite_eq_right hc, charCoeff_one_eq_zero_of_one_lt_gcd r c.q c.a b hr c.q_pos c.coprime hbr hg]
    simp

private theorem smoothedPrimeSum_eq_at_wrap (r b Y : ℕ) (c : RatCenter) (α : ℝ) :
    smoothedPrimeSum r b Y α =
      smoothedPrimeSum r b Y ((c.a:ℝ)/(c.q:ℝ)+wrap (α-c.val)) := by
  unfold smoothedPrimeSum RatCenter.val
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply e_eq_of_sub_int (k := round (α - (c.a : ℝ) / (c.q : ℝ)) * (j : ℤ))
  unfold wrap
  push_cast
  ring

theorem shortResidual_eq_on_cell {r b Y Q : ℕ} (hr : 0 < r) (hY : 2 ≤ Y)
    {c : RatCenter} {α : ℝ} (hcell : α ∈ voronoiCell Q c)
    (hb : b < r) (hbr : Nat.Coprime b r) [NeZero (r*c.q)] :
    smoothedPrimeSum r b Y α - shortContModel r b Y Q α =
      shortLocalRemainder r b Y c.a c.q (wrap (α-c.val)) := by
  have hc : c ∈ (centers Q).filter (fun c => c.q ≤ Q) :=
    Finset.mem_filter.mpr ⟨hcell.1,mem_centers_iff.mp hcell.1⟩
  have hm : shortContModel r b Y Q α =
      modelCoeff r b c * shortContKernel r b Y (wrap (α-c.val)) := by
    unfold shortContModel
    rw [Finset.sum_eq_single_of_mem c hc]
    · exact Set.indicator_of_mem hcell _
    · intro c' _ hn
      exact Set.indicator_of_notMem
        (fun h' => (Set.disjoint_left.mp (voronoiCell_disjoint hn)) h' hcell) _
  exact (congrArg₂ (· - ·) (smoothedPrimeSum_eq_at_wrap r b Y c α)
    (hm.trans (shortLocalMain_eq hr hY c hb hbr _).symm) :
    smoothedPrimeSum r b Y α - shortContModel r b Y Q α =
      smoothedPrimeSum r b Y ((c.a:ℝ)/(c.q:ℝ)+wrap (α-c.val)) -
        shortLocalMain r b Y c.a c.q (wrap (α-c.val)))

set_option maxHeartbeats 2000000 in
theorem shortResidual_average_local_of_meanSquare (h : LocalTwistedMeanSquare) :
    ∃ C : ℝ, 0<C ∧ ∀ {r Y Q K : ℕ}, 0<r → r≤Y → 2≤Y →
      3≤Q → Q^2≤K → Q^2≤Y/r → ∀ x : ℝ,
      (∫ α in x-1/(K:ℝ)..x+1/(K:ℝ), (1/(r.totient:ℝ)) *
        ∑ b ∈ coprimeClasses r,
          ‖smoothedPrimeSum r b Y α - shortContModel r b Y Q α‖^2) ≤
        C*(Y:ℝ)/((r.totient:ℝ)*Q)*Real.log (2*(Y:ℝ))^2 := by
  obtain ⟨C,hC,hcut⟩ := shortPrimeTwistedMeanSquare h
  refine ⟨9*(3/2)*(18*C+4), by positivity, ?_⟩
  intro r Y Q K hr hrY hY hQ hQK hQY x
  let δ : ℝ := 1/(K:ℝ)
  let L := Real.log (2*(Y:ℝ))
  have hQ₀ : 0<Q := by omega
  have hQ' : (0:ℝ)<Q := Nat.cast_pos.mpr hQ₀
  have hK : 0<K := (Nat.pow_pos hQ₀).trans_le hQK
  have hK' : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hδQ : δ*(Q:ℝ)^2 ≤ 1 := by
    dsimp [δ]
    rw [one_div, inv_mul_eq_div]
    exact (div_le_one hK').2 (by exact_mod_cast hQK)
  have h2K : (2:ℝ) ≤ K := by
    exact_mod_cast (show 2 ≤ K from
      (show 2 ≤ 3^2 by decide).trans ((Nat.pow_le_pow_left hQ 2).trans hQK))
  have hδhalf : δ≤1/2 := div_le_div_of_nonneg_left zero_le_one zero_lt_two h2K
  have hY' : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  let I := shortWindowCenters Q x δ
  let G (c : RatCenter) (β : ℝ) : ℝ :=
    letI : NeZero (r*c.q) := ⟨Nat.mul_ne_zero hr.ne' c.q_pos.ne'⟩
    (1/(r.totient:ℝ))*∑ b ∈ coprimeClasses r, ‖shortLocalRemainder r b Y c.a c.q β‖^2
  have hG (c : RatCenter) : Continuous (G c) := by
    let _ : NeZero (r*c.q) := ⟨Nat.mul_ne_zero hr.ne' c.q_pos.ne'⟩
    exact continuous_const.mul (continuous_sum_finset (coprimeClasses r) fun b _ =>
      (continuous_shortLocalRemainder r b Y c.a c.q).norm.pow 2)
  have hG₀ (c : RatCenter) (β : ℝ) : 0 ≤ G c β := by dsimp [G]; positivity
  have hpiece (c : RatCenter) (hc : c ∈ I) :
      (∫ α in x-δ..x+δ, shortCellMassDensity Q c (G c) α) ≤
        (3/2)*(18*C+4)*(Y:ℝ)/((r.totient:ℝ)*Q)*L^2 := by
    have hcQ := mem_centers_iff.mp (Finset.mem_filter.mp hc).1
    have hq' : (0:ℝ)<c.q := Nat.cast_pos.mpr c.q_pos
    have hqY : c.q ≤ Y := by
      have hQYnat : Q ≤ Y := ((Nat.le_self_pow (by decide : 2 ≠ 0) Q).trans hQY).trans (Nat.div_le_self _ _)
      exact hcQ.trans hQYnat
    let η : ℝ := 3/(2*((c.q:ℝ)*Q))
    have hη₁ : (r:ℝ)/Y ≤ η := by
      have hQprod : (Q:ℝ)^2 ≤ (Y:ℝ)/r := by
        apply (le_div_iff₀ hr').2
        exact_mod_cast (Nat.mul_le_mul_right r hQY).trans (by simpa [Nat.mul_comm] using Nat.mul_div_le Y r)
      have hqQ : (c.q:ℝ)*Q ≤ (Y:ℝ)/r := by
        refine (mul_le_mul_of_nonneg_right (show (c.q:ℝ) ≤ Q by exact_mod_cast hcQ) hQ'.le).trans ?_
        rwa [← sq]
      have hb := (le_div_iff₀ hr').1 hqQ
      dsimp [η]
      apply (div_le_div_iff₀ hY' (by positivity)).2
      nlinarith only [hb,hY'.le]
    have hη₂ : η ≤ 1/2 := by
      have h3 : (3:ℝ)≤Q := by exact_mod_cast hQ
      have hq₁ : (1:ℝ)≤c.q := Nat.one_le_cast.mpr c.q_pos
      have hb := mul_le_mul_of_nonneg_right hq₁ hQ'.le
      dsimp [η]
      exact (div_le_iff₀ (by positivity)).2 (by linarith [hb])
    let _ : NeZero (r*c.q) := ⟨Nat.mul_ne_zero hr.ne' c.q_pos.ne'⟩
    have hi := shortLocalRemainder_avg_interval_bound hC hcut (a := c.a) hr c.q_pos hrY hqY hY hη₁ hη₂
    calc (∫ α in x-δ..x+δ, shortCellMassDensity Q c (G c) α) ≤ ∫ β in -η..η, G c β :=
          shortCellMassDensity_arc_le hQ c (hG c) (hG₀ c) (by linarith) (by linarith)
      _ ≤ (18*C+4)*((c.q:ℝ)*(Y:ℝ)/r.totient)*η*L^2 := hi
      _ = _ := by dsimp [η]; field_simp
  let F (α : ℝ) := (1/(r.totient:ℝ))*∑ b ∈ coprimeClasses r,
    ‖smoothedPrimeSum r b Y α - shortContModel r b Y Q α‖^2
  have hsum (α : ℝ) (hα : α ∈ Set.uIcc (x-δ) (x+δ)) :
      F α = ∑ c ∈ I, shortCellMassDensity Q c (G c) α := by
    rw [uIcc_of_le (by linarith : x-δ≤x+δ)] at hα
    obtain ⟨c,hc,hcell⟩ := voronoiCell_cover Q hQ₀ α
    have hIc : c ∈ I := Finset.mem_filter.mpr ⟨hc,⟨α,hα,hcell⟩⟩
    rw [Finset.sum_eq_single_of_mem c hIc]
    · rw [shortCellMassDensity, Set.indicator_of_mem hcell]
      let _ : NeZero (r*c.q) := ⟨Nat.mul_ne_zero hr.ne' c.q_pos.ne'⟩
      exact congrArg (fun z : ℝ => (1/(r.totient:ℝ))*z)
        (Finset.sum_congr (rfl : coprimeClasses r = coprimeClasses r) fun b hb =>
          congrArg (fun z : ℂ => ‖z‖^2)
            (shortResidual_eq_on_cell hr hY hcell (mem_coprimeClasses.mp hb).1 (mem_coprimeClasses.mp hb).2))
    · intro c' _ hn
      exact Set.indicator_of_notMem
        (fun hc' => (Set.disjoint_left.mp (voronoiCell_disjoint hn)) hc' hcell) _
  have hI : I.card ≤ 9 := shortWindowCenters_card_le_nine (by omega) x δ hδQ
  have hPn : 0 ≤ (3/2)*(18*C+4)*(Y:ℝ)/((r.totient:ℝ)*Q)*L^2 := by positivity
  change (∫ α in x-δ..x+δ, F α) ≤ _
  rw [intervalIntegral.integral_congr hsum, intervalIntegral_finset_sum
    (fun c _ => shortCellMassDensity_intervalIntegrable Q c (hG c) (hG₀ c) _ _)]
  calc _ ≤ ∑ _c ∈ I, (3/2)*(18*C+4)*(Y:ℝ)/((r.totient:ℝ)*Q)*L^2 :=
        Finset.sum_le_sum hpiece
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right (show (I.card:ℝ) ≤ 9 by exact_mod_cast hI) hPn).trans_eq
        (by dsimp [L]; ring)

end FareyGoldbach
