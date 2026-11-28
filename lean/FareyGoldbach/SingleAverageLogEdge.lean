import FareyGoldbach.SingleAverageGoldbach

open scoped BigOperators Classical

namespace FareyGoldbach

/-- The fixed-class fourth moment needed on active dyadic blocks. -/
def FixedClassPrimeFourthBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ {r b Y : ℕ}, 0 < r → b < r → Nat.Coprime b r → r ≤ Y →
    (r:ℝ) ≤ 4*((Y:ℝ)/r) →
    (∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b Y x‖^4) ≤
      K*((r:ℝ)/r.totient)^4*((Y:ℝ)/r)^3

/-- Choose the integer totient cutoff at the ratio of the two dyadic scales. -/
private theorem log_edge_cutoff {H B : ℝ} (hH : 0 ≤ H) (hB : 0 < B) :
    ∃ D : ℕ, 1 ≤ D ∧
      B*Real.log (2*(D:ℝ))+H/(D:ℝ) ≤ 2*(B*(1+Real.log (2+H/B))) := by
  let u := H/B
  have hu : 0 ≤ u := div_nonneg hH hB.le
  let D := ⌈1+u⌉₊
  have hd : 1+u ≤ (D:ℝ) := Nat.le_ceil _
  have hd' : (1:ℝ) ≤ D := by linarith
  have hpos : 0 < (D:ℝ) := by linarith
  have hub := (Nat.ceil_lt_add_one (show 0 ≤ 1+u by linarith)).le
  have hle : (D:ℝ) ≤ 2+u := by dsimp [D]; linarith
  have hlog : Real.log (2*(D:ℝ)) ≤ 1+Real.log (2+u) := by
    rw [Real.log_mul (by norm_num) hpos.ne']
    linarith [Real.log_le_log hpos hle,Real.log_two_lt_d9]
  have htail : H/(D:ℝ) ≤ B := by
    apply (div_le_iff₀ hpos).2
    calc H = B*u := by dsimp [u]; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hB.le
  have hlg : 0 ≤ Real.log (2+u) := Real.log_nonneg (by linarith)
  refine ⟨D, by exact_mod_cast hd', ?_⟩
  change B*Real.log (2*(D:ℝ))+H/(D:ℝ) ≤ 2*(B*(1+Real.log (2+u)))
  nlinarith only [mul_le_mul_of_nonneg_left hlog hB.le,htail,mul_nonneg hB.le hlg]

/-- Combine the fixed-class fourth moment with the smoothed twist estimate and
the first averaged energy on each active dyadic block. -/
theorem single_average_log_edge_dyadic_of_fourth (h : SmoothedTwistEstimate)
    (h₄ : FixedClassPrimeFourthBound) : SingleAverageLogEdgeDyadicBound := by
  obtain ⟨C,hC,hTw⟩ := h
  obtain ⟨K,hK,hfour⟩ := h₄
  obtain ⟨M,hM,hmix⟩ := fixed_mixed_integral_fourth_bound hC hTw K hK
  let F : ℝ := (3*(3*C+1)^2*(2:ℝ)^15+3+3*(2:ℝ)^39)*(1+2*C)
  let J : ℝ := 2*(262144:ℝ)^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hJ : 0 < J := by norm_num [J]
  refine ⟨J*(F+2*M),by positivity,?_⟩
  intro r Y hr b₁ hH hBactive
  dsimp only
  have hH26 : 2^26 ≤ Y/r := le_trans (by norm_num) hH
  have hY2 : 2 ≤ Y := (le_trans (by norm_num : 2 ≤ 2^72) hH).trans (Nat.div_le_self _ _)
  have hrY : r ≤ Y := by
    calc r = r*1 := (mul_one _).symm
         _ ≤ r*(Y/r) := Nat.mul_le_mul_left _ (by omega)
         _ ≤ Y := Nat.mul_div_le _ _
  have hr' : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have ht' : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hY' : (0:ℝ) < Y := Nat.cast_pos.mpr (by omega)
  let H := (Y:ℝ)/r
  let L := Real.log (2*(Y:ℝ))
  let a := (r.totient:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let B := a^2*(r:ℝ)*L^2
  let G := κ^4*H^2
  let U := a^2*Real.sqrt H*L^3
  let V := B*(1+Real.log (2+H/B))
  have hHp : 0 < H := div_pos hY' hr'
  have ha : 0 < a := div_pos ht' hr'
  have hκ : 0 < κ := div_pos hr' ht'
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (one_le_log_two_mul hY2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hlg : 0 ≤ Real.log (2+H/B) := Real.log_nonneg (by have := div_pos hHp hB; linarith)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hκa : κ*a=1 := by dsimp [κ,a]; field_simp
  have hκa₂ : κ^2*a^2=1 := by rw [← mul_pow,hκa,one_pow]
  have hYr : (Y:ℝ) = (r:ℝ)*H := by dsimp [H]; field_simp
  have heU : κ^2*H^2*Real.sqrt H*L^3 = G*U := by
    dsimp only [G,U]
    calc _ = κ^2*H^2*Real.sqrt H*L^3*(κ^2*a^2) := by rw [hκa₂,mul_one]
         _ = _ := by ring
  obtain ⟨D,hD,hcut⟩ := log_edge_cutoff hHp.le hB
  have heV :
      κ^2*Y*H*L^2*Real.log (2*(D:ℝ))+κ^4*H^3/(D:ℝ) =
      G*(B*Real.log (2*(D:ℝ))+H/(D:ℝ)) := by
    dsimp only [G,B]
    rw [hYr]
    calc _ = κ^2*((r:ℝ)*H)*H*L^2*Real.log (2*(D:ℝ))*(κ^2*a^2)+κ^4*H^3/(D:ℝ) := by rw [hκa₂,mul_one]
         _ = _ := by ring
  have hrB := (edge_basics hr hY2 hrY).1
  change (r:ℝ) ≤ 4*B at hrB
  change B ≤ H at hBactive
  have hfour' := hfour hr (mem_coprimeClasses.mp b₁.2).1
    (mem_coprimeClasses.mp b₁.2).2 hrY (show (r:ℝ) ≤ 4*H by linarith only [hrB,hBactive])
  have hmixed : ∀ b₂ ∈ coprimeClasses r,
      (∫ x in (0:ℝ)..1, ‖routeARemainder r b₁.1 Y x‖^2 *
        ‖modelSum r b₂ Y (routeAQ Y r) (routeAQ Y r) x‖^2) ≤ (2*M)*(G*V) := by
    intro b₂ hb₂
    have hm := hmix hr (mem_coprimeClasses.mp b₁.2).1 (mem_coprimeClasses.mp b₁.2).2
      (mem_coprimeClasses.mp hb₂).1 hH hfour' D hD
    change _ ≤ M*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ))+κ^4*H^3/(D:ℝ)) at hm
    rw [heV] at hm
    exact hm.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcut hG.le) hM.le).trans_eq
      (by dsimp only [V]; ring))
  have hfirst := routeA_first_energy hC hTw hr (mem_coprimeClasses.mp b₁.2).1
    (mem_coprimeClasses.mp b₁.2).2 hH hBactive
  change _ ≤ F*(κ^2*H^2*Real.sqrt H*L^3) at hfirst
  rw [heU] at hfirst
  have he := routeA_single_dyadic_of_energies hr hH26 b₁ hfirst hmixed
  change singleAvgDyadicExceptions Y r hr b₁ ≤ (J*(F+2*M))*(U+V)
  apply le_of_mul_le_mul_right _ hG
  calc singleAvgDyadicExceptions Y r hr b₁*G =
        (262144:ℝ)^2*(singleAvgDyadicExceptions Y r hr b₁*((1/262144:ℝ)*κ^2*H)^2) := by dsimp [G]; ring
       _ ≤ (262144:ℝ)^2*(2*(F*(G*U)+(2*M)*(G*V))) := mul_le_mul_of_nonneg_left he (by positivity)
       _ = J*(F*U+(2*M)*V)*G := by dsimp [J]; ring
       _ ≤ _ := by
         have hh : F*U+(2*M)*V ≤ (F+2*M)*(U+V) := by
           nlinarith only [mul_nonneg hF hV,mul_nonneg hM.le hU]
         exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hh hJ.le).trans_eq (by ring)) hG.le

/-- Global single-average logarithmic estimate under the two analytic inputs. -/
theorem single_average_log_edge_of_fourth (h : SmoothedTwistEstimate)
    (h₄ : FixedClassPrimeFourthBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C*singleAvgLogEdgeBudget X r :=
  singleAvgLogEdge_of_dyadic (single_average_log_edge_dyadic_of_fourth h h₄)

end FareyGoldbach