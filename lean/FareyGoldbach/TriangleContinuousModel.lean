import FareyGoldbach.ShortWeightedKernel
import FareyGoldbach.TriangularFrequencyKernel

/-! # Triangular averages of the continuous principal Farey model -/

open MeasureTheory Set Complex

namespace FareyGoldbach

private noncomputable def modelPair (r b₁ b₂ Y : ℕ) (x t : ℝ) : ℂ :=
  shortContKernel r b₁ Y t * shortContKernel r b₂ Y t * e (-(x*t))

private lemma continuous_modelPair {Y : ℕ} (hY : 1 ≤ Y) (r b₁ b₂ : ℕ) (x : ℝ) :
    Continuous (modelPair r b₁ b₂ Y x) :=
  ((continuous_shortContKernel hY r b₁).mul (continuous_shortContKernel hY r b₂)).mul
    (continuous_e_real.comp (continuous_const.mul continuous_id).neg)

private noncomputable def weightedSquare (r b Y : ℕ) (t : ℝ) : ℝ :=
  (1 + ((Y:ℝ)/r)*|t|) * ‖shortContKernel r b Y t‖^2

private lemma continuous_weightedSquare {Y : ℕ} (hY : 1 ≤ Y) (r b : ℕ) :
    Continuous (weightedSquare r b Y) := by
  unfold weightedSquare
  exact (continuous_const.add (continuous_const.mul continuous_abs)).mul
    ((continuous_shortContKernel hY r b).norm.pow 2)

private noncomputable def pairMajorant (r b₁ b₂ Y : ℕ) (t : ℝ) : ℝ :=
  (weightedSquare r b₁ Y t + weightedSquare r b₂ Y t) / 2

private lemma continuous_pairMajorant {Y : ℕ} (hY : 1 ≤ Y) (r b₁ b₂ : ℕ) :
    Continuous (pairMajorant r b₁ b₂ Y) :=
  ((continuous_weightedSquare hY r b₁).add (continuous_weightedSquare hY r b₂)).div_const _

private lemma integral_pairMajorant {r Y : ℕ} (hr : 0<r) (hrY : r≤Y) (hY : 1≤Y)
    (b₁ b₂ : ℕ) :
    (∫ t in (-(1/2):ℝ)..1/2, pairMajorant r b₁ b₂ Y t) ≤ 4096*((Y:ℝ)/r) := by
  simp only [pairMajorant, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add ((continuous_weightedSquare hY r b₁).intervalIntegrable ..)
    ((continuous_weightedSquare hY r b₂).intervalIntegrable ..)]
  have h₁ := shortContKernel_weighted_l2 hr hrY hY b₁
  have h₂ := shortContKernel_weighted_l2 hr hrY hY b₂
  change (∫ t in _.._, weightedSquare r b₁ Y t) ≤ _ at h₁
  change (∫ t in _.._, weightedSquare r b₂ Y t) ≤ _ at h₂
  linarith

private lemma modelPair_majorized (r b₁ b₂ Y : ℕ) (x t : ℝ) :
    ‖modelPair r b₁ b₂ Y x t‖ ≤ pairMajorant r b₁ b₂ Y t ∧
    ((Y:ℝ)/r)*|t| * ‖modelPair r b₁ b₂ Y x t‖ ≤ pairMajorant r b₁ b₂ Y t := by
  simp only [modelPair, norm_mul, norm_e, mul_one, pairMajorant, weightedSquare]
  let a := ‖shortContKernel r b₁ Y t‖
  let b := ‖shortContKernel r b₂ Y t‖
  let v := ((Y:ℝ)/r)*|t|
  change a*b ≤ ((1+v)*a^2+(1+v)*b^2)/2 ∧ v*(a*b) ≤ _
  have hv : 0≤v := by dsimp [v]; positivity
  have h := sq_nonneg (a-b)
  constructor
  · nlinarith [mul_nonneg hv (sq_nonneg a),mul_nonneg hv (sq_nonneg b)]
  · nlinarith [mul_nonneg hv h, sq_nonneg a, sq_nonneg b]

private noncomputable def clippedTriangle (η t : ℝ) : ℝ := max 0 (1-|t|/η)

private lemma continuous_clippedTriangle (η : ℝ) : Continuous (clippedTriangle η) := by
  unfold clippedTriangle
  fun_prop

private lemma clippedTriangle_bounds {η : ℝ} (hη : 0<η) (t : ℝ) :
    0 ≤ clippedTriangle η t ∧ clippedTriangle η t ≤ 1 ∧
      1-clippedTriangle η t ≤ |t|/η := by
  unfold clippedTriangle
  exact ⟨le_max_left ..,max_le (by norm_num) (by linarith [div_nonneg (abs_nonneg t) hη.le]),
    by linarith [le_max_right (0:ℝ) (1-|t|/η)]⟩

private noncomputable def taperedPair (r b₁ b₂ Y : ℕ) (η x : ℝ) : ℂ :=
  ∫ t in (-(1/2):ℝ)..1/2, (clippedTriangle η t:ℂ) * modelPair r b₁ b₂ Y x t

private lemma taperedPair_eq_short (r b₁ b₂ Y : ℕ) {η : ℝ} (hη : 0<η)
    (hηh : η≤1/2) (x : ℝ) : taperedPair r b₁ b₂ Y η x =
    ∫ t in -η..η, (clippedTriangle η t:ℂ) * modelPair r b₁ b₂ Y x t := by
  unfold taperedPair
  rw [intervalIntegral.integral_of_le (by norm_num),intervalIntegral.integral_of_le (by linarith)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc (by linarith) hηh)
  intro t ht
  have ht' : η ≤ |t| := by
    by_contra! h
    exact ht.2 ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
  have hz : clippedTriangle η t = 0 :=
    max_eq_left (by linarith [(le_div_iff₀ hη).2 (by simpa using ht' : 1*η ≤ |t|)])
  simp [hz]

private lemma taperedPair_norm_le {r Y : ℕ} (hr : 0<r) (hrY : r≤Y) (hY : 1≤Y)
    {η : ℝ} (hη : 0<η) (b₁ b₂ : ℕ) (x : ℝ) :
    ‖taperedPair r b₁ b₂ Y η x‖ ≤ 4096*((Y:ℝ)/r) := by
  have hc := continuous_pairMajorant hY r b₁ b₂
  apply le_trans _ (integral_pairMajorant hr hrY hY b₁ b₂)
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ (hc.intervalIntegrable ..)
  apply ae_of_all
  intro t _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (clippedTriangle_bounds hη t).1]
  exact (mul_le_of_le_one_left (norm_nonneg _) (clippedTriangle_bounds hη t).2.1).trans
    (modelPair_majorized r b₁ b₂ Y x t).1

private lemma taperedPair_loss {r Y : ℕ} (hr : 0<r) (hrY : r≤Y) (hY : 1≤Y)
    {η : ℝ} (hη : 0<η) (b₁ b₂ : ℕ) (x : ℝ) :
    ‖(∫ t in (-(1/2):ℝ)..1/2, modelPair r b₁ b₂ Y x t) - taperedPair r b₁ b₂ Y η x‖ ≤
      4096/η := by
  let H := (Y:ℝ)/r
  let F := modelPair r b₁ b₂ Y x
  let G := pairMajorant r b₁ b₂ Y
  have hH : 0<H := by dsimp [H]; positivity
  have hF : Continuous F := continuous_modelPair hY r b₁ b₂ x
  have hG : Continuous G := continuous_pairMajorant hY r b₁ b₂
  have hP : Continuous (fun t ↦ (clippedTriangle η t:ℂ)*F t) :=
    (Complex.continuous_ofReal.comp (continuous_clippedTriangle η)).mul hF
  change ‖(∫ t in _.._, F t) - ∫ t in _.._, (clippedTriangle η t:ℂ)*F t‖ ≤ _
  rw [← intervalIntegral.integral_sub (hF.intervalIntegrable ..) (hP.intervalIntegrable ..)]
  have hpt (t : ℝ) : ‖F t - (clippedTriangle η t:ℂ)*F t‖ ≤ (H*η)⁻¹*G t := by
    rw [← one_sub_mul,← Complex.ofReal_one,← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr (clippedTriangle_bounds hη t).2.1)]
    calc
      _ ≤ (|t|/η)*‖F t‖ := mul_le_mul_of_nonneg_right (clippedTriangle_bounds hη t).2.2
                                  (norm_nonneg _)
      _ = (H*η)⁻¹*(H*|t| * ‖F t‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (modelPair_majorized r b₁ b₂ Y x t).2 (by positivity)
  calc
    _ ≤ ∫ t in (-(1/2):ℝ)..1/2, (H*η)⁻¹*G t :=
      intervalIntegral.norm_integral_le_of_norm_le (by norm_num) (ae_of_all _ (fun t _ => hpt t))
        ((continuous_const.mul hG).intervalIntegrable ..)
    _ = (H*η)⁻¹ * ∫ t in (-(1/2):ℝ)..1/2, G t := intervalIntegral.integral_const_mul ..
    _ ≤ (H*η)⁻¹*(4096*H) :=
      mul_le_mul_of_nonneg_left (integral_pairMajorant hr hrY hY b₁ b₂) (by positivity)
    _ = 4096/η := by field_simp

private lemma taperedPair_re_lower {r Y : ℕ} (hr : 0<r) (hrY : r≤Y) (hY : 1≤Y)
    {η : ℝ} (hη : 0<η) (hηh : η≤1/2) {b₁ b₂ k : ℕ}
    (hnlo : Y≤2*(r*k+b₁+b₂)) (hnhi : r*k+b₁+b₂≤Y)
    (hlarge : (2:ℝ)^28≤((Y:ℝ)/r)*η) :
    (1/32768:ℝ)*((Y:ℝ)/r) ≤ (taperedPair r b₁ b₂ Y η (k:ℝ)).re := by
  let F := modelPair r b₁ b₂ Y (k:ℝ)
  let W := taperedPair r b₁ b₂ Y η (k:ℝ)
  have hout : ‖(∫ t, F t) - (∫ t in (-(1/2):ℝ)..1/2, F t)‖ ≤ 80 :=
    shortCont_unit_tail hY r b₁ b₂ k
  have hin := taperedPair_loss hr hrY hY hη b₁ b₂ (k:ℝ)
  have hall : ‖(∫ t, F t)-W‖ ≤ 80+4096/η :=
    (norm_sub_le_norm_sub_add_norm_sub _ (∫ t in (-(1/2):ℝ)..1/2, F t) _).trans (add_le_add hout hin)
  have hDiff := le_trans (le_abs_self _) ((Complex.abs_re_le_norm _).trans hall)
  have hid : (∫ t, F t) = (((Y:ℝ)/r)*shortBumpConvolution (((r:ℝ)*k+b₁+b₂)/Y):ℝ) :=
    integral_shortContKernel_mul_e hr hY b₁ b₂ k
  rw [hid,Complex.sub_re, Complex.ofReal_re] at hDiff
  have hYpos : (0:ℝ)<Y := by positivity
  have hv₁ : 1/2 ≤ ((r:ℝ)*k+b₁+b₂)/Y := by
    apply (le_div_iff₀ hYpos).2
    have hcast : (Y:ℝ) ≤ 2*((r:ℝ)*k+b₁+b₂) := by exact_mod_cast hnlo
    linarith
  have hv₂ : ((r:ℝ)*k+b₁+b₂)/Y ≤ 1 := by
    apply (div_le_iff₀ hYpos).2
    simpa using (show (r:ℝ)*k+b₁+b₂ ≤ Y by exact_mod_cast hnhi)
  have hconv := mul_le_mul_of_nonneg_left (shortBumpConvolution_lower hv₁ hv₂)
    (by positivity : 0≤(Y:ℝ)/r)
  have herr : 80+4096/η ≤ ((Y:ℝ)/r)/32768 := by
    rw [← le_sub_iff_add_le'] 
    apply (div_le_iff₀ hη).2
    nlinarith
  change _ ≤ W.re
  linarith

/-- Continuous main term on the central Farey arc, including its arithmetic density. -/
noncomputable def triangleQOneModel (r b Y : ℕ) (t : ℝ) : ℂ :=
  (((r:ℝ)/r.totient:ℝ):ℂ)*shortContKernel r b Y t

/-- The normalized triangular Fourier coefficient of two central-arc models. -/
noncomputable def triangleModelCoefficient (r b₁ b₂ Y : ℕ) (η x : ℝ) : ℂ :=
  ∫ t in -η..η, (triangleWindow η t:ℂ) *
    (triangleQOneModel r b₁ Y t * triangleQOneModel r b₂ Y t * e (-(x*t)))

private lemma triangleModelCoefficient_eq (r b₁ b₂ Y : ℕ) {η : ℝ} (hη : 0<η)
    (hηh : η≤1/2) (x : ℝ) : triangleModelCoefficient r b₁ b₂ Y η x =
    ((η⁻¹*((r:ℝ)/r.totient)^2:ℝ):ℂ) * taperedPair r b₁ b₂ Y η x := by
  rw [taperedPair_eq_short r b₁ b₂ Y hη hηh x,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [triangleQOneModel, modelPair, triangleWindow, clippedTriangle,
    Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem triangleModelCoefficient_norm_le {r Y : ℕ} {η : ℝ}
    (hr : 0<r) (hrY : r≤Y) (hY : 1≤Y) (hη : 0<η) (hηh : η≤1/2)
    (b₁ b₂ : ℕ) (x : ℝ) :
    ‖triangleModelCoefficient r b₁ b₂ Y η x‖ ≤
      4096*η⁻¹*((r:ℝ)/r.totient)^2*((Y:ℝ)/r) := by
  rw [triangleModelCoefficient_eq r b₁ b₂ Y hη hηh x, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (η⁻¹*((r:ℝ)/r.totient)^2)*(4096*((Y:ℝ)/r)) :=
      mul_le_mul_of_nonneg_left (taperedPair_norm_le hr hrY hY hη b₁ b₂ x) (by positivity)
    _ = _ := by ring

theorem triangleModelCoefficient_re_lower {r Y : ℕ} {η : ℝ}
    (hr : 0<r) (hrY : r≤Y) (hY : 1≤Y) (hη : 0<η) (hηh : η≤1/2)
    {b₁ b₂ k : ℕ} (hnlo : Y≤2*(r*k+b₁+b₂)) (hnhi : r*k+b₁+b₂≤Y)
    (hlarge : (2:ℝ)^28≤((Y:ℝ)/r)*η) :
    ((1:ℝ)/32768)*η⁻¹*((r:ℝ)/r.totient)^2*((Y:ℝ)/r) ≤
      (triangleModelCoefficient r b₁ b₂ Y η (k:ℝ)).re := by
  rw [triangleModelCoefficient_eq r b₁ b₂ Y hη hηh (k:ℝ), Complex.re_ofReal_mul]
  exact le_trans (le_of_eq (by ring))
    (mul_le_mul_of_nonneg_left (taperedPair_re_lower hr hrY hY hη hηh hnlo hnhi hlarge)
      (by positivity : 0≤η⁻¹*((r:ℝ)/r.totient)^2))


end FareyGoldbach
