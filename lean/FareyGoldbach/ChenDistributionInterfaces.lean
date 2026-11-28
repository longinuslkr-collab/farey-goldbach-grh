import FareyGoldbach.ChenElementaryError
import FareyGoldbach.ChenNumericalCertificate

/-! # Unsigned arithmetic-distribution inputs for Chen's sieve -/

open Filter
open scoped Topology Classical

namespace FareyGoldbach

def chenSiftingPrimes (N z : ℕ) : Finset ℕ :=
  (Finset.range z).filter (fun p => p.Prime ∧ ¬p∣N)

def chenSiftingProduct (N z : ℕ) : ℕ := ∏ p ∈ chenSiftingPrimes N z, p

theorem chenSiftingProduct_squarefree (N z : ℕ) : Squarefree (chenSiftingProduct N z) := by
  unfold chenSiftingProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (Finset.mem_filter.mp hp).2.1
      (Finset.mem_filter.mp hq).2.1).mpr hne)
  · intro _ hp
    exact (Finset.mem_filter.mp hp).2.1.squarefree

theorem chenSiftingProduct_primeFactors (N z : ℕ) :
    (chenSiftingProduct N z).primeFactors = chenSiftingPrimes N z :=
  Nat.primeFactors_prod (fun _ hp => ((Finset.mem_filter.mp hp).2).1)

theorem chenRough_iff_coprime_product (N z a : ℕ) :
    chenRough N z a ↔ a.Coprime (chenSiftingProduct N z) := by
  rw [chenSiftingProduct, Nat.coprime_prod_right_iff]
  unfold chenRough chenSiftingPrimes
  constructor
  · intro h p hp
    obtain ⟨hr,hp,hN⟩ := Finset.mem_filter.mp hp
    exact (hp.coprime_iff_not_dvd.mpr (h p hr hp hN)).symm
  · intro h p hr hp hN
    exact hp.coprime_iff_not_dvd.mp (h p (Finset.mem_filter.mpr ⟨hr,hp,hN⟩)).symm

theorem chenSiftingProduct_coprime (N z : ℕ) :
    (chenSiftingProduct N z).Coprime N := by
  rw [chenSiftingProduct, Nat.coprime_prod_left_iff]
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hp).2.2

/-- Reflection identifies the unsifted Chen carrier with the primes at most N. -/
theorem chenA_card_eq_primeCounting (N : ℕ) : (chenA N).card=Nat.primeCounting N := by
  rw [←Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_bij' (fun a _ => N-a) (fun p _ => N-p)
  · intro a ha
    exact Nat.mem_primesLE.mpr ⟨Nat.sub_le ..,(Finset.mem_filter.mp ha).2⟩
  · intro p hp
    obtain ⟨hh,hp⟩ := Nat.mem_primesLE.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [show N-(N-p)=p by omega]⟩
  · intro a ha
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    omega
  · intro p hp
    have hh := (Nat.mem_primesLE.mp hp).1
    omega

/-- The target scale of every remainder, before division by a singular factor. -/
noncomputable def chenLogScale (N : ℕ) : ℝ := (N:ℝ)/Real.log (N:ℝ)^2

/-- The count before subtraction of the predicted local main term. -/
noncomputable def chenAPError (A : Finset ℕ) (mass : ℝ) (d : ℕ) : ℝ :=
  ((chenDivisible A d).card:ℝ)-mass/(d.totient:ℝ)

noncomputable def chenMediumMass (N q : ℕ) : ℝ :=
  if q∣N then 0 else ((chenA N).card:ℝ)/(q.totient:ℝ)

noncomputable def chenPrimeAPError (N : ℕ) (d : ℕ) : ℝ :=
  chenAPError (chenA N) (chenA N).card d

noncomputable def chenMediumAPError (N q d : ℕ) : ℝ :=
  chenAPError (chenDivisible (chenA N) q) (chenMediumMass N q) d

noncomputable def chenSwitchingAPError (N d : ℕ) : ℝ :=
  let B := chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)
  chenAPError B B.card d

/-- The plain sum of absolute errors over reduced moduli. -/
noncomputable def chenReducedError (N D : ℕ) (err : ℕ→ℝ) : ℝ :=
  ∑ d ∈ (Finset.Ico 1 D).filter (fun d => d.Coprime N), |err d|

/-- The conditioned moduli that occur in the linear sieve for the medium-prime terms. -/
noncomputable def chenMediumError (N D : ℕ) : ℝ :=
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  ∑ q ∈ chenMediumPrimes z y,
    ∑ d ∈ (Finset.Ico 1 (D/q)).filter (fun d => d∣chenSiftingProduct N z),
      |chenMediumAPError N q d|

/-- Data at a supplied level function, which can be logarithmically reduced or a fixed power. -/
def ChenPrimeAPDistributionAt (D : ℕ→ℕ) : Prop :=
  Tendsto (fun N : ℕ => ((chenA N).card:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1) ∧
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
    chenReducedError N (D N) (chenPrimeAPError N) ≤ ε*chenLogScale N ∧
    chenMediumError N (D N) ≤ ε*chenLogScale N

/-- A one-sided mass asymptotic suffices for the switched sequence. The error
is measured against its own cardinality divided by the totient. -/
def ChenSwitchingDistributionAt (D : ℕ→ℕ) : Prop :=
  (∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
    ((chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ) ≤
      (chenSwitchIntegral+ε)*((N:ℝ)/Real.log (N:ℝ))) ∧
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
    chenReducedError N (D N) (chenSwitchingAPError N) ≤ ε*chenLogScale N

noncomputable def chenPowerLevel (θ : ℝ) (N : ℕ) : ℕ := ⌊(N:ℝ)^θ⌋₊

noncomputable def chenLogLevel (A : ℕ) (N : ℕ) : ℕ :=
  ⌊Real.sqrt (N:ℝ)/Real.log (N:ℝ)^A⌋₊

/-- Distribution to each fixed power strictly below one half. -/
def ChenPrimeAPDistribution : Prop :=
  ∀ θ : ℝ, 11/24<θ → θ<1/2 → ChenPrimeAPDistributionAt (chenPowerLevel θ)

/-- The same quantifier order for switched products, so both estimates can be
used at a single fixed power with a positive sieve margin. -/
def ChenSwitchingDistribution : Prop :=
  ∀ θ : ℝ, 11/24<θ → θ<1/2 → ChenSwitchingDistributionAt (chenPowerLevel θ)

theorem chenReducedError_mono {N D D' : ℕ} (hle : D≤D') (err : ℕ→ℝ) :
    chenReducedError N D err ≤ chenReducedError N D' err := by
  unfold chenReducedError
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hi,hc⟩ := Finset.mem_filter.mp hd
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hl,hu.trans_le hle⟩,hc⟩
  · intro d _ _
    exact abs_nonneg (err d)

theorem chenMediumError_mono {N D D' : ℕ} (hle : D≤D') :
    chenMediumError N D ≤ chenMediumError N D' := by
  unfold chenMediumError
  apply Finset.sum_le_sum
  intro q _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hi,hc⟩ := Finset.mem_filter.mp hd
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hl,hu.trans_le (Nat.div_le_div_right hle)⟩,hc⟩
  · intro d _ _
    exact abs_nonneg _

theorem ChenPrimeAPDistributionAt.mono {D E : ℕ→ℕ}
    (h : ChenPrimeAPDistributionAt D) (hle : ∀ᶠ N in atTop, E N≤D N) :
    ChenPrimeAPDistributionAt E := by
  refine ⟨h.1,?_⟩
  intro ε hε
  filter_upwards [h.2 ε hε, hle] with N hN hl he
  exact ⟨(chenReducedError_mono hl _).trans (hN he).1, (chenMediumError_mono hl).trans (hN he).2⟩

theorem ChenSwitchingDistributionAt.mono {D E : ℕ→ℕ}
    (h : ChenSwitchingDistributionAt D) (hle : ∀ᶠ N in atTop, E N≤D N) :
    ChenSwitchingDistributionAt E := by
  refine ⟨h.1,?_⟩
  intro ε hε
  filter_upwards [h.2 ε hε, hle] with N hN hl he
  exact (chenReducedError_mono hl _).trans (hN he)

end FareyGoldbach
