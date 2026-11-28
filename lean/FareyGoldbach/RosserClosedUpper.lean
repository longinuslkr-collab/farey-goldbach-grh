import FareyGoldbach.RosserSuzukiCoefficients
import FareyGoldbach.LinearSieveFactors

open Filter
open scoped Topology
namespace FareyGoldbach

/-- Finitely many strict prime cutoffs persist for parameters sufficiently close
to one from the right, so the uniform upper comparison includes its endpoint. -/
theorem rosser_upper_at_one_of_right {P D : ℕ} {A V E : ℝ} (hD : 2≤D)
    (hcut : ∀ p ∈ P.primeFactors, p < ⌈(D:ℝ)^(1/(1:ℝ))⌉₊)
    (hupper : ∀ s : ℝ, 1<s → s≤3 →
      (∀ p∈P.primeFactors, p<⌈(D:ℝ)^(1/s)⌉₊) → A≤V*(linearSieveUpperFactor s+E)) :
    A≤V*(linearSieveUpperFactor 1+E) := by
  have hDr : 0<(D:ℝ) := by exact_mod_cast (show 0<D by omega)
  have hpow : ContinuousAt (fun s : ℝ => (D:ℝ)^(1/s)) 1 := by fun_prop (disch := positivity)
  have hF : ContinuousAt (fun s : ℝ => V*(linearSieveUpperFactor s+E)) 1 := by
    unfold linearSieveUpperFactor
    fun_prop (disch := norm_num)
  apply ge_of_tendsto (hF.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 1)))
  have hpc : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ p∈P.primeFactors, p<⌈(D:ℝ)^(1/s)⌉₊ := by
    rw [Filter.eventually_all_finset]
    intro p hp
    have hpD := Nat.lt_ceil.mp (hcut p hp)
    have hlim := hpow.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (1:ℝ)))
    exact (hlim.eventually (Ioi_mem_nhds hpD)).mono fun _ hs =>
      Nat.lt_ceil.mpr hs
  filter_upwards [hpc,(self_mem_nhdsWithin : ∀ᶠ s : ℝ in 𝓝[>] 1, 1<s),
    (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1:ℝ)<3)))] with s hcs hs1 hs3
  exact hupper s hs1 (le_of_lt hs3) hcs

end FareyGoldbach
