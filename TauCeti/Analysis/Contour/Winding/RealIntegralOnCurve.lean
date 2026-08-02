/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.RealIntegral
public import TauCeti.Analysis.Contour.Crossing.PVAggregation
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.Crossing.Windows
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.PerWindow.CPV
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The real bounded-integrand formula for the winding number, on the curve (Hungerbühler–Wasem
Prop 2.3, on-curve case)

For a closed piecewise-`C¹` immersion `γ` that passes through a point `s` (so the generalized
winding number `windingNumber γ a b s` is a genuine Cauchy principal value, not the ordinary
index integral of the off-curve case in `Winding.RealIntegral`), this file proves the on-curve
form of Hungerbühler–Wasem Proposition 2.3: `n_s(γ)` is a **real** number, equal to the ordinary
(non-principal-value) integral of the real winding integrand, whenever that integrand is
interval-integrable:

`n_s(γ) = (1 / 2π) ∫_a^b (x ẏ - y ẋ) / (x² + y²) dt`, `x + i y = γ - s`.

This bundles two independent facts about the single-point Cauchy principal value
`L := 2πi · n_s(γ)` of the Cauchy kernel `(z - s)⁻¹` along `γ`:

* **Reality** (`Re L = 0`): the real part of the truncated index integral telescopes to
  `Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖` regardless of any branch-cut/slit-plane data — the
  real part of `Complex.log` never depends on a branch — and this vanishes by closedness.
* **The integral identity** (`Im L = 2π ∫ h`, `h` the real winding integrand): a dominated-
  convergence argument shows the truncated integral of `h` itself (not composed with a branch of
  `arg`) tends to its ordinary integral, since `h` is interval-integrable and `γ` meets `s` only
  finitely often.

Both facts are read off the *same* explicit principal-value witness constructed by aggregating
the plain (avoiding) pieces and the per-crossing windows along the sorted crossing list, mirroring
`IsPwC1ImmersionOn.cauchyPVExistsAt_inv_sub` but keeping the aggregated value explicit instead of
only asserting its existence.

## Main results

* `TauCeti.Contour.windingNumber_eq_real_integral_of_onCurve` — the on-curve real bounded-integrand
  formula.

## Provenance

New assembly for this roadmap target (HW Prop 2.3, on-curve case), built from existing
Tau Ceti contour-integration infrastructure: the per-crossing window value
(`perWindow_truncated_integral_tendsto`), the sorted-crossing aggregation
(`hasCauchyPVAt_along_sorted`), and the existence machinery of `InvSubCPVExistence.lean`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Proposition 2.3.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-! ### The real part of a complex derivative along the real embeddings -/

private theorem hasDerivAt_re {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t) :
    HasDerivAt (fun u => (f u).re) D.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf

private theorem hasDerivAt_im {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t) :
    HasDerivAt (fun u => (f u).im) D.im t :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf

/-- The derivative of the squared complex modulus, in the real-parameter chain-rule form used to
differentiate the log-norm below. -/
private theorem hasDerivAt_normSq {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t) :
    HasDerivAt (fun u => Complex.normSq (f u)) (2 * ((starRingEnd ℂ (f t) * D).re)) t := by
  have hre := hasDerivAt_re hf
  have him := hasDerivAt_im hf
  have h1 : HasDerivAt (fun u => (f u).re * (f u).re) (D.re * (f t).re + (f t).re * D.re) t :=
    hre.mul hre
  have h2 : HasDerivAt (fun u => (f u).im * (f u).im) (D.im * (f t).im + (f t).im * D.im) t :=
    him.mul him
  have key : HasDerivAt (fun u => Complex.normSq (f u))
      (D.re * (f t).re + (f t).re * D.re + (D.im * (f t).im + (f t).im * D.im)) t :=
    (h1.add h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => by
      simp [Complex.normSq_apply])
  have hval : D.re * (f t).re + (f t).re * D.re + (D.im * (f t).im + (f t).im * D.im)
      = 2 * ((starRingEnd ℂ (f t) * D).re) := by
    simp [Complex.mul_re]; ring
  rwa [hval] at key

/-- **The log-norm derivative.** Wherever a real-parametrized curve is differentiable and avoids
`0`, the real-valued function `t ↦ Real.log ‖f t‖` is differentiable, with derivative the real
part of the index integrand `(f t)⁻¹ * deriv f t` — unconditionally, with no slit-plane or branch
data: `Complex.log`'s real part `Real.log ∘ norm` never depends on a choice of branch. -/
private theorem hasDerivAt_log_norm {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t)
    (hne : f t ≠ 0) :
    HasDerivAt (fun u => Real.log ‖f u‖) (((f t)⁻¹ * D).re) t := by
  have hnsq := hasDerivAt_normSq hf
  have hnsq_pos : (0 : ℝ) < Complex.normSq (f t) := Complex.normSq_pos.mpr hne
  have hlog : HasDerivAt (fun u => Real.log (Complex.normSq (f u)))
      ((Complex.normSq (f t))⁻¹ * (2 * ((starRingEnd ℂ (f t) * D).re))) t :=
    HasDerivAt.comp t (Real.hasDerivAt_log hnsq_pos.ne') hnsq
  have hval : ((Complex.normSq (f t))⁻¹ * (2 * ((starRingEnd ℂ (f t) * D).re)))
      = 2 * (((f t)⁻¹ * D).re) := by
    have hre : ((f t)⁻¹ * D).re = (Complex.normSq (f t))⁻¹ * (starRingEnd ℂ (f t) * D).re := by
      have hrw : (f t)⁻¹ * D = ((Complex.normSq (f t) : ℝ)⁻¹ : ℂ) * (starRingEnd ℂ (f t) * D) := by
        rw [Complex.inv_def]; push_cast; ring
      rw [hrw, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    rw [hre]; ring
  rw [hval] at hlog
  have hdiv := hlog.div_const 2
  have heq2 : (fun u => Real.log (Complex.normSq (f u)) / 2) = fun u => Real.log ‖f u‖ := by
    funext u
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
  rw [heq2] at hdiv
  have hval2 : 2 * (((f t)⁻¹ * D).re) / 2 = ((f t)⁻¹ * D).re := by ring
  rwa [hval2] at hdiv

/-- **The real part of the plain-piece contour integral telescopes to the log-norm difference of
its endpoints**, with no slit-plane hypothesis needed: the real part of `Complex.log` never
depends on a branch, unlike its imaginary part (the argument), which is exactly the content the
generalized winding number keeps track of. -/
private theorem re_integral_inv_sub_mul_deriv_eq_log_norm {γ : ℝ → ℂ} {s : ℂ} {l u : ℝ}
    {P : Set ℝ} (hlu : l ≤ u) (hP : P.Countable) (hγ_cont : ContinuousOn γ (Icc l u))
    (hγ_diff : ∀ t ∈ Ioo l u \ P, DifferentiableAt ℝ γ t) (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (h_int : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume l u) :
    (∫ t in l..u, (γ t - s)⁻¹ * deriv γ t).re = Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ := by
  have hγ_cont' : ContinuousOn γ [[l, u]] := by rwa [uIcc_of_le hlu]
  have h_ne' : ∀ t ∈ [[l, u]], γ t - s ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (h_ne t (by rwa [uIcc_of_le hlu] at ht))
  have hcont : ContinuousOn (fun t => Real.log ‖γ t - s‖) [[l, u]] := fun t ht => by
    have h2 : ContinuousWithinAt (fun t => ‖γ t - s‖) [[l, u]] t :=
      ((hγ_cont' t ht).sub continuousWithinAt_const).norm
    exact (Real.continuousAt_log (norm_ne_zero_iff.mpr (h_ne' t ht))).tendsto.comp h2
  have hderiv : ∀ t ∈ Ioo (min l u) (max l u) \ P,
      HasDerivAt (fun t => Real.log ‖γ t - s‖) (((γ t - s)⁻¹ * deriv γ t).re) t := by
    intro t ht
    rw [min_eq_left hlu, max_eq_right hlu] at ht
    have hγt : DifferentiableAt ℝ γ t := hγ_diff t ht
    have hγt' : HasDerivAt (fun t => γ t - s) (deriv γ t) t := hγt.hasDerivAt.sub_const s
    have hne_t : γ t - s ≠ 0 := sub_ne_zero.mpr (h_ne t (Ioo_subset_Icc_self ht.1))
    exact hasDerivAt_log_norm hγt' hne_t
  have hint_re : IntervalIntegrable (fun t => ((γ t - s)⁻¹ * deriv γ t).re) volume l u :=
    ⟨h_int.1.re, h_int.2.re⟩
  have hFTC := integral_eq_of_hasDerivAt_off_countable
    (fun t => Real.log ‖γ t - s‖) (fun t => ((γ t - s)⁻¹ * deriv γ t).re) hP hcont hderiv hint_re
  rw [← RCLike.re_to_complex, ← intervalIntegral_re h_int]
  simpa only [RCLike.re_to_complex] using hFTC

/-! ### Telescoping the real part of the window/piece aggregation -/

/-- **Real-part analogue of `hasCauchyPVAt_along_sorted`.** Mirrors its exact geometric hypotheses
on the sorted crossing list and its induction, but only tracks the real part of the aggregated
value against a real-valued boundary function `Ψ`, needing no `HasCauchyPVAt` witness for the
plain pieces — only the (avoidance-conditioned) real part of their value. -/
private theorem re_windowPieceSum_along_sorted {γ : ℝ → ℂ} {s : ℂ} {p : ℝ → ℝ → ℂ} {w : ℝ → ℂ}
    {Ψ : ℝ → ℝ} {A b r m : ℝ}
    (h_piece : ∀ l u : ℝ, A ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) →
      (p l u).re = Ψ u - Ψ l)
    (h_win_re : ∀ t : ℝ, (w t).re = Ψ (t + r) - Ψ (t - r)) :
    ∀ (sorted : List ℝ), sorted.SortedLT → (sorted ≠ [] → 0 ≤ r) →
    ∀ a : ℝ, A ≤ a → a ≤ b → (∀ t ∈ sorted, a ≤ t - r) → (∀ t ∈ sorted, t + r ≤ b) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r ≤ |t - t'|) →
      (∀ u ∈ Icc a b, (∀ t ∈ sorted, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - s‖) →
      (windowPieceSum r p w b sorted a).re = Ψ b - Ψ a := by
  intro sorted
  induction sorted with
  | nil =>
    intro _ _ a hA hab _ _ _ h_far
    rw [windowPieceSum_nil]
    exact h_piece a b hA hab le_rfl
      fun u hu => h_far u hu fun t ht => absurd ht (List.not_mem_nil)
  | cons t rest IH =>
    intro h_sorted hr a hA hab h_lo h_hi h_pair h_far
    have hr_nonneg : 0 ≤ r := hr (List.cons_ne_nil t rest)
    have h_head_lo : a ≤ t - r := h_lo t List.mem_cons_self
    have h_head_hi : t + r ≤ b := h_hi t List.mem_cons_self
    have h_rest_above : ∀ t' ∈ rest, t + r ≤ t' - r := fun t' ht' => by
      have h_lt : t < t' := (List.pairwise_cons.mp h_sorted.pairwise).1 t' ht'
      have h_sep := h_pair t List.mem_cons_self t' (List.mem_cons_of_mem t ht') (ne_of_gt h_lt)
      rw [abs_sub_comm, abs_of_pos (by linarith)] at h_sep
      linarith
    have h_left : (p a (t - r)).re = Ψ (t - r) - Ψ a := by
      refine h_piece a (t - r) hA h_head_lo (by linarith) fun u hu => ?_
      refine h_far u ⟨hu.1, by linarith [hu.2]⟩ fun t' ht' h_in => ?_
      rcases List.mem_cons.mp ht' with rfl | h_rest
      · linarith [hu.2, h_in.1]
      · linarith [hu.2, h_in.1, h_rest_above t' h_rest]
    have h_rest : (windowPieceSum r p w b rest (t + r)).re = Ψ b - Ψ (t + r) := IH
      ((List.pairwise_cons.mp h_sorted.pairwise).2).sortedLT (fun _ => hr_nonneg) (t + r)
      (by linarith) h_head_hi (fun t' ht' => h_rest_above t' ht')
      (fun t' ht' => h_hi t' (List.mem_cons_of_mem t ht'))
      (fun t' ht' t'' ht'' hne => h_pair t' (List.mem_cons_of_mem t ht')
        t'' (List.mem_cons_of_mem t ht'') hne)
      (fun u hu h_avoid => h_far u ⟨by linarith [hu.1], hu.2⟩ fun t' ht' => by
        rcases List.mem_cons.mp ht' with rfl | h_rest
        · exact fun h_in => absurd hu.1 (not_le.mpr h_in.2)
        · exact h_avoid t' h_rest)
    rw [windowPieceSum_cons, Complex.add_re, Complex.add_re, h_left, h_win_re, h_rest]
    ring

/-! ### The DCT bridge: the principal value of a bare integrand at a finitely-crossed point is
its ordinary integral -/

/-- **The Cauchy-kernel excision of a genuinely integrable, bare real integrand converges to its
ordinary integral**, whenever the curve meets the excision point only finitely often. Unlike
`HasCauchyPVWith.of_integrable_of_crossings_measure_zero`, `h` need not be of the composed shape
`f (γ t) * deriv γ t`: this is what lets it apply to the real winding integrand, an imaginary
part, not itself expressible that way. -/
private theorem tendsto_integral_truncated_of_integrable_of_finite_crossings
    {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ} {h : ℝ → ℝ} (hγ_cont : ContinuousOn γ (uIcc a b))
    (h_int : IntervalIntegrable h volume a b)
    (h_fin : (Set.uIoc a b ∩ γ ⁻¹' {s}).Finite) :
    Tendsto (fun ε : ℝ => ∫ t in a..b, if ‖γ t - s‖ > ε then h t else 0) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in a..b, h t)) := by
  have hK_closed : ∀ ε : ℝ, IsClosed {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε} := fun ε =>
    ((hγ_cont.sub continuousOn_const).norm).preimage_isClosed_of_isClosed
      (by rw [← Icc_min_max]; exact isClosed_Icc) isClosed_Iic
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun t => if ‖γ t - s‖ > ε then h t else 0) (volume.restrict (Set.uIoc a b)) := fun ε => by
    refine (h_int.def'.aestronglyMeasurable.indicator (hK_closed ε).measurableSet.compl).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    by_cases h_far : ‖γ t - s‖ > ε
    · have h_mem : t ∈ {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε}ᶜ :=
        fun hK => absurd hK.2 (not_le.mpr h_far)
      rw [Set.indicator_of_mem h_mem, if_pos h_far]
    · have h_notMem : t ∉ {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε}ᶜ := fun hKc =>
        hKc ⟨Set.uIoc_subset_uIcc ht, not_lt.mp h_far⟩
      rw [Set.indicator_of_notMem h_notMem, if_neg h_far]
  have hle : ∀ ε : ℝ, ∀ t : ℝ, ‖if ‖γ t - s‖ > ε then h t else 0‖ ≤ ‖h t‖ := fun ε t => by
    by_cases hcond : ‖γ t - s‖ > ε <;> simp [hcond]
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      Tendsto (fun ε : ℝ => if ‖γ t - s‖ > ε then h t else 0) (𝓝[>] (0 : ℝ)) (𝓝 (h t)) := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
      (h_fin.measure_zero volume)] with t ht htI
    have hne : γ t ≠ s := fun heq => ht ⟨htI, heq⟩
    have hpos : (0 : ℝ) < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ t - s‖ > ε := by
      filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε using hε.2
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with ε hε using (if_pos hε).symm
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => ‖h t‖)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun t _ => hle ε t)
    h_int.norm hae

/-! ### Assembly -/

/-- **Hungerbühler–Wasem Proposition 2.3, on-curve case.** For a closed piecewise-`C¹` immersion
`γ` on `[a, b]` all of whose value-`s` parameters are interior, with the real winding integrand
`h t := realWindingIntegrand (γ t - s) (deriv γ t)` interval-integrable, the generalized winding
number `n_s(γ)` is a real number, equal to the ordinary (non-principal-value) integral of `h`:

`n_s(γ) = (1 / 2π) ∫_a^b (x ẏ - y ẋ) / (x² + y²) dt`, `x + i y = γ - s`.

Combined with `windingNumber_eq_real_integral_of_closed` (the off-curve case), this is the real
bounded-integrand formula in full: on or off the curve, the generalized winding number is the
ordinary integral of the same real integrand, once that integrand is known to be integrable. -/
theorem windingNumber_eq_real_integral_of_onCurve {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (h_int : IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume a b) :
    windingNumber γ a b s
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) : ℝ) : ℂ) := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · simp
  set T : Finset ℝ := (h_imm.finite_crossings (z₀ := s)).toFinset with hT_def
  have hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := fun {_} => by
    rw [hT_def, h_imm.mem_toFinset_finite_crossings, uIcc_of_le hab.le]
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T := fun t ht h_eq => hT_mem.mpr ⟨ht, h_eq⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := fun t ht => h_interior t (hT_mem.mp ht).1 (hT_mem.mp ht).2
  have hγ_cont : ContinuousOn γ (Icc a b) := h_imm.continuousOn.mono (uIcc_of_le hab.le).ge
  have hγ_cont' : ContinuousOn γ (uIcc a b) := by rwa [uIcc_of_le hab.le]
  have h_int_tr : ∀ ε : ℝ, 0 < ε → IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) volume a b :=
    fun _ hε => intervalIntegrable_inv_sub_truncated h_imm.continuousOn
      h_imm.isPiecewiseC1On.intervalIntegrable_deriv hε
  obtain ⟨p, hp⟩ := h_imm.isPiecewiseC1On.exists_finset_differentiableAt
  have hP : (↑p : Set ℝ).Countable := p.countable_toSet
  have hγ_diff : ∀ t ∈ Ioo a b \ (↑p : Set ℝ), DifferentiableAt ℝ γ t := fun t ht => by
    rw [min_eq_left hab.le, max_eq_right hab.le] at hp
    exact hp t ht
  have h_fin_crossings : (Set.uIoc a b ∩ γ ⁻¹' {s}).Finite :=
    (h_imm.finite_crossings (z₀ := s)).subset
      (inter_subset_inter_left _ (Set.uIoc_subset_uIcc (α := ℝ)))
  -- The plain-piece value: the ordinary contour integral away from `s`.
  set p' : ℝ → ℝ → ℂ := fun l u => ∫ t in l..u, (γ t - s)⁻¹ * deriv γ t with hp'_def
  -- The window value: the explicit log-norm-plus-argument limit at each crossing.
  choose! R hR_pos L_R L_L hL_R hL_L h_spec using
    fun t₀ (ht₀ : t₀ ∈ T) => exists_radius_perWindow_tendsto_value h_imm hab (h_Ioo t₀ ht₀)
      (hT_mem.mp ht₀).2
  obtain ⟨ρ, hρ_pos, h_endpts, h_pair, hρ_le_R⟩ := exists_common_window_radius_le h_Ioo R hR_pos
  set w : ℝ → ℂ := fun t => ((Real.log ‖γ (t + ρ) - s‖ - Real.log ‖γ (t - ρ) - s‖ : ℝ) : ℂ) +
    ((((-L_L t) / (γ (t - ρ) - s)).arg + ((γ (t + ρ) - s) / L_R t).arg : ℝ) : ℂ) * Complex.I
    with hw_def
  have h_unique : ∀ t₀ ∈ T, ∀ t ∈ Icc (t₀ - ρ) (t₀ + ρ), γ t = s → t = t₀ := fun t₀ ht₀ t ht h_eq =>
    eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (h_endpts t₀ ht₀) (h_pair t₀ ht₀) h_complete ht h_eq
  have h_win : ∀ t ∈ T, HasCauchyPVAt γ (t - ρ) (t + ρ) (fun z => (z - s)⁻¹) s (w t) := by
    intro t ht
    refine HasCauchyPVAt.intro
      (eventually_intervalIntegrable_truncated_window (g := fun z => (z - s)⁻¹) hab.le
        (by linarith [(h_endpts t ht).1]) (by linarith [(h_endpts t ht).2]) hρ_pos.le h_int_tr) ?_
    exact h_spec t ht ρ hρ_pos (hρ_le_R t ht) (by linarith [(h_endpts t ht).1])
      (by linarith [(h_endpts t ht).2]) (h_unique t ht)
  have h_far := exists_complement_windows_dist_lower_bound hγ_cont h_complete (fun _ => ρ)
    fun t _ => hρ_pos
  have hHCPV :
      HasCauchyPVAt γ a b (fun z => (z - s)⁻¹) s (windowPieceSum ρ p' w b (T.sort (· ≤ ·)) a) :=
    hasCauchyPVAt_along_sorted (g := fun z => (z - s)⁻¹)
      (fun l u hA hlu hu h_far' => hasCauchyPVAt_plain_piece (g := fun z => (z - s)⁻¹) hab.le
        h_far.choose_spec.1 h_int_tr hA hlu hu h_far')
      (T.sort (· ≤ ·)) (Finset.sortedLT_sort T)
      (fun _ => hρ_pos.le) a le_rfl hab.le
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).1])
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).2])
      (fun t ht t' ht' hne => (h_pair t ((Finset.mem_sort _).mp ht) t'
        ((Finset.mem_sort _).mp ht') hne).le)
      (fun t ht => h_win t ((Finset.mem_sort _).mp ht))
      (fun u hu h_avoid => h_far.choose_spec.2 u hu
        fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))
  set L : ℂ := windowPieceSum ρ p' w b (T.sort (· ≤ ·)) a with hL_def
  have hwind : windingNumber γ a b s = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L :=
    windingNumber_eq_of_hasCauchyPVAt hHCPV
  -- Reality: the real part telescopes to a boundary difference that vanishes by closedness.
  have h_piece_re : ∀ l u : ℝ, a ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, h_far.choose ≤ ‖γ t - s‖) →
      (p' l u).re = Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ := by
    intro l u hA hlu hu h_far'
    have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq => by
      have := h_far' t ht
      rw [h_eq, sub_self, norm_zero] at this
      linarith [h_far.choose_spec.1]
    refine re_integral_inv_sub_mul_deriv_eq_log_norm hlu hP
      (hγ_cont.mono (Icc_subset_Icc hA hu))
      (fun t ht => hγ_diff t ⟨Ioo_subset_Ioo hA hu ht.1, ht.2⟩) h_ne ?_
    refine intervalIntegrable_inv_sub_mul_deriv ?_ ?_
      (h_imm.isPiecewiseC1On.intervalIntegrable_deriv.mono_set (by
        rw [uIcc_of_le hlu, uIcc_of_le hab.le]
        exact Icc_subset_Icc hA hu))
    · rw [uIcc_of_le hlu]; exact hγ_cont.mono (Icc_subset_Icc hA hu)
    · intro t ht; rw [uIcc_of_le hlu] at ht; exact h_ne t ht
  have h_win_re : ∀ t : ℝ, (w t).re = Real.log ‖γ (t + ρ) - s‖ - Real.log ‖γ (t - ρ) - s‖ :=
    fun t => by simp [hw_def]
  have hRe : L.re = 0 := by
    have := re_windowPieceSum_along_sorted h_piece_re h_win_re
      (T.sort (· ≤ ·)) (Finset.sortedLT_sort T) (fun _ => hρ_pos.le) a le_rfl hab.le
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).1])
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).2])
      (fun t ht t' ht' hne => (h_pair t ((Finset.mem_sort _).mp ht) t'
        ((Finset.mem_sort _).mp ht') hne).le)
      (fun u hu h_avoid => h_far.choose_spec.2 u hu
        fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))
    rw [this, hclosed, sub_self]
  -- The integral identity: the imaginary part is the ordinary integral of the real integrand.
  have hIm : L.im = ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) := by
    have h1 : Tendsto (fun ε : ℝ => (∫ t in a..b,
        if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0).im) (𝓝[>] (0 : ℝ)) (𝓝 L.im) :=
      (Complex.continuous_im.tendsto L).comp hHCPV.tendsto
    have h2 : Tendsto (fun ε : ℝ => ∫ t in a..b,
        if ‖γ t - s‖ > ε then realWindingIntegrand (γ t - s) (deriv γ t) else 0) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t))) :=
      tendsto_integral_truncated_of_integrable_of_finite_crossings hγ_cont' h_int h_fin_crossings
    have heq : (fun ε : ℝ => (∫ t in a..b,
        if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0).im)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ∫ t in a..b,
        if ‖γ t - s‖ > ε then realWindingIntegrand (γ t - s) (deriv γ t) else 0) := by
      filter_upwards [hHCPV.eventually_intervalIntegrable] with ε hε
      rw [← RCLike.im_to_complex, ← intervalIntegral_im hε]
      refine intervalIntegral.integral_congr fun t _ => ?_
      by_cases hcond : ‖γ t - s‖ > ε
      · simp only [if_pos hcond, RCLike.im_to_complex, realWindingIntegrand_eq_div,
          Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.sub_re, Complex.sub_im,
          Complex.normSq_sub]
        ring
      · simp [hcond]
    exact tendsto_nhds_unique (h1.congr' heq) h2
  rw [hwind, ← Complex.re_add_im L, hRe, hIm]
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  push_cast
  field_simp
  ring

end TauCeti.Contour

end
