/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic.TFAE

/-!
-/

@[expose] public section

open scoped Topology NNReal ENNReal BoundedContinuousFunction
open Filter MeasureTheory Set

variable {α : Type*} {Ω : α → Type*} [∀ a, MeasurableSpace (Ω a)]

/-
Some definitions can actually be defined for `Measure` instead of `ProbabilityMeasure`, but to avoid
coercion issues when we prove equivalences between them, we use `ProbabilityMeasure` in all these
definitions. Also we don't want to use the typeclass assumption `IsProbabilityMeasure` because we
need to use the topology on `ProbabilityMeasure`.
-/

section Definitions

def Contiguous1 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ ⦃s : ∀ a, Set (Ω a)⦄ ⦃h : Filter α⦄, (∀ a, MeasurableSet (s a)) → h ≤ l →
    Tendsto (fun a => P a (s a)) h (𝓝 0) → Tendsto (fun a => Q a (s a)) h (𝓝 0)

/-- We require `h` to be nontrivial in the following definition because otherwise
`Tendsto ... h ...` is trivial by `Filter.tendsto_bot`. -/
def Contiguous2 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (L : ProbabilityMeasure ℝ≥0∞) ⦃h : Filter α⦄, h ≤ l → h.NeBot →
    Tendsto (fun a => (Q a).map
      ((Measure.measurable_rnDeriv (P a) (Q a)).aemeasurable)) h (𝓝 L) →
      L {0} = 0

def Contiguous3 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (V : ProbabilityMeasure ℝ≥0∞) ⦃h : Filter α⦄, h ≤ l → h.NeBot →
    Tendsto (fun a => (P a).map
      ((Measure.measurable_rnDeriv (Q a) (P a)).aemeasurable)) h (𝓝 V) →
      ∫⁻ ω, ω ∂V = 1

/-- The following notion of convergence in measure is introduced because the current mathlib
version only support for a single measure. -/
def TendstoInMeasure (μ : ∀ α, ProbabilityMeasure (Ω α))
    (f : ∀ α, Ω α → ℝ) (l : Filter α) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i => μ i { x | ε ≤ |f i x| }) l (𝓝 0)

def Contiguous4 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (T : ∀ α, Ω α → ℝ) ⦃h : Filter α⦄, h ≤ l → TendstoInMeasure P T h →
    TendstoInMeasure Q T h

/-- This corresponds to the definition of sequences for contiguity. -/
def Contiguous5 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ ⦃s : ∀ a, Set (Ω a)⦄, (∀ a, MeasurableSet (s a)) →
    Tendsto (fun a => P a (s a)) l (𝓝 0) → Tendsto (fun a => Q a (s a)) l (𝓝 0)

end Definitions

section -- Contiguous1 and contiguous4 are equivalent.

lemma NNReal.tendsto_of_tendsto_of_le {l : Filter α} {f g : α → ℝ≥0}
    (hfg : ∀ᶠ a in l, f a ≤ g a) (hg : Tendsto g l (𝓝 0)) :
    Tendsto f l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) hg (by simp) hfg

lemma setOf_le_abs_indicator_one_eq {β : Type*} (s : Set β) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    {x | ε ≤ |s.indicator (fun _ => (1 : ℝ)) x|} = s := by
  ext x
  by_cases hx : x ∈ s
  · simp [hx, hε1]
  · simp [hx, hε0.not_ge]

/-- Given `0 < δ`. We only need to check convergence for `0 < ε ≤ δ` to conclude convergence in
measure. -/
lemma tendstoInMeasure_iff_forall_le {μ : ∀ a, ProbabilityMeasure (Ω a)}
    {f : ∀ a, Ω a → ℝ} {l : Filter α} {δ : ℝ} (hδ : 0 < δ) :
    TendstoInMeasure μ f l ↔
      ∀ ε, 0 < ε → ε ≤ δ →
        Tendsto (fun i => μ i {x | ε ≤ |f i x|}) l (𝓝 0) := by
  refine ⟨fun h ε hε _ => h ε hε, fun h ε hε => ?_⟩
  by_cases! hεδ : ε ≤ δ
  · exact h ε hε hεδ
  · refine NNReal.tendsto_of_tendsto_of_le ?_ (h δ hδ le_rfl)
    filter_upwards with i using (μ i).apply_mono fun x hx => hεδ.le.trans hx

/-- The probability of a sequence of sets converges to zero iff their corresponding indicator
functions converge in measure to zero. -/
lemma tendstoInMeasure_iff (s : ∀ a, Set (Ω a))
    (P : ∀ a, ProbabilityMeasure (Ω a)) (l : Filter α) :
    Tendsto (fun a => (P a) (s a)) l (𝓝 0) ↔
      TendstoInMeasure P (fun a => (s a).indicator fun _ => 1) l where
  mp ht := by
    refine (tendstoInMeasure_iff_forall_le zero_lt_one).2 fun ε hε hε1 => ?_
    exact ht.congr fun a => by rw [setOf_le_abs_indicator_one_eq (s a) hε hε1]
  mpr ht :=
    (ht 1 zero_lt_one).congr fun a => by rw [setOf_le_abs_indicator_one_eq (s a) zero_lt_one le_rfl]

theorem contiguous1_iff_contiguous4 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    Contiguous1 l P Q ↔ Contiguous4 l P Q where
  mp hc := by
    refine fun s h hle hp ε hε => NNReal.tendsto_of_tendsto_of_le
      (g := fun a => (Q a) (toMeasurable (P a) {x | ε ≤ |s a x|})) ?_ ?_
    · filter_upwards with a using (Q a).apply_mono <| subset_toMeasurable _ _
    · refine hc (fun a => measurableSet_toMeasurable _ _) hle ((hp ε hε).congr ?_)
      simp [← ENNReal.coe_inj]
  mpr hc := by
    refine fun s h hms hle hp => (tendstoInMeasure_iff s Q h).2 ?_
    exact hc (fun a => (s a).indicator (fun _ => 1)) hle <| (tendstoInMeasure_iff s P h).1 hp

private noncomputable def truncBCF (n : ℕ) : ℝ≥0∞ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨ENNReal.truncateToReal n, ENNReal.continuous_truncateToReal (by simp)⟩

private lemma rnDeriv_measureReal_le {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set Y) (hs : MeasurableSet s) (n : ℕ) :
    ν.real s ≤ n * μ.real s +
      (1 - ∫ x, ENNReal.truncateToReal n (ν.rnDeriv μ x) ∂μ) := by
  let f : Y → ℝ := fun x ↦ ENNReal.truncateToReal n (ν.rnDeriv μ x)
  have hf : Integrable f μ := Integrable.of_bound
    (((ENNReal.continuous_truncateToReal (by simp)).measurable.comp
      (Measure.measurable_rnDeriv ν μ)).aestronglyMeasurable) n
    (Filter.Eventually.of_forall fun x ↦ by
      simpa [f, abs_of_nonneg ENNReal.truncateToReal_nonneg] using
        ENNReal.truncateToReal_le (by simp : (n : ℝ≥0∞) ≠ ∞)
          (x := ν.rnDeriv μ x))
  have hs_le : ∫ x in s, f x ∂μ ≤ n * μ.real s := by
    calc
      ∫ x in s, f x ∂μ ≤ ‖∫ x in s, f x ∂μ‖ := le_abs_self _
      _ ≤ n * μ.real s := norm_setIntegral_le_of_norm_le_const
        (measure_lt_top μ s) fun x _ ↦ by
          simpa [f, abs_of_nonneg ENNReal.truncateToReal_nonneg] using
            ENNReal.truncateToReal_le (by simp : (n : ℝ≥0∞) ≠ ∞)
  have hc_le : ∫ x in sᶜ, f x ∂μ ≤ ν.real sᶜ := by
    refine (setIntegral_mono_on_ae hf.integrableOn
      (Measure.integrableOn_toReal_rnDeriv (measure_ne_top ν sᶜ)) hs.compl ?_).trans
      (Measure.setIntegral_toReal_rnDeriv_le (measure_ne_top ν sᶜ))
    filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
    intro _
    change (min (n : ℝ≥0∞) (ν.rnDeriv μ x)).toReal ≤ (ν.rnDeriv μ x).toReal
    exact ENNReal.toReal_mono hx.ne (min_le_right _ _)
  have hcomp : ν.real sᶜ = 1 - ν.real s := by
    rw [measureReal_compl hs, probReal_univ]
  linarith [integral_add_compl hs hf]

private lemma tendsto_measure_zero_of_rnDeriv_law
    {h : Filter α} (P Q : ∀ i, ProbabilityMeasure (Ω i))
    (s : ∀ i, Set (Ω i)) (hs : ∀ i, MeasurableSet (s i))
    (hP : Tendsto (fun i ↦ P i (s i)) h (𝓝 0))
    (V : ProbabilityMeasure ℝ≥0∞)
    (hV : Tendsto (fun i ↦ (P i).map
      ((Measure.measurable_rnDeriv (Q i) (P i)).aemeasurable)) h (𝓝 V))
    (hmean : ∫⁻ x, x ∂V = 1) :
    Tendsto (fun i ↦ Q i (s i)) h (𝓝 0) := by
  rw [← NNReal.tendsto_coe, Metric.tendsto_nhds]
  intro ε hε
  have htrunc : Tendsto
      (fun n : ℕ ↦ ∫ x, truncBCF n x ∂(V : Measure ℝ≥0∞)) atTop (𝓝 1) := by
    have hsup : (⨆ n : ℕ, ∫⁻ x, min x n ∂V) = 1 := by
      calc
        (⨆ n : ℕ, ∫⁻ x, min x n ∂V) = ∫⁻ x, ⨆ n : ℕ, min x n ∂V := by
          rw [lintegral_iSup]
          · exact fun n ↦ measurable_id.min measurable_const
          · exact fun _ _ hab ↦ fun x ↦ min_le_min_left _ <| mod_cast hab
        _ = ∫⁻ x, x ∂V := lintegral_congr fun x ↦ by
          rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
        _ = 1 := hmean
    have ht := tendsto_atTop_iSup
      (f := fun n : ℕ ↦ ∫⁻ x, min x n ∂(V : Measure ℝ≥0∞))
      (fun _ _ hab ↦ lintegral_mono fun x ↦ min_le_min_left x <| mod_cast hab)
    rw [hsup] at ht
    have htr := ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞) |>.comp ht
    convert htr using 1
    · funext n
      simp only [Function.comp_apply, truncBCF,
        BoundedContinuousFunction.mkOfCompact_apply]
      change (∫ x, (min (n : ℝ≥0∞) x).toReal ∂(V : Measure ℝ≥0∞)) = _
      rw [MeasureTheory.integral_toReal]
      · congr with x
        rw [min_comm]
      · exact (measurable_const.min measurable_id).aemeasurable
      · exact ae_of_all _ fun _ ↦ by simp
    · simp
  have he4 : 0 < ε / 4 := div_pos hε (by positivity)
  have hev : ∀ᶠ n : ℕ in atTop,
      1 - ε / 4 < ∫ x, truncBCF n x ∂(V : Measure ℝ≥0∞) :=
    (tendsto_order.1 htrunc).1 _ (sub_lt_self 1 he4)
  obtain ⟨n, hn⟩ := hev.exists
  have hIv := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hV) (truncBCF n)
  have hIv' : Tendsto (fun i ↦ ∫ x, ENNReal.truncateToReal n
      ((Q i : Measure (Ω i)).rnDeriv (P i) x) ∂(P i)) h
      (𝓝 (∫ x, truncBCF n x ∂(V : Measure ℝ≥0∞))) := by
    refine hIv.congr' ?_
    filter_upwards with i
    change (∫ x, truncBCF n x ∂Measure.map _ (P i : Measure (Ω i))) =
      ∫ x, ENNReal.truncateToReal n
        ((Q i : Measure (Ω i)).rnDeriv (P i) x) ∂(P i)
    exact integral_map (μ := (P i : Measure (Ω i)))
      (φ := (Q i : Measure (Ω i)).rnDeriv (P i))
      (Measure.measurable_rnDeriv (Q i : Measure (Ω i))
        (P i : Measure (Ω i))).aemeasurable
      (truncBCF n).continuous.aestronglyMeasurable
  have hPreal : Tendsto (fun i ↦ (P i (s i) : ℝ)) h (𝓝 0) := NNReal.tendsto_coe.2 hP
  have hnP : Tendsto (fun i ↦ (n : ℝ) * (P i (s i) : ℝ)) h (𝓝 0) :=
    by simpa using (tendsto_const_nhds.mul hPreal :
      Tendsto (fun i ↦ (n : ℝ) * (P i (s i) : ℝ)) h (𝓝 ((n : ℝ) * 0)))
  have hnPsmall : ∀ᶠ i in h, (n : ℝ) * (P i (s i) : ℝ) < ε / 4 :=
    (tendsto_order.1 hnP).2 _ he4
  have hIsmall : ∀ᶠ i in h,
      (∫ x, truncBCF n x ∂(V : Measure ℝ≥0∞)) - ε / 4 <
        ∫ x, ENNReal.truncateToReal n
          ((Q i : Measure (Ω i)).rnDeriv (P i) x) ∂(P i) :=
    (tendsto_order.1 hIv').1 _ (sub_lt_self _ he4)
  filter_upwards [hnPsmall, hIsmall] with i hnPi hIi
  have hbound := rnDeriv_measureReal_le
    (P i : Measure (Ω i)) (Q i : Measure (Ω i)) (s i) (hs i) n
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn] at hbound
  have hlt : (Q i (s i) : ℝ) < ε := by linarith
  simpa [Real.dist_eq] using hlt

section -- Contiguous1 implies contiguous2

private lemma measure_rnDeriv_le_inter_nullSet {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (δ : ℝ≥0∞) :
    μ ({x | μ.rnDeriv ν x ≤ δ} ∩
      (Measure.mutuallySingular_singularPart μ ν).nullSet) ≤ δ := by
  let hsing := Measure.mutuallySingular_singularPart μ ν
  let e := {x | μ.rnDeriv ν x ≤ δ} ∩ hsing.nullSet
  have he : MeasurableSet e :=
    ((Measure.measurable_rnDeriv μ ν) measurableSet_Iic).inter hsing.measurableSet_nullSet
  have hsing_zero : μ.singularPart ν e = 0 :=
    measure_mono_null inter_subset_right hsing.measure_nullSet
  change μ e ≤ δ
  calc
    μ e = (μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)) e := by
      rw [Measure.singularPart_add_rnDeriv]
    _ = ∫⁻ x in e, μ.rnDeriv ν x ∂ν := by
      rw [Measure.add_apply, hsing_zero, zero_add, withDensity_apply _ he]
    _ ≤ ∫⁻ _x in e, δ ∂ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem he] with x hx
      exact hx.1
    _ = δ * ν e := setLIntegral_const e δ
    _ ≤ δ * 1 := by
      gcongr
      exact (measure_mono (subset_univ e)).trans_eq (measure_univ : ν univ = 1)
    _ = δ := mul_one δ

private noncomputable def invSucc (n : ℕ) : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹

private lemma iInter_Iio_invSucc : (⋂ n : ℕ, Iio (invSucc n)) = ({0} : Set ℝ≥0∞) := by
  ext x
  simp only [mem_iInter, mem_Iio, mem_singleton_iff]
  constructor
  · intro hx
    by_contra hx0
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx0
    have hn' : invSucc n ≤ (n : ℝ≥0∞)⁻¹ := by
      exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)
    exact (not_lt_of_ge (hx n).le) (hn'.trans_lt hn)
  · rintro rfl n
    simp [invSucc]

private lemma le_measure_singleton_zero_of_lt_Iio_invSucc
    {μ : Measure ℝ≥0∞} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (h : ∀ n, c < μ (Iio (invSucc n))) : c ≤ μ {0} := by
  rw [← iInter_Iio_invSucc, Antitone.measure_iInter]
  · exact le_iInf fun n ↦ (h n).le
  · intro i j hij
    exact Iio_subset_Iio <| ENNReal.inv_le_inv.mpr <| by
      exact_mod_cast Nat.add_le_add_right hij 1
  · exact fun _ ↦ measurableSet_Iio.nullMeasurableSet
  · exact ⟨0, measure_ne_top μ _⟩

private lemma measure_inter_singularPart_nullSet {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) (e : Set Y) :
    ν (e ∩ (Measure.mutuallySingular_singularPart μ ν).nullSet) = ν e := by
  rw [← sdiff_compl]
  exact measure_sdiff_null
    (Measure.mutuallySingular_singularPart μ ν).measure_compl_nullSet

theorem Contiguous1.contiguous2 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a))
    (hPQ : Contiguous1 l P Q) : Contiguous2 l P Q := by
  intro L h hle hh hR
  by_contra hL
  have hLpos : 0 < (L : Measure ℝ≥0∞) {0} := by
    rw [show (L : Measure ℝ≥0∞) {0} = L {0} by
      simp [ProbabilityMeasure.coeFn_def]]
    exact pos_iff_ne_zero.mpr (by exact_mod_cast hL)
  obtain ⟨c, hc0, hcL⟩ := exists_between hLpos
  let R : ∀ i, ProbabilityMeasure ℝ≥0∞ := fun i ↦ (Q i).map
    ((Measure.measurable_rnDeriv (P i) (Q i)).aemeasurable)
  have hA : ∀ n : ℕ, ∀ᶠ i in h,
      c < (R i : Measure ℝ≥0∞) (Iio (invSucc n)) := by
    intro n
    have hcset : c < (L : Measure ℝ≥0∞) (Iio (invSucc n)) := hcL.trans_le <|
      measure_mono fun x hx ↦ by
        simp only [mem_singleton_iff] at hx
        subst x
        simp [invSucc]
    exact eventually_lt_of_lt_liminf <| hcset.trans_le <|
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hR isOpen_Iio
  let B : Set α := {i | ∀ n, c < (R i : Measure ℝ≥0∞) (Iio (invSucc n))}
  by_cases hB : ∃ᶠ i in h, i ∈ B
  · let m := h ⊓ principal B
    have hm : m.NeBot := frequently_iff_neBot.1 hB
    let s : ∀ i, Set (Ω i) := fun i ↦
      {x | (P i : Measure (Ω i)).rnDeriv (Q i) x = 0} ∩
        (Measure.mutuallySingular_singularPart (P i) (Q i)).nullSet
    have hs : ∀ i, MeasurableSet (s i) := fun i ↦
      (Measure.measurable_rnDeriv
        (P i : Measure (Ω i)) (Q i : Measure (Ω i))
          (measurableSet_singleton (0 : ℝ≥0∞))).inter
          (Measure.mutuallySingular_singularPart
            (P i : Measure (Ω i)) (Q i : Measure (Ω i))).measurableSet_nullSet
    have hPs : Tendsto (fun i ↦ P i (s i)) m (𝓝 0) := by
      have hz : ∀ i, P i (s i) = 0 := by
        intro i
        rw [← ENNReal.coe_inj]
        rw [show (P i (s i) : ℝ≥0∞) = (P i : Measure (Ω i)) (s i) by
          simp [ProbabilityMeasure.coeFn_def]]
        simp only [ENNReal.coe_zero]
        apply le_zero_iff.mp
        simpa [s] using measure_rnDeriv_le_inter_nullSet
          (P i : Measure (Ω i)) (Q i : Measure (Ω i)) 0
      simpa only [hz] using
        (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ≥0)) m (𝓝 0))
    have hQs := hPQ hs (inf_le_left.trans hle) hPs
    have hcQ : ∀ᶠ i in m, c ≤ (Q i : Measure (Ω i)) (s i) := by
      have hBm : ∀ᶠ i in m, i ∈ B := mem_inf_of_right (by simp)
      filter_upwards [hBm] with i hi
      have hcR : c ≤ (R i : Measure ℝ≥0∞) {0} :=
        le_measure_singleton_zero_of_lt_Iio_invSucc hi
      calc
        c ≤ (R i : Measure ℝ≥0∞) {0} := hcR
        _ = (Q i : Measure (Ω i))
            {x | (P i : Measure (Ω i)).rnDeriv (Q i) x = 0} := by
          exact ProbabilityMeasure.map_apply' (Q i)
            (Measure.measurable_rnDeriv (P i) (Q i)).aemeasurable
              (measurableSet_singleton (0 : ℝ≥0∞))
        _ = (Q i : Measure (Ω i)) (s i) := by
          symm
          exact measure_inter_singularPart_nullSet
            (P i : Measure (Ω i)) (Q i : Measure (Ω i)) _
    have hQsmall : ∀ᶠ i in m, (Q i : Measure (Ω i)) (s i) < c := by
      have hQe : Tendsto (fun i ↦ (Q i (s i) : ℝ≥0∞)) m (𝓝 0) :=
        Filter.Tendsto.comp (ENNReal.continuous_coe.tendsto 0) hQs
      have he := (tendsto_order.1 hQe).2 c hc0
      simpa [ProbabilityMeasure.coeFn_def] using he
    exact (hcQ.and hQsmall).exists.elim fun _ hi ↦ (not_lt_of_ge hi.1) hi.2
  · classical
    let A : α → ℕ → Prop := fun i n ↦
      c < (R i : Measure ℝ≥0∞) (Iio (invSucc n))
    let k : α → ℕ := fun i ↦ if hi : ∃ n, ¬A i n then Nat.find hi else 0
    have hnotB : ∀ᶠ i in h, ∃ n, ¬A i n := by
      have hnot := not_frequently.mp hB
      filter_upwards [hnot] with i hi
      simpa only [B, A, Set.mem_ofPred_eq, not_forall] using hi
    have hk : Tendsto k h atTop := by
      refine tendsto_atTop.2 fun N ↦ ?_
      filter_upwards [hA N, hnotB] with i hiN hiex
      have hiN' : A i N := hiN
      have hkbad : ¬A i (k i) := by
        simp only [k, hiex, dite_true]
        exact Nat.find_spec hiex
      have hNk : N < k i := by
        by_contra hnot
        have hkiN : k i ≤ N := Nat.le_of_not_gt hnot
        apply hkbad
        exact hiN'.trans_le <| measure_mono <| Iio_subset_Iio <|
          ENNReal.inv_le_inv.mpr <| by
            exact_mod_cast Nat.add_le_add_right hkiN 1
      exact hNk.le
    let d : α → ℝ≥0∞ := fun i ↦ invSucc (k i - 1)
    have hd : Tendsto d h (𝓝 0) := by
      rw [ENNReal.nhds_zero_basis.tendsto_right_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      have hNk : ∀ᶠ i in h, N + 1 ≤ k i :=
        hk.eventually (eventually_ge_atTop (N + 1))
      filter_upwards [hNk] with i hi
      have hpred : N ≤ k i - 1 := by omega
      have hdN : d i ≤ invSucc N := ENNReal.inv_le_inv.mpr (by
        exact_mod_cast Nat.add_le_add_right hpred 1)
      have hsucc : invSucc N ≤ (N : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr (by
        exact_mod_cast Nat.le_succ N)
      exact hdN.trans_lt (hsucc.trans_lt hN)
    let s : ∀ i, Set (Ω i) := fun i ↦
      {x | (P i : Measure (Ω i)).rnDeriv (Q i) x < d i} ∩
        (Measure.mutuallySingular_singularPart (P i) (Q i)).nullSet
    have hs : ∀ i, MeasurableSet (s i) := fun i ↦
      (Measure.measurable_rnDeriv (P i : Measure (Ω i))
        (Q i : Measure (Ω i)) measurableSet_Iio).inter
          (Measure.mutuallySingular_singularPart
            (P i : Measure (Ω i)) (Q i : Measure (Ω i))).measurableSet_nullSet
    have hPle : ∀ i, (P i : Measure (Ω i)) (s i) ≤ d i := by
      intro i
      refine (measure_mono ?_).trans <|
        measure_rnDeriv_le_inter_nullSet
          (P i : Measure (Ω i)) (Q i : Measure (Ω i)) (d i)
      intro x hx
      change (P i : Measure (Ω i)).rnDeriv (Q i) x < d i ∧
        x ∈ (Measure.mutuallySingular_singularPart (P i) (Q i)).nullSet at hx
      change (P i : Measure (Ω i)).rnDeriv (Q i) x ≤ d i ∧
        x ∈ (Measure.mutuallySingular_singularPart (P i) (Q i)).nullSet
      exact ⟨hx.1.le, hx.2⟩
    have hPe : Tendsto (fun i ↦ (P i : Measure (Ω i)) (s i)) h (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hd
        (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall hPle)
    have hPs : Tendsto (fun i ↦ P i (s i)) h (𝓝 0) := by
      have ht := (ENNReal.tendsto_toNNReal_iff (a := 0) ENNReal.zero_ne_top
        (fun i ↦ measure_ne_top (P i) (s i))).2 hPe
      simpa [Function.comp_def, ProbabilityMeasure.coeFn_def] using ht
    have hQs := hPQ hs hle hPs
    have hcQ : ∀ᶠ i in h, c < (Q i : Measure (Ω i)) (s i) := by
      filter_upwards [hnotB, hk.eventually (eventually_ge_atTop 1)] with i hiex hki
      have hkprev : A i (k i - 1) := by
        by_contra hbad
        have hfind : k i ≤ k i - 1 := by
          simpa only [k, hiex, dite_true] using Nat.find_min' hiex hbad
        omega
      calc
        c < (R i : Measure ℝ≥0∞) (Iio (d i)) := hkprev
        _ = (Q i : Measure (Ω i))
            {x | (P i : Measure (Ω i)).rnDeriv (Q i) x < d i} := by
          exact ProbabilityMeasure.map_apply' (Q i)
            (Measure.measurable_rnDeriv (P i) (Q i)).aemeasurable measurableSet_Iio
        _ = (Q i : Measure (Ω i)) (s i) := by
          symm
          exact measure_inter_singularPart_nullSet
            (P i : Measure (Ω i)) (Q i : Measure (Ω i)) _
    have hQe : Tendsto (fun i ↦ (Q i (s i) : ℝ≥0∞)) h (𝓝 0) :=
      Filter.Tendsto.comp (ENNReal.continuous_coe.tendsto 0) hQs
    have hQsmall : ∀ᶠ i in h, (Q i : Measure (Ω i)) (s i) < c := by
      have he := (tendsto_order.1 hQe).2 c hc0
      simpa [ProbabilityMeasure.coeFn_def] using he
    exact (hcQ.and hQsmall).exists.elim fun _ hi ↦ (not_lt_of_ge hi.2.le) hi.1

end

section -- Contiguous2 and contiguous3 are equivalent

private lemma rnDeriv_large_measure_le {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) (s : Set Y) (hs : MeasurableSet s)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδtop : δ ≠ ∞) :
    ν (s ∩ {x | δ < μ.rnDeriv ν x}) ≤ δ⁻¹ * μ s := by
  have hmul : δ * ν (s ∩ {x | δ < μ.rnDeriv ν x}) ≤ μ s := by
    calc
      δ * ν (s ∩ {x | δ < μ.rnDeriv ν x}) =
          ∫⁻ _x in s ∩ {x | δ < μ.rnDeriv ν x}, δ ∂ν :=
        (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in s ∩ {x | δ < μ.rnDeriv ν x}, μ.rnDeriv ν x ∂ν := by
        refine lintegral_mono_ae ?_
        have he : MeasurableSet (s ∩ {x | δ < μ.rnDeriv ν x}) :=
          hs.inter ((Measure.measurable_rnDeriv μ ν) measurableSet_Ioi)
        filter_upwards [ae_restrict_mem he] with x hx
        exact hx.2.le
      _ ≤ ∫⁻ x in s, μ.rnDeriv ν x ∂ν := by
        exact lintegral_mono' (Measure.restrict_mono inter_subset_left le_rfl) le_rfl
      _ ≤ μ s := Measure.setLIntegral_rnDeriv_le s
  calc
    ν (s ∩ {x | δ < μ.rnDeriv ν x}) =
        δ⁻¹ * (δ * ν (s ∩ {x | δ < μ.rnDeriv ν x})) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hδ.ne' hδtop, one_mul]
    _ ≤ δ⁻¹ * μ s := mul_le_mul' le_rfl hmul

private lemma iInter_Iic_invSucc : (⋂ n : ℕ, Iic (invSucc n)) = ({0} : Set ℝ≥0∞) := by
  ext x
  simp only [mem_iInter, mem_Iic, mem_singleton_iff]
  constructor
  · intro hx
    apply le_zero_iff.mp
    by_contra hne
    have hx0 : x ≠ 0 := by
      intro hx
      exact hne (by simp [hx])
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx0
    have hn' : invSucc n ≤ (n : ℝ≥0∞)⁻¹ := by
      exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)
    exact (not_lt_of_ge (hx n)) (hn'.trans_lt hn)
  · rintro rfl
    simp

private theorem Contiguous2.contiguous1 {l : Filter α}
    (P Q : ∀ i, ProbabilityMeasure (Ω i))
    (hPQ : Contiguous2 l P Q) : Contiguous1 l P Q := by
  intro s h hs hle hP
  by_contra hQ
  rw [NNReal.nhds_zero_basis.tendsto_right_iff] at hQ
  simp only [mem_Iio] at hQ
  push Not at hQ
  obtain ⟨ε, hε, hQε⟩ := hQ
  let B : Set α := {i | ε ≤ Q i (s i)}
  let m := h ⊓ principal B
  have hm : m.NeBot := frequently_iff_neBot.1 hQε
  let R : ∀ i, ProbabilityMeasure ℝ≥0∞ := fun i ↦ (Q i).map
    ((Measure.measurable_rnDeriv (P i) (Q i)).aemeasurable)
  obtain ⟨L, _, hL⟩ := isCompact_univ.exists_mapClusterPt (f := m) (u := R) (by simp)
  obtain ⟨u, hum, huL⟩ := mapClusterPt_iff_ultrafilter.1 hL
  have huP : Tendsto (fun i ↦ P i (s i)) u (𝓝 0) :=
    hP.mono_left (hum.trans inf_le_left)
  have hLzero : L {0} = 0 :=
    hPQ L (hum.trans <| inf_le_left.trans hle) inferInstance huL
  have hlow : ∀ n : ℕ,
      ((ε : ℝ≥0∞) / 2) ≤ (L : Measure ℝ≥0∞) (Iic (invSucc n)) := by
    intro n
    let δ : ℝ≥0∞ := invSucc n
    have hδ : 0 < δ := by simp [δ, invSucc]
    have hlarge : Tendsto
        (fun i ↦ δ⁻¹ * ((P i (s i) : ℝ≥0) : ℝ≥0∞)) u (𝓝 0) := by
      have hPu : Tendsto (fun i ↦ ((P i (s i) : ℝ≥0) : ℝ≥0∞)) u (𝓝 0) :=
        (ENNReal.continuous_coe.tendsto 0).comp huP
      simpa using ENNReal.Tendsto.const_mul hPu (Or.inr (by simp [δ, invSucc]))
    have hsmall : ∀ᶠ i in u,
        δ⁻¹ * ((P i (s i) : ℝ≥0) : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
      (tendsto_order.1 hlarge).2 _
        (ENNReal.div_pos (by exact_mod_cast hε.ne') (by simp))
    have hBu : ∀ᶠ i in u, i ∈ B := hum (mem_inf_of_right (by simp))
    have hRlow : ∀ᶠ i in u,
        ((ε : ℝ≥0∞) / 2) ≤ (R i : Measure ℝ≥0∞) (Iic δ) := by
      filter_upwards [hsmall, hBu] with i hi hiB
      have hbad := rnDeriv_large_measure_le
        (P i : Measure (Ω i)) (Q i : Measure (Ω i)) (s i) (hs i) δ hδ
          (by simp [δ, invSucc])
      have hsplit : (Q i : Measure (Ω i)) (s i) ≤
          (Q i : Measure (Ω i))
              (s i ∩ {x | δ < (P i : Measure (Ω i)).rnDeriv (Q i) x}) +
            (Q i : Measure (Ω i))
              {x | (P i : Measure (Ω i)).rnDeriv (Q i) x ≤ δ} := by
        calc
          _ ≤ (Q i : Measure (Ω i))
              ((s i ∩ {x | δ < (P i : Measure (Ω i)).rnDeriv (Q i) x}) ∪
                {x | (P i : Measure (Ω i)).rnDeriv (Q i) x ≤ δ}) := by
            apply measure_mono
            intro x hx
            by_cases hxd : δ < (P i : Measure (Ω i)).rnDeriv (Q i) x
            · exact Or.inl ⟨hx, hxd⟩
            · exact Or.inr (le_of_not_gt hxd)
          _ ≤ _ := measure_union_le _ _
      have heps : (ε : ℝ≥0∞) ≤ (Q i : Measure (Ω i)) (s i) := by
        change ε ≤ Q i (s i) at hiB
        simpa [ProbabilityMeasure.coeFn_def] using ENNReal.coe_le_coe.mpr hiB
      have hhalf : (ε : ℝ≥0∞) / 2 ≤
          (Q i : Measure (Ω i))
            {x | (P i : Measure (Ω i)).rnDeriv (Q i) x ≤ δ} := by
        apply ENNReal.le_of_add_le_add_left (a := (ε : ℝ≥0∞) / 2)
        · exact ENNReal.div_ne_top (by simp) (by simp)
        · calc
            (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 = ε := ENNReal.add_halves _
            _ ≤ (Q i : Measure (Ω i)) (s i) := heps
            _ ≤ _ := hsplit
            _ ≤ (ε : ℝ≥0∞) / 2 +
                (Q i : Measure (Ω i))
                  {x | (P i : Measure (Ω i)).rnDeriv (Q i) x ≤ δ} := by
              gcongr
              exact hbad.trans (by
                simpa [ProbabilityMeasure.coeFn_def] using hi.le)
      rw [show (R i : Measure ℝ≥0∞) (Iic δ) =
          (Q i : Measure (Ω i))
            {x | (P i : Measure (Ω i)).rnDeriv (Q i) x ≤ δ} by
        exact ProbabilityMeasure.map_apply' (Q i)
          (Measure.measurable_rnDeriv (P i) (Q i)).aemeasurable measurableSet_Iic]
      exact hhalf
    calc
      (ε : ℝ≥0∞) / 2 ≤ u.limsup (fun i ↦ (R i : Measure ℝ≥0∞) (Iic δ)) :=
        le_limsup_of_frequently_le hRlow.frequently
      _ ≤ (L : Measure ℝ≥0∞) (Iic δ) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto huL isClosed_Iic
  have hzero : ((ε : ℝ≥0∞) / 2) ≤ (L : Measure ℝ≥0∞) {0} := by
    rw [← iInter_Iic_invSucc, Antitone.measure_iInter]
    · exact le_iInf hlow
    · intro i j hij
      exact Iic_subset_Iic.mpr <| ENNReal.inv_le_inv.mpr <| by
        exact_mod_cast Nat.add_le_add_right hij 1
    · exact fun _ ↦ measurableSet_Iic.nullMeasurableSet
    · exact ⟨0, measure_ne_top (L : Measure ℝ≥0∞) _⟩
  have hpos : 0 < (ε : ℝ≥0∞) / 2 :=
    ENNReal.div_pos (by exact_mod_cast hε.ne') (by simp)
  have hLmeasure : (L : Measure ℝ≥0∞) {0} = 0 := by
    simpa [ProbabilityMeasure.coeFn_def] using
      congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hLzero
  exact (hpos.trans_le hzero).ne' hLmeasure

private noncomputable def rnTail {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) (n : ℕ) : Set Y :=
  ({x | (n : ℝ≥0∞) < ν.rnDeriv μ x} ∩
    (Measure.mutuallySingular_singularPart ν μ).nullSet) ∪
      (Measure.mutuallySingular_singularPart ν μ).nullSetᶜ

private lemma measurableSet_rnTail {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) (n : ℕ) : MeasurableSet (rnTail μ ν n) := by
  exact (((Measure.measurable_rnDeriv ν μ) measurableSet_Ioi).inter
    (Measure.mutuallySingular_singularPart ν μ).measurableSet_nullSet).union
      (Measure.mutuallySingular_singularPart ν μ).measurableSet_nullSet.compl

private lemma measure_rnTail_le_inv {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) : μ (rnTail μ ν n) ≤ (n : ℝ≥0∞)⁻¹ := by
  let S := (Measure.mutuallySingular_singularPart ν μ).nullSet
  have hSc : μ Sᶜ = 0 :=
    (Measure.mutuallySingular_singularPart ν μ).measure_compl_nullSet
  have hS : MeasurableSet S :=
    (Measure.mutuallySingular_singularPart ν μ).measurableSet_nullSet
  have hdisj : Disjoint ({x | (n : ℝ≥0∞) < ν.rnDeriv μ x} ∩ S) Sᶜ :=
    disjoint_compl_right.mono_left inter_subset_right
  calc
    μ (rnTail μ ν n) = μ ({x | (n : ℝ≥0∞) < ν.rnDeriv μ x} ∩ S) := by
      change μ (({x | (n : ℝ≥0∞) < ν.rnDeriv μ x} ∩ S) ∪ Sᶜ) = _
      rw [measure_union hdisj hS.compl, hSc, add_zero]
    _ ≤ μ {x | (n : ℝ≥0∞) ≤ ν.rnDeriv μ x} := by
      apply measure_mono
      intro x hx
      change (n : ℝ≥0∞) < ν.rnDeriv μ x ∧ x ∈ S at hx
      change (n : ℝ≥0∞) ≤ ν.rnDeriv μ x
      exact hx.1.le
    _ ≤ (n : ℝ≥0∞)⁻¹ := by
      have hmarkov := mul_meas_ge_le_lintegral (μ := μ)
        (Measure.measurable_rnDeriv ν μ) (n : ℝ≥0∞)
      have hint : ∫⁻ x, ν.rnDeriv μ x ∂μ ≤ 1 :=
        (Measure.lintegral_rnDeriv_le).trans_eq measure_univ
      apply ENNReal.le_inv_iff_mul_le.2
      rw [mul_comm]
      exact hmarkov.trans hint

private lemma one_sub_truncIntegral_le_measure_rnTail
    {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) :
    1 - (∫ x, ENNReal.truncateToReal n (ν.rnDeriv μ x) ∂μ) ≤
      ν.real (rnTail μ ν n) := by
  let S := (Measure.mutuallySingular_singularPart ν μ).nullSet
  let e := rnTail μ ν n
  have he : MeasurableSet e := measurableSet_rnTail μ ν n
  have hec : eᶜ = {x | ν.rnDeriv μ x ≤ n} ∩ S := by
    ext x
    by_cases hx : x ∈ S <;> simp [e, rnTail, S, hx, not_lt]
  have hsing_zero : ν.singularPart μ eᶜ = 0 := by
    rw [hec]
    exact measure_mono_null inter_subset_right
      (Measure.mutuallySingular_singularPart ν μ).measure_nullSet
  have hQec : ν eᶜ = ∫⁻ x in eᶜ, ν.rnDeriv μ x ∂μ := by
    calc
      ν eᶜ = (ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)) eᶜ := by
        rw [Measure.singularPart_add_rnDeriv]
      _ = ∫⁻ x in eᶜ, ν.rnDeriv μ x ∂μ := by
        rw [Measure.add_apply, hsing_zero, zero_add, withDensity_apply _ he.compl]
  have hle : ν eᶜ ≤ ∫⁻ x, min (n : ℝ≥0∞) (ν.rnDeriv μ x) ∂μ := by
    rw [hQec]
    calc
      ∫⁻ x in eᶜ, ν.rnDeriv μ x ∂μ ≤
          ∫⁻ x in eᶜ, min (n : ℝ≥0∞) (ν.rnDeriv μ x) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem he.compl] with x hx
        rw [hec] at hx
        exact (min_eq_right hx.1).ge
      _ ≤ ∫⁻ x, min (n : ℝ≥0∞) (ν.rnDeriv μ x) ∂μ :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  have hfin : (∫⁻ x, min (n : ℝ≥0∞) (ν.rnDeriv μ x) ∂μ) ≠ ∞ := by
    exact ne_of_lt <| (lintegral_mono fun _ ↦ min_le_left _ _).trans_lt <| by simp
  have hreal : ν.real eᶜ ≤
      ∫ x, ENNReal.truncateToReal n (ν.rnDeriv μ x) ∂μ := by
    rw [measureReal_def, show (∫ x, ENNReal.truncateToReal n (ν.rnDeriv μ x) ∂μ) =
      (∫⁻ x, min (n : ℝ≥0∞) (ν.rnDeriv μ x) ∂μ).toReal by
        change (∫ x, (min (n : ℝ≥0∞) (ν.rnDeriv μ x)).toReal ∂μ) = _
        rw [MeasureTheory.integral_toReal]
        · exact (measurable_const.min (Measure.measurable_rnDeriv ν μ)).aemeasurable
        · exact ae_of_all _ fun _ ↦ by simp]
    exact ENNReal.toReal_mono hfin hle
  rw [measureReal_compl he, probReal_univ] at hreal
  linarith

private lemma antitone_rnTail {Y : Type*} [MeasurableSpace Y] (μ ν : Measure Y) :
    Antitone (rnTail μ ν) := by
  intro i j hij x hx
  change (((j : ℕ) : ℝ≥0∞) < ν.rnDeriv μ x ∧
    x ∈ (Measure.mutuallySingular_singularPart ν μ).nullSet) ∨
      x ∈ (Measure.mutuallySingular_singularPart ν μ).nullSetᶜ at hx
  change (((i : ℕ) : ℝ≥0∞) < ν.rnDeriv μ x ∧
    x ∈ (Measure.mutuallySingular_singularPart ν μ).nullSet) ∨
      x ∈ (Measure.mutuallySingular_singularPart ν μ).nullSetᶜ
  rcases hx with hx | hx
  · exact Or.inl ⟨(by exact_mod_cast hij : (i : ℝ≥0∞) ≤ j).trans_lt hx.1, hx.2⟩
  · exact Or.inr hx

private theorem Contiguous1.contiguous3 {l : Filter α}
    (P Q : ∀ i, ProbabilityMeasure (Ω i))
    (hPQ : Contiguous1 l P Q) : Contiguous3 l P Q := by
  intro V h hle hh hV
  have hIv (n : ℕ) : Tendsto (fun i ↦ ∫ x, ENNReal.truncateToReal n
      ((Q i : Measure (Ω i)).rnDeriv (P i) x) ∂(P i)) h
      (𝓝 (∫ x, truncBCF n x ∂(V : Measure ℝ≥0∞))) := by
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hV) (truncBCF n)
    refine ht.congr' ?_
    filter_upwards with i
    change (∫ x, truncBCF n x ∂Measure.map _ (P i : Measure (Ω i))) = _
    exact integral_map (μ := (P i : Measure (Ω i)))
      (φ := (Q i : Measure (Ω i)).rnDeriv (P i))
      (Measure.measurable_rnDeriv (Q i : Measure (Ω i))
        (P i : Measure (Ω i))).aemeasurable
      (truncBCF n).continuous.aestronglyMeasurable
  have hsource_le (n : ℕ) (i : α) :
      ∫ x, ENNReal.truncateToReal n
        ((Q i : Measure (Ω i)).rnDeriv (P i) x) ∂(P i) ≤ 1 := by
    have hb := rnDeriv_measureReal_le
      (P i : Measure (Ω i)) (Q i : Measure (Ω i))
      (∅ : Set (Ω i)) MeasurableSet.empty n
    simp only [measureReal_empty] at hb
    linarith
  have hVtrunc_le (n : ℕ) :
      ∫ x, truncBCF n x ∂(V : Measure ℝ≥0∞) ≤ 1 :=
    le_of_tendsto (hIv n) (Eventually.of_forall (hsource_le n))
  have hmean_le : ∫⁻ x, x ∂V ≤ 1 := by
    rw [show (∫⁻ x, x ∂V) = ⨆ n : ℕ, ∫⁻ x, min x n ∂V by
      rw [← lintegral_iSup]
      · congr with x
        rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
      · exact fun n ↦ measurable_id.min measurable_const
      · exact fun _ _ hab ↦ fun x ↦ min_le_min_left _ <| mod_cast hab]
    refine iSup_le fun n ↦ ?_
    have hfin : (∫⁻ x, min x n ∂(V : Measure ℝ≥0∞)) ≠ ∞ :=
      ne_of_lt <| (lintegral_mono fun _ ↦ min_le_right _ _).trans_lt <| by simp
    apply (ENNReal.toReal_le_toReal hfin ENNReal.one_ne_top).1
    have heq : ∫ x, truncBCF n x ∂(V : Measure ℝ≥0∞) =
        (∫⁻ x, min x n ∂(V : Measure ℝ≥0∞)).toReal := by
      simp only [truncBCF, BoundedContinuousFunction.mkOfCompact_apply]
      change (∫ x, (min (n : ℝ≥0∞) x).toReal ∂(V : Measure ℝ≥0∞)) = _
      rw [MeasureTheory.integral_toReal]
      · congr with x
        rw [min_comm]
      · exact (measurable_const.min measurable_id).aemeasurable
      · exact ae_of_all _ fun _ ↦ by simp
    rw [← heq]
    exact hVtrunc_le n
  apply le_antisymm hmean_le
  by_contra hmean
  have hmean_lt : ∫⁻ x, x ∂V < 1 := lt_of_not_ge hmean
  let r := (∫⁻ x, x ∂V).toReal
  let c := (1 - r) / 4
  have hmean_fin : (∫⁻ x, x ∂V) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hmean_le
  have hr : r < 1 :=
    (ENNReal.toReal_lt_toReal hmean_fin ENNReal.one_ne_top).2 hmean_lt
  have hc : 0 < c := div_pos (sub_pos.2 hr) (by positivity)
  have hA : ∀ n : ℕ, ∀ᶠ i in h, c < (Q i : Measure (Ω i)).real
      (rnTail (P i) (Q i) (n + 1)) := by
    intro n
    have hlim := hIv (n + 1)
    have hVle : ∫ x, truncBCF (n + 1) x ∂(V : Measure ℝ≥0∞) ≤ r := by
      have hlin :
          (∫⁻ x, min x ((n + 1 : ℕ) : ℝ≥0∞) ∂(V : Measure ℝ≥0∞)) ≤
            ∫⁻ x, x ∂V := lintegral_mono fun _ ↦ min_le_left _ _
      have htr : ∫ x, truncBCF (n + 1) x ∂(V : Measure ℝ≥0∞) =
          (∫⁻ x, min x (n + 1) ∂(V : Measure ℝ≥0∞)).toReal := by
        simp only [truncBCF, BoundedContinuousFunction.mkOfCompact_apply]
        change (∫ x, (min ((n + 1 : ℕ) : ℝ≥0∞) x).toReal
          ∂(V : Measure ℝ≥0∞)) = _
        rw [MeasureTheory.integral_toReal]
        · congr with x
          norm_num [Nat.cast_add, Nat.cast_one]
          rw [min_comm]
        · exact (measurable_const.min measurable_id).aemeasurable
        · exact ae_of_all _ fun _ ↦ by simp
      rw [htr]
      norm_num [Nat.cast_add, Nat.cast_one] at hlin ⊢
      exact ENNReal.toReal_mono hmean_fin hlin
    have hevent := (tendsto_order.1 hlim).2 (r + c)
      (hVle.trans_lt (lt_add_of_pos_right _ hc))
    filter_upwards [hevent] with i hi
    have htail := one_sub_truncIntegral_le_measure_rnTail
      (P i : Measure (Ω i)) (Q i : Measure (Ω i)) (n + 1)
    norm_num [Nat.cast_add, Nat.cast_one] at hi htail
    dsimp only [c] at *
    rw [ProbabilityMeasure.measureReal_eq_coe_coeFn]
    linarith
  let B : Set α := {i | ∀ n, c < (Q i : Measure (Ω i)).real
    (rnTail (P i) (Q i) (n + 1))}
  by_cases hB : ∃ᶠ i in h, i ∈ B
  · let m := h ⊓ principal B
    have hm : m.NeBot := frequently_iff_neBot.1 hB
    let s : ∀ i, Set (Ω i) := fun i ↦ ⋂ n : ℕ, rnTail (P i) (Q i) (n + 1)
    have hs : ∀ i, MeasurableSet (s i) := fun i ↦
      MeasurableSet.iInter fun n ↦ measurableSet_rnTail
        (P i : Measure (Ω i)) (Q i : Measure (Ω i)) (n + 1)
    have hPzero : ∀ i, (P i : Measure (Ω i)) (s i) = 0 := by
      intro i
      apply le_zero_iff.mp
      by_contra hpos
      obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt (lt_of_not_ge hpos).ne'
      have hmono : (P i : Measure (Ω i)) (s i) ≤
          (P i : Measure (Ω i)) (rnTail (P i) (Q i) (N + 1)) :=
        measure_mono <| iInter_subset _ N
      have hmark := measure_rnTail_le_inv
        (P i : Measure (Ω i)) (Q i : Measure (Ω i)) (N + 1)
      have hinv : ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ (N : ℝ≥0∞)⁻¹ :=
        ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ N)
      exact (not_lt_of_ge (hmono.trans (hmark.trans hinv))) hN
    have hPs : Tendsto (fun i ↦ P i (s i)) m (𝓝 0) := by
      have hz : ∀ i, P i (s i) = 0 := by
        intro i
        rw [← ENNReal.coe_inj]
        simpa [ProbabilityMeasure.coeFn_def] using hPzero i
      simpa only [hz] using
        (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ≥0)) m (𝓝 0))
    have hQs := hPQ hs (inf_le_left.trans hle) hPs
    have hcQ : ∀ᶠ i in m, c ≤ (Q i : Measure (Ω i)).real (s i) := by
      have hBm : ∀ᶠ i in m, i ∈ B := mem_inf_of_right (by simp)
      filter_upwards [hBm] with i hi
      have ht := tendsto_measure_iInter_atTop
        (μ := (Q i : Measure (Ω i)))
        (s := fun n : ℕ ↦ rnTail (P i) (Q i) (n + 1))
        (fun n ↦ (measurableSet_rnTail (P i : Measure (Ω i))
          (Q i : Measure (Ω i)) (n + 1)).nullMeasurableSet)
        (fun _ _ hab ↦ antitone_rnTail (P i : Measure (Ω i))
          (Q i : Measure (Ω i)) (Nat.add_le_add_right hab 1))
        ⟨0, measure_ne_top (Q i : Measure (Ω i)) (rnTail (P i) (Q i) 1)⟩
      have htR := (ENNReal.tendsto_toReal (measure_ne_top (Q i) (s i))).comp ht
      apply ge_of_tendsto htR
      simpa only [Function.comp_apply, measureReal_def] using
        (Eventually.of_forall fun n ↦ (hi n).le)
    have hQreal : Tendsto (fun i ↦ (Q i : Measure (Ω i)).real (s i)) m (𝓝 0) := by
      change Tendsto (fun i ↦ (Q i (s i) : ℝ)) (h ⊓ principal B) (𝓝 (0 : ℝ))
      exact NNReal.tendsto_coe.2 hQs
    have hQsmall := (tendsto_order.1 hQreal).2 c hc
    exact (hcQ.and hQsmall).exists.elim fun _ hi ↦ (not_lt_of_ge hi.1) hi.2
  · classical
    let A : α → ℕ → Prop := fun i n ↦ c < (Q i : Measure (Ω i)).real
      (rnTail (P i) (Q i) (n + 1))
    let k : α → ℕ := fun i ↦ if hi : ∃ n, ¬A i n then Nat.find hi else 0
    have hnotB : ∀ᶠ i in h, ∃ n, ¬A i n := by
      have hb := not_frequently.mp hB
      filter_upwards [hb] with i hi
      simpa only [B, A, Set.mem_ofPred_eq, not_forall] using hi
    have hk : Tendsto k h atTop := by
      refine tendsto_atTop.2 fun N ↦ ?_
      filter_upwards [hA N, hnotB] with i hiN hiex
      have hkbad : ¬A i (k i) := by
        simp only [k, hiex, dite_true]
        exact Nat.find_spec hiex
      have hNk : N < k i := by
        by_contra hnot
        have hkiN : k i ≤ N := Nat.le_of_not_gt hnot
        apply hkbad
        exact hiN.trans_le <| measureReal_mono <|
          antitone_rnTail (P i : Measure (Ω i)) (Q i : Measure (Ω i)) <|
            Nat.add_le_add_right hkiN 1
      exact hNk.le
    let s : ∀ i, Set (Ω i) := fun i ↦ rnTail (P i) (Q i) (k i)
    have hs : ∀ i, MeasurableSet (s i) := fun i ↦ by
      simpa only [s] using measurableSet_rnTail
        (P i : Measure (Ω i)) (Q i : Measure (Ω i)) (k i)
    have hinv : Tendsto (fun i ↦ (k i : ℝ≥0∞)⁻¹) h (𝓝 0) := by
      rw [ENNReal.nhds_zero_basis.tendsto_right_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      filter_upwards [hk.eventually (eventually_ge_atTop N)] with i hi
      exact (ENNReal.inv_le_inv.mpr (by exact_mod_cast hi)).trans_lt hN
    have hPe : Tendsto (fun i ↦ (P i : Measure (Ω i)) (s i)) h (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      · exact Eventually.of_forall fun _ ↦ bot_le
      · filter_upwards [hk.eventually (eventually_ge_atTop 1)] with i hi
        exact measure_rnTail_le_inv (P i : Measure (Ω i)) (Q i : Measure (Ω i))
          (k i)
    have hPs : Tendsto (fun i ↦ P i (s i)) h (𝓝 0) := by
      have ht := (ENNReal.tendsto_toNNReal_iff (a := 0) ENNReal.zero_ne_top
        (fun i ↦ measure_ne_top (P i) (s i))).2 hPe
      simpa [Function.comp_def, ProbabilityMeasure.coeFn_def] using ht
    have hQs := hPQ hs hle hPs
    have hcQ : ∀ᶠ i in h, c < (Q i : Measure (Ω i)).real (s i) := by
      filter_upwards [hnotB, hk.eventually (eventually_ge_atTop 1)] with i hiex hki
      have hkprev : A i (k i - 1) := by
        by_contra hbad
        have hfind : k i ≤ k i - 1 := by
          simpa only [k, hiex, dite_true] using Nat.find_min' hiex hbad
        omega
      simpa only [A, s, Nat.sub_add_cancel hki] using hkprev
    have hQreal : Tendsto (fun i ↦ (Q i : Measure (Ω i)).real (s i)) h (𝓝 0) := by
      change Tendsto (fun i ↦ (Q i (s i) : ℝ)) h (𝓝 (0 : ℝ))
      exact NNReal.tendsto_coe.2 hQs
    have hQsmall := (tendsto_order.1 hQreal).2 c hc
    exact (hcQ.and hQsmall).exists.elim fun _ hi ↦ (not_lt_of_ge hi.1.le) hi.2

private theorem contiguous1_of_contiguous3 {l : Filter α}
    (P Q : ∀ i, ProbabilityMeasure (Ω i))
    (hPQ : Contiguous3 l P Q) : Contiguous1 l P Q := by
  intro s h hs hle hP
  by_contra hQ
  obtain ⟨t, ht, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hQ
  let m := h ⊓ principal {i | Q i (s i) ∉ t}
  have hm : m.NeBot := frequently_iff_neBot.1 hfreq
  let R : ∀ i, ProbabilityMeasure ℝ≥0∞ := fun i ↦ (P i).map
    ((Measure.measurable_rnDeriv (Q i) (P i)).aemeasurable)
  obtain ⟨V, _, hV⟩ := isCompact_univ.exists_mapClusterPt (f := m) (u := R) (by simp)
  obtain ⟨u, hum, huV⟩ := mapClusterPt_iff_ultrafilter.1 hV
  have hul : (u : Filter α) ≤ l := hum.trans <| inf_le_left.trans hle
  have hmean : ∫⁻ x, x ∂V = 1 := hPQ V hul inferInstance huV
  have hPu : Tendsto (fun i ↦ P i (s i)) u (𝓝 0) :=
    hP.mono_left (hum.trans inf_le_left)
  have hQu : Tendsto (fun i ↦ Q i (s i)) u (𝓝 0) :=
    tendsto_measure_zero_of_rnDeriv_law P Q s hs hPu V huV hmean
  have hbad : ∀ᶠ i in u, Q i (s i) ∉ t :=
    hum (mem_inf_of_right (by simp))
  exact (hQu.eventually ht).and hbad |>.exists.elim fun _ hi ↦ hi.2 hi.1

theorem contiguous2_iff_contiguous3 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    Contiguous2 l P Q ↔ Contiguous3 l P Q := by
  constructor
  · exact fun h ↦ (h.contiguous1 P Q).contiguous3 P Q
  · exact fun h ↦ (contiguous1_of_contiguous3 P Q h).contiguous2 P Q

end

section -- Contiguous3 implies contiguous1

theorem Contiguous3.contiguous1 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a))
    (hPQ : Contiguous3 l P Q) : Contiguous1 l P Q :=
  contiguous1_of_contiguous3 P Q hPQ

end

/-- The first four definitions of contiguity are equivalent. -/
theorem Contiguous.TFAE {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    List.TFAE [Contiguous1 l P Q, Contiguous2 l P Q, Contiguous3 l P Q, Contiguous4 l P Q] := by
  tfae_have 1 ↔ 4 := (contiguous1_iff_contiguous4 P Q)
  tfae_have 2 ↔ 3 := (contiguous2_iff_contiguous3 P Q)
  tfae_have 1 → 2 := fun h => h.contiguous2
  tfae_have 3 → 1 := fun h => h.contiguous1
  tfae_finish

section -- Contiguous5 and contiguous1 are equivalent.

theorem Contiguous1.contiguous5 {l : Filter α} {P Q : ∀ a, ProbabilityMeasure (Ω a)}
    (hPQ : Contiguous1 l P Q) : Contiguous5 l P Q :=
  fun _ hs hP => hPQ hs le_rfl hP

/-- `Contiguous5` implies `Contiguous1` for filters with a decreasing countable basis that are
finer than the cofinite filter. -/
theorem Contiguous5.contiguous1_of_hasAntitoneBasis_le_cofinite {l : Filter α}
    {P Q : ∀ a, ProbabilityMeasure (Ω a)} {b : ℕ → Set α} (hPQ : Contiguous5 l P Q)
    (hb : l.HasAntitoneBasis b) (hl : l ≤ cofinite) : Contiguous1 l P Q := by
  intro s h hs hle hP
  by_contra hQ
  rw [NNReal.nhds_zero_basis.tendsto_right_iff] at hQ
  simp only [mem_Iio] at hQ
  push Not at hQ
  obtain ⟨ε, hε, hQε⟩ := hQ
  classical
  have hchoose : ∀ k : ℕ, ∃ a : α,
      ε ≤ Q a (s a) ∧ P a (s a) < (((k + 1 : ℕ) : ℝ≥0)⁻¹) ∧ a ∈ b k := by
    intro k
    have hPk : ∀ᶠ a in h, P a (s a) < (((k + 1 : ℕ) : ℝ≥0)⁻¹) :=
      (NNReal.nhds_zero_basis.tendsto_right_iff.1 hP) _ (by positivity)
    have hbk : ∀ᶠ a in h, a ∈ b k := hle (hb.mem k)
    exact (hQε.and_eventually (hPk.and hbk)).exists
  choose u hu using hchoose
  let t : ∀ a, Set (Ω a) := fun a => if ∃ k, u k = a then s a else ∅
  have ht_meas : ∀ a, MeasurableSet (t a) := by
    intro a
    by_cases ha : ∃ k, u k = a
    · simp [t, ha, hs a]
    · simp [t, ha]
  have htP : Tendsto (fun a => P a (t a)) l (𝓝 0) := by
    rw [NNReal.nhds_zero_basis.tendsto_right_iff]
    intro δ hδ
    obtain ⟨K, hKpos, hK⟩ := NNReal.exists_nat_pos_inv_lt hδ
    let F : Set α := u '' {k | k < K}
    filter_upwards [hl ((Set.finite_lt_nat K).image u).compl_mem_cofinite] with a haF
    by_cases harange : ∃ k, u k = a
    · rcases harange with ⟨k, rfl⟩
      have hkge : K ≤ k := by
        by_contra hk
        exact haF ⟨k, Nat.lt_of_not_ge hk, rfl⟩
      have hle_inv : (((k + 1 : ℕ) : ℝ≥0)⁻¹) ≤ (K : ℝ≥0)⁻¹ := by
        exact inv_anti₀ (by exact_mod_cast hKpos) (by exact_mod_cast hkge.trans k.le_succ)
      have huk_range : ∃ j, u j = u k := ⟨k, rfl⟩
      simpa [t, huk_range] using ((hu k).2.1.trans_le hle_inv).trans hK
    · simp [t, harange, hδ]
  have hsmall : ∀ᶠ k : ℕ in atTop, Q (u k) (t (u k)) < ε :=
    (NNReal.nhds_zero_basis.tendsto_right_iff.1
      ((hPQ ht_meas htP).comp (hb.tendsto fun k => (hu k).2.2))) ε hε
  obtain ⟨k, hltε⟩ := hsmall.exists
  have huk_range : ∃ j, u j = u k := ⟨k, rfl⟩
  exact (not_lt_of_ge (by simpa [t, huk_range] using (hu k).1)) hltε

/-- Contiguous5 implies contiguous1 under the assumption that the filter `l` is countably generated
and `≤ cofinite`. -/
theorem Contiguous5.contiguous1_of_isCountablyGenerated_le_cofinite {l : Filter α}
    [l.IsCountablyGenerated] {P Q : ∀ a, ProbabilityMeasure (Ω a)}
    (hPQ : Contiguous5 l P Q) (hl : l ≤ cofinite) : Contiguous1 l P Q := by
  obtain ⟨b, _, hb⟩ := (Filter.basis_sets l).exists_antitone_subbasis
  exact hPQ.contiguous1_of_hasAntitoneBasis_le_cofinite hb hl

section Nat

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P Q : ∀ n, ProbabilityMeasure (Ω n)}

theorem Contiguous5.contiguous1_atTop (hPQ : Contiguous5 atTop P Q) :
    Contiguous1 atTop P Q := by
  refine hPQ.contiguous1_of_hasAntitoneBasis_le_cofinite (b := Set.Ici) ?_ atTop_le_cofinite
  exact ⟨atTop_basis, fun _ _ hij _ hx => hij.trans hx⟩

theorem contiguous5_atTop_iff_contiguous1 :
    Contiguous1 atTop P Q ↔ Contiguous5 atTop P Q :=
  ⟨Contiguous1.contiguous5, Contiguous5.contiguous1_atTop⟩

/-- All definitions of contiguity are equivalent for the `atTop` filter on `ℕ`. -/
theorem Contiguous.nat_TFAE :
    List.TFAE [Contiguous1 atTop P Q, Contiguous2 atTop P Q, Contiguous3 atTop P Q,
      Contiguous4 atTop P Q, Contiguous5 atTop P Q] := by
  tfae_have 1 ↔ 4 := contiguous1_iff_contiguous4 P Q
  tfae_have 2 ↔ 3 := contiguous2_iff_contiguous3 P Q
  tfae_have 1 → 2 := fun h ↦ h.contiguous2 P Q
  tfae_have 3 → 1 := fun h ↦ h.contiguous1 P Q
  tfae_have 1 ↔ 5 := contiguous5_atTop_iff_contiguous1
  tfae_finish

end Nat

end

#min_imports -- Let's keep this until we finish all the proof.
