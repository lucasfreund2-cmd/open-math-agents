import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-
SPDX-License-Identifier: Apache-2.0

The quadratic-form nonnegativity and integral calculation are adapted from
Jacob Parish / Plasma AI, plasma-ai/erdos-173 at
bc41fe8950bafe3d69fc58f2a422f1dee9a1e943, Erdos173/Transfer/Sample.lean.
That source adapts OpenAI's openai/math at
adc7f1241b42e322a6451854ab7e4b4c146bf78a; see its OAI/README.md.
License: https://www.apache.org/licenses/LICENSE-2.0

Changes: extracted the independent L² moment argument, removed all carrier and
coloring machinery, renamed the namespace, and assembled the exact bridge lemma.
-/

namespace OMAL2Moments

open MeasureTheory
open scoped ENNReal InnerProductSpace

def qform (a b c : ℝ) : ℝ := 1 + a * b + a * c + b * c

lemma qform_nonneg {a b c : ℝ} (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) : 0 ≤ qform a b c := by
  have h₁ : 0 ≤ (1 + a) * (1 + b) * (1 + c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h₂ : 0 ≤ (1 - a) * (1 - b) * (1 - c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  unfold qform
  nlinarith

lemma integral_qform {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A B C : Lp ℂ 2 μ) (hA : ∀ᵐ η ∂μ, (A η).im = 0) (hB : ∀ᵐ η ∂μ, (B η).im = 0) :
    Integrable (fun η => qform (A η).re (B η).re (C η).re) μ ∧
      ∫ η, qform (A η).re (B η).re (C η).re ∂μ =
        (1 + ⟪A, B⟫_ℂ + ⟪A, C⟫_ℂ + ⟪B, C⟫_ℂ).re := by
  have hre (V W : Lp ℂ 2 μ) (hV : ∀ᵐ η ∂μ, (V η).im = 0) :
      (fun η => RCLike.re (⟪V η, W η⟫_ℂ)) =ᵐ[μ] fun η => (V η).re * (W η).re := by
    filter_upwards [hV] with η h
    simp [RCLike.inner_apply, h, mul_comm]
  have hint (V W : Lp ℂ 2 μ) (hV : ∀ᵐ η ∂μ, (V η).im = 0) :
      Integrable (fun η => (V η).re * (W η).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) V W).re.congr (hre V W hV)
  have hval (V W : Lp ℂ 2 μ) (hV : ∀ᵐ η ∂μ, (V η).im = 0) :
      ∫ η, (V η).re * (W η).re ∂μ = (⟪V, W⟫_ℂ).re := by
    rw [← integral_congr_ae (hre V W hV), integral_re (L2.integrable_inner V W), ← L2.inner_def]
    rfl
  have i₁ : Integrable (fun η => 1 + (A η).re * (B η).re) μ :=
    (integrable_const _).add (hint A B hA)
  have i₂ : Integrable (fun η => 1 + (A η).re * (B η).re + (A η).re * (C η).re) μ :=
    i₁.add (hint A C hA)
  refine ⟨i₂.add (hint B C hB), ?_⟩
  unfold qform
  rw [integral_add i₂ (hint B C hB), integral_add i₁ (hint A C hA),
    integral_add (integrable_const _) (hint A B hA), hval A B hA, hval A C hA, hval B C hB]
  simp

theorem bridge (Ω : Type*) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A B C : Lp ℂ 2 ν)
    (hA : ∀ᵐ ω ∂ν, (A ω).im = 0 ∧ -1 ≤ (A ω).re ∧ (A ω).re ≤ 1)
    (hB : ∀ᵐ ω ∂ν, (B ω).im = 0 ∧ -1 ≤ (B ω).re ∧ (B ω).re ≤ 1)
    (hC : ∀ᵐ ω ∂ν, (C ω).im = 0 ∧ -1 ≤ (C ω).re ∧ (C ω).re ≤ 1)
    (hmean : (1 + inner ℂ A B + inner ℂ A C + inner ℂ B C).re = 0) :
    ∀ᵐ ω ∂ν,
      1 + (A ω).re * (B ω).re + (A ω).re * (C ω).re + (B ω).re * (C ω).re = 0 := by
  obtain ⟨hint, hvalue⟩ := integral_qform ν A B C
    (hA.mono fun _ h => h.1) (hB.mono fun _ h => h.1)
  have hnn : 0 ≤ᵐ[ν] fun ω => qform (A ω).re (B ω).re (C ω).re := by
    filter_upwards [hA, hB, hC] with ω ha hb hc
    exact qform_nonneg ha.2 hb.2 hc.2
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp (hvalue.trans hmean)
  filter_upwards [hzero] with ω hω
  simpa only [qform, Pi.zero_apply] using hω

end OMAL2Moments

/-- The analytic moment-to-pointwise bridge for the bounded continuous field. -/
theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro Ω mΩ ν hν A B C hA hB hC hmean
  exact OMAL2Moments.bridge Ω ν A B C hA hB hC hmean
