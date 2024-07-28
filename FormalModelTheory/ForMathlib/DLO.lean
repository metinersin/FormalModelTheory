import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Order
import FormalModelTheory.ForMathlib.Structure
import FormalModelTheory.ForMathlib.Theory

open Cardinal
open FirstOrder
open Language
open Structure
open Theory

universe w

notation "L≤" => Language.order

theorem countably_saturated_of_mk_eq_aleph0_of_dlo :
    ∀ {M : Type w} [Nonempty M] [L≤.Structure M] [M ⊨ L≤.dlo],
    #M = ℵ₀ → countably_saturated L≤.dlo M := by
  sorry

theorem aleph0_categorical_of_dlo : L≤.dlo.categorical ℵ₀ := by
  apply aleph0_categorical_of_countably_saturated
  apply countably_saturated_of_mk_eq_aleph0_of_dlo
