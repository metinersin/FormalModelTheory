-- This module serves as the root of the `FormalModelTheory` library.
-- Import modules here that should be built as part of the library.
import FormalModelTheory.Basic

/-!
## Main Definitions

## Main Theorems

* `countably_saturated_of_mk_eq_aleph0_of_dlo`: Countably infinite models of DLO
  are countably saturated.

* `aleph0_categorical_of_dlo`: DLO is ℵ₀-categorical.
-/

open Cardinal
open FirstOrder
open Language
open Theory
open Structure

universe w

notation "L≤" => Language.order

theorem countably_saturated_of_mk_eq_aleph0_of_dlo :
    ∀ {M : Type w} [Fact (#M = ℵ₀)] [L≤.Structure M] [M ⊨ L≤.dlo],
    countably_saturated (T := L≤.dlo) M := by
  sorry

theorem aleph0_categorical_of_dlo : L≤.dlo.categorical ℵ₀ := by
  apply aleph0_categorical_of_countably_saturated_of_mk_eq_aleph0
  apply countably_saturated_of_mk_eq_aleph0_of_dlo
