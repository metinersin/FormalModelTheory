import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Types
import Mathlib.ModelTheory.Order

/-!
## Main Definitions
* `saturated`: A model M is κ-saturated if for any A ⊆ M with #A ≤ κ, all types
  over A are realized in M.

* `countably_saturated`: A model is countably saturated if it is countably
  infinite and ℵ₀-saturated.

* `categorical`: A theory is κ-categorical for a cardinal κ if all models of it
  with cardinality κ are isomorphic.

## Main Theorems

* `iso_of_countably_saturated`: Countably saturated models are isomorphic.

* `aleph0_categorical_of_countably_saturated_of_mk_eq_aleph0`: If all the
  countably infinite models of a theory T is countably saturated, then T is
  ℵ₀-categorical.
-/

open Cardinal

instance {α} [h : Fact (#α = ℵ₀)] : Nonempty α :=
  Cardinal.mk_ne_zero_iff.mp (by simp [aleph0_ne_zero, h.out])

namespace FirstOrder.Language

universe u v w
variable {L : Language.{u, v}}

namespace Structure

variable {T : L.Theory}
variable (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T]
variable (N : Type w) [Nonempty N] [L.Structure N] [N ⊨ T]

def saturated (κ : Cardinal.{w}) : Prop :=
  ∀ {α : Type w}, #α < κ → ∀ p : T.CompleteType α, p ∈ T.realizedTypes M α

def countably_saturated : Prop :=
  ∃ _ : Fact (#M = ℵ₀), saturated (T := T) M ℵ₀

theorem iso_of_countably_saturated :
    countably_saturated (T := T) M → countably_saturated (T := T) N →
    Nonempty (M ≃[L] N) := by
  sorry

end Structure

namespace Theory

variable (T : L.Theory)

def categorical (κ : Cardinal.{w}) : Prop :=
  ∀ {M N : Type w} [L.Structure M] [L.Structure N] [M ⊨ T] [N ⊨ T],
  #M = κ → #N = κ → Nonempty (M ≃[L] N)

open Structure

theorem aleph0_categorical_of_countably_saturated_of_mk_eq_aleph0
    (h : ∀ {M : Type w} [Fact (#M = ℵ₀)] [L.Structure M] [M ⊨ T],
    countably_saturated (T := T) M) : categorical.{u, v, w} T ℵ₀ := by
  unfold categorical
  intro M N _ _ _ _ _ _
  have : Fact (#M = ℵ₀) := ⟨by assumption⟩
  have : Fact (#N = ℵ₀) := ⟨by assumption⟩
  exact iso_of_countably_saturated M N h h

end Theory

end FirstOrder.Language
