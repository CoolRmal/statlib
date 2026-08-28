/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/

module

public import Mathlib.Init

/-!
# Potential Responses

This module supplies an assumption-free functional representation of potential responses.

`PotentialResponse.select` produces a theoretical selected response, not a recorded outcome.
`PotentialResponse.comp` performs same-unit substitution.

Causal assumptions, estimands, estimators, probability structure, and statistical inference are
deferred to later modules.
-/

@[expose] public section

/-- A potential response assigns a value to each intervention and unit. -/
abbrev PotentialResponse
    (Intervention : Type*) (Unit : Type*) (Value : Type*) :=
  Intervention → Unit → Value

namespace PotentialResponse

variable {Intervention : Type*} {Unit : Type*} {Value : Type*} {Index : Type*}

/-- Selects each unit's response at the intervention supplied for that unit. -/
def select
    (response : PotentialResponse Intervention Unit Value)
    (intervention : Unit → Intervention) :
    Unit → Value :=
  fun u ↦ response (intervention u) u

/-- Substitutes an intervention response into a response, evaluating both at the same unit. -/
def comp
    (response : PotentialResponse Intervention Unit Value)
    (intervention :
      PotentialResponse Index Unit Intervention) :
    PotentialResponse Index Unit Value :=
  fun index u ↦ response (intervention index u) u

@[simp] theorem select_apply
    (response : PotentialResponse Intervention Unit Value)
    (intervention : Unit → Intervention)
    (u : Unit) :
    response.select intervention u =
      response (intervention u) u := rfl

@[simp] theorem comp_apply
    (response : PotentialResponse Intervention Unit Value)
    (intervention :
      PotentialResponse Index Unit Intervention)
    (index : Index)
    (u : Unit) :
    response.comp intervention index u =
      response (intervention index u) u := rfl

end PotentialResponse
