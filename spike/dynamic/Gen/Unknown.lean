import Dyn

namespace Unknown
open Core Dyn

set_option maxRecDepth 4096

abbrev parseChartGroupByFieldId.pre (value' : Val) (h : Heap) : Prop :=
  Is h .any value'
def parseChartGroupByFieldId (value' : Val) : M Val := do
  return (← (do if truthy (← (do bin .eq (typeOf value') (str "string"))) then (pure value') else (pure (str ""))))
abbrev parseChartDecimalPlaces.pre (value' : Val) (h : Heap) : Prop :=
  Is h .any value'
def parseChartDecimalPlaces (value' : Val) : M Val := do
  let number' ← (do if truthy (← (do bin .eq (typeOf value') (str "bigint"))) then (do toNum value') else (pure value'))
  return (← (do if truthy (← (do let a3 := (← (do let a2 := (← (do let a1 := (← (do bin .eq (typeOf number') (str "number"))); if truthy a1 then (pure (isInteger number')) else pure a1)); if truthy a2 then (do bin .ge number' (num 0)) else pure a2)); if truthy a3 then (do bin .le number' (num 5)) else pure a3)) then (pure number') else (pure .null)))
end Unknown
