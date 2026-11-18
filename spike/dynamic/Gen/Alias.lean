import Dyn

namespace Alias
open Core Dyn

set_option maxRecDepth 4096

abbrev messageIsEmpty.pre (message' : Val) (h : Heap) : Prop :=
  Is h (.union [(.obj [("role", (.lit (str "user"))), ("content", (.union [.str, (.arr .any)])), ("metadata", (.union [.undef, (.obj [])]))]), (.obj [("role", (.lit (str "assistant"))), ("content", (.union [.str, (.arr .any)])), ("toolCalls", (.union [.undef, (.arr .any)])), ("usage", (.union [.undef, (.obj [("completionTokens", .any), ("promptTokens", .any), ("promptTokensDetails", .any), ("completionTokensDetails", .any)])])), ("metadata", (.union [.undef, (.obj [])]))]), (.obj [("role", (.lit (str "thinking"))), ("content", (.union [.str, (.arr .any)])), ("signature", (.union [.undef, .str])), ("redactedThinking", (.union [.undef, .str])), ("toolCalls", (.union [.undef, (.arr .any)])), ("reasoning_details", (.union [.undef, (.arr .any)])), ("metadata", (.union [.undef, (.obj [])]))]), (.obj [("role", (.lit (str "system"))), ("content", .str), ("metadata", (.union [.undef, (.obj [])]))]), (.obj [("role", (.lit (str "tool"))), ("content", .str), ("toolCallId", .str), ("metadata", (.union [.undef, (.obj [])]))])]) message'
def messageIsEmpty (message' : Val) : M Val := do
  if truthy (← (do bin .eq (← (do pure (typeOf (← (do (fun o => field o "content") message'))))) (str "string"))) then
    return (← (do bin .eq (← (do let r1 := (← (do (fun o => field o "content") message')); method .trim r1 [])) (str "")))
  if truthy (← (do isArray (← (do (fun o => field o "content") message')))) then
    return (← (do let r2 := (← (do (fun o => field o "content") message')); jsEvery r2 (fun item' _ => do
      return (← (do let a4 := (← (do bin .eq (← (do (fun o => field o "type") item')) (str "text"))); if truthy a4 then (do bin .eq (← (do let r3 := (← (do (fun o => field o "text") item')); if nullish r3 then pure .undef else method .trim r3 [])) (str "")) else pure a4)))))
  return (.bool false)
abbrev addSpaceToAnyEmptyMessages.pre (messages' : Val) (h : Heap) : Prop :=
  Is h (.arr (.union [(.obj [("role", (.lit (str "user"))), ("content", (.union [.any, .any])), ("metadata", (.union [.any, .any]))]), (.obj [("role", (.lit (str "assistant"))), ("content", (.union [.any, .any])), ("toolCalls", (.union [.any, .any])), ("usage", (.union [.any, .any])), ("metadata", (.union [.any, .any]))]), (.obj [("role", (.lit (str "thinking"))), ("content", (.union [.any, .any])), ("signature", (.union [.any, .any])), ("redactedThinking", (.union [.any, .any])), ("toolCalls", (.union [.any, .any])), ("reasoning_details", (.union [.any, .any])), ("metadata", (.union [.any, .any]))]), (.obj [("role", (.lit (str "system"))), ("content", .str), ("metadata", (.union [.any, .any]))]), (.obj [("role", (.lit (str "tool"))), ("content", .str), ("toolCallId", .str), ("metadata", (.union [.any, .any]))])])) messages'
def addSpaceToAnyEmptyMessages (messages' : Val) : M Val := do
  return (← (do let r1 := messages'; jsMap r1 (fun message' _ => do
      if truthy (← (do messageIsEmpty message')) then
        let o2 := message'
        setField o2 "content" (str " ")
      return message')))
end Alias
