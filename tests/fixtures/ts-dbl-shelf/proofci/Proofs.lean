import TsDbl
open Aeneas Aeneas.Std Result src.pricing

set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 2000000

theorem shelf_nan (min : Js.Dbl) :
    shelfPrice (Js.Dbl.lit 0x7ff8000000000000) min ⦃ r => r = min ⦄ := by
  have hn : Js.Dbl.lit 0x7ff8000000000000 = ⟨Core.F64.nan⟩ := by decide
  rw [hn]
  unfold shelfPrice
  simp [Js.Dbl.isFinite, Js.Dbl.isNaN, Core.F64.isFin, Core.F64.isNan, Core.F64.lt,
    WP.spec_ok]
