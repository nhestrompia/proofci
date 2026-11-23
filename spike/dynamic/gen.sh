#!/bin/sh
# Regenerates Gen/ from the corpus checkouts in CORPUS (default ~/corpus).
set -e
C=${CORPUS:-$HOME/corpus}
cd "$(dirname "$0")"
A=$C/AppFlowy-Web/src/application/database-yjs
node dyn.mjs $A/chart-extended-settings.ts Unknown parseChartGroupByFieldId parseChartDecimalPlaces > Gen/Unknown.lean
node dyn.mjs $A/dashboard-private.ts Union isDashboardPrivateKeyOfUser dashboardPrivateStorageKey > Gen/Union.lean
node dyn.mjs $C/continue/core/llm/messages.ts Alias addSpaceToAnyEmptyMessages > Gen/Alias.lean
node dyn.mjs $C/continue/core/util/messageContent.ts Closure renderContextItemsWithStatus > Gen/Closure.lean
node dyn.mjs $A/fields/formula/budget.ts Budget FormulaEvaluationBudget > Gen/Budget.lean
node dyn.mjs $C/immich/web/src/lib/utils/slideshow-history.ts Slideshow SlideshowHistory > Gen/Slideshow.lean
node dyn.mjs fixtures.ts Fixtures colorIndexes bumpBoth padCode firstAbove sumIndexed halvings lastOf lastCh ruler padRight flatten > Gen/Fixtures.lean
node dyn.mjs ../../examples/ts-bank/src/ledger.ts Bank calculateFee transfer sumAmounts > Gen/Bank.lean
