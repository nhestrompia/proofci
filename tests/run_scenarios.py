"""Run the scenarios in parallel, optionally one shard of them.

    python3 -m tests.run_scenarios --shard 2/5 --jobs 4 [--output DIR] [NAME ...]
"""

from tests.test_scenarios import main

raise SystemExit(main())
