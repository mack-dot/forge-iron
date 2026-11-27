# Forge Iron Build & Proving-Speed Targets
#
# Usage:
#   make factory-heap    # Build local forge_factory.heap (never commit *.heap!)
#   make runtime         # Cleanly build frozen runtime/hol4 theories
#   make counter         # Cleanly build kernels/counter/hol4 theories
#   make test-fast       # Run fast unit + holctl tests

HOLMAKE ?= Holmake
HOL     ?= hol
TIMEOUT ?= gtimeout

BASE_HEAP = $(CAKEMLDIR)/cv_translator/cake_compile_heap
FACTORY_HEAP = $(CURDIR)/forge_factory.heap

.PHONY: runtime counter guardrail factory-heap test-fast clean-heap

runtime:
	cd runtime/hol4 && $(TIMEOUT) 1200 $(HOLMAKE) --qof -j 1 --no_prereqs \
		forge_runtimeSpecTheory.uo \
		forge_arm8ErasureTheory.uo \
		forge_shimProofTheory.uo \
		forge_frameRunnerTheory.uo \
		forge_slotUtilTheory.uo \
		forge_frame64ComposeTheory.uo

counter: runtime
	cd kernels/counter/hol4 && $(TIMEOUT) 900 $(HOLMAKE) --qof -j 1 --no_prereqs

guardrail: runtime
	cd kernels/guardrail/hol4 && $(TIMEOUT) 900 $(HOLMAKE) --qof -j 1 --no_prereqs

factory-heap: runtime
	@test -n "$(CAKEMLDIR)" || (echo "error: set CAKEMLDIR" >&2; exit 1)
	cd runtime/hol4 && $(HOL) buildheap -b "$(BASE_HEAP)" -o "$(FACTORY_HEAP)" \
		ml_translatorLib blastLib cfLib \
		forge_arm8ErasureTheory forge_shimProofTheory forge_frameRunnerTheory forge_frame64ComposeTheory
	@ls -lh "$(FACTORY_HEAP)"

test-fast:
	python3 scripts/tests/test_iron_law.py
	python3 scripts/tests/test_hol_repl.py

clean-heap:
	rm -f "$(FACTORY_HEAP)"
