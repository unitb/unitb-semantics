
.PHONY: all root logic models refinement syntax clean lines decomposition

LEAN_OPT =
LEAN_PATH = $(shell pwd):/usr/local/bin/../lib/lean/library:$(shell printenv LEAN_PATH)

all:
	LEAN_PATH=$(LEAN_PATH) lean $(LEAN_OPT) --make > errors.txt

root: logic models refinement syntax decomposition util/data/array.olean code

logic: unitb/logic/liveness.olean unitb/refinement/basic.olean

code: unitb/code/syntax.olean unitb/code/semantics.olean

models: unitb/models/nondet.olean unitb/models/det.olean unitb/models/simple.olean unitb/models/sched.olean unitb/models/ghost.olean

refinement: unitb/refinement/resched_data_ref.olean unitb/refinement/split.olean unitb/refinement/split_merge.olean unitb/refinement/reschedule.olean

syntax: unitb/syntax/exists.olean unitb/syntax/simple/machine.olean

decomposition: unitb/decomposition/component.olean

%.olean: %.lean $(shell lean $< --deps)
	LEAN_PATH=$(LEAN_PATH) lean $(LEAN_OPT) --make $<

clean:
	/usr/bin/find . -name "*.olean" -delete

lines:
	wc `/usr/bin/find . -name "*.lean"`
