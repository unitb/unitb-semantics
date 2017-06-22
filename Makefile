
.PHONY: all root logic models refinement syntax clean lines

LEAN_OPT =
LEAN_PATH = $(shell pwd):/usr/local/bin/../lib/lean/library:$(shell printenv LEAN_PATH)

all:
	LEAN_PATH=$(LEAN_PATH) lean $(LEAN_OPT) --make > errors.txt

root: logic models refinement syntax util/data/array.olean code

logic: unity/logic.olean unity/refinement.olean

code: unity/code/syntax.olean unity/code/semantics.olean

models: unity/models/nondet.olean unity/models/det.olean unity/models/simple.olean unity/models/sched.olean

refinement: unity/models/refinement/resched_data_ref.olean unity/models/refinement/split.olean unity/models/refinement/split_merge.olean unity/models/refinement/reschedule.olean

syntax: unity/syntax/exists.olean unity/syntax/simple/machine.olean

%.olean: %.lean $(shell lean $< --deps)
	LEAN_PATH=$(LEAN_PATH) lean $(LEAN_OPT) $<

clean:
	/usr/bin/find . -name "*.olean" -delete

lines:
	wc `/usr/bin/find . -name "*.lean"`
